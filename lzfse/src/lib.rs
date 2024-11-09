//! Rust bindings for the LZFSE reference implementation
//!
//! <https://github.com/lzfse/lzfse>
//!
//! # Example
//!
//! ```
//! use lzfse::{decode_buffer, encode_buffer};
//!
//! let input: &[u8] = &[0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE];
//!
//! // compression
//! // in the worst case lzfse will fallback to return the input uncompressed
//! // and add a magic header to indicate this. that requires 12 bytes (see lzfse_encode.c)
//! let max_outlen = input.len() + 12;
//! let mut compressed = vec![0; max_outlen];
//!
//! let bytes_out = encode_buffer(&input[..], &mut compressed[..]).unwrap();
//! assert!(bytes_out < input.len());
//!
//! // decompression
//! // need to allocate 1 byte more since lzfse returns input.len() if the buffer is too small
//! let mut uncompressed = vec![0; input.len() + 1];
//! let bytes_in = decode_buffer(&compressed[0..bytes_out], &mut uncompressed[..]).unwrap();
//!
//! assert_eq!(bytes_in, input.len());
//! assert_eq!(input[..], uncompressed[..bytes_in]);
//! ````
//!
//! # Scratch Buffer Example
//!
//! The `encode_buffer_scratch` and `decode_buffer_scratch` functions allow for encoding and decoding
//! using a scratch buffer to avoid allocations by the underlying library. This makes it possible to
//! use the Rust crate with `no_std` and a custom allocator.
//!
//! ```
//! use lzfse::{encode_buffer_scratch, decode_buffer_scratch, Scratch};
//!
//! let input: &[u8] = &[0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE,
//!                      0xF, 0xE, 0xE, 0xD, 0xF, 0xA, 0xC, 0xE];
//!
//! let mut compressed = vec![0; input.len() + 12];
//! let mut scratch = Scratch::new();
//!
//! let bytes_out = encode_buffer_scratch(&input, &mut compressed, &mut scratch).unwrap();
//! assert!(bytes_out < input.len());
//!
//! let mut uncompressed = vec![0; input.len() + 1];
//! let bytes_in = decode_buffer_scratch(&compressed[0..bytes_out], &mut uncompressed, &mut scratch).unwrap();
//!
//! assert_eq!(bytes_in, input.len());
//! assert_eq!(input[..], uncompressed[..bytes_in]);
//! ```

extern crate lzfse_sys as ffi;

use std::ffi::c_void;
use std::ptr::NonNull;
use std::sync::atomic::AtomicUsize;
use std::{alloc, cmp, mem, ptr};

/// This type represents all possible errors that can occur when decompressing data.
#[derive(PartialEq, Debug)]
pub enum Error {
    /// The buffer was not large enough for the decompressed data.
    BufferTooSmall,
    /// Decompression failed because the input was invalid.
    CompressFailed,
}

/// Compress input into byte array
pub fn encode_buffer(input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
    let out_size = unsafe {
        ffi::lzfse_encode_buffer(
            output.as_mut_ptr(),
            output.len(),
            input.as_ptr(),
            input.len(),
            ptr::null_mut(),
        )
    };

    if out_size == 0 {
        Err(Error::CompressFailed)
    } else {
        Ok(out_size)
    }
}

/// Decompress input into byte array
pub fn decode_buffer(input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
    let out_size = unsafe {
        ffi::lzfse_decode_buffer(
            output.as_mut_ptr(),
            output.len(),
            input.as_ptr(),
            input.len(),
            ptr::null_mut(),
        )
    };

    if out_size == output.len() {
        Err(Error::BufferTooSmall)
    } else {
        Ok(out_size)
    }
}

pub struct Scratch {
    buf: NonNull<u8>,
}

unsafe impl Send for Scratch {}
unsafe impl Sync for Scratch {}

impl Drop for Scratch {
    fn drop(&mut self) {
        let layout = Self::layout();
        // SAFETY: this type owns the allocation, and the pointer will never be used again
        unsafe {
            alloc::dealloc(self.buf.as_ptr(), layout);
        }
    }
}

impl Scratch {
    pub fn new() -> Self {
        let layout = Self::layout();
        let buf = unsafe { alloc::alloc(layout) };
        let buf = NonNull::new(buf).unwrap_or_else(|| alloc::handle_alloc_error(layout));
        Self { buf }
    }

    fn as_mut_ptr(&mut self) -> *mut c_void {
        self.buf.as_ptr().cast()
    }

    fn size() -> usize {
        // We could use a Once here, but we assume calling the scratch size functions is consistent and
        // cheap enough that we don't care if multiple threads try to initialize the value at the same
        // time.
        static SCRATCH_SIZE: AtomicUsize = AtomicUsize::new(0);

        let size = SCRATCH_SIZE.load(std::sync::atomic::Ordering::Relaxed);
        if size != 0 {
            return size;
        }

        // SAFETY: lzfse_encode_scratch_size and lzfse_decode_scratch_size are always safe to call
        let size = unsafe {
            cmp::max(
                ffi::lzfse_encode_scratch_size(),
                ffi::lzfse_decode_scratch_size(),
            )
        };
        SCRATCH_SIZE.store(size, std::sync::atomic::Ordering::Relaxed);
        debug_assert_ne!(size, 0);
        size
    }

    fn layout() -> alloc::Layout {
        let size = Self::size();
        // lzfse does not document the alignment requirement of the scratch buffer.
        // It appears to require alignment to the size of a pointer (the buffer is cast to a pointer to
        // a struct which contains a pointer as its largest aligned member), but we'll be safe and
        // overalign it to at least 16 bytes
        alloc::Layout::from_size_align(size, cmp::max(mem::align_of::<*mut u8>(), 16)).unwrap()
    }
}

/// Compress input into byte array using a scratch buffer
pub fn encode_buffer_scratch(
    input: &[u8],
    output: &mut [u8],
    scratch: &mut Scratch,
) -> Result<usize, Error> {
    let out_size = unsafe {
        ffi::lzfse_encode_buffer(
            output.as_mut_ptr(),
            output.len(),
            input.as_ptr(),
            input.len(),
            scratch.as_mut_ptr(),
        )
    };

    if out_size == 0 {
        Err(Error::CompressFailed)
    } else {
        Ok(out_size)
    }
}

/// Decompress input into byte array using a scratch buffer
pub fn decode_buffer_scratch(
    input: &[u8],
    output: &mut [u8],
    scratch: &mut Scratch,
) -> Result<usize, Error> {
    let out_size = unsafe {
        ffi::lzfse_decode_buffer(
            output.as_mut_ptr(),
            output.len(),
            input.as_ptr(),
            input.len(),
            scratch.as_mut_ptr(),
        )
    };

    if out_size == output.len() {
        Err(Error::BufferTooSmall)
    } else {
        Ok(out_size)
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;

    use super::*;

    #[test]
    fn round_trip() {
        let input: Vec<u8> = (0..1024).map(|_| rand::random::<u8>()).collect();
        // lzfse will fallback to return the input uncompressed and add a magic header to indicate this
        // this requires 12 byte (see lzfse_encode.c)
        let max_outlen = input.len() + 12;
        let mut compressed = vec![0; max_outlen];

        let bytes_out = encode_buffer(&input[..], &mut compressed[..]).unwrap();
        assert_ne!(bytes_out, 0);

        // need to allocate 1 byte more since lzfse returns input.len() if the buffer is too small
        let mut uncompressed = vec![0; input.len() + 1];
        let bytes_in = decode_buffer(&compressed[0..bytes_out], &mut uncompressed[..]).unwrap();

        assert_eq!(bytes_in, input.len());
        assert_eq!(input[..], uncompressed[..bytes_in]);
    }

    #[test]
    fn decode_buffer_to_small() {
        let input: Vec<u8> = (0..1024).map(|_| rand::random::<u8>()).collect();
        // lzfse will fallback to return the input uncompressed and add a magic header to indicate this
        // this requires 12 byte (see lzfse_encode.c)
        let max_outlen = input.len() + 12;
        let mut compressed = vec![0; max_outlen];

        let bytes_out = encode_buffer(&input[..], &mut compressed[..]).unwrap();
        assert_ne!(bytes_out, 0);

        // this is one byte too small
        let mut uncompressed = vec![0; input.len()];
        let result = decode_buffer(&compressed[0..bytes_out], &mut uncompressed[..]);

        assert_eq!(result, Err(Error::BufferTooSmall));
    }

    #[test]
    fn encode_buffer_to_small() {
        let input = [0xC0, 0xFF, 0xEE, 0xBA, 0xBE];
        let max_outlen = input.len();
        let mut compressed = vec![0; max_outlen];

        // this is not compressible
        let result = encode_buffer(&input[..], &mut compressed[..]);
        assert_eq!(result, Err(Error::CompressFailed));
    }

    #[test]
    fn round_trip_scratch() {
        let input: Vec<u8> = (0..1024).map(|_| rand::random::<u8>()).collect();
        // lzfse will fallback to return the input uncompressed and add a magic header to indicate this
        // this requires 12 byte (see lzfse_encode.c)
        let max_outlen = input.len() + 12;
        let mut compressed = vec![0; max_outlen];

        let mut scratch = Scratch::new();
        let bytes_out =
            encode_buffer_scratch(&input[..], &mut compressed[..], &mut scratch).unwrap();
        assert_ne!(bytes_out, 0);

        // need to allocate 1 byte more since lzfse returns input.len() if the buffer is too small
        let mut uncompressed = vec![0; input.len() + 1];
        let bytes_in = decode_buffer_scratch(
            &compressed[0..bytes_out],
            &mut uncompressed[..],
            &mut scratch,
        )
        .unwrap();

        assert_eq!(bytes_in, input.len());
        assert_eq!(input[..], uncompressed[..bytes_in]);
    }

    #[test]
    fn decode_buffer_to_small_scratch() {
        let input: Vec<u8> = (0..1024).map(|_| rand::random::<u8>()).collect();
        // lzfse will fallback to return the input uncompressed and add a magic header to indicate this
        // this requires 12 byte (see lzfse_encode.c)
        let max_outlen = input.len() + 12;
        let mut compressed = vec![0; max_outlen];

        let mut scratch = Scratch::new();
        let bytes_out =
            encode_buffer_scratch(&input[..], &mut compressed[..], &mut scratch).unwrap();
        assert_ne!(bytes_out, 0);

        // this is one byte too small
        let mut uncompressed = vec![0; input.len()];
        let result = decode_buffer_scratch(
            &compressed[0..bytes_out],
            &mut uncompressed[..],
            &mut scratch,
        );

        assert_eq!(result, Err(Error::BufferTooSmall));
    }

    #[test]
    fn encode_buffer_to_small_scratch() {
        let input = [0xC0, 0xFF, 0xEE, 0xBA, 0xBE];
        let max_outlen = input.len();
        let mut compressed = vec![0; max_outlen];

        let mut scratch = Scratch::new();
        // this is not compressible
        let result = encode_buffer_scratch(&input[..], &mut compressed[..], &mut scratch);
        assert_eq!(result, Err(Error::CompressFailed));
    }
}
