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

extern crate lzfse_sys as ffi;

use std::ffi::c_void;
use std::{alloc, mem, ptr};

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

fn scratch_layout(size: usize) -> alloc::Layout {
    debug_assert_ne!(size, 0);
    let array_layout = alloc::Layout::array::<u8>(size).expect("scratch size fits in an isize");
    // lzfse does not document the alignment requirement of the scratch buffer.
    // It appears to require alignment to the size of a pointer, but we'll be safe and overalign it
    // to 16 bytes
    array_layout
        .align_to(mem::align_of::<*mut u8>().max(16))
        .unwrap()
}

pub struct EncodeScratch {
    buf: *mut u8,
}

impl Drop for EncodeScratch {
    fn drop(&mut self) {
        let layout = Self::layout();
        unsafe {
            // SAFETY:
            //  - self.buf was allocated with the same layout
            //    - the scratch size function _must_ return the same value every time, and does
            //  - this type owns the allocation, and the pointer will never be used again
            alloc::dealloc(self.buf, layout);
        }
    }
}

impl EncodeScratch {
    pub fn new() -> Self {
        let layout = Self::layout();
        Self {
            buf: unsafe { alloc::alloc(layout) },
        }
    }

    fn layout() -> alloc::Layout {
        let size = unsafe { ffi::lzfse_encode_scratch_size() };
        scratch_layout(size)
    }

    fn as_mut_ptr(&mut self) -> *mut c_void {
        self.buf.cast()
    }
}

pub struct DecodeScratch {
    buf: *mut u8,
}

impl Drop for DecodeScratch {
    fn drop(&mut self) {
        let layout = Self::layout();
        unsafe {
            // SAFETY:
            //  - self.buf was allocated with the same layout
            //    - the scratch size function _must_ return the same value every time, and does
            //  - this type owns the allocation, and the pointer will never be used again
            alloc::dealloc(self.buf, layout);
        }
    }
}

impl DecodeScratch {
    pub fn new() -> Self {
        let layout = Self::layout();
        Self {
            buf: unsafe { alloc::alloc(layout) },
        }
    }

    fn layout() -> alloc::Layout {
        let size = unsafe { ffi::lzfse_decode_scratch_size() };
        scratch_layout(size)
    }

    fn as_mut_ptr(&mut self) -> *mut c_void {
        self.buf.cast()
    }
}

pub fn encode_buffer_scratch(
    input: &[u8],
    output: &mut [u8],
    scratch: &mut EncodeScratch,
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

pub fn decode_buffer_scratch(
    input: &[u8],
    output: &mut [u8],
    scratch: &mut DecodeScratch,
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

        let mut scratch_encode = EncodeScratch::new();
        let bytes_out =
            encode_buffer_scratch(&input[..], &mut compressed[..], &mut scratch_encode).unwrap();
        assert_ne!(bytes_out, 0);

        let mut scratch_decode = DecodeScratch::new();
        // need to allocate 1 byte more since lzfse returns input.len() if the buffer is too small
        let mut uncompressed = vec![0; input.len() + 1];
        let bytes_in = decode_buffer_scratch(
            &compressed[0..bytes_out],
            &mut uncompressed[..],
            &mut scratch_decode,
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

        let mut encode_scratch = EncodeScratch::new();
        let bytes_out =
            encode_buffer_scratch(&input[..], &mut compressed[..], &mut encode_scratch).unwrap();
        assert_ne!(bytes_out, 0);

        // this is one byte too small
        let mut uncompressed = vec![0; input.len()];
        let mut decode_scratch = DecodeScratch::new();
        let result = decode_buffer_scratch(
            &compressed[0..bytes_out],
            &mut uncompressed[..],
            &mut decode_scratch,
        );

        assert_eq!(result, Err(Error::BufferTooSmall));
    }

    #[test]
    fn encode_buffer_to_small_scratch() {
        let input = [0xC0, 0xFF, 0xEE, 0xBA, 0xBE];
        let max_outlen = input.len();
        let mut compressed = vec![0; max_outlen];

        let mut scratch = EncodeScratch::new();
        // this is not compressible
        let result = encode_buffer_scratch(&input[..], &mut compressed[..], &mut scratch);
        assert_eq!(result, Err(Error::CompressFailed));
    }
}
