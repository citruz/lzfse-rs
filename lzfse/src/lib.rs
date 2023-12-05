//! Rust bindings for the LZFSE reference implementation
//!
//! https://github.com/lzfse/lzfse
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

extern crate libc;
extern crate lzfse_sys as ffi;

use libc::size_t;

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
            output.as_mut_ptr() as *mut _,
            output.len() as size_t,
            input.as_ptr() as *const _,
            input.len() as size_t,
            0 as *mut _,
        ) as usize
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
            output.as_mut_ptr() as *mut _,
            output.len() as size_t,
            input.as_ptr() as *const _,
            input.len() as size_t,
            0 as *mut _,
        ) as usize
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
}
