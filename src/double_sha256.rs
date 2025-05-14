use crypto_common::OutputSizeUser;
use digest::consts::U32;
use digest::generic_array::GenericArray;
use digest::Digest;
use sha2::Sha256; // Digest trait comes from sha2’s re-export

/// Bitcoin-style *double* SHA-256: `SHA256(SHA256(data))`.
#[derive(Clone, Default)]
pub struct DoubleSha256 {
    inner: Sha256, // first-round engine
}

impl OutputSizeUser for DoubleSha256 {
    type OutputSize = U32;
}

impl Digest for DoubleSha256 {
    #[inline(always)]
    fn new() -> Self {
        Self::default()
    }

    /// Stream data into the *first* SHA-256 round.
    #[inline(always)]
    fn update(&mut self, data: impl AsRef<[u8]>) {
        self.inner.update(data);
    }

    /// `SHA256(SHA256(data))`
    #[inline(always)]
    fn finalize(self) -> GenericArray<u8, Self::OutputSize> {
        let first = self.inner.finalize(); // SHA256(data)
        Sha256::digest(first) // SHA256(SHA256(data))
    }

    /// Same as `finalize`, but leave the hasher ready for new input.
    #[inline(always)]
    fn finalize_reset(&mut self) -> GenericArray<u8, Self::OutputSize> {
        // `finalize_reset` clears `inner` for us, so we can re-use it.
        let first = self.inner.finalize_reset();
        Sha256::digest(first)
    }

    /// Clear internal state.
    #[inline(always)]
    fn reset(&mut self) {
        self.inner.reset();
    }

    fn new_with_prefix(prefix: impl AsRef<[u8]>) -> Self {
        todo!("DoubleSha256::new_with_prefix is not implemented yet")
    }

    fn chain_update(self, data: impl AsRef<[u8]>) -> Self
    where
        Self: Sized,
    {
        todo!("DoubleSha256::chain_update is not implemented yet")
    }

    fn finalize_into(self, _out: &mut GenericArray<u8, Self::OutputSize>) {
        todo!("DoubleSha256::finalize_into is not implemented yet")
    }

    fn finalize_into_reset(&mut self, _out: &mut GenericArray<u8, Self::OutputSize>) {
        todo!("DoubleSha256::finalize_into_reset is not implemented yet")
    }

    fn output_size() -> usize {
        todo!("DoubleSha256::output_size is not implemented yet")
    }

    fn digest(data: impl AsRef<[u8]>) -> GenericArray<u8, Self::OutputSize> {
        todo!("DoubleSha256::digest is not implemented yet")
    }
}

#[cfg(test)]
mod tests {
    use super::DoubleSha256;
    use hex_literal::hex;
    use sha2::Digest; // pulls in the same trait we just implemented

    #[test]
    fn abc_vector() {
        let mut h = DoubleSha256::new();
        h.update(b"abc");
        let out = h.finalize();
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&out);

        assert_eq!(
            hash,
            hex!("4f8b42c22dd3729b519ba6f68d2da7cc5b2d606d05daed5ad5128cc03e6c6358")
        );
    }
}
