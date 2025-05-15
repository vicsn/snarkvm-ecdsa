use bitcoin::secp256k1::SecretKey;
use ecdsa::hazmat::bits2field;
use ecdsa::signature::DigestVerifier;

//use ecdsa::SigningKey;
use k256::ecdsa::{Signature, SigningKey, VerifyingKey};
use k256::elliptic_curve::Field;
use rand::rngs::OsRng;
use rand::{thread_rng, RngCore};
use sha3::{Digest, Keccak256};
use snarkvm_console_network::prelude::Uniform;

//
// Data structures
// ===============
//

#[derive(Clone)]
pub struct ECDSAPublicKey {
    pub public_key: k256::ecdsa::VerifyingKey,
}

#[derive(Clone)]
pub struct ECDSASignature {
    pub signature: k256::ecdsa::Signature,
}

//
// Sampling functions
// ==================
//
// These are useful as dummy values when we just want to compile the circuit
// (and don't care about the assignment).
//

/// Samples a message of length `size`.
pub fn sample_msg(size: usize) -> Vec<u8> {
    let rng = &mut OsRng::default();
    let mut res = Vec::with_capacity(size);
    for _ in 0..size {
        //res.push(u8::rand(rng));
        res.push(0);
    }
    res
}

/// Samples a public key and signature based on a message
pub fn sample_pubkey_sig(msg: &[u8]) -> (ECDSAPublicKey, ECDSASignature) {
    // generate keypair
    let rng = &mut OsRng::default();
    let secret_key = k256::ecdsa::SigningKey::random(rng);
    let public_key = secret_key.verifying_key().clone();

    let mut hasher = crate::double_sha256::DoubleSha256::new();
    hasher.update(&msg);
    println!("console hash {:?}", hasher.finalize());

    // hash bytes
    let mut hasher = crate::double_sha256::DoubleSha256::new();
    hasher.update(&msg);

    // sign
    let (signature, _) = secret_key.sign_digest_recoverable(hasher.clone()).unwrap();

    (ECDSAPublicKey { public_key }, ECDSASignature { signature })
}

/// Generates `num` tuples of (public key, msg, signature) with messages of length `msg_len`.
pub fn generate_signatures(msg_len: usize, num: usize) -> Vec<(VerifyingKey, Vec<u8>, Signature)> {
    let mut res = vec![];

    for _ in 0..num {
        // generate keypair
        let secret_key: SigningKey = SigningKey::random(&mut rand::rngs::OsRng);
        let public_key = secret_key.verifying_key();

        // generate msg_len random bytes
        let mut msg = vec![0u8; msg_len];
        //thread_rng().fill_bytes(&mut msg);

        // hash msg
        let mut hasher = crate::double_sha256::DoubleSha256::new();
        hasher.update(&msg);

        //println!("keccark hash: {:?}", &hasher.clone().finalize());

        // generate signature
        let (signature, _) = secret_key.sign_digest_recoverable(hasher.clone()).unwrap();

        // // verify the signature
        // assert!(public_key.verify_digest(hasher, &signature).is_ok());

        res.push((public_key.clone(), msg, signature));
    }

    res
}

use bitcoin::{secp256k1::Secp256k1, Address, Network, PrivateKey, PublicKey};

/// Generate a (priv-key, pub-key, address) tuple for the chosen Bitcoin network.
pub fn generate_key_material(network: Network) -> (PrivateKey, PublicKey, Address) {
    let secp = Secp256k1::new();
    let (secret_key, secp_pub_key) = secp.generate_keypair(&mut OsRng);

    let priv_key = PrivateKey::new(secret_key, network);
    let pub_key = PublicKey::new(secp_pub_key);
    let address = Address::p2pkh(&pub_key, network);

    (priv_key, pub_key, address)
}

pub fn key_and_address_as_bytes(priv_key: &PrivateKey, addr: &Address) -> ([u8; 32], Vec<u8>) {
    let raw_secret: [u8; 32] = {
        let secret: &SecretKey = &priv_key.inner;
        secret.secret_bytes()
    };
    let addr_bytes: Vec<u8> = addr.to_string().into_bytes();

    (raw_secret, addr_bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    use bitcoin::{secp256k1, secp256k1::SecretKey, Address, Network, PrivateKey};
    use std::str::{from_utf8, FromStr};

    #[test]
    fn generates_consistent_key_material() {
        let (priv_key, pub_key, addr) = generate_key_material(Network::Testnet);
        let secp = Secp256k1::new();
        assert_eq!(pub_key, priv_key.public_key(&secp));

        let expected_addr = Address::p2pkh(&pub_key, Network::Testnet);
        assert_eq!(addr, expected_addr);

        let wif = priv_key.to_wif();
        let decoded = bitcoin::PrivateKey::from_wif(&wif).expect("decode WIF");
        assert_eq!(decoded, priv_key);
    }
}
