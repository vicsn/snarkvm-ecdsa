// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use rand::rngs::OsRng;
use snarkvm_algorithms::{
    crypto_hash::PoseidonSponge,
    polycommit::kzg10::UniversalParams,
    snark::varuna::{self, AHPForR1CS, CircuitProvingKey, CircuitVerifyingKey, VarunaHidingMode},
    traits::SNARK,
};
use snarkvm_circuit::{
    environment::{Assignment, Circuit},
    Environment as _,
};
use snarkvm_circuit_environment::{Eject, Inject, Mode};
use snarkvm_console::network::Testnet3 as Network;
use snarkvm_console_network::Network as _;
use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
use std::collections::BTreeMap;

use crate::circuit;
use crate::console;
use crate::Tuples;

use log::info;

//
// Aliases
// =======
//

type FS = PoseidonSponge<Fq, 2, 1>;
type VarunaInst = varuna::VarunaSNARK<Bls12_377, FS, VarunaHidingMode>;

//
// Functions
// =========
//

/// Our circuit synthesizer.
pub fn run_circuit(
    public_key: console::ECDSAPublicKey,
    signature: console::ECDSASignature,
    msg: Vec<u8>,
    compile_mode: bool,
) -> Assignment<Fr> {
    // reset circuit writer
    Circuit::reset();

    // sample msg and witness as public input
    let msg = circuit::Message::new(Mode::Public, msg.clone());

    println!(
        "public_key: {:?}, sig: {:?}",
        &public_key.public_key, &signature.signature
    );
    // sample pubkey and sig and witness as public input
    let public_key = circuit::ECDSAPublicKey::new(Mode::Public, public_key);
    let signature = circuit::ECDSASignature::new(Mode::Public, signature);

    // // run circuit
    circuit::verify_one(public_key, signature, msg, compile_mode);

    // return circuit
    Circuit::eject_assignment_and_reset()
}

/// Setup the parameters.
pub fn setup(
    num_constraints: usize,
    num_variables: usize,
    num_non_zero: usize,
) -> UniversalParams<Bls12_377> {
    // Note: you can change this to increase the size of the circuit.
    // Of course, the higher these values, the slower the prover...
    let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(
        num_constraints,
        num_variables,
        num_non_zero,
    )
    .unwrap();

    VarunaInst::universal_setup(max_degree).unwrap()
}

/// Compile the circuit.
pub fn compile(
    urs: &UniversalParams<Bls12_377>,
    msg_len: usize,
) -> (
    CircuitProvingKey<Bls12_377, VarunaHidingMode>,
    CircuitVerifyingKey<Bls12_377>,
) {
    let msg = console::sample_msg(msg_len);
    let (public_key, signature) = console::sample_pubkey_sig(&msg);

    let compile_mode = true;
    let circuit = run_circuit(public_key, signature, msg, compile_mode);

    println!("num constraints: {}", circuit.num_constraints());
    println!("num public: {}", circuit.num_public());
    println!("num private: {}", circuit.num_private());
    println!("num non-zeros: {:?}", circuit.num_nonzeros());
    VarunaInst::circuit_setup(&urs, &circuit).unwrap()
}

/// Run and prove the circuit.
pub fn prove(
    urs: &UniversalParams<Bls12_377>,
    pk: &CircuitProvingKey<Bls12_377, VarunaHidingMode>,
    tuples: Tuples,
) -> varuna::Proof<Bls12_377> {
    // Prepare the instances.
    let mut instances = Vec::new();

    let mut assignments = crossbeam::thread::scope(|s| -> Vec<Assignment<Fr>> {
        let mut assignments = Vec::new();
        let mut handles = Vec::new();

        for tuple in &tuples {
            handles.push(s.spawn(move |_| -> Assignment<Fr> {
                let (public_key, msg, signature) = tuple.clone();
                let public_key = console::ECDSAPublicKey { public_key };
                let signature = console::ECDSASignature { signature };

                let compile_mode = false;
                let mut assignment = run_circuit(public_key, signature, msg, compile_mode);

                assignment
            }));
        }

        for h in handles {
            assignments.push(h.join().unwrap());
        }

        assignments
    })
    .unwrap();

    instances.push((pk, &assignments[..]));

    // Compute the proof.
    let rng = &mut OsRng::default();
    let universal_prover = urs.to_universal_prover().unwrap();
    let fiat_shamir = Network::varuna_fs_parameters();
    let proof = VarunaInst::prove_batch(&universal_prover, fiat_shamir, &instances, rng).unwrap();

    proof
}

/// Verify a proof.
pub fn verify_proof(
    urs: &UniversalParams<Bls12_377>,
    vk: &CircuitVerifyingKey<Bls12_377>,
    tuples: &Tuples,
    proof: &varuna::Proof<Bls12_377>,
) {
    // Note: this is a hacky way of formatting public inputs,
    // we shouldn't have to run the circuit to do that.
    let mut inputs = Vec::with_capacity(tuples.len());
    for tuple in tuples {
        let (public_key, msg, signature) = tuple.clone();
        let public_key = console::ECDSAPublicKey { public_key };
        let signature = console::ECDSASignature { signature };

        let msg = circuit::Message::new(Mode::Public, msg.clone());
        let public_key = circuit::ECDSAPublicKey::new(Mode::Public, public_key);
        let signature = circuit::ECDSASignature::new(Mode::Public, signature);

        let assignment = Circuit::eject_assignment_and_reset();

        // prepare input
        let mut inputs_i = vec![];
        for (_, input) in assignment.public_inputs() {
            inputs_i.push(*input);
        }
        inputs.push(inputs_i);
    }

    // verify
    let mut keys_to_inputs = BTreeMap::new();
    keys_to_inputs.insert(vk, &inputs[..]);
    let fiat_shamir = Network::varuna_fs_parameters();
    let universal_verifier = urs.to_universal_verifier().unwrap();

    // Note: same comment here, verify_batch could verify several proofs instead of one ;)
    let result =
        VarunaInst::verify_batch(&universal_verifier, fiat_shamir, &keys_to_inputs, proof).unwrap();
    assert!(result);
}
