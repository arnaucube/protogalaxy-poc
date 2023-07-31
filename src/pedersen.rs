/// pedersen.rs file adapted from https://github.com/arnaucube/nova-study
use ark_ec::{CurveGroup, Group};
use ark_std::{rand::Rng, UniformRand};
use std::marker::PhantomData;

use crate::utils::{vec_add, vec_scalar_mul};

use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::Absorb;

pub struct Proof<C: CurveGroup> {
    R: C,
    u_: Vec<C::ScalarField>,
    ru_: C::ScalarField,
}

pub struct Params<C: CurveGroup> {
    h: C,
    pub generators: Vec<C::Affine>,
}

pub struct Pedersen<C: CurveGroup>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    _c: PhantomData<C>,
}

impl<C: CurveGroup> Pedersen<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let h_scalar = C::ScalarField::rand(rng);
        let g: C = C::generator();
        let generators: Vec<C::Affine> = vec![C::Affine::rand(rng); max];
        let params: Params<C> = Params::<C> {
            h: g.mul(h_scalar),
            generators,
        };
        params
    }

    pub fn commit(
        params: &Params<C>,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField, // random value is provided, in order to be choosen by other parts of the protocol
    ) -> Commitment<C> {
        let cm = params.h.mul(r) + C::msm(&params.generators[..v.len()], v).unwrap();
        Commitment::<C>(cm)
    }

    pub fn prove(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: &Commitment<C>, // TODO maybe it makes sense to not have a type wrapper and use directly C
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Proof<C> {
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenge_vec(v.len());

        let R: C = params.h.mul(r1) + C::msm(&params.generators, &d).unwrap();

        transcript.add_point(&cm.0);
        transcript.add_point(&R);
        let e = transcript.get_challenge();

        let u_ = vec_add(&vec_scalar_mul(v, &e), &d);
        let ru_ = e * r + r1;

        Proof::<C> { R, u_, ru_ }
    }
    pub fn verify(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField, C>,
        cm: Commitment<C>,
        proof: Proof<C>,
    ) -> bool {
        // r1, d just to match Prover's transcript
        transcript.get_challenge(); // r_1
        transcript.get_challenge_vec(proof.u_.len()); // d

        transcript.add_point(&cm.0);
        transcript.add_point(&proof.R);
        let e = transcript.get_challenge();
        let lhs = proof.R + cm.0.mul(e);
        let rhs = params.h.mul(proof.ru_) + C::msm(&params.generators, &proof.u_).unwrap();
        if lhs != rhs {
            return false;
        }
        true
    }
}

#[derive(Clone, Debug)]
pub struct Commitment<C: CurveGroup>(pub C);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::poseidon_test_config;
    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    fn test_pedersen_vector() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<G1Projective>::new_params(&mut rng, n);
        let poseidon_config = poseidon_test_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::commit(&params, &v, &r);
        let proof = Pedersen::prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = Pedersen::verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }
}
