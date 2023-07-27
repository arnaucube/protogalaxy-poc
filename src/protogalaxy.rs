use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::fields::PrimeField;
use ark_std::log2;
use ark_std::{One, Zero};
use std::marker::PhantomData;
use std::ops::Add;

use ark_poly::{univariate::SparsePolynomial, Polynomial};

use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen, Proof as PedersenProof};
use crate::transcript::Transcript;
use crate::utils::*;

// naive impl of pow_i for betas, assuming that betas=(b, b^2, b^4, ..., b^{2^{t-1}})
fn pow_i<F: PrimeField>(i: usize, betas: &Vec<F>) -> F {
    // WIP check if makes more sense to do it with ifs instead of arithmetic

    let n = 2_u64.pow(betas.len() as u32);
    let b = bit_decompose(i as u64, n as usize);

    let mut r: F = F::one();
    for (j, beta_i) in betas.iter().enumerate() {
        let mut b_j = F::zero();
        if b[j] {
            b_j = F::one();
        }
        r *= (F::one() - b_j) + b_j * betas[j];
    }
    r
}

fn pow_i_over_x<F: PrimeField>(i: usize, betas: &Vec<F>, deltas: &Vec<F>) -> SparsePolynomial<F> {
    assert_eq!(betas.len(), deltas.len());

    let n = 2_u64.pow(betas.len() as u32);
    let b = bit_decompose(i as u64, n as usize);

    let mut r: SparsePolynomial<F> =
        SparsePolynomial::<F>::from_coefficients_vec(vec![(0, F::one())]); // start with r(x) = 1
    for (j, beta_i) in betas.iter().enumerate() {
        if b[j] {
            let curr: SparsePolynomial<F> =
                SparsePolynomial::<F>::from_coefficients_vec(vec![(0, betas[j]), (1, deltas[j])]);
            r = r.mul(&curr);
        }
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon_test_config;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::One;
    use ark_std::UniformRand;

    #[test]
    fn test_pow_i() {
        let mut rng = ark_std::test_rng();
        let t = 4;
        let n = 16;
        let beta = Fr::rand(&mut rng);
        let betas = powers_of_beta(beta, t);
        let not_betas = all_powers(beta, n);

        for i in 0..n {
            assert_eq!(pow_i(i, &betas), not_betas[i]);
        }
    }

    #[test]
    fn test_pow_i_over_x() {
        let mut rng = ark_std::test_rng();
        let t = 3;
        let n = 8;
        // let beta = Fr::rand(&mut rng);
        // let delta = Fr::rand(&mut rng);
        let beta = Fr::from(3);
        let delta = Fr::from(5);
        let betas = powers_of_beta(beta, t);
        let deltas = powers_of_beta(delta, t);

        // for i in 0..n {
        //     dbg!(pow_i_over_x(i, &betas, &deltas));
        // }
    }
}
