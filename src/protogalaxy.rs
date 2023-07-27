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

#[derive(Clone, Debug)]
pub struct CommittedInstance<C: CurveGroup> {
    phi: Commitment<C>,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
}

#[derive(Clone, Debug)]
pub struct Witness<C: CurveGroup> {
    w: Vec<C::ScalarField>,
    r_w: C::ScalarField,
}

#[derive(Clone, Debug)]
pub struct Folding<C: CurveGroup> {
    _phantom: PhantomData<C>,
}
impl<C: CurveGroup> Folding<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    // WIP naming of functions
    pub fn prover(
        tr: &mut Transcript<C::ScalarField, C>,
        pedersen_params: &PedersenParams<C>,
        r1cs: R1CS<C::ScalarField>,
        // running instance
        instance: CommittedInstance<C>,
        w: Witness<C>,
        // incomming instances
        vec_instances: Vec<CommittedInstance<C>>,
        vec_w: Vec<Witness<C>>,
    ) {
        let t = instance.betas.len();
        let n = r1cs.A[0].len();

        let delta = tr.get_challenge();

        let deltas = powers_of_beta(delta, t);

        let f_w = eval_f(&r1cs, &w.w);
        dbg!(w.w.len());
        dbg!(f_w.len());
        dbg!(n);

        // F(X)
        let mut F_X: SparsePolynomial<C::ScalarField> = SparsePolynomial::zero();
        for i in 0..n {
            let lhs = pow_i_over_x::<C::ScalarField>(i, &instance.betas, &deltas);
            let curr = &lhs * f_w[i];
            F_X = F_X.add(curr);
        }
        // TODO return F(X)

        let alpha = tr.get_challenge();
        // eval F(alpha)
        let F_alpha = F_X.evaluate(&alpha);

        // betas*
        let betas_star: Vec<C::ScalarField> = instance
            .betas
            .iter()
            .zip(
                deltas
                    .iter()
                    .map(|delta_i| alpha * delta_i)
                    .collect::<Vec<C::ScalarField>>(),
            )
            .map(|(beta_i, delta_i_alpha)| *beta_i + delta_i_alpha)
            .collect();

        // sanity check: check that the new randomized instnace (the original instance but with
        // 'refreshed' randomness) satisfies the relation.
        assert!(check_instance(
            r1cs,
            CommittedInstance {
                phi: instance.phi,
                betas: betas_star,
                e: F_alpha,
            },
            w.clone(),
        ));
    }
}

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

#[derive(Clone, Debug)]
pub struct R1CS<F: PrimeField> {
    pub A: Vec<Vec<F>>,
    pub B: Vec<Vec<F>>,
    pub C: Vec<Vec<F>>,
}

// f(w) in R1CS context
fn eval_f<F: PrimeField>(r1cs: &R1CS<F>, w: &Vec<F>) -> Vec<F> {
    let AzBz = hadamard(&mat_vec_mul(&r1cs.A, &w), &mat_vec_mul(&r1cs.B, &w));
    let Cz = mat_vec_mul(&r1cs.C, &w);
    let f_w = vec_sub(&AzBz, &Cz);
    f_w
}

fn check_instance<C: CurveGroup>(
    r1cs: R1CS<C::ScalarField>,
    instance: CommittedInstance<C>,
    w: Witness<C>,
) -> bool {
    let n = 2_u64.pow(instance.betas.len() as u32) as usize;
    dbg!(n);
    dbg!(w.w.len());

    let f_w = eval_f(&r1cs, &w.w); // f(w)
    dbg!(f_w.len());

    let mut r = C::ScalarField::zero();
    for i in 0..n {
        r += pow_i(i, &instance.betas) * f_w[i];
    }
    if instance.e == r {
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon_test_config;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_std::One;
    use ark_std::UniformRand;

    pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
        let mut R: Vec<Vec<F>> = vec![Vec::new(); M.len()];
        for i in 0..M.len() {
            R[i] = vec![F::zero(); M[i].len()];
            for j in 0..M[i].len() {
                R[i][j] = F::from(M[i][j] as u64);
            }
        }
        R
    }
    pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
        let mut r: Vec<F> = vec![F::zero(); z.len()];
        for i in 0..z.len() {
            r[i] = F::from(z[i] as u64);
        }
        r
    }

    pub fn get_test_r1cs<F: PrimeField>() -> R1CS<F> {
        // R1CS for: x^3 + x + 5 = y (example from article
        // https://www.vitalik.ca/general/2016/12/10/qap.html )
        let A = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 1, 0, 0, /**/ 0, 0],
            vec![0, 1, 0, 0, 1, 0, /**/ 0, 0],
            vec![5, 0, 0, 0, 0, 1, /**/ 0, 0],
            //
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
        ]);
        let B = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 1, 0, 0, 0, 0, /**/ 0, 0],
            vec![1, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![1, 0, 0, 0, 0, 0, /**/ 0, 0],
            //
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
        ]);
        let C = to_F_matrix::<F>(vec![
            vec![0, 0, 0, 1, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 1, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 1, /**/ 0, 0],
            vec![0, 0, 1, 0, 0, 0, /**/ 0, 0],
            //
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
            vec![0, 0, 0, 0, 0, 0, /**/ 0, 0],
        ]);

        let r1cs = R1CS::<F> { A, B, C };
        r1cs
    }

    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        // z = (1, io, w)
        to_F_vec(vec![
            1,
            input,
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
            0,                                 // pad to pow of 2
            0,
        ])
    }

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

    #[test]
    fn test_eval_f() {
        let r1cs = get_test_r1cs::<Fr>();
        let mut z = get_test_z::<Fr>(3);

        let f_w = eval_f(&r1cs, &z);
        assert!(is_zero_vec(&f_w));

        z[1] = Fr::from(111);
        let f_w = eval_f(&r1cs, &z);
        assert!(!is_zero_vec(&f_w));
    }

    #[test]
    fn test_fold_prover() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config = poseidon_test_config::<Fr>();

        let r1cs = get_test_r1cs::<Fr>();
        let mut z = get_test_z::<Fr>(3);

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let n = z.len();
        let t = log2(n) as usize;
        dbg!(n);
        dbg!(t);

        let beta = Fr::rand(&mut rng);
        let betas = powers_of_beta(beta, t);

        let witness = Witness::<G1Projective> {
            w: z, // WIP
            r_w: Fr::rand(&mut rng),
        };
        let phi = Pedersen::<G1Projective>::commit(&pedersen_params, &witness.w, &witness.r_w);
        let instance = CommittedInstance::<G1Projective> {
            phi,
            betas,
            e: Fr::zero(),
        };

        Folding::<G1Projective>::prover(
            &mut transcript_p,
            &pedersen_params,
            r1cs,
            instance,
            witness,
            Vec::new(),
            Vec::new(),
        );
    }
}
