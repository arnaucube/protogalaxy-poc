use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::fields::PrimeField;
use ark_std::log2;
use ark_std::{cfg_into_iter, One, Zero};
use std::marker::PhantomData;
use std::ops::{Add, Mul};

use ark_ff::{batch_inversion, FftField};
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
};

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
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: CommittedInstance<C>,
        w: Witness<C>,
        // incomming instances
        vec_instances: Vec<CommittedInstance<C>>,
        vec_w: Vec<Witness<C>>,
    ) -> (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        CommittedInstance<C>,
        Witness<C>,
    ) {
        let t = instance.betas.len();
        let n = r1cs.A[0].len();

        // TODO initialize transcript
        let delta = tr.get_challenge();
        let deltas = powers_of_beta(delta, t);

        let f_w = eval_f(&r1cs, &w.w);
        // println!("is f(w) {:?}", f_w);

        // F(X)
        let mut F_X: SparsePolynomial<C::ScalarField> = SparsePolynomial::zero();
        for i in 0..n {
            let lhs = pow_i_over_x::<C::ScalarField>(i, &instance.betas, &deltas);
            let curr = &lhs * f_w[i];
            F_X = F_X.add(curr);
        }

        let F_X_dense = DensePolynomial::from(F_X.clone());
        tr.add_vec(&F_X_dense.coeffs);

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
                phi: instance.phi.clone(),
                betas: betas_star.clone(),
                e: F_alpha,
            },
            w.clone(),
        ));

        let gamma = tr.get_challenge();

        // TODO WIP compute G(X) & K(X)
        let G_evals: Vec<C::ScalarField> = vec![C::ScalarField::zero(); n];
        let G_X: DensePolynomial<C::ScalarField> =
            Evaluations::<C::ScalarField>::from_vec_and_domain(G_evals.clone(), H).interpolate();
        // dbg!(&G_X);
        let (K_X, remainder) = G_X.divide_by_vanishing_poly(H).unwrap();
        // dbg!(&K_X);
        assert!(remainder.is_zero());

        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();

        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi.0 * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi.0 * L_X[i].evaluate(&gamma);
        }
        let mut w_star: Vec<C::ScalarField> = vec_scalar_mul(&w.w, &L_X[0].evaluate(&gamma));
        for i in 0..k {
            w_star = vec_add(
                &w_star,
                &vec_scalar_mul(&vec_w[i].w, &L_X[i].evaluate(&gamma)),
            );
        }

        (
            F_X_dense.coeffs,
            K_X.coeffs,
            CommittedInstance {
                betas: betas_star,
                phi: Commitment(phi_star),
                e: e_star,
            },
            Witness {
                w: w_star,
                r_w: w.r_w,
            },
        )
    }

    pub fn verifier(
        tr: &mut Transcript<C::ScalarField, C>,
        pedersen_params: &PedersenParams<C>,
        r1cs: R1CS<C::ScalarField>,
        // running instance
        instance: CommittedInstance<C>,
        // incomming instances
        vec_instances: Vec<CommittedInstance<C>>,
        // polys from P
        F_coeffs: Vec<C::ScalarField>,
        K_coeffs: Vec<C::ScalarField>,
    ) -> CommittedInstance<C> {
        let t = instance.betas.len();
        let n = r1cs.A[0].len();

        let delta = tr.get_challenge();
        let deltas = powers_of_beta(delta, t);

        tr.add_vec(&F_coeffs);

        let alpha = tr.get_challenge();
        let alphas = all_powers(alpha, n);

        // dbg!(instance.e);
        // dbg!(F_coeffs[0]);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e;
        for (i, F_i) in F_coeffs.iter().enumerate() {
            F_alpha += *F_i * alphas[i];
        }

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

        let gamma = tr.get_challenge();

        let k = vec_instances.len();
        let domain_k = GeneralEvaluationDomain::<C::ScalarField>::new(k).unwrap();
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(domain_k);
        let Z_X: DensePolynomial<C::ScalarField> = domain_k.vanishing_polynomial().into();
        let K_X: DensePolynomial<C::ScalarField> =
            DensePolynomial::<C::ScalarField>::from_coefficients_vec(K_coeffs);
        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi.0 * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi.0 * L_X[i].evaluate(&gamma);
        }

        // return the folded instance
        CommittedInstance {
            betas: betas_star,
            phi: Commitment(phi_star),
            e: e_star,
        }
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

// method from caulk: https://github.com/caulk-crypto/caulk/tree/8210b51fb8a9eef4335505d1695c44ddc7bf8170/src/multi/setup.rs#L300
fn lagrange_polys<F: PrimeField>(domain_n: GeneralEvaluationDomain<F>) -> Vec<DensePolynomial<F>> {
    let mut lagrange_polynomials: Vec<DensePolynomial<F>> = Vec::new();

    for i in 0..domain_n.size() {
        let evals: Vec<F> = cfg_into_iter!(0..domain_n.size())
            .map(|k| if k == i { F::one() } else { F::zero() })
            .collect();
        lagrange_polynomials.push(Evaluations::from_vec_and_domain(evals, domain_n).interpolate());
    }
    lagrange_polynomials
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
    r1cs: &R1CS<C::ScalarField>,
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
    fn test_fold() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config = poseidon_test_config::<Fr>();

        let k = 5;

        let r1cs = get_test_r1cs::<Fr>();
        let mut z = get_test_z::<Fr>(3);
        let mut zs: Vec<Vec<Fr>> = Vec::new();
        for i in 0..k {
            let z_i = get_test_z::<Fr>(i + 4);
            zs.push(z_i);
        }

        // init Prover & Verifier's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let n = z.len();
        let t = log2(n) as usize;
        dbg!(n);
        dbg!(t);

        let beta = Fr::rand(&mut rng);
        let betas = powers_of_beta(beta, t);

        let witness = Witness::<G1Projective> {
            w: z.clone(), // WIP
            r_w: Fr::rand(&mut rng),
        };
        let phi = Pedersen::<G1Projective>::commit(&pedersen_params, &witness.w, &witness.r_w);
        let instance = CommittedInstance::<G1Projective> {
            phi,
            betas: betas.clone(),
            e: Fr::zero(),
        };
        // same for the other instances
        let mut witnesses: Vec<Witness<G1Projective>> = Vec::new();
        let mut instances: Vec<CommittedInstance<G1Projective>> = Vec::new();
        for i in 0..k {
            let witness_i = Witness::<G1Projective> {
                w: zs[i].clone(), // WIP
                r_w: Fr::rand(&mut rng),
            };
            let phi_i =
                Pedersen::<G1Projective>::commit(&pedersen_params, &witness_i.w, &witness_i.r_w);
            let instance_i = CommittedInstance::<G1Projective> {
                phi: phi_i,
                betas: betas.clone(),
                e: Fr::zero(),
            };
            witnesses.push(witness_i);
            instances.push(instance_i);
        }

        let (F_coeffs, K_coeffs, folded_instance, folded_witness) = Folding::<G1Projective>::prover(
            &mut transcript_p,
            &pedersen_params,
            &r1cs,
            instance.clone(),
            witness,
            instances.clone(),
            witnesses,
        );
        dbg!(&F_coeffs);

        // veriier
        let folded_instance_v = Folding::<G1Projective>::verifier(
            &mut transcript_v,
            &pedersen_params,
            r1cs.clone(), // TODO rm clone do borrow
            instance,
            instances,
            F_coeffs,
            K_coeffs,
        );

        assert_eq!(folded_instance.phi.0, folded_instance_v.phi.0);
        assert_eq!(folded_instance.betas, folded_instance_v.betas);
        assert_eq!(folded_instance.e, folded_instance_v.e);

        // assert!(check_instance(&r1cs, folded_instance, folded_witness));
    }
}
