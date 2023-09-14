use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::fields::PrimeField;
use ark_std::log2;
use ark_std::{cfg_into_iter, Zero};
use std::marker::PhantomData;

use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
};

use crate::pedersen::Commitment;
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
    #![allow(clippy::type_complexity)]
    pub fn prove(
        transcript: &mut Transcript<C::ScalarField, C>,
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C>,
        w: &Witness<C>,
        // incomming instances
        vec_instances: &[CommittedInstance<C>],
        vec_w: &[Witness<C>],
    ) -> (
        CommittedInstance<C>,
        Witness<C>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
    ) {
        let t = instance.betas.len();
        let n = r1cs.A[0].len();
        assert_eq!(w.w.len(), n);
        assert_eq!(log2(n) as usize, t);

        // TODO initialize transcript
        let delta = transcript.get_challenge();
        let deltas = powers_of_beta(delta, t);

        let f_w = eval_f(r1cs, &w.w);

        // F(X)

        let F_X: SparsePolynomial<C::ScalarField> =
            calc_f_from_btree(&f_w, &instance.betas, &deltas);

        let F_X_dense = DensePolynomial::from(F_X.clone());
        transcript.add_vec(&F_X_dense.coeffs);

        let alpha = transcript.get_challenge();

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
            &CommittedInstance {
                phi: instance.phi.clone(),
                betas: betas_star.clone(),
                e: F_alpha,
            },
            w,
        ));

        let mut ws: Vec<Vec<C::ScalarField>> = Vec::new();
        ws.push(w.w.clone());
        for wj in vec_w.iter() {
            assert_eq!(wj.w.len(), n);
            ws.push(wj.w.clone());
        }

        let k = vec_instances.len();
        let H = GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).unwrap();
        // WIP review t/d
        let EH = GeneralEvaluationDomain::<C::ScalarField>::new(t * k + 1).unwrap();
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);

        // K(X) computation in a naive way, next iterations will compute K(X) as described in Claim
        // 4.5 of the paper.
        let mut G_evals: Vec<C::ScalarField> = vec![C::ScalarField::zero(); EH.size()];
        for (hi, h) in EH.elements().enumerate() {
            // each iteration evaluates G(h)
            // inner = L_0(x) * w + \sum_k L_i(x) * w_j
            let mut inner: Vec<C::ScalarField> = vec![C::ScalarField::zero(); ws[0].len()];
            for (i, w) in ws.iter().enumerate() {
                // Li_w = Li(X) * wj
                let mut Li_w: Vec<DensePolynomial<C::ScalarField>> =
                    vec![DensePolynomial::<C::ScalarField>::zero(); w.len()];
                for (j, wj) in w.iter().enumerate() {
                    let Li_wj = &L_X[i] * *wj;
                    Li_w[j] = Li_wj;
                }
                // Li_w_h = Li_w(h) = Li(h) * wj
                let mut Liw_h: Vec<C::ScalarField> = vec![C::ScalarField::zero(); w.len()];
                for (j, _) in Li_w.iter().enumerate() {
                    Liw_h[j] = Li_w[j].evaluate(&h);
                }

                for j in 0..inner.len() {
                    inner[j] += Liw_h[j];
                }
            }
            let f_ev = eval_f(r1cs, &inner);

            let mut Gsum = C::ScalarField::zero();
            for (i, f_ev_i) in f_ev.iter().enumerate() {
                let pow_i_betas = pow_i(i, &betas_star);
                let curr = pow_i_betas * f_ev_i;
                Gsum += curr;
            }
            G_evals[hi] = Gsum;
        }
        let G_X: DensePolynomial<C::ScalarField> =
            Evaluations::<C::ScalarField>::from_vec_and_domain(G_evals.clone(), EH).interpolate();
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        // K(X) = (G(X)- F(alpha)*L_0(X)) / Z(X)
        let L0_e = &L_X[0] * F_alpha; // L0(X)*F(a) will be 0 in the native case
        let G_L0e = &G_X - &L0_e;
        // TODO move division by Z_X to the prev loop
        let (K_X, remainder) = G_L0e.divide_by_vanishing_poly(H).unwrap();
        assert!(remainder.is_zero()); // sanity check

        transcript.add_vec(&K_X.coeffs);

        let gamma = transcript.get_challenge();

        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi.0 * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi.0 * L_X[i + 1].evaluate(&gamma);
        }
        let mut w_star: Vec<C::ScalarField> = vec_scalar_mul(&w.w, &L_X[0].evaluate(&gamma));
        for i in 0..k {
            w_star = vec_add(
                &w_star,
                &vec_scalar_mul(&vec_w[i].w, &L_X[i + 1].evaluate(&gamma)),
            );
        }
        let mut r_w_star: C::ScalarField = w.r_w * L_X[0].evaluate(&gamma);
        for i in 0..k {
            r_w_star += vec_w[i].r_w * L_X[i + 1].evaluate(&gamma);
        }

        (
            CommittedInstance {
                betas: betas_star,
                phi: Commitment(phi_star),
                e: e_star,
            },
            Witness {
                w: w_star,
                r_w: r_w_star,
            },
            F_X_dense.coeffs,
            K_X.coeffs,
        )
    }

    pub fn verify(
        transcript: &mut Transcript<C::ScalarField, C>,
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C>,
        // incomming instances
        vec_instances: &[CommittedInstance<C>],
        // polys from P
        F_coeffs: Vec<C::ScalarField>,
        K_coeffs: Vec<C::ScalarField>,
    ) -> CommittedInstance<C> {
        let t = instance.betas.len();
        let n = r1cs.A[0].len();

        let delta = transcript.get_challenge();
        let deltas = powers_of_beta(delta, t);

        transcript.add_vec(&F_coeffs);

        let alpha = transcript.get_challenge();
        let alphas = all_powers(alpha, n);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e;
        for (i, F_i) in F_coeffs.iter().skip(1).enumerate() {
            F_alpha += *F_i * alphas[i + 1];
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

        let k = vec_instances.len();
        let H = GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).unwrap();
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        let K_X: DensePolynomial<C::ScalarField> =
            DensePolynomial::<C::ScalarField>::from_coefficients_vec(K_coeffs);

        transcript.add_vec(&K_X.coeffs);

        let gamma = transcript.get_challenge();

        let e_star =
            F_alpha * L_X[0].evaluate(&gamma) + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star: C = instance.phi.0 * L_X[0].evaluate(&gamma);
        for i in 0..k {
            phi_star += vec_instances[i].phi.0 * L_X[i + 1].evaluate(&gamma);
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
    for (j, beta_j) in betas.iter().enumerate() {
        let mut b_j = F::zero();
        if b[j] {
            b_j = F::one();
        }
        r *= (F::one() - b_j) + b_j * beta_j;
    }
    r
}

// lagrange_polys method from caulk: https://github.com/caulk-crypto/caulk/tree/8210b51fb8a9eef4335505d1695c44ddc7bf8170/src/multi/setup.rs#L300
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

fn calc_f_from_btree<F: PrimeField>(fw: &[F], betas: &[F], deltas: &[F]) -> SparsePolynomial<F> {
    assert_eq!(fw.len() & (fw.len() - 1), 0);
    assert_eq!(betas.len(), deltas.len());
    let mut layers: Vec<Vec<SparsePolynomial<F>>> = Vec::new();
    let leaves: Vec<SparsePolynomial<F>> = fw
        .iter()
        .enumerate()
        .map(|e| SparsePolynomial::<F>::from_coefficients_slice(&[(0, *e.1)]))
        .collect();
    layers.push(leaves.to_vec());
    let mut currentNodes = leaves.clone();
    while currentNodes.len() > 1 {
        let index = layers.len();
        let limit: usize = (2 * currentNodes.len())
            - 2usize.pow(
                (currentNodes.len() & (currentNodes.len() - 1))
                    .try_into()
                    .unwrap(),
            );
        layers.push(vec![]);
        for (i, ni) in currentNodes.iter().enumerate().step_by(2) {
            if i >= limit {
                layers[index] = currentNodes[0..limit].to_vec();
                break;
            }
            let left = ni.clone();
            let right = SparsePolynomial::<F>::from_coefficients_vec(vec![
                (0, betas[layers.len() - 2]),  // FIXME
                (1, deltas[layers.len() - 2]), // FIXME
            ])
            .mul(&currentNodes[i + 1]);

            layers[index].push(left + right);
        }
        currentNodes = layers[index].clone();
    }
    let root_index = layers.len() - 1;
    layers[root_index][0].clone()
}

#[derive(Clone, Debug)]
pub struct R1CS<F: PrimeField> {
    pub A: Vec<Vec<F>>,
    pub B: Vec<Vec<F>>,
    pub C: Vec<Vec<F>>,
}

// f(w) in R1CS context
fn eval_f<F: PrimeField>(r1cs: &R1CS<F>, w: &[F]) -> Vec<F> {
    let AzBz = hadamard(&mat_vec_mul(&r1cs.A, w), &mat_vec_mul(&r1cs.B, w));
    let Cz = mat_vec_mul(&r1cs.C, w);
    vec_sub(&AzBz, &Cz)
}

fn check_instance<C: CurveGroup>(
    r1cs: &R1CS<C::ScalarField>,
    instance: &CommittedInstance<C>,
    w: &Witness<C>,
) -> bool {
    assert_eq!(instance.betas.len(), log2(w.w.len()) as usize);

    let f_w = eval_f(r1cs, &w.w); // f(w)

    let mut r = C::ScalarField::zero();
    for (i, f_w_i) in f_w.iter().enumerate() {
        r += pow_i(i, &instance.betas) * f_w_i;
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
    fn test_eval_f() {
        let r1cs = get_test_r1cs::<Fr>();
        let mut z = get_test_z::<Fr>(3);

        let f_w = eval_f(&r1cs, &z);
        assert!(is_zero_vec(&f_w));

        z[1] = Fr::from(111);
        let f_w = eval_f(&r1cs, &z);
        assert!(!is_zero_vec(&f_w));
    }

    // k represents the number of instances to be fold, appart from the running instance
    fn prepare_inputs(
        k: usize,
    ) -> (
        Witness<G1Projective>,
        CommittedInstance<G1Projective>,
        Vec<Witness<G1Projective>>,
        Vec<CommittedInstance<G1Projective>>,
    ) {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec

        let z = get_test_z::<Fr>(3);
        let mut zs: Vec<Vec<Fr>> = Vec::new();
        for i in 0..k {
            let z_i = get_test_z::<Fr>(i + 4);
            zs.push(z_i);
        }

        let n = z.len();
        let t = log2(n) as usize;

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

        (witness, instance, witnesses, instances)
    }

    #[test]
    fn test_fold_native_case() {
        let k = 6;
        let (witness, instance, witnesses, instances) = prepare_inputs(k);
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let (folded_instance, folded_witness, F_coeffs, K_coeffs) = Folding::<G1Projective>::prove(
            &mut transcript_p,
            &r1cs,
            &instance,
            &witness,
            &instances,
            &witnesses,
        );

        // veriier
        let folded_instance_v = Folding::<G1Projective>::verify(
            &mut transcript_v,
            &r1cs,
            &instance,
            &instances,
            F_coeffs,
            K_coeffs,
        );

        // check that prover & verifier folded instances are the same values
        assert_eq!(folded_instance.phi.0, folded_instance_v.phi.0);
        assert_eq!(folded_instance.betas, folded_instance_v.betas);
        assert_eq!(folded_instance.e, folded_instance_v.e);
        assert!(!folded_instance.e.is_zero());

        // check that the folded instance satisfies the relation
        assert!(check_instance(&r1cs, &folded_instance, &folded_witness));
    }

    #[test]
    fn test_fold_various_iterations() {
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        let (mut running_witness, mut running_instance, _, _) = prepare_inputs(0);

        // fold k instances on each of num_iters iterations
        let k = 6;
        let num_iters = 10;
        for _ in 0..num_iters {
            // generate the instances to be fold
            let (_, _, witnesses, instances) = prepare_inputs(k);

            let (folded_instance, folded_witness, F_coeffs, K_coeffs) =
                Folding::<G1Projective>::prove(
                    &mut transcript_p,
                    &r1cs,
                    &running_instance,
                    &running_witness,
                    &instances,
                    &witnesses,
                );

            // veriier
            let folded_instance_v = Folding::<G1Projective>::verify(
                &mut transcript_v,
                &r1cs,
                &running_instance,
                &instances,
                F_coeffs,
                K_coeffs,
            );

            // check that prover & verifier folded instances are the same values
            assert_eq!(folded_instance.phi.0, folded_instance_v.phi.0);
            assert_eq!(folded_instance.betas, folded_instance_v.betas);
            assert_eq!(folded_instance.e, folded_instance_v.e);
            assert!(!folded_instance.e.is_zero());

            // check that the folded instance satisfies the relation
            assert!(check_instance(&r1cs, &folded_instance, &folded_witness));

            running_witness = folded_witness;
            running_instance = folded_instance;
        }
    }
}
