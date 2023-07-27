/// transcript.rs file and adapted from https://github.com/arnaucube/nova-study
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use std::marker::PhantomData;

use ark_crypto_primitives::sponge::poseidon::{PoseidonConfig, PoseidonSponge};
use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};

pub struct Transcript<F: PrimeField + Absorb, C: CurveGroup>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    // where F is the Constraint Field (eq. C::ScalarField)
    sponge: PoseidonSponge<F>,
    _c: PhantomData<C>,
}
impl<F: PrimeField + Absorb, C: CurveGroup> Transcript<F, C>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn new(poseidon_config: &PoseidonConfig<F>) -> Self {
        let sponge = PoseidonSponge::<F>::new(poseidon_config);
        Transcript {
            sponge,
            _c: PhantomData,
        }
    }
    pub fn add(&mut self, v: &F) {
        self.sponge.absorb(&v);
    }
    pub fn add_vec(&mut self, v: &[F]) {
        self.sponge.absorb(&v);
    }
    pub fn add_point(&mut self, v: &C) {
        let v_affine = v.into_affine();
        let xy = v_affine.xy().unwrap(); // WIP
        self.sponge.absorb(&vec![xy.0, xy.1]);
    }
    pub fn get_challenge(&mut self) -> F {
        let c = self.sponge.squeeze_field_elements(1);
        self.add(&c[0]);
        c[0]
    }
    pub fn get_challenge_vec(&mut self, n: usize) -> Vec<F> {
        let c = self.sponge.squeeze_field_elements(n);
        self.sponge.absorb(&c);
        c
    }
}

use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;

// WARNING this is for test only
pub fn poseidon_test_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}
