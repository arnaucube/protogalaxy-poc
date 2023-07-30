use ark_ff::fields::PrimeField;
use ark_std::cfg_iter;

pub fn vec_add<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] + b[i];
    }
    r
}

pub fn vec_sub<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] - b[i];
    }
    r
}

pub fn vec_scalar_mul<F: PrimeField>(vec: &[F], c: &F) -> Vec<F> {
    let mut result = vec![F::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = *a * c;
    }
    result
}
pub fn is_zero_vec<F: PrimeField>(vec: &[F]) -> bool {
    for e in vec {
        if !e.is_zero() {
            return false;
        }
    }
    true
}

#[allow(clippy::needless_range_loop)]
pub fn mat_vec_mul<F: PrimeField>(M: &Vec<Vec<F>>, z: &[F]) -> Vec<F> {
    // TODO assert len
    let mut r: Vec<F> = vec![F::zero(); M.len()];
    for i in 0..M.len() {
        for j in 0..M[i].len() {
            r[i] += M[i][j] * z[j];
        }
    }
    r
}

pub fn hadamard<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect()
}

// returns (b, b^2, b^4, ..., b^{2^{t-1}}) TODO find better name
pub fn powers_of_beta<F: PrimeField>(b: F, t: usize) -> Vec<F> {
    let mut r = vec![F::zero(); t];
    r[0] = b;
    for i in 1..t {
        r[i] = r[i - 1].square();
    }
    r
}
pub fn all_powers<F: PrimeField>(a: F, n: usize) -> Vec<F> {
    let mut r = vec![F::zero(); n];
    // TODO more efficiently
    for i in 0..n {
        r[i] = a.pow([i as u64]);
    }
    r
}

pub fn bit_decompose(input: u64, n: usize) -> Vec<bool> {
    let mut res = Vec::with_capacity(n);
    let mut i = input;
    for _ in 0..n {
        res.push(i & 1 == 1);
        i >>= 1;
    }
    res
}
