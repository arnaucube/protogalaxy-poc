# protogalaxy-poc [![Test](https://github.com/arnaucube/protogalaxy-poc/workflows/Test/badge.svg)](https://github.com/arnaucube/protogalaxy-poc/actions?query=workflow%3ATest)

Proof of concept implementation of ProtoGalaxy (https://eprint.iacr.org/2023/1106.pdf) using [arkworks](https://github.com/arkworks-rs).

> Do not use in production.

Thanks to [Liam Eagen](https://twitter.com/LiamEagen) and [Ariel Gabizon](https://twitter.com/rel_zeta_tech) for their kind explanations.

This code has been done in the context of the research on folding schemes in [0xPARC](https://0xparc.org).

![protogalaxy img from Wikipedia](https://upload.wikimedia.org/wikipedia/commons/thumb/4/49/Stellar_Fireworks_Finale.jpg/303px-Stellar_Fireworks_Finale.jpg)

(img: protogalaxies colliding, [from Wikipedia](https://en.wikipedia.org/wiki/File:Stellar_Fireworks_Finale.jpg))

## Details
Implementation of ProtoGalaxy's scheme described in section 4 of the paper.

Current version implements the folding on prover & verifier and it works for k-to-1 instances and with multiple iterations, but it is not optimized.
Next steps in terms of implementation include: F(X) O(n) construction following Claim 4.4, compute K(X) in O(kd log(kd)M + ndkC) as described in Claim 4.5, add tests folding in multiple iterations and also in a tree approach, add the decider and integrate with some existing R1CS tooling for the R1CS & witness generation.

### Usage

Example of folding k+1 instances:
```rust
// assume we have:
// an R1CS instance 'r1cs'
// a valid witness 'w' from our running instance
// k valid 'witnesses' to be fold

// compute the committed instance for our running witness
let phi = Pedersen::<G1Projective>::commit(&pedersen_params, &witness.w, &witness.r_w);
let instance = CommittedInstance::<G1Projective> {
    phi,
    betas: betas.clone(),
    e: Fr::zero(),
};

// compute the k committed instances to be fold
let mut instances: Vec<CommittedInstance<G1Projective>> = Vec::new();
for i in 0..k {
    let phi_i =
	Pedersen::<G1Projective>::commit(&pedersen_params, &witnesses[i].w, &witnesses[i].r_w);
    let instance_i = CommittedInstance::<G1Projective> {
	phi: phi_i,
	betas: betas.clone(),
	e: Fr::zero(),
    };
    instances.push(instance_i);
}

// set the initial random betas
let beta = Fr::rand(&mut rng);
let betas = powers_of_beta(beta, t);

// Prover folds the instances and witnesses
let (F_coeffs, K_coeffs, folded_instance, folded_witness) = Folding::<G1Projective>::prover(
    &mut transcript_p,
    &r1cs,
    instance.clone(),
    witness,
    instances.clone(),
    witnesses,
);

// verifier folds the instances
let folded_instance_v = Folding::<G1Projective>::verifier(
    &mut transcript_v,
    &r1cs,
    instance,
    instances,
    F_coeffs,
    K_coeffs,
);

// check that the folded instance satisfies the relation
assert!(check_instance(&r2cs, folded_instance, folded_witness));

// now, the folded instance & witness can be folded again with n other instances.
```
(see the actual code for more details)
