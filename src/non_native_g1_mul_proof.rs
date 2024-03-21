#[cfg(test)]
mod test {
    pub type Scalar = ark_bls12_381::fr::Fr;
    use crate::non_native_affine_field_var::G1Var;
    use anyhow::Error;
    use ark_bls12_381::{Bls12_381, Fq as bls12_fq, G1Affine, G1Projective};
    use ark_ec::models::bls12::Bls12;
    use ark_ec::AffineRepr;
    use ark_ff::PrimeField;
    use ark_groth16::{prepare_verifying_key, Groth16, ProvingKey};
    use ark_r1cs_std::{
        fields::{fp::FpVar, nonnative::NonNativeFieldVar},
        prelude::*,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use rand;
    use std::ops::Mul;

    #[derive(Clone)]
    struct PolyEvaluationCircuit<F: PrimeField> {
        commit: G1Projective,
        g1_generator: G1Affine,
        scalar: F,
    }

    impl<F: PrimeField> ConstraintSynthesizer<F> for PolyEvaluationCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let scalar_var = FpVar::new_witness(cs.clone(), || Ok(self.scalar))?;

            let coeff_commit_x =
                NonNativeFieldVar::<bls12_fq, F>::new_witness(cs.clone(), || Ok(self.commit.x))?;
            let coeff_commit_y =
                NonNativeFieldVar::<bls12_fq, F>::new_witness(cs.clone(), || Ok(self.commit.y))?;

            let g1_x =
                NonNativeFieldVar::<bls12_fq, F>::new_constant(cs.clone(), self.g1_generator.x)?;
            let g1_y =
                NonNativeFieldVar::<bls12_fq, F>::new_constant(cs.clone(), self.g1_generator.y)?;

            let mut g1_generator_var = G1Var::new(g1_x, g1_y);
            g1_generator_var = g1_generator_var.mul(&scalar_var)?;

            println!(
                "x values equal: {:?}",
                g1_generator_var.x.value() == coeff_commit_x.value()
            );
            println!(
                "y values equal: {:?}",
                g1_generator_var.y.value() == coeff_commit_y.value()
            );
            println!(
                "z values equal: {:?}",
                g1_generator_var.z.value()? == self.commit.z
            );

            g1_generator_var.x.enforce_equal(&coeff_commit_x)?;

            Ok(())
        }
    }

    #[test]
    fn verify_non_native_proof() -> Result<(), Error> {
        let rng = &mut rand::thread_rng();
        let scalar = Scalar::from(3);
        let g1_generator = G1Affine::generator();
        let commit = g1_generator.mul(scalar);

        let circuit = PolyEvaluationCircuit {
            commit: commit,
            g1_generator: G1Affine::generator(),
            scalar,
        };
        let proving_key: ProvingKey<Bls12_381> =
            Groth16::<Bls12<ark_bls12_381::Config>>::generate_random_parameters_with_reduction(
                circuit.clone(),
                rng,
            )?;

        println!("=======================");

        let proof = Groth16::<Bls12<ark_bls12_381::Config>>::create_random_proof_with_reduction(
            circuit,
            &proving_key,
            rng,
        )?;

        let pvk = prepare_verifying_key(&proving_key.vk);

        let verified = Groth16::<Bls12<ark_bls12_381::Config>>::verify_proof(&pvk, &proof, &[])?;
        assert!(verified, "===> Proof is not verified");

        Ok(())
    }
}
