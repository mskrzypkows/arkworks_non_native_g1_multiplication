use ark_bls12_381::g1::Config;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    prelude::*,
};
use ark_relations::r1cs::SynthesisError;
use tracing::debug;

pub type G1Var<F> = NonNativeAffineVar<Config, F>;

#[derive(Clone, Debug)]
pub struct NonNativeAffineVar<P: SWCurveConfig, F: PrimeField>
where
    P::BaseField: PrimeField,
{
    pub x: NonNativeFieldVar<P::BaseField, F>,
    pub y: NonNativeFieldVar<P::BaseField, F>,
    pub infinity: Boolean<F>,
}

impl<P: SWCurveConfig + Clone, F: PrimeField> NonNativeAffineVar<P, F>
where
    P::BaseField: PrimeField,
{
    pub fn new(
        x: NonNativeFieldVar<P::BaseField, F>,
        y: NonNativeFieldVar<P::BaseField, F>,
    ) -> Self {
        Self::new_inner(x, y)
    }

    fn new_inner(
        x: NonNativeFieldVar<P::BaseField, F>,
        y: NonNativeFieldVar<P::BaseField, F>,
    ) -> Self {
        Self {
            x,
            y,
            infinity: Boolean::<F>::FALSE,
        }
    }

    fn zero() -> Self {
        Self {
            x: NonNativeFieldVar::zero(),
            y: NonNativeFieldVar::zero(),
            infinity: Boolean::<F>::TRUE,
        }
    }

    fn is_zero(&self) -> &Boolean<F> {
        &self.infinity
    }

    pub fn mul(&mut self, scalar_var: &FpVar<F>) -> Result<(), SynthesisError> {
        self.mul_num_bits(scalar_var, 255)
    }

    /// Multiplication by double-and-add, iterative, index increasing
    /// https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
    pub fn mul_num_bits(
        &mut self,
        scalar_var: &FpVar<F>,
        num_bits: u32,
    ) -> Result<(), SynthesisError> {
        debug!("mul num_bits: {num_bits}");
        let bits = scalar_var.to_bits_le()?;

        let mut res = Self::zero();
        let mut doubled = self.clone();

        let mut bit_processed = 0;
        for bit in bits.iter().take(num_bits as usize) {
            bit_processed += 1;
            debug!("bit: {bit_processed}");

            let mut res_clone = res.clone();
            res_clone.add_assign(&doubled)?;

            res = bit.select(&res_clone, &res)?;
            doubled.double_in_place_non_zero()?;
        }

        *self = res;
        Ok(())
    }

    fn double_in_place_non_zero(&mut self) -> Result<(), SynthesisError> {
        let x1 = &self.x;
        let y1 = &self.y;
        let x1x1 = x1.square()?;

        // this is done for BSL12-381 curve, so the coefficient a = 0
        // the curve formula is y^2 = x^3 + 4
        let numerator = x1x1.double()? + x1x1;
        let denominator = y1.double()?;
        let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;

        let x3 = lambda.square()? - x1.double()?;
        self.y = lambda * (x1 - x3.clone()) - y1;
        self.x = x3;
        Ok(())
    }

    fn add_assign(&mut self, other: &Self) -> Result<(), SynthesisError> {
        let other_clone_for_self_zero = other.clone();
        let mut self_clone = self.clone();
        self_clone.add_assign_non_zero_not_equal_points(other)?;

        *self = self
            .is_zero()
            .select(&other_clone_for_self_zero, &self_clone)?;
        Ok(())
    }

    fn add_assign_non_zero_not_equal_points(&mut self, other: &Self) -> Result<(), SynthesisError> {
        let x1 = &self.x;
        let x2 = &other.x;
        let y1 = &self.y;
        let y2 = &other.y;

        let numerator = y2 - y1;
        let denominator = x2 - x1;
        // assuming we're not adding the same points, so the denominator is not zero
        let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;

        let x3 = lambda.square()? - x1 - x2;
        self.y = lambda * (x1 - &x3) - y1;
        self.x = x3;

        Ok(())
    }
}

impl<P: SWCurveConfig, F: PrimeField> EqGadget<F> for NonNativeAffineVar<P, F>
where
    P::BaseField: PrimeField,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let is_x_eq = self.x.is_eq(&other.x)?;
        let is_y_eq = self.y.is_eq(&other.y)?;
        is_x_eq.and(&is_y_eq)
    }
}

impl<P: SWCurveConfig + Clone, F: PrimeField> CondSelectGadget<F> for NonNativeAffineVar<P, F>
where
    P::BaseField: PrimeField,
{
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = NonNativeFieldVar::<P::BaseField, F>::conditionally_select(
            cond,
            &true_value.x,
            &false_value.x,
        )?;
        let y = NonNativeFieldVar::<P::BaseField, F>::conditionally_select(
            cond,
            &true_value.y,
            &false_value.y,
        )?;
        let infinity =
            Boolean::<F>::conditionally_select(cond, &true_value.infinity, &false_value.infinity)?;

        Ok(Self { x, y, infinity })
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use anyhow::Error;
    use ark_bls12_381::{Fq as bls12_fq, G1Affine};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::BigInteger;
    use ark_relations::r1cs::ConstraintSystem;
    use std::ops::Mul;
    type Scalar = ark_bls12_381::fr::Fr;

    #[test]
    fn add_two_different_points() -> Result<(), Error> {
        let cs = ConstraintSystem::<Scalar>::new_ref();
        let g1_generator = G1Affine::generator();
        let point_1 = g1_generator.mul(Scalar::from(5)).into_affine();
        let point_2 = g1_generator.mul(Scalar::from(7)).into_affine();

        let p_1_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_1.x))?;
        let p_1_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_1.y))?;
        let p_2_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_2.x))?;
        let p_2_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_2.y))?;

        let mut non_native_p1 = G1Var::new(p_1_x, p_1_y);
        let non_native_p2 = G1Var::new(p_2_x, p_2_y);

        let sum_native = point_1 + point_2;
        let sum_native_affine = sum_native.into_affine();
        non_native_p1.add_assign_non_zero_not_equal_points(&non_native_p2)?;

        assert_eq!(sum_native_affine.x, non_native_p1.x.value()?);
        assert_eq!(sum_native_affine.y, non_native_p1.y.value()?);

        Ok(())
    }

    #[test]
    fn add_two_equal_points() -> Result<(), Error> {
        let cs = ConstraintSystem::<Scalar>::new_ref();
        let g1_generator = G1Affine::generator();
        let point_1 = g1_generator.mul(Scalar::from(5)).into_affine();
        let g1_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_1.x))?;
        let g1_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(point_1.y))?;

        let doubled_native = point_1 + point_1;
        let doubled_native_affine = doubled_native.into_affine();

        let mut g1_var = G1Var::new(g1_x, g1_y);
        g1_var.double_in_place_non_zero()?;

        assert_eq!(doubled_native_affine.x, g1_var.x.value()?);
        assert_eq!(doubled_native_affine.y, g1_var.y.value()?);

        Ok(())
    }

    #[test]
    fn multiply_non_native_affine_var_by_scalars() -> Result<(), Error> {
        multiply_by_scalar(1)?;
        multiply_by_scalar(2)?;
        multiply_by_scalar(13)?;
        multiply_by_scalar(25)?;
        Ok(())
    }

    fn multiply_by_scalar(scalar_value: u64) -> Result<(), Error> {
        let scalar = Scalar::from(scalar_value);
        let g1_generator = G1Affine::generator();
        let g1_multiplied_native = g1_generator.mul(scalar).into_affine();

        let cs = ConstraintSystem::<Scalar>::new_ref();

        let g1_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.x))?;
        let g1_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.y))?;

        let mut g1_generator_var = G1Var::new(g1_x, g1_y);
        let scalar_var = FpVar::new_witness(cs.clone(), || Ok(scalar))?;
        g1_generator_var.mul_num_bits(&scalar_var, scalar.into_bigint().num_bits())?;

        assert_eq!(g1_generator_var.x.value()?, g1_multiplied_native.x);
        assert_eq!(g1_generator_var.y.value()?, g1_multiplied_native.y);

        Ok(())
    }
}