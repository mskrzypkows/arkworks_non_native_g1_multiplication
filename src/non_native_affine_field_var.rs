#![allow(unused)] // TODO remove when used in release code

use std::ops::BitAnd;

use ark_bls12_381::g1::Config;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    prelude::*,
    R1CSVar,
};
use ark_relations::r1cs::SynthesisError;

pub type G1Var<F> = NonNativeAffineVar<Config, F>;

#[derive(Clone, Debug)]
pub struct NonNativeAffineVar<P: SWCurveConfig, F: PrimeField>
where
    P::BaseField: PrimeField,
{
    pub x: NonNativeFieldVar<P::BaseField, F>,
    pub y: NonNativeFieldVar<P::BaseField, F>,
    pub z: NonNativeFieldVar<P::BaseField, F>,
}

impl<P: SWCurveConfig + Clone, F: PrimeField> NonNativeAffineVar<P, F>
where
    P::BaseField: PrimeField,
{
    pub fn new(
        x: NonNativeFieldVar<P::BaseField, F>,
        y: NonNativeFieldVar<P::BaseField, F>,
    ) -> Self {
        Self::new_inner(x, y, NonNativeFieldVar::one())
    }

    fn new_inner(
        x: NonNativeFieldVar<P::BaseField, F>,
        y: NonNativeFieldVar<P::BaseField, F>,
        z: NonNativeFieldVar<P::BaseField, F>,
    ) -> Self {
        Self { x, y, z }
    }

    fn zero() -> Self {
        Self::new_inner(
            NonNativeFieldVar::one(),
            NonNativeFieldVar::one(),
            NonNativeFieldVar::zero(),
        )
    }

    fn is_zero(&self) -> Result<Boolean<F>, SynthesisError> {
        self.z.is_zero()
    }

    pub fn mul(&mut self, scalar_var: &FpVar<F>) -> Result<(), SynthesisError> {
        let bits = scalar_var.to_bits_le()?;
        self.mul_internal(bits.iter().rev())
    }

    fn mul_internal<'a>(
        &mut self,
        bits_le_rev: impl Iterator<Item = &'a Boolean<F>>,
    ) -> Result<(), SynthesisError> {
        let mut res = Self::zero();
        let temp = Self::new_inner(self.x.clone(), self.y.clone(), self.z.clone());

        let mut first_positive_bit: Boolean<F> = Boolean::constant(false);
        for bit in bits_le_rev {
            res.double_in_place()?;
            res = first_positive_bit.select(&res, &Self::zero())?;

            first_positive_bit = first_positive_bit.or(bit)?;
            let mut res_clone = res.clone();
            res_clone.add_assign(temp.clone())?;

            res = bit.select(&res_clone, &res)?;
        }

        self.x = res.x;
        self.y = res.y;
        self.z = res.z;
        Ok(())
    }

    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        let mut self_clone_doubled = self.clone();
        self_clone_doubled.double_in_place_non_zero()?;

        *self = self.is_zero()?.select(self, &self_clone_doubled)?;

        Ok(())
    }

    fn double_in_place_non_zero(&mut self) -> Result<(), SynthesisError> {
        // A = X1^2
        let mut a = self.x.clone();
        a.square_in_place()?;

        // B = Y1^2
        let mut b = self.y.clone();
        b.square_in_place()?;

        // C = B^2
        let mut c: NonNativeFieldVar<P::BaseField, F> = b.clone();
        c.square_in_place()?;

        // D = 2*((X1+B)^2-A-C)
        //   = 2 * (X1 + Y1^2)^2 - A - C
        //   = 2 * 2 * X1 * Y1^2
        let d = if [1, 2].contains(&P::BaseField::extension_degree()) {
            let mut d = self.x.clone();
            d *= &b;
            d.double()?.double()?
        } else {
            unreachable!("This part of the code should not be reachable for extension degrees other than 1 or 2.");
            // let mut d = self.x.clone();
            // d += &b;
            // d.square_in_place()?;
            // d -= a.clone();
            // d -= c.clone();
            // d.double()?
        };

        // E = 3*A
        let e = a.clone() + a.double()?;

        // Z3 = 2*Y1*Z1
        self.z *= &self.y;
        self.z = self.z.double()?; // TODO replace with double_in_place after release of ark-ff > "0.4.2"

        // F = E^2
        // X3 = F-2*D
        self.x = e.clone();
        self.x.square_in_place()?;
        self.x -= &d.double()?;

        // Y3 = E*(D-X3)-8*C
        self.y = d;
        self.y -= &self.x;
        self.y *= &e;
        c = c.double()?.double()?.double()?;

        self.y -= c;

        Ok(())
    }

    fn add(mut self, other: Self) -> Result<Self, SynthesisError> {
        self.add_assign(other)?;
        Ok(self)
    }

    /// Using http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
    fn add_assign(&mut self, other: Self) -> Result<(), SynthesisError> {
        let other_clone_for_self_zero = Self {
            x: other.x.clone(),
            y: other.y.clone(),
            z: NonNativeFieldVar::one(),
        };

        let mut self_clone = self.clone();
        self_clone.add_non_zero(other);

        *self = self
            .is_zero()?
            .select(&other_clone_for_self_zero, &self_clone)?;
        Ok(())
    }

    fn add_non_zero(&mut self, other: Self) -> Result<(), SynthesisError> {
        // Z1Z1 = Z1^2
        let mut z1z1 = self.z.clone();
        z1z1.square_in_place()?;

        // U2 = X2*Z1Z1
        let mut u2 = other.x.clone();
        u2 *= &z1z1;

        // S2 = Y2*Z1*Z1Z1
        let mut s2 = self.z.clone();
        s2 *= &other.y;
        s2 *= &z1z1;

        let equal_points = self.x.is_eq(&u2)?.and(&self.y.is_eq(&s2)?)?;
        let mut self_clone_doubled = self.clone();
        self_clone_doubled.double_in_place()?;
        self.add_different_points(u2, s2);

        *self = equal_points.select(&self_clone_doubled, &self)?;

        Ok(())
    }

    fn add_different_points(
        &mut self,
        u2: NonNativeFieldVar<P::BaseField, F>,
        s2: NonNativeFieldVar<P::BaseField, F>,
    ) -> Result<(), SynthesisError> {
        // If we're adding -a and a together, self.z becomes zero as H becomes zero.

        // H = U2-X1
        let mut h = u2;
        h -= &self.x;

        // HH = H^2
        let mut hh = h.clone();
        hh.square_in_place()?;

        // I = 4*HH
        let mut i = hh;
        i = i.double()?.double()?;

        // J = -H*I
        let mut j = h.clone();
        j.negate_in_place()?;
        j *= &i;

        // r = 2*(S2-Y1)
        let mut r = s2;
        r -= &self.y;
        r = r.double()?; // TODO replace with double_in_place after release of ark-ff > "0.4.2"

        // V = X1*I
        let mut v = self.x.clone();
        v *= &i;

        // X3 = r^2 + J - 2*V
        self.x = r.square()?;
        self.x += &j;
        self.x -= &v.double()?;

        // Y3 = r*(V-X3) + 2*Y1*J
        v -= &self.x;

        self.y = self.y.double()?; // TODO replace with double_in_place after release of ark-ff > "0.4.2"
        self.y = sum_of_products::<P, F, 2>(&[r, self.y.clone()], &[v, j]);

        // Z3 = 2 * Z1 * H;
        // Can alternatively be computed as (Z1+H)^2-Z1Z1-HH, but the latter is slower.
        self.z *= &h;
        self.z = self.z.double()?; // TODO replace with double_in_place after release of ark-ff > "0.4.2"

        Ok(())
    }
}

/// Returns `sum([a_i * b_i])`.
#[inline]
fn sum_of_products<P: SWCurveConfig, F: PrimeField, const T: usize>(
    a: &[NonNativeFieldVar<P::BaseField, F>; T],
    b: &[NonNativeFieldVar<P::BaseField, F>; T],
) -> NonNativeFieldVar<P::BaseField, F>
where
    P::BaseField: PrimeField,
{
    let mut sum = NonNativeFieldVar::<P::BaseField, F>::zero();
    for i in 0..a.len() {
        sum += a[i].clone() * b[i].clone();
    }
    sum
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
        let z = NonNativeFieldVar::<P::BaseField, F>::conditionally_select(
            cond,
            &true_value.z,
            &false_value.z,
        )?;

        Ok(NonNativeAffineVar::<P, F>::new_inner(x, y, z))
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use anyhow::Error;
    use ark_bls12_381::{Bls12_381, Fq as bls12_fq, G1Affine, G1Projective};
    use ark_ec::AffineRepr;
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
        SynthesisError,
    };
    use std::ops::Mul;
    pub type Scalar = ark_bls12_381::fr::Fr;

    fn multiply_by_scalar(scalar_value: u64) -> Result<(), Error> {
        let scalar = Scalar::from(scalar_value);
        let g1_generator = G1Affine::generator();
        let g1_multiplied_native = g1_generator.mul(scalar);

        let cs = ConstraintSystem::<Scalar>::new_ref();
        let x_from_native = NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || {
            Ok(g1_multiplied_native.x)
        })?;
        let y_from_native = NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || {
            Ok(g1_multiplied_native.y)
        })?;
        let z_from_native = NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || {
            Ok(g1_multiplied_native.z)
        })?;

        let g1_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.x))?;
        let g1_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.y))?;

        let mut g1_generator_var = G1Var::new(g1_x, g1_y);
        let scalar_var = FpVar::new_witness(cs.clone(), || Ok(scalar))?;

        let bits = scalar_var.to_bits_le()?;
        g1_generator_var.mul_internal(bits.iter().take(5).rev())?; // only 5 bits to speedup tests

        assert_eq!(g1_generator_var.x.value(), x_from_native.value());
        assert_eq!(g1_generator_var.y.value(), y_from_native.value());
        assert_eq!(g1_generator_var.z.value(), z_from_native.value());

        Ok(())
    }

    #[test]
    fn add_two_equal_points() -> Result<(), Error> {
        let cs = ConstraintSystem::<Scalar>::new_ref();
        let g1_generator = G1Affine::generator();
        let g1_x =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.x))?;
        let g1_y =
            NonNativeFieldVar::<bls12_fq, Scalar>::new_witness(cs.clone(), || Ok(g1_generator.y))?;

        let mut g1_var_1 = G1Var::new(g1_x, g1_y);
        let mut g1_var_2 = g1_var_1.clone();

        let add = g1_var_1.add_assign(g1_var_1.clone())?;
        g1_var_2.double_in_place()?;

        assert_eq!(g1_var_1.x.value(), g1_var_2.x.value());
        assert_eq!(g1_var_1.y.value(), g1_var_2.y.value());
        assert_eq!(g1_var_1.z.value(), g1_var_2.z.value());

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
}
