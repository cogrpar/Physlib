import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp

/-
DESCRIPTION
Proves the validity of the kinematic equations for functions with the
properties characterized by those representing the motion of particles
with constant acceleration in one dimension.
-/

set_option quotPrecheck false
open Interval intervalIntegral
def zero : ℝ := 0

namespace NewtonianMechanics

  /- EXTERNAL VARIABLES -/

  /- VARIABLES -/
    -- x is the 1-dimensional displacement of an object as a function of time
    variable (x : ℝ → ℝ)

    -- v is the 1-dimensional velocity of an object as a function of time
    variable (v : ℝ → ℝ)

    -- a is the 1-dimensional acceleration of an object as a function of time
    variable (a : ℝ → ℝ)

    -- delta t is the change in the time between two instances t1 and t2
    variable (Δt : ℝ → ℝ → ℝ)

    -- delta x is the change in the position vector between t1 and t2
    variable (Δx : ℝ → ℝ → ℝ)

    -- delta v is the change in the velocity vector between t1 and t2
    variable (Δv : ℝ → ℝ → ℝ)

    -- average velocity is defined as delta x over delta t
    variable (vAvrg : ℝ → ℝ → ℝ)

    -- delta a is change in the acceleration vector between t1 and t2
    variable (Δa : ℝ → ℝ → ℝ)

    -- average acceleration is defined as delta v over delta t
    variable (aAvrg : ℝ → ℝ → ℝ)

  /- ASSUMPTIONS -/
    -- delta t is the change in the time between two instances t1 and t2
    variable (deltaT : (t1 t2 : ℝ) → Δt t1 t2 = t2 - t1)

    -- delta x is the change in the position vector between t1 and t2
    variable (deltaX : (t1 t2 : ℝ) → Δx t1 t2 = x t2 - x t1)

    -- delta v is the change in the velocity vector between t1 and t2
    variable (deltaV : (t1 t2 : ℝ) → Δv t1 t2 = v t2 - v t1)

    -- velocity equals the derivative of position
    variable (xDerivEqV : ∀ t : ℝ, ∀ τ ∈ [[zero, t]], HasDerivAt x (v τ) τ)

    -- average velocity is defined as delta x over delta t
    variable (vAvrgEqDelXOverDelT : (t1 t2 : ℝ) → vAvrg t1 t2 = (Δx t1 t2) / (Δt t1 t2))

    -- average velocity is defined also equals (v₀ + vₜ) / 2
    variable (vAvrgEqV0PlusVtDiv2 : (t1 t2 : ℝ) → vAvrg t1 t2 = (v t1 + v t2) / 2)

    -- v is integrable for all intervals
    variable (vIntegrable : ∀ t : ℝ, IntervalIntegrable (fun τ => v τ) MeasureTheory.volume zero t)

    -- acceleration equals the derivative of velocity
    variable (vDerivEqA : ∀ t : ℝ, ∀ τ ∈ [[zero, t]], HasDerivAt v (a τ) τ)

    -- delta a is change in the acceleration vector between t1 and t2
    variable (deltaA : (t1 t2 : ℝ) → Δa t1 t2 = a t2 - a t1)

    -- average acceleration is defined as delta v over delta t
    variable (aAvrgEqDelVOverDelT : (t1 t2 : ℝ) → aAvrg t1 t2 = (Δv t1 t2) / (Δt t1 t2))

    -- a is integrable for all intervals
    variable (aIntegrable : ∀ t : ℝ, IntervalIntegrable (fun τ => a τ) MeasureTheory.volume zero t)

    -- the kinematic equations require the assumption that acceleration is constant
    variable (assumeConstantAcceleration : ∀ t : ℝ, a t = a 0)

  namespace causes

    -- a proof that Δt from zero to some time t is equal to t
    -- ASSUMPTIONS USED: Δt deltaT
    theorem delTFromZeroIsT : ∀ t : ℝ, Δt 0 t = t :=
      fun t => by simp [deltaT 0 t]
    notation:min "$delTFromZeroIsT" t =>
      delTFromZeroIsT Δt deltaT t

    -- a proof that the integral of acceleration from 0 to t is equal to Δv
    -- ASSUMPTIONS USED: v a Δv deltaV vDerivEqA aIntegrable
    theorem integralAEqDelV : ∀ t : ℝ, (∫ τ in zero..t, a τ) = Δv 0 t :=
      fun t => calc
        (∫ τ : ℝ in zero..t, a τ) = v t - v zero := by rw [integral_eq_sub_of_hasDerivAt (vDerivEqA t) (aIntegrable t)]
        _ = v t - v 0 := by congr
        _ = Δv 0 t:= by rw [← deltaV]
    notation:min "$integralAEqDelV" t =>
      integralAEqDelV v a Δv deltaV vDerivEqA aIntegrable t

    -- a proof that the integral of velocity from 0 to t is equal to Δx
    -- ASSUMPTIONS USED: x v Δx deltaX xDerivEqV vIntegrable
    theorem integralVEqDelX : ∀ t : ℝ, (∫ τ in zero..t, v τ) = Δx 0 t :=
      fun t => calc
        (∫ τ : ℝ in zero..t, v τ) = x t - x zero := by rw [integral_eq_sub_of_hasDerivAt (xDerivEqV t) (vIntegrable t)]
        _ = x t - x 0 := by congr
        _ = Δx 0 t:= by rw [← deltaX]
    notation:min "$integralVEqDelX" t =>
      integralVEqDelX x v Δx deltaX xDerivEqV vIntegrable t

    -- a proof that average acceleration equals acceleration from zero to any time t
    -- ASSUMPTIONS USED: v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration
    theorem aAvrgEqA : ∀ t : ℝ, t ≠ 0 → aAvrg 0 t = a t :=
      fun t tNe0 => calc
        aAvrg 0 t = (Δv 0 t) / t := by rw [aAvrgEqDelVOverDelT, $delTFromZeroIsT t]
        _ = (∫ τ in zero..t, a τ) / t := by rw [$integralAEqDelV t]
        _ = (∫ t' in zero..t, 1 * a 0) / t := by simp [assumeConstantAcceleration]
        _ = (∫ t' in zero..t, 1) * a 0 / t := by simp [MeasureTheory.integral_const (a 0)]
        _ = (t - zero) * a 0 / t := by rw [integral_one]
        _ = (t - 0) * a 0 / t := by congr
        _ = a 0 * (t / t) := by simp; rw [mul_comm]; field_simp
        _ = a 0 * 1 := by rw [← div_self tNe0]
        _ = a t := by rw [mul_one (a 0)]; simp [assumeConstantAcceleration]
    notation:min "$aAvrgEqA" t ";" tNe0 =>
      aAvrgEqA v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration t tNe0

    -- a proof that Δv 0 t / Δt 0 t equals a assuming constant acceleration
    -- ASSUMPTIONS USED: v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration
    theorem delVOverDelTIsA : ∀ t : ℝ, t ≠ 0 → Δv 0 t / Δt 0 t = a t :=
      fun t tNe0 => calc
        Δv 0 t / Δt 0 t = aAvrg 0 t := by rw [aAvrgEqDelVOverDelT]
        _ = a t := by rw [$aAvrgEqA t; tNe0]
    notation:min "$delVOverDelTIsA" t ";" tNe0 =>
      delVOverDelTIsA v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration t tNe0

  end causes

  namespace laws

    -- a proof that x(t) = x₀ + vAvrg * t
    -- ASSUMPTIONS USED: x Δt Δx vAvrg deltaT deltaX vAvrgEqDelXOverDelT
    theorem kinematicEquation1 : ∀ t : ℝ, (x t) = (x 0) + (vAvrg 0 t) * t :=
      fun t => by
        by_cases h : t = 0
        . calc
          (x t) = (x 0) := by rw [h]
          _ = (x 0) + (vAvrg 0 t) * 0 := by ring
          _ = (x 0) + (vAvrg 0 t) * t := by rw [← h]
        . calc
          (x t) = x 0 + Δx 0 t := by simp [deltaX 0 t]
          _ = x 0 + Δx 0 t / t * t := by field_simp
          _ = x 0 + Δx 0 t / Δt 0 t * Δt 0 t := by rw [$delTFromZeroIsT t]
          _ = x 0 + vAvrg 0 t * Δt 0 t := by rw [vAvrgEqDelXOverDelT]
          _ = x 0 + vAvrg 0 t * t := by simp [deltaT 0 t]
    notation:min "$kinematicEquation1" t =>
      kinematicEquation1 x Δt Δx vAvrg deltaT deltaX vAvrgEqDelXOverDelT t

    -- a proof that v(t) = v₀ + at
    -- ASSUMPTIONS USED: v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration
    theorem kinematicEquation2 : ∀ t : ℝ, (v t) = (v 0) + (a t) * t :=
      fun t => by
        by_cases h : t = 0
        . calc
          (v t) = (v 0) := by rw [h]
          _ = (v 0) + (a t) * 0 := by ring
          _ = (v 0) + (a t) * t := by rw [← h]
        . calc
          v t = v 0 + Δv 0 t := by simp [deltaV 0 t]
          _ = v 0 + Δv 0 t / t * t := by field_simp
          _ = v 0 + Δv 0 t / Δt 0 t * Δt 0 t := by rw [$delTFromZeroIsT t]
          _ = v 0 + a t * Δt 0 t := by rw [$delVOverDelTIsA t; h]
          _ = v 0 + a t * t := by simp [deltaT 0 t]
    notation:min "$kinematicEquation2" t =>
      kinematicEquation2 v a Δt Δv aAvrg deltaT deltaV vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration t

    -- a proof that x(t) = x₀ + v₀t + 1/2 * a * t ^ 2
    -- ASSUMPTIONS USED: x v a Δt Δx Δv vAvrg aAvrg deltaT deltaX deltaV vAvrgEqDelXOverDelT vAvrgEqV0PlusVtDiv2 vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration
    theorem kinematicEquation3 : ∀ t : ℝ, (x t) = (x 0) + (v 0) * t + 1/2 * (a t) * t^2 :=
      fun t => calc
        (x t) = (x 0) + (vAvrg 0 t) * t := by rw [$kinematicEquation1 t]
        _ = (x 0) + (v 0 + v t) / 2 * t := by rw [vAvrgEqV0PlusVtDiv2 0 t]
        _ = (x 0) + (v 0 + (v 0 + (a t) * t)) / 2 * t := by rw [$kinematicEquation2 t]
        _ = (x 0) + (v 0) * t + 1/2 * (a t) * (t * t) := by ring
        _ = (x 0) + (v 0) * t + 1/2 * (a t) * t^2 := by simp [pow_two t]
    notation:min "$kinematicEquation3" t =>
      kinematicEquation3 x v a Δt Δx Δv vAvrg aAvrg deltaT deltaX deltaV vAvrgEqDelXOverDelT vAvrgEqV0PlusVtDiv2 vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration t

    -- a proof that v^2 = v₀^2 + 2ad
    -- ASSUMPTIONS USED: x v a Δt Δx Δv vAvrg aAvrg deltaT deltaX deltaV vAvrgEqDelXOverDelT vAvrgEqV0PlusVtDiv2 vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration
    theorem kinematicEquation4 : ∀ t : ℝ, (v t)^2 = (v 0)^2 + 2 * (a t) * (Δx 0 t) :=
      fun t =>
        have kEq3Rewritten : Δx 0 t = (v 0) * t + 1/2 * (a t) * t^2 := calc
          Δx 0 t = x t - x 0 := by rw [deltaX]
          _ = (v 0) * t + 1/2 * (a t) * t^2 := by rw [$kinematicEquation3 t]; ring
        calc
          (v t)^2 = (v 0 + (a t) * t)^2 := by rw [$kinematicEquation2 t]
          _ = (v 0 + (a t) * t) * (v 0 + (a t) * t) := by simp [pow_two]
          _ = (v 0) * (v 0) + 2 * (a t) * ((v 0) * t + 1/2 * (a t) * t^2) := by ring; simp [pow_two t]
          _ = (v 0) * (v 0) + 2 * (a t) * (Δx 0 t) := by rw [kEq3Rewritten]
          _ = (v 0)^2 + 2 * (a t) * (Δx 0 t) := by simp [pow_two (v 0)]
    notation:min "$kinematicEquation4" t =>
      kinematicEquation4 x v a Δt Δx Δv vAvrg aAvrg deltaT deltaX deltaV vAvrgEqDelXOverDelT vAvrgEqV0PlusVtDiv2 vDerivEqA aAvrgEqDelVOverDelT aIntegrable assumeConstantAcceleration t

  end laws

end NewtonianMechanics
