import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp

-- https://www.eftaylor.com/pub/newton_mechanics.html

set_option quotPrecheck false
open Interval intervalIntegral
open MeasureTheory

namespace NewtonianMechanics

  /- EXTERNAL VARIABLES -/
    -- x is the 1-dimensional displacement of an object as a function of time
    variable (x : ℝ → ℝ)

    -- v is the 1-dimensional velocity of an object as a function of time
    variable (v : ℝ → ℝ)

    -- a is the 1-dimensional acceleration of an object as a function of time
    variable (a : ℝ → ℝ)

    -- delta t is the change in the time between two instances t1 and t2
    variable (Δt : ℝ → ℝ → ℝ)

  /- VARIABLES -/
    -- m is the mass of a particle
    variable (m : ℝ)

    -- U is the potential energy of a particle at time t
    variable (U : ℝ → ℝ)

    -- K is the kinetic energy of a particle at time t
    noncomputable def K : ℝ → ℝ := fun t => 1/2 * m * (v t)^2

    -- S is the action of a particle along a trajectory from t1 to t2
    noncomputable def S : ℝ → ℝ → ℝ := fun t1 t2 => ∫ τ in t1..t2, (K v m τ) - (U τ)

    -- UAvrg is the average potential energy from t1 to t2
    noncomputable def UAvrg : ℝ → ℝ → ℝ := fun t1 t2 => (∫ τ in t1..t2, U τ) / (t2 - t1)

    -- KAvrg is the average kinetic energy from t1 to t2
    noncomputable def KAvrg : ℝ → ℝ → ℝ := fun t1 t2 => (∫ τ in t1..t2, K v m τ) / (t2 - t1)

  /- ASSUMPTIONS -/
    -- U and K are integrable over the reals
    variable (KIntegrable : ∀ t1 t2 : ℝ, IntervalIntegrable (fun τ => K v m τ) MeasureTheory.volume t1 t2)
    variable (UIntegrable : ∀ t1 t2 : ℝ, IntervalIntegrable (fun τ => U τ) MeasureTheory.volume t1 t2)

    -- the derivative of S with respect to time is 0 (principle of stationary action)

  namespace causes

    -- a proof that S(t1, t2) = (KAvrg(t1, t2) - UAvrg(t1, t2)) * (t1 - t2)
    -- ASSUMPTIONS USED:
    theorem sEqKMinusUTimesDelT : ∀ t1 t2 : ℝ, S v m U t1 t2 = (KAvrg v m t1 t2 - UAvrg U t1 t2) * (t2 - t1) :=
      fun t1 t2 => by
        apply Eq.symm
        by_cases h : t1 = t2
        . calc
          (KAvrg v m t1 t2 - UAvrg U t1 t2) * (t2 - t1) = 0 := by rw [h]; simp
          _ = ∫ τ in t1..t1, (K v m τ) - (U τ) := by simp [integral_empty]
          _ = ∫ τ in t1..t2, (K v m τ) - (U τ) := by rw [h]
          _ = S v m U t1 t2 := by congr
        . calc
          (KAvrg v m t1 t2 - UAvrg U t1 t2) * (t2 - t1) =
            ((∫ τ in t1..t2, K v m τ) / (t2 - t1) - (∫ τ in t1..t2, U τ) / (t2 - t1)) * (t2 - t1) := by congr
          _ = (∫ τ in t1..t2, K v m τ) - (∫ τ in t1..t2, U τ) := by simp
          _ = ∫ τ in t1..t2, (K v m τ) - (U τ) := by rw [integral_sub (KIntegrable t1 t2) (UIntegrable t1 t2)]
          _ = S v m U t1 t2 := by congr


  end causes

  namespace laws

    -- a proof that for a free particle, Δx1/Δt=Δx2/Δt, implying Newton's first law


    -- a proof that -dU/dt = ma (or equivalently F = ma), Newton's second law

  end laws

end NewtonianMechanics
