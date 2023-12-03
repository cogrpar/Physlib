import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp

-- https://www.eftaylor.com/pub/newton_mechanics.html

set_option quotPrecheck false
--open Interval intervalIntegral

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

    -- U is the potential energy of a particle at position x and time t
    variable (U : ℝ → ℝ → ℝ)

    -- K is the kinetic energy of a particle at time t
    noncomputable def K : ℝ → ℝ := fun t => 1/2 * m * (v t)^2

    -- S is the action of a particle along a trajectory from (x1, t1) to (x2, t2)
    variable (S : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)

    -- UAvrg is the average potential energy from (x1, t1) to (x2, t2)
    variable (UAvrg : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)

    -- KAvrg is the average kinetic energy from t1 to t2
    variable (KAvrg : ℝ → ℝ → ℝ)

  /- ASSUMPTIONS -/

  namespace causes

  end causes

  namespace laws

  end laws

end NewtonianMechanics
