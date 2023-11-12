import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Vector
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp

/-
DESCRIPTION
Proves that motion in different reference frames can be calculated by
vector addition. It is shown that in such a system of inertial
reference frames, if two frames have no acceleration relative to one
another, there will be no relative acceleration observed between them
in any other frame.
-/

set_option quotPrecheck false
open Interval intervalIntegral

namespace NewtonianMechanics

  /- EXTERNAL VARIABLES -/

  /- VARIABLES -/
    -- set of all reference frames in the system
    variable (refFrames : Set String)

    -- relative displacement between A and B in A's reference frame
    variable (relR : String → String → ℝ → Vector ℝ 3)

    -- relative velocity of B in A's reference frame
    variable (relV : String → String → ℝ → Vector ℝ 3)

    -- relative acceleration of B in A's reference frame
    variable (relA : String → String → ℝ → Vector ℝ 3)

    -- x component of 3 dimensional cartesian vector
    def relVecX : (ℝ → Vector ℝ 3) → ℝ → ℝ :=
      fun vec t => (vec t).get 0

    -- y component of 3 dimensional cartesian vector
    def relVecY : (ℝ → Vector ℝ 3) → ℝ → ℝ :=
      fun vec t => (vec t).get 1

    -- z component of 3 dimensional cartesian vector
    def relVecZ : (ℝ → Vector ℝ 3) → ℝ → ℝ :=
      fun vec t => (vec t).get 2

    -- define vector addition for 3 dimensional cartesian vectors
    def threeDVectorSum : Vector ℝ 3 → Vector ℝ 3 → Vector ℝ 3 :=
      fun vecA vecB =>
        ⟨[vecA.get 0 + vecB.get 0,
          vecA.get 1 + vecB.get 1,
          vecA.get 2 + vecB.get 2], rfl⟩

    -- define the square of the magnitude of a cartesian vector
    def vecMagSqr : Vector ℝ 3 → ℝ :=
      fun vec =>
        (vec.get 0) * (vec.get 0) +
        (vec.get 1) * (vec.get 1) +
        (vec.get 2) * (vec.get 2)

  /- ASSUMPTIONS -/
    -- displacement has the property that relR A C t = relR A B t + relR B C t
    variable (rComponentsBetweenFramesIsSum : ∀ A B C : String, ∀ t : ℝ,
                                              A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                                              relVecX (relR A C) t = relVecX (relR A B) t + relVecX (relR B C) t ∧
                                              relVecY (relR A C) t = relVecY (relR A B) t + relVecY (relR B C) t ∧
                                              relVecZ (relR A C) t = relVecZ (relR A B) t + relVecZ (relR B C) t)

    -- velocity is derivative of displacement
    variable (relRDerivEqV : ∀ A B : String, ∀ t : ℝ,
                             A ∈ refFrames ∧ B ∈ refFrames →
                             HasDerivAt (relVecX (relR A B)) (relVecX (relV A B) t) t ∧
                             HasDerivAt (relVecY (relR A B)) (relVecY (relV A B) t) t ∧
                             HasDerivAt (relVecZ (relR A B)) (relVecZ (relV A B) t) t)

    -- acceleration is derivative of velocity
    variable (relVDerivEqA : ∀ A B : String, ∀ t : ℝ,
                             A ∈ refFrames ∧ B ∈ refFrames →
                             HasDerivAt (relVecX (relV A B)) (relVecX (relA A B) t) t ∧
                             HasDerivAt (relVecY (relV A B)) (relVecY (relA A B) t) t ∧
                             HasDerivAt (relVecZ (relV A B)) (relVecZ (relA A B) t) t)

  namespace causes

    theorem eqSumComponentsEqVecSum : ∀ vec1 vec2 vec3 : ℝ → Vector ℝ 3, ∀ t : ℝ,
                                      relVecX vec1 t + relVecX vec2 t = relVecX vec3 t ∧
                                      relVecY vec1 t + relVecY vec2 t = relVecY vec3 t ∧
                                      relVecZ vec1 t + relVecZ vec2 t = relVecZ vec3 t →
                                      threeDVectorSum (vec1 t) (vec2 t) = vec3 t :=
      fun vec1 vec2 vec3 t componentsSumEq => by
        have eqX := componentsSumEq.left
        have eqY := componentsSumEq.right.left
        have eqZ := componentsSumEq.right.right
        ext i
        match i with
        | 0 => calc
          (threeDVectorSum (vec1 t) (vec2 t)).get 0 = (relVecX vec1 t) + (relVecX vec2 t) := by congr
          _ = relVecX vec3 t := by rw [eqX]
          _ = (vec3 t).get 0 := by congr
        | 1 => calc
          (threeDVectorSum (vec1 t) (vec2 t)).get 1 = (relVecY vec1 t) + (relVecY vec2 t) := by congr
          _ = relVecY vec3 t := by rw [eqY]
          _ = (vec3 t).get 1 := by congr
        | 2 => calc
          (threeDVectorSum (vec1 t) (vec2 t)).get 2 = (relVecZ vec1 t) + (relVecZ vec2 t) := by congr
          _ = relVecZ vec3 t := by rw [eqZ]
          _ = (vec3 t).get 2 := by congr

    -- proof of function extensionality for rComponentsBetweenFramesIsSum wrapped in lambda
    -- ASSUMPTIONS USED: refFrames relR rComponentsBetweenFramesIsSum
    theorem funextRComponentsBetweenFramesIsSum :
      ∀ A B C : String,
      A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
      (fun t => relVecX (relR A C) t) = (fun t => relVecX (relR A B) t + relVecX (relR B C) t) ∧
      (fun t => relVecY (relR A C) t) = (fun t => relVecY (relR A B) t + relVecY (relR B C) t) ∧
      (fun t => relVecZ (relR A C) t) = (fun t => relVecZ (relR A B) t + relVecZ (relR B C) t) :=
      fun A B C ABCAreFrames =>
        let eqX : (fun t => relVecX (relR A C) t) = (fun t => relVecX (relR A B) t + relVecX (relR B C) t) := by
          funext
          rw [(rComponentsBetweenFramesIsSum A B C _ ABCAreFrames).left]
        let eqY : (fun t => relVecY (relR A C) t) = (fun t => relVecY (relR A B) t + relVecY (relR B C) t) := by
          funext
          rw [(rComponentsBetweenFramesIsSum A B C _ ABCAreFrames).right.left]
        let eqZ : (fun t => relVecZ (relR A C) t) = (fun t => relVecZ (relR A B) t + relVecZ (relR B C) t) := by
          funext
          rw [(rComponentsBetweenFramesIsSum A B C _ ABCAreFrames).right.right]
        And.intro eqX (And.intro eqY eqZ)
    notation:min "$funextRComponentsBetweenFramesIsSum" A ";" B ";" C ";" ABCAreFrames =>
      funextRComponentsBetweenFramesIsSum refFrames relR rComponentsBetweenFramesIsSum A B C ABCAreFrames

  end causes

  namespace laws

    -- a proof that relX A C = relX A B + relX B C
    -- ASSUMPTIONS USED: refFrames relR rComponentsBetweenFramesIsSum
    theorem rBetweenFramesIsSum : ∀ A B C : String, ∀ t : ℝ,
                                  A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                                  relR A C t = threeDVectorSum (relR A B t) (relR B C t) :=
      fun A B C t ABCAreFrames => by
        let eqX : relVecX (relR A B) t + relVecX (relR B C) t = relVecX (relR A C) t := by
          rw [(rComponentsBetweenFramesIsSum A B C t ABCAreFrames).left]
        let eqY : relVecY (relR A B) t + relVecY (relR B C) t = relVecY (relR A C) t := by
          rw [(rComponentsBetweenFramesIsSum A B C t ABCAreFrames).right.left]
        let eqZ : relVecZ (relR A B) t + relVecZ (relR B C) t = relVecZ (relR A C) t := by
          rw [(rComponentsBetweenFramesIsSum A B C t ABCAreFrames).right.right]
        rw [causes.eqSumComponentsEqVecSum (relR A B) (relR B C) (relR A C) t
                                           (And.intro eqX (And.intro eqY eqZ))]
    notation:min "$rBetweenFramesIsSum" A ";" B ";" C ";" t ";" ABCAreFrames =>
      rBetweenFramesIsSum refFrames relR rComponentsBetweenFramesIsSum A B C t ABCAreFrames

    -- a proof that relV A C = relV A B + relV B C
    -- ASSUMPTIONS USED: refFrames relR relV rComponentsBetweenFramesIsSum relRDerivEqV
    theorem vBetweenFramesIsSum : ∀ A B C : String, ∀ t : ℝ,
                                  A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                                  relV A C t = threeDVectorSum (relV A B t) (relV B C t) :=
      fun A B C t ABCAreFrames => by
        let vEqDerivRAB := (relRDerivEqV A B t (And.intro ABCAreFrames.left ABCAreFrames.right.left))
        let vEqDerivRBC := (relRDerivEqV B C t (And.intro ABCAreFrames.right.left ABCAreFrames.right.right))
        let vEqDerivRAC := (relRDerivEqV A C t (And.intro ABCAreFrames.left ABCAreFrames.right.right))
        let eqX : relVecX (relV A B) t + relVecX (relV B C) t = relVecX (relV A C) t := calc
          relVecX (relV A B) t + relVecX (relV B C) t =
          deriv (relVecX (relR A B)) t + deriv (relVecX (relR B C)) t := by
            rw [vEqDerivRAB.left.deriv,
                vEqDerivRBC.left.deriv]
          _ = deriv (fun t => relVecX (relR A B) t + relVecX (relR B C) t) t := by
            rw [(deriv_add vEqDerivRAB.left.differentiableAt
                           vEqDerivRBC.left.differentiableAt)]
          _ = deriv (fun t => relVecX (relR A C) t) t := by
            rw [($funextRComponentsBetweenFramesIsSum A; B; C; ABCAreFrames).left]
          _ = relVecX (relV A C) t := by
            rw [← vEqDerivRAC.left.deriv]
        let eqY : relVecY (relV A B) t + relVecY (relV B C) t = relVecY (relV A C) t := calc
          relVecY (relV A B) t + relVecY (relV B C) t =
          deriv (relVecY (relR A B)) t + deriv (relVecY (relR B C)) t := by
            rw [vEqDerivRAB.right.left.deriv,
                vEqDerivRBC.right.left.deriv]
          _ = deriv (fun t => relVecY (relR A B) t + relVecY (relR B C) t) t := by
            rw [(deriv_add vEqDerivRAB.right.left.differentiableAt
                           vEqDerivRBC.right.left.differentiableAt)]
          _ = deriv (fun t => relVecY (relR A C) t) t := by
            rw [($funextRComponentsBetweenFramesIsSum A; B; C; ABCAreFrames).right.left]
          _ = relVecY (relV A C) t := by
            rw [← vEqDerivRAC.right.left.deriv]
        let eqZ : relVecZ (relV A B) t + relVecZ (relV B C) t = relVecZ (relV A C) t := calc
          relVecZ (relV A B) t + relVecZ (relV B C) t =
          deriv (relVecZ (relR A B)) t + deriv (relVecZ (relR B C)) t := by
            rw [vEqDerivRAB.right.right.deriv,
                vEqDerivRBC.right.right.deriv]
          _ = deriv (fun t => relVecZ (relR A B) t + relVecZ (relR B C) t) t := by
            rw [(deriv_add vEqDerivRAB.right.right.differentiableAt
                           vEqDerivRBC.right.right.differentiableAt)]
          _ = deriv (fun t => relVecZ (relR A C) t) t := by
            rw [($funextRComponentsBetweenFramesIsSum A; B; C; ABCAreFrames).right.right]
          _ = relVecZ (relV A C) t := by
            rw [← vEqDerivRAC.right.right.deriv]
        rw [causes.eqSumComponentsEqVecSum (relV A B) (relV B C) (relV A C) t
                                           (And.intro eqX (And.intro eqY eqZ))]
    notation:min "$vBetweenFramesIsSum" A ";" B ";" C ";" t ";" ABCAreFrames =>
      vBetweenFramesIsSum refFrames relR relV rComponentsBetweenFramesIsSum relRDerivEqV A B C t ABCAreFrames


    -- a proof that relV A C = relV A B + relV B C
    -- ASSUMPTIONS USED:
    theorem aBetweenFramesIsSum : ∀ A B C : String, ∀ t : ℝ,
                    A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                    relA A C t = threeDVectorSum (relA A B t) (relA B C t) :=
      sorry

    -- a proof that if frames A and B have no relative a, they have the same a relative to all other frames
    -- ASSUMPTIONS USED:
    theorem inertialFrames : ∀ A B C : String, ∀ t : ℝ,
                    A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                    vecMagSqr (relA B C t) = 0 → relA A B t = relA A C t :=
      sorry

  end laws

end NewtonianMechanics
