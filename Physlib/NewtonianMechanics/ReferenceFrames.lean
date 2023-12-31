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

    theorem sumVecZeroIsVec : ∀ vec : Vector ℝ 3, threeDVectorSum ⟨[0, 0, 0], rfl⟩ vec = vec :=
      fun vec => by
        ext i
        match i with
        | 0 => calc
          (threeDVectorSum ⟨[0, 0, 0], rfl⟩ vec).get 0 = 0 + vec.get 0 := by congr
          _ = vec.get 0 := by simp [add_zero (vec.get 0)]
        | 1 => calc
          (threeDVectorSum ⟨[0, 0, 0], rfl⟩ vec).get 1 = 0 + vec.get 1 := by congr
          _ = vec.get 1 := by simp [add_zero (vec.get 1)]
        | 2 => calc
          (threeDVectorSum ⟨[0, 0, 0], rfl⟩ vec).get 2 = 0 + vec.get 2 := by congr
          _ = vec.get 2 := by simp [add_zero (vec.get 2)]

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

    theorem eqVecSumEqSumComponents : ∀ vec1 vec2 vec3 : ℝ → Vector ℝ 3, ∀ t : ℝ,
                                      threeDVectorSum (vec1 t) (vec2 t) = vec3 t →
                                      relVecX vec1 t + relVecX vec2 t = relVecX vec3 t ∧
                                      relVecY vec1 t + relVecY vec2 t = relVecY vec3 t ∧
                                      relVecZ vec1 t + relVecZ vec2 t = relVecZ vec3 t :=
      fun vec1 vec2 vec3 t vecSumEq =>
        let eqX : relVecX vec1 t + relVecX vec2 t = relVecX vec3 t := calc
          relVecX vec1 t + relVecX vec2 t = (threeDVectorSum (vec1 t) (vec2 t)).get 0 := by congr
          _ = (threeDVectorSum (vec1 t) (vec2 t)).get 0 := by congr
          _ = (vec3 t).get 0 := by rw [vecSumEq]
          _ = relVecX vec3 t := by congr
        let eqY : relVecY vec1 t + relVecY vec2 t = relVecY vec3 t := calc
          relVecY vec1 t + relVecY vec2 t = (threeDVectorSum (vec1 t) (vec2 t)).get 1 := by congr
          _ = (threeDVectorSum (vec1 t) (vec2 t)).get 1 := by congr
          _ = (vec3 t).get 1 := by rw [vecSumEq]
          _ = relVecY vec3 t := by congr
        let eqZ : relVecZ vec1 t + relVecZ vec2 t = relVecZ vec3 t := calc
          relVecZ vec1 t + relVecZ vec2 t = (threeDVectorSum (vec1 t) (vec2 t)).get 2 := by congr
          _ = (threeDVectorSum (vec1 t) (vec2 t)).get 2 := by congr
          _ = (vec3 t).get 2 := by rw [vecSumEq]
          _ = relVecZ vec3 t := by congr
        And.intro eqX (And.intro eqY eqZ)

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

    -- proof of function extensionality for vComponentsBetweenFramesIsSum wrapped in lambda
    -- ASSUMPTIONS USED: relV
    theorem funextVComponentsBetweenFramesIsSum :
      ∀ A B C : String,
      (∀ t : ℝ, threeDVectorSum (relV A B t) (relV B C t) = relV A C t) →
      (fun t => relVecX (relV A C) t) = (fun t => relVecX (relV A B) t + relVecX (relV B C) t) ∧
      (fun t => relVecY (relV A C) t) = (fun t => relVecY (relV A B) t + relVecY (relV B C) t) ∧
      (fun t => relVecZ (relV A C) t) = (fun t => relVecZ (relV A B) t + relVecZ (relV B C) t) :=
      fun A B C vBetweenFramesIsSum =>
        let eqX : (fun t => relVecX (relV A C) t) = (fun t => relVecX (relV A B) t + relVecX (relV B C) t) := by
          funext t
          rw [← (eqVecSumEqSumComponents (relV A B) (relV B C) (relV A C) t (vBetweenFramesIsSum t)).left]
        let eqY : (fun t => relVecY (relV A C) t) = (fun t => relVecY (relV A B) t + relVecY (relV B C) t) := by
          funext t
          rw [← (eqVecSumEqSumComponents (relV A B) (relV B C) (relV A C) t (vBetweenFramesIsSum t)).right.left]
        let eqZ : (fun t => relVecZ (relV A C) t) = (fun t => relVecZ (relV A B) t + relVecZ (relV B C) t) := by
          funext t
          rw [← (eqVecSumEqSumComponents (relV A B) (relV B C) (relV A C) t (vBetweenFramesIsSum t)).right.right]
        And.intro eqX (And.intro eqY eqZ)
    notation:min "$funextVComponentsBetweenFramesIsSum" A ";" B ";" C ";" vBetweenFramesIsSum =>
      funextVComponentsBetweenFramesIsSum relV A B C vBetweenFramesIsSum

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

    -- a proof that relA A C = relA A B + relA B C
    -- ASSUMPTIONS USED: refFrames relR relV relA rComponentsBetweenFramesIsSum relRDerivEqV relVDerivEqA
    theorem aBetweenFramesIsSum : ∀ A B C : String, ∀ t : ℝ,
                    A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                    relA A C t = threeDVectorSum (relA A B t) (relA B C t) :=
      fun A B C t ABCAreFrames => by
        let aEqDerivVAB := (relVDerivEqA A B t (And.intro ABCAreFrames.left ABCAreFrames.right.left))
        let aEqDerivVBC := (relVDerivEqA B C t (And.intro ABCAreFrames.right.left ABCAreFrames.right.right))
        let aEqDerivVAC := (relVDerivEqA A C t (And.intro ABCAreFrames.left ABCAreFrames.right.right))
        let eqX : relVecX (relA A B) t + relVecX (relA B C) t = relVecX (relA A C) t := calc
          relVecX (relA A B) t + relVecX (relA B C) t =
          deriv (relVecX (relV A B)) t + deriv (relVecX (relV B C)) t := by
            rw [aEqDerivVAB.left.deriv,
                aEqDerivVBC.left.deriv]
          _ = deriv (fun t => relVecX (relV A B) t + relVecX (relV B C) t) t := by
            rw [(deriv_add aEqDerivVAB.left.differentiableAt
                           aEqDerivVBC.left.differentiableAt)]
          _ = deriv (fun t => relVecX (relV A C) t) t := by
            rw [($funextVComponentsBetweenFramesIsSum A; B; C;
                  (fun t' => by rw [($vBetweenFramesIsSum A; B; C; t'; ABCAreFrames)])).left]
          _ = relVecX (relA A C) t := by
            rw [← aEqDerivVAC.left.deriv]
        let eqY : relVecY (relA A B) t + relVecY (relA B C) t = relVecY (relA A C) t := calc
          relVecY (relA A B) t + relVecY (relA B C) t =
          deriv (relVecY (relV A B)) t + deriv (relVecY (relV B C)) t := by
            rw [aEqDerivVAB.right.left.deriv,
                aEqDerivVBC.right.left.deriv]
          _ = deriv (fun t => relVecY (relV A B) t + relVecY (relV B C) t) t := by
            rw [(deriv_add aEqDerivVAB.right.left.differentiableAt
                           aEqDerivVBC.right.left.differentiableAt)]
          _ = deriv (fun t => relVecY (relV A C) t) t := by
            rw [($funextVComponentsBetweenFramesIsSum A; B; C;
                  (fun t' => by rw [($vBetweenFramesIsSum A; B; C; t'; ABCAreFrames)])).right.left]
          _ = relVecY (relA A C) t := by
            rw [← aEqDerivVAC.right.left.deriv]
        let eqZ : relVecZ (relA A B) t + relVecZ (relA B C) t = relVecZ (relA A C) t := calc
          relVecZ (relA A B) t + relVecZ (relA B C) t =
          deriv (relVecZ (relV A B)) t + deriv (relVecZ (relV B C)) t := by
            rw [aEqDerivVAB.right.right.deriv,
                aEqDerivVBC.right.right.deriv]
          _ = deriv (fun t => relVecZ (relV A B) t + relVecZ (relV B C) t) t := by
            rw [(deriv_add aEqDerivVAB.right.right.differentiableAt
                           aEqDerivVBC.right.right.differentiableAt)]
          _ = deriv (fun t => relVecZ (relV A C) t) t := by
            rw [($funextVComponentsBetweenFramesIsSum A; B; C;
                  (fun t' => by rw [($vBetweenFramesIsSum A; B; C; t'; ABCAreFrames)])).right.right]
          _ = relVecZ (relA A C) t := by
            rw [← aEqDerivVAC.right.right.deriv]
        rw [causes.eqSumComponentsEqVecSum (relA A B) (relA B C) (relA A C) t
                                           (And.intro eqX (And.intro eqY eqZ))]
    notation:min "$aBetweenFramesIsSum" A ";" B ";" C ";" t ";" ABCAreFrames =>
      aBetweenFramesIsSum refFrames relR relV relA rComponentsBetweenFramesIsSum relRDerivEqV relVDerivEqA A B C t ABCAreFrames

    -- a proof that if frames A and B have no relative a, they have the same a relative to all other frames
    -- ASSUMPTIONS USED: refFrames relR relV relA rComponentsBetweenFramesIsSum relRDerivEqV relVDerivEqA
    theorem inertialFrames : ∀ A B C : String, ∀ t : ℝ,
                    A ∈ refFrames ∧ B ∈ refFrames ∧ C ∈ refFrames →
                    relA A B t = ⟨[0, 0, 0], rfl⟩ →
                    relA A C t = relA B C t :=
      fun A B C t ABCAreFrames relAIsZero => calc
        relA A C t = threeDVectorSum (relA A B t) (relA B C t) := by rw [← $aBetweenFramesIsSum A; B; C; t; ABCAreFrames]
        _ = threeDVectorSum ⟨[0, 0, 0], rfl⟩ (relA B C t) := by rw [relAIsZero]
        _ = relA B C t := by rw [causes.sumVecZeroIsVec]
    notation:min "$inertialFrames" A ";" B ";" C ";" t ";" ABCAreFrames ";" relAIsZero =>
      inertialFrames A B C t ABCAreFrames relAIsZero refFrames relR relV relA rComponentsBetweenFramesIsSum relRDerivEqV relVDerivEqA

  end laws

end NewtonianMechanics
