/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.RealizedConnectors
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianComparisonAngle
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem riemannianDistance_nonneg (g : SmoothRiemannianMetric I M)
    (x y : M) : 0 ≤ riemannianDistance (I := I) g x y :=
  ENNReal.toReal_nonneg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_comm (g : SmoothRiemannianMetric I M)
    (x y : M) :
    riemannianEDistOf (I := I) g x y =
      riemannianEDistOf (I := I) g y x := by
  unfold riemannianEDistOf
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm (I := I) (x := x) (y := y)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_triangle (g : SmoothRiemannianMetric I M)
    (x y z : M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y +
        riemannianEDistOf (I := I) g y z := by
  unfold riemannianEDistOf
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)


@[simp] theorem riemannianDistance_self (g : SmoothRiemannianMetric I M)
    (x : M) : riemannianDistance (I := I) g x x = 0 := by
  unfold riemannianDistance
  rw [riemannianEDistOf_self]
  rfl


theorem riemannianDistance_comm (g : SmoothRiemannianMetric I M)
    (x y : M) :
    riemannianDistance (I := I) g x y =
      riemannianDistance (I := I) g y x := by
  unfold riemannianDistance
  exact congrArg ENNReal.toReal (riemannianEDistOf_comm (I := I) g x y)

theorem riemannianDistance_triangle (g : SmoothRiemannianMetric I M)
    {x y z : M}
    (hxy : riemannianEDistOf (I := I) g x y ≠ ⊤)
    (hyz : riemannianEDistOf (I := I) g y z ≠ ⊤) :
    riemannianDistance (I := I) g x z ≤
      riemannianDistance (I := I) g x y +
        riemannianDistance (I := I) g y z := by
  unfold riemannianDistance
  rw [← ENNReal.toReal_add hxy hyz]
  exact ENNReal.toReal_mono ((ENNReal.add_ne_top).2 ⟨hxy, hyz⟩)
    (riemannianEDistOf_triangle (I := I) g x y z)

theorem riemannianComparisonAngle_sideInequalities
    (g : SmoothRiemannianMetric I M) (x o y : M)
    (hox : riemannianEDistOf (I := I) g o x ≠ ⊤)
    (hoy : riemannianEDistOf (I := I) g o y ≠ ⊤)
    (hxy : riemannianEDistOf (I := I) g x y ≠ ⊤) :
    |riemannianDistance (I := I) g o x -
        riemannianDistance (I := I) g o y| ≤
        riemannianDistance (I := I) g x y ∧
      riemannianDistance (I := I) g x y ≤
        riemannianDistance (I := I) g o x +
          riemannianDistance (I := I) g o y := by
  have hxo : riemannianEDistOf (I := I) g x o ≠ ⊤ := by
    rw [riemannianEDistOf_comm (I := I) g x o]
    exact hox
  have hyx : riemannianEDistOf (I := I) g y x ≠ ⊤ := by
    rw [riemannianEDistOf_comm (I := I) g y x]
    exact hxy
  have hleft := riemannianDistance_triangle (I := I) g hoy hyx
  have hright := riemannianDistance_triangle (I := I) g hox hxy
  have hforward := riemannianDistance_triangle (I := I) g hxo hoy
  rw [riemannianDistance_comm (I := I) g y x] at hleft
  rw [riemannianDistance_comm (I := I) g x o] at hforward
  refine ⟨(abs_le).2 ⟨?_, ?_⟩, hforward⟩
  · linarith
  · linarith

section Connectors

variable [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
variable [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedMinimizingConnector.edist_ne_top
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    riemannianEDistOf (I := I) g p q ≠ ⊤ := by
  rw [c.realizes]
  exact ENNReal.ofReal_ne_top

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedMinimizingConnector.riemannianDistance_eq_length
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    riemannianDistance (I := I) g p q = c.length := by
  unfold riemannianDistance
  rw [c.realizes, ENNReal.toReal_ofReal c.length_nonneg]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedMinimizingConnector.riemannianDistance_eq_length_rev
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    riemannianDistance (I := I) g q p = c.length := by
  rw [riemannianDistance_comm (I := I) g q p]
  exact c.riemannianDistance_eq_length

def RealizedMinimizingConnector.reverse
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    RealizedMinimizingConnector (I := I) g q p where
  curve := fun t ↦ c.curve ((-1 : ℝ) * t + c.length)
  length := c.length
  length_nonneg := c.length_nonneg
  source := by simpa using c.target
  target := by
    convert c.source using 1
    ring_nf
  smooth := by
    apply c.smooth.comp
      (((contMDiff_const.mul contMDiff_id).add contMDiff_const).contMDiffOn)
    intro t ht
    change (-1 : ℝ) * t + c.length ∈ Icc (0 : ℝ) c.length
    constructor <;> linarith [ht.1, ht.2]
  geodesic := by
    intro t ht
    exact hasGeodesicEquationAt_comp_affine (I := I)
      (c.geodesic ((-1 : ℝ) * t + c.length) (by
        constructor <;> linarith [ht.1, ht.2]))
  unitSpeed := by
    intro t ht
    have htime : (-1 : ℝ) * t + c.length ∈ Ioo (0 : ℝ) c.length := by
      constructor <;> linarith [ht.1, ht.2]
    have hsmoothAt : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c.curve
        ((-1 : ℝ) * t + c.length) :=
      (c.smooth ((-1 : ℝ) * t + c.length) ⟨htime.1.le, htime.2.le⟩).contMDiffAt
        (Filter.mem_of_superset (Ioo_mem_nhds htime.1 htime.2) Ioo_subset_Icc_self)
    have hvel := curveVelocity_comp_affine (I := I) c.curve (-1) c.length t
      (hsmoothAt.mdifferentiableAt (by norm_num))
    change g.inner (c.curve ((-1 : ℝ) * t + c.length))
      (curveVelocity (I := I) (fun s : ℝ ↦ c.curve ((-1 : ℝ) * s + c.length)) t)
      (curveVelocity (I := I) (fun s : ℝ ↦ c.curve ((-1 : ℝ) * s + c.length)) t) = 1
    rw [hvel]
    simp only [curveVelocity, neg_one_smul, map_neg, neg_apply, neg_neg]
    convert c.unitSpeed ((-1 : ℝ) * t + c.length) htime using 1
    with_unfolding_all rfl
  realizes := by
    rw [riemannianEDistOf_comm (I := I) g q p]
    exact c.realizes

end Connectors

end DifferentialGeometry.Toponogov
