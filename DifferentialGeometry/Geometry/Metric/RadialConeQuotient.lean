import DifferentialGeometry.Geometry.Metric.RadialConeData
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

open scoped NNReal

namespace GC.MetricGeometry

noncomputable def radialConeDataSeparationQuotient
    {X : Type*} [PseudoMetricSpace X] (p : X) (H : ℝ≥0 → X → X)
    (hzero : ∀ x, H 0 x = p) (hone : ∀ x, H 1 x = x)
    (hsq : ∀ (s t : ℝ≥0) (x y : X),
      dist (H s x) (H t y) ^ 2 =
        (s : ℝ) ^ 2 * dist p x ^ 2 + (t : ℝ) ^ 2 * dist p y ^ 2 -
          (s : ℝ) * (t : ℝ) * (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2)) :
    RadialConeData (SeparationQuotient.mk p) := by
  have hscale (t : ℝ≥0) (x y : X) :
      dist (H t x) (H t y) ^ 2 = (t : ℝ) ^ 2 * dist x y ^ 2 := by
    rw [hsq]
    ring
  have hrespect (t : ℝ≥0) (x y : X) (hxy : Inseparable x y) :
      SeparationQuotient.mk (H t x) = SeparationQuotient.mk (H t y) := by
    apply dist_eq_zero.mp
    rw [SeparationQuotient.dist_mk]
    have h := hscale t x y
    rw [hxy.dist_eq_zero] at h
    nlinarith [dist_nonneg (x := H t x) (y := H t y)]
  refine ⟨fun t => SeparationQuotient.lift (fun x => SeparationQuotient.mk (H t x))
    (hrespect t), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    simp only [SeparationQuotient.lift_mk, hzero]
  · intro x
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    simp only [SeparationQuotient.lift_mk, hone]
  · intro s t x y
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    simp only [SeparationQuotient.lift_mk, SeparationQuotient.dist_mk, radialConeKernel]
    rw [hsq]
    ring

@[simp] theorem radialConeDataSeparationQuotient_map_mk
    {X : Type*} [PseudoMetricSpace X] (p : X) (H : ℝ≥0 → X → X)
    (hzero : ∀ x, H 0 x = p) (hone : ∀ x, H 1 x = x)
    (hsq : ∀ (s t : ℝ≥0) (x y : X),
      dist (H s x) (H t y) ^ 2 =
        (s : ℝ) ^ 2 * dist p x ^ 2 + (t : ℝ) ^ 2 * dist p y ^ 2 -
          (s : ℝ) * (t : ℝ) * (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2))
    (t : ℝ≥0) (x : X) :
    (radialConeDataSeparationQuotient p H hzero hone hsq).map t (SeparationQuotient.mk x) =
      SeparationQuotient.mk (H t x) := rfl

end GC.MetricGeometry
