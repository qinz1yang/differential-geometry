import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv



noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set
open scoped Bundle Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in



theorem exists_metric_mfderiv_bound (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ≥0, ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v) := by
  let A : MetricUnitTangent g → F := fun p =>
    mfderiv I 𝓘(ℝ, F) f (MetricUnitTangent.base p) (MetricUnitTangent.vec p)
  have hA : Continuous A :=
    continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).continuous.comp
      ((hf.continuous_tangentMap le_rfl).comp continuous_subtype_val))
  obtain ⟨B, hB⟩ := ((metricUnit_compact g).image hA).isBounded.exists_norm_le
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hC (p : MetricUnitTangent g) : ‖A p‖ ≤ C :=
    (hB (A p) (mem_image_of_mem A (mem_univ p))).trans (le_max_left _ _)
  refine ⟨C, fun x v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · let s := Real.sqrt (g.inner x v v)
    have hs : 0 < s := Real.sqrt_pos.mpr (g.pos x v hv)
    have hsq : s * s = g.inner x v v := Real.mul_self_sqrt (g.pos x v hv).le
    let w : TangentSpace I x := s⁻¹ • v
    have hw : g.inner x w w = 1 := by
      dsimp only [w]
      rw [metric_smul2, ← hsq]
      field_simp
    let p : MetricUnitTangent g := ⟨TotalSpace.mk' E x w, hw⟩
    have hwp : ‖(mfderiv I 𝓘(ℝ, F) f x w : F)‖ ≤ C := hC p
    have hvec : v = s • w := by simp [w, smul_smul, hs.ne']
    calc
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ =
          s * ‖(mfderiv I 𝓘(ℝ, F) f x w : F)‖ := by
        conv_lhs => rw [hvec, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      _ ≤ s * C := mul_le_mul_of_nonneg_left hwp hs.le
      _ = C * Real.sqrt (g.inner x v v) := mul_comm _ _

end DifferentialGeometry.Geometry
