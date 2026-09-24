import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Normed.Group.Bounded
import DifferentialGeometry.Topology.Manifold.BumpFunction.Nested
import Mathlib.Topology.Algebra.Support

section

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_nested_chart_cutoffs_pullback_metric_coefficients
    (g : SmoothRiemannianMetric I M) (center : M) :
    let Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
      (extChartAtPartialDiffeomorph I ∞ center).symm
    ∃ χ ρ : SmoothBumpFunction I center,
      tsupport (ρ : M → ℝ) ⊆ interior {p | χ p = 1} ∩ Φ.target ∧
      ρ center = 1 ∧ (∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) ∧
      ContMDiff I 𝓘(ℝ, E) ∞ (fun p => χ p • Φ.symm p) ∧
      HasCompactSupport (fun p => χ p • Φ.symm p) ∧
      let A : M → E →L[ℝ] E →L[ℝ] ℝ :=
        fun p => ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)
      ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ A ∧
      HasCompactSupport A ∧
      (∀ p, LinearMap.IsPosSemidef (A p).toBilinForm) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖A p‖ ≤ C := by
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
    (extChartAtPartialDiffeomorph I ∞ center).symm
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let χ : SmoothBumpFunction I center := Classical.choice inferInstance
  obtain ⟨ρ, hρ⟩ := χ.exists_tsupport_subset_interior_one
  have htarget : Φ.target = (chartAt H center).source := by
    change (extChartAt I center).source = _
    exact extChartAt_source I center
  have hF : ContMDiff I 𝓘(ℝ, E) ∞ (fun p => χ p • Φ.symm p) := by
    change ContMDiff I 𝓘(ℝ, E) ∞ (fun p => χ p • extChartAt I center p)
    exact χ.contMDiff_smul contMDiffOn_extChartAt
  have hFc : HasCompactSupport (fun p => χ p • Φ.symm p) := by
    exact χ.hasCompactSupport.mono
      (Function.support_smul_subset_left (χ : M → ℝ) (fun p => Φ.symm p))
  have hcoeff : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)) (chartAt H center).source := by
    rw [← htarget]
    exact (contDiffOn_pullback_metric_coefficients g Φ.open_source
      Φ.contMDiffOn_toFun).contMDiffOn.comp Φ.contMDiffOn_invFun
        (fun p hp => Φ.toOpenPartialHomeomorph.map_target hp)
  let A : M → E →L[ℝ] E →L[ℝ] ℝ :=
    fun p => ρ p • pullbackMetricCoefficients g Φ (Φ.symm p)
  have hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ A :=
    ρ.contMDiff_smul hcoeff
  have hAc : HasCompactSupport A := by
    exact ρ.hasCompactSupport.mono (Function.support_smul_subset_left
      (ρ : M → ℝ) (fun p => pullbackMetricCoefficients g Φ (Φ.symm p)))
  have hpos (p : M) : LinearMap.IsPosSemidef (A p).toBilinForm := by
    have hp := pullbackMetricCoefficients_isPosSemidef g Φ (Φ.symm p)
    refine ⟨⟨fun v w => ?_⟩, ⟨fun v => ?_⟩⟩
    · change ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) v w =
        ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) w v
      exact congrArg (fun r : ℝ => ρ p * r) (hp.isSymm.eq v w)
    · change 0 ≤ ρ p * pullbackMetricCoefficients g Φ (Φ.symm p) v v
      exact mul_nonneg ρ.nonneg (hp.isNonneg.nonneg v)
  obtain ⟨C, hC⟩ := hA.continuous.bounded_above_of_compact_support hAc
  refine ⟨χ, ρ, ?_, ρ.eq_one, fun p => ⟨ρ.nonneg, ρ.le_one⟩, hF, hFc,
    hA, hAc, hpos, max C 0, le_max_right _ _, fun p => (hC p).trans (le_max_left _ _)⟩
  rwa [htarget]

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem smul_pullbackMetricCoefficients_fderiv_of_tsupport_subset
    (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (χ ρ : M → ℝ)
    (hρ : tsupport ρ ⊆ interior {p | χ p = 1} ∩ Φ.target)
    {U : V → M} {z : V} (hU : MDifferentiableAt 𝓘(ℝ, V) I U z) (v w : V) :
    ρ (U z) * pullbackMetricCoefficients g Φ (Φ.symm (U z))
      (fderiv ℝ (fun x => χ (U x) • Φ.symm (U x)) z v)
      (fderiv ℝ (fun x => χ (U x) • Φ.symm (U x)) z w) =
      ρ (U z) * g.inner (U z)
        (mfderiv 𝓘(ℝ, V) I U z v) (mfderiv 𝓘(ℝ, V) I U z w) := by
  by_cases hz : ρ (U z) = 0
  · simp only [hz, zero_mul]
  · have hp := hρ (subset_closure hz)
    have heq : (fun x => χ (U x) • Φ.symm (U x)) =ᶠ[𝓝 z] Φ.symm ∘ U := by
      filter_upwards [hU.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hp.1)] with x hx
      have hχx : χ (U x) = 1 :=
        (interior_subset : interior {p : M | χ p = 1} ⊆ {p : M | χ p = 1}) hx
      simp only [hχx, one_smul, Function.comp_apply]
    rw [heq.fderiv_eq]
    exact congrArg (fun r : ℝ => ρ (U z) * r)
      (pullbackMetricCoefficients_fderiv_symm g Φ hU hp.2 v w)

end DifferentialGeometry.Geometry

end

end
