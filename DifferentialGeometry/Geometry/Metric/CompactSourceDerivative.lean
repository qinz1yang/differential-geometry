import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv








noncomputable section

open Set Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_metric_mfderiv_norm (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : V → M} {U : Set V} (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U) :
    ContinuousOn (fun p : V × V => Real.sqrt (g.inner (f p.1)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2)))
      (U ×ˢ univ) := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  have htf := hf.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hv : Continuous (fun p : V × V =>
      (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).symm.continuous
  have hcont : ContinuousOn (fun p : V × V =>
      TotalSpace.mk' E (f p.1) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2)) (U ×ˢ univ) := by
    apply (htf.comp hv.continuousOn (fun p hp => hp.1)).congr
    intro p hp
    dsimp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hp.1)]
  exact (hcont.inner_bundle hcont).sqrt

set_option backward.isDefEq.respectTransparency false in


theorem exists_compact_source_mfderiv_bound [FiniteDimensional ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ x ∈ S, ∀ v : V,
      Real.sqrt (g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)) ≤ C * ‖v‖ := by
  let A : V × V → ℝ := fun p => Real.sqrt (g.inner (f p.1)
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2))
  have hc : ContinuousOn A (S ×ˢ Metric.closedBall (0 : V) 1) :=
    (continuousOn_metric_mfderiv_norm g hU hf).mono (fun p hp => ⟨hSU hp.1, mem_univ _⟩)
  obtain ⟨B, hB⟩ := ((hS.prod (isCompact_closedBall (0 : V) 1)).image_of_continuousOn hc).isBounded.exists_norm_le
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hC (x : V) (hx : x ∈ S) (v : V) (hv : ‖v‖ ≤ 1) : A (x, v) ≤ C := by
    have h := hB (A (x, v)) (mem_image_of_mem A
      (show (x, v) ∈ S ×ˢ Metric.closedBall (0 : V) 1 from
        ⟨hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨C, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvn, inv_mul_cancel₀ hvn.ne']
  have hnorm : v = ‖v‖ • w := by simp [w, smul_smul, hvn.ne']
  calc
    Real.sqrt (g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)) = ‖v‖ * A (x, w) := by
      conv_lhs => rw [hnorm]
      rw [show mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x (‖v‖ • w) =
        ‖v‖ • mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x w from map_smul _ _ _,
        sqrt_metric_smul, abs_of_pos hvn]
    _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left (hC x hx w hw.le) hvn.le
    _ = C * ‖v‖ := mul_comm _ _

end DifferentialGeometry.Geometry
