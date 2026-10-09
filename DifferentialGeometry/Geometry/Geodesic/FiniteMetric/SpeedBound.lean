import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Speed bound for the geodesic flow of a finite-regularity metric

For `g : ContMDiffRiemannianMetric I (r + 1)`, `1 ≤ r`, on a manifold whose distance is the
Riemannian distance of a bundle metric with the norm of `g` (`hnorm`): an arc of the geodesic flow
has length speed × time (`pathELength_proj_geodesicFlow`, using CM1.b speed conservation), hence
`dist_proj_geodesicFlow_le` and the Lipschitz bound `dist_expMap_smul_le` for `t ↦ exp_x (t v)`
(finite-order form of the smooth `maximalGeodesic_edist_le_speed_mul_time`). Lane CM-H, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The projected geodesic flow is `C¹` on every compact time interval of its domain. -/
theorem contMDiffOn_proj_geodesicFlow (hr : 1 ≤ r) {p : TangentBundle I M} {s t : ℝ}
    (hsub : ∀ τ ∈ Icc s t, (p, τ) ∈ g.geodesicFlowDomain) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun τ => (g.geodesicFlow p τ).proj) (Icc s t) := by
  have htime : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r
      (fun τ : ℝ => (p, τ)) := contMDiff_const.prodMk contMDiff_id
  have hflow := (g.contMDiffOn_geodesicFlow hr).comp htime.contMDiffOn
    (s := Icc s t) (fun τ hτ => hsub τ hτ)
  have hproj : ContMDiff I.tangent I r (TotalSpace.proj : TangentBundle I M → M) :=
    Bundle.contMDiff_proj (TangentSpace I)
  exact (hproj.comp_contMDiffOn hflow).of_le (by exact_mod_cast hr)

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

omit [IsRiemannianManifold I M] in
/-- The length of a geodesic arc is speed times time. -/
theorem pathELength_proj_geodesicFlow (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {s t : ℝ}
    (hsub : ∀ τ ∈ Icc s t, (p, τ) ∈ g.geodesicFlowDomain) :
    pathELength I (fun τ => (g.geodesicFlow p τ).proj) s t =
      ENNReal.ofReal (Real.sqrt (g.inner p.proj p.snd p.snd) * (t - s)) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hconst : ∀ τ ∈ Icc s t,
      ‖mfderiv 𝓘(ℝ, ℝ) I (fun σ => (g.geodesicFlow p σ).proj) τ 1‖ₑ =
        ENNReal.ofReal (Real.sqrt (g.inner p.proj p.snd p.snd)) := by
    intro τ hτ
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I (fun σ => (g.geodesicFlow p σ).proj) τ 1 :
        TangentSpace I (g.geodesicFlow p τ).proj) = (g.geodesicFlow p τ).snd := by
      rw [(g.hasMFDerivAt_geodesicFlow_proj hr (hsub τ hτ)).mfderiv]
      exact one_smul ℝ _
    rw [h1, hnorm, g.inner_geodesicFlow_eq hr p τ (hsub τ hτ)]
  rw [setLIntegral_congr_fun measurableSet_Icc hconst, setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- **Speed bound.** Along the geodesic flow, the Riemannian distance between two positions is at
most the (constant) speed times the elapsed time. -/
theorem dist_proj_geodesicFlow_le (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {s t : ℝ}
    (hsub : ∀ τ ∈ uIcc s t, (p, τ) ∈ g.geodesicFlowDomain) :
    dist (g.geodesicFlow p s).proj (g.geodesicFlow p t).proj ≤
      Real.sqrt (g.inner p.proj p.snd p.snd) * |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this (fun τ hτ => hsub τ (uIcc_comm s t ▸ hτ)) (le_of_not_ge hst)
  have hsub' : ∀ τ ∈ Icc s t, (p, τ) ∈ g.geodesicFlowDomain := fun τ hτ =>
    hsub τ (by rwa [uIcc_of_le hst])
  have hle := riemannianEDist_le_pathELength (I := I)
    (g.contMDiffOn_proj_geodesicFlow hr hsub') rfl rfl hst
  rw [pathELength_proj_geodesicFlow g hr hnorm hsub', ← IsRiemannianManifold.out (I := I),
    edist_dist] at hle
  rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hst))).mp hle

/-- **Lipschitz bound for the radial geodesic** `t ↦ exp_x (t v)` on any time interval of the flow
domain. -/
theorem dist_expMap_smul_le (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} (v : TangentSpace I x) {s t : ℝ}
    (hsub : ∀ τ ∈ uIcc s t, ((⟨x, v⟩ : TangentBundle I M), τ) ∈ g.geodesicFlowDomain) :
    dist (g.expMap (⟨x, s • v⟩ : TangentBundle I M)) (g.expMap (⟨x, t • v⟩ : TangentBundle I M)) ≤
      Real.sqrt (g.inner x v v) * |t - s| := by
  rw [g.expMap_smul_eq_proj_geodesicFlow hr x v s (hsub s left_mem_uIcc),
    g.expMap_smul_eq_proj_geodesicFlow hr x v t (hsub t right_mem_uIcc)]
  exact g.dist_proj_geodesicFlow_le hr hnorm hsub

end Bundle.ContMDiffRiemannianMetric
