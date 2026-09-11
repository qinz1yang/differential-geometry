import DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic
import DifferentialGeometry.Analysis.Calculus.Derivative.DifferentialComparison









noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

set_option backward.isDefEq.respectTransparency false in
theorem eventually_riemannianEDistOf_eq_normal_norm
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∀ᶠ q in 𝓝 p, riemannianEDistOf g p q =
      ENNReal.ofReal (Real.sqrt (g.inner p
        (normalChartAt g p q) (normalChartAt g p q))) := by
  let ψ := normalChartAt (I := I) g p
  have hψ : ContinuousAt ψ p := ψ.contMDiffOn_toFun.continuousOn.continuousAt
    (ψ.open_source.mem_nhds (normalChartAt_source g p))
  have hn : ContinuousAt (fun q => Real.sqrt (g.inner p (ψ q) (ψ q))) p := by
    exact ((g.inner p).continuous₂.continuousAt.comp (hψ.prodMk hψ)).sqrt
  have hsmall : ∀ᶠ q in 𝓝 p,
      Real.sqrt (g.inner p (ψ q) (ψ q)) < metricCoerciveExpRadius g p := by
    apply hn.eventually (gt_mem_nhds ?_)
    simpa only [ψ, normalChartAt_centre, map_zero, Real.sqrt_zero] using
      metricCoerciveExpRadius_pos g p
  filter_upwards [ψ.open_source.mem_nhds (normalChartAt_source g p), hsmall] with q hq hsmall
  have hround : q = expMap g p (ψ q) :=
    (ψ.left_inv hq).symm.trans (normalChartAt_symm_apply g p (ψ.map_source hq))
  exact (congrArg (riemannianEDistOf g p) hround).trans
    (edist_exp_eq_radius_of_metric g p hsmall)

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
theorem sqrt_metric_smul (g : SmoothRiemannianMetric I M) (p : M)
    (c : ℝ) (v : E) :
    Real.sqrt (g.inner p (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner p v v) := by
  have h : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasFDerivAt_normal_coordinates (g : SmoothRiemannianMetric I M)
    {u : V → M} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x) :
    HasFDerivAt (normalChartAt g (u x) ∘ u) (mfderiv 𝓘(ℝ, V) I u x) x := by
  have hc := (normalChartAt (I := I) g (u x)).mdifferentiableAt one_ne_zero
    (normalChartAt_source g (u x))
  have hh := hc.hasMFDerivAt.comp x hu.hasMFDerivAt
  rw [mfderiv_normalChartAt_self] at hh
  convert! hh.hasFDerivAt using 1

set_option backward.isDefEq.respectTransparency false in


theorem tendsto_riemannianEDistOf_ray (g : SmoothRiemannianMetric I M)
    {u : V → M} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x) (w : V) :
    Tendsto (fun t : ℝ => |t| * (riemannianEDistOf g (u x) (u (x + t⁻¹ • w))).toReal)
      atTop (𝓝 (Real.sqrt (g.inner (u x)
        (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x w)))) := by
  have hU := hasFDerivAt_normal_coordinates g hu
  have hd := hU.lim w tendsto_norm_atTop_atTop
  have hn : Continuous (fun v : E => Real.sqrt (g.inner (u x) v v)) := by
    exact ((g.inner (u x)).continuous₂.comp (continuous_id.prodMk continuous_id)).sqrt
  have hlim := hn.continuousAt.tendsto.comp hd
  have hray : Tendsto (fun t : ℝ => x + t⁻¹ • w) atTop (𝓝 x) := by
    have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := x)).add (hi.smul (tendsto_const_nhds (x := w)))
  have heq := (hu.continuousAt.tendsto.comp hray).eventually
    (eventually_riemannianEDistOf_eq_normal_norm g (u x))
  apply hlim.congr'
  filter_upwards [heq] with t ht
  dsimp only [Function.comp_apply] at ht ⊢
  erw [ht, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  simp only [normalChartAt_centre, sub_zero, sqrt_metric_smul]

section Comparison

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [J.Boundaryless] [T2Space (TangentBundle J N)]

set_option backward.isDefEq.respectTransparency false in


theorem metric_differential_le_of_edist_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {u : V → M} {v : V → N} {x : V} {L : ℝ≥0}
    (hu : MDifferentiableAt 𝓘(ℝ, V) I u x)
    (hv : MDifferentiableAt 𝓘(ℝ, V) J v x)
    (hbound : ∀ y, riemannianEDistOf h (v x) (v y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g (u x) (u y)) (w : V) :
    Real.sqrt (h.inner (v x) (mfderiv 𝓘(ℝ, V) J v x w) (mfderiv 𝓘(ℝ, V) J v x w)) ≤
      L * Real.sqrt (g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x w)) := by
  have hlu := tendsto_riemannianEDistOf_ray g hu w
  have hlv := tendsto_riemannianEDistOf_ray h hv w
  apply le_of_tendsto_of_tendsto hlv (tendsto_const_nhds.mul hlu)
  have hray : Tendsto (fun t : ℝ => x + t⁻¹ • w) atTop (𝓝 x) := by
    have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := x)).add (hi.smul (tendsto_const_nhds (x := w)))
  have hlocal := (hu.continuousAt.tendsto.comp hray).eventually
    (eventually_riemannianEDistOf_eq_normal_norm g (u x))
  filter_upwards [hlocal] with t ht
  have hfin : riemannianEDistOf g (u x) (u (x + t⁻¹ • w)) ≠ ⊤ := by
    dsimp only [Function.comp_apply] at ht
    rw [ht]
    exact ENNReal.ofReal_ne_top
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
    (hbound (x + t⁻¹ • w))
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, mul_left_comm] using hh

end Comparison

end DifferentialGeometry.Geometry
