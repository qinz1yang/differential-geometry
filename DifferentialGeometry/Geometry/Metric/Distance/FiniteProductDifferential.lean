import DifferentialGeometry.Geometry.Metric.Distance.FiniteDifferential
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameExamples

/-!
# Differential of an actual local L² metric decomposition

An exact local squared-distance identity gives the sum of the ambient metric pairings and the
ordinary vector-space pairing. The proof uses genuine finite normal-chart distance limits.
-/

set_option autoImplicit false
noncomputable section
open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.FiniteMetricDistance

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inner_self_mfderiv_eq_of_l2_dist_sq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)))
    {u v : V → M} {a : V → F} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x)
    (hv : MDifferentiableAt 𝓘(ℝ, V) I v x) (ha : DifferentiableAt ℝ a x)
    (hdist : ∀ᶠ y in 𝓝 x,
      dist (u x) (u y) ^ 2 = dist (v x) (v y) ^ 2 + dist (a x) (a y) ^ 2) (w : V) :
    g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x w) =
      g.inner (v x) (mfderiv 𝓘(ℝ, V) I v x w) (mfderiv 𝓘(ℝ, V) I v x w) +
        inner ℝ (fderiv ℝ a x w) (fderiv ℝ a x w) := by
  have hline : Tendsto (fun t : ℝ => x + t⁻¹ • w) atTop (𝓝 x) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul
        (tendsto_const_nhds (x := w)))
  have hvector : Tendsto (fun t : ℝ => |t| * dist (a x) (a (x + t⁻¹ • w))) atTop
      (𝓝 ‖fderiv ℝ a x w‖) := by
    have h := (ha.hasFDerivAt.lim w tendsto_norm_atTop_atTop).norm
    apply h.congr'
    filter_upwards with t
    simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm']
  have heq : (fun t : ℝ => (|t| * dist (u x) (u (x + t⁻¹ • w))) ^ 2) =ᶠ[atTop]
      (fun t : ℝ => (|t| * dist (v x) (v (x + t⁻¹ • w))) ^ 2 +
        (|t| * dist (a x) (a (x + t⁻¹ • w))) ^ 2) := by
    filter_upwards [hline.eventually hdist] with t ht
    rw [mul_pow, mul_pow, mul_pow, ht]
    ring
  have h := tendsto_nhds_unique (((tendsto_dist_ray g hr hnorm hu w).pow 2).congr' heq)
    (((tendsto_dist_ray g hr hnorm hv w).pow 2).add (hvector.pow 2))
  rw [Real.sq_sqrt (g.inner_self_nonneg' (u x) _),
    Real.sq_sqrt (g.inner_self_nonneg' (v x) _), ← real_inner_self_eq_norm_sq] at h
  exact h

theorem inner_mfderiv_eq_of_l2_dist_sq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)))
    {u v : V → M} {a : V → F} {x : V} (hu : MDifferentiableAt 𝓘(ℝ, V) I u x)
    (hv : MDifferentiableAt 𝓘(ℝ, V) I v x) (ha : DifferentiableAt ℝ a x)
    (hdist : ∀ᶠ y in 𝓝 x,
      dist (u x) (u y) ^ 2 = dist (v x) (v y) ^ 2 + dist (a x) (a y) ^ 2) (w z : V) :
    g.inner (u x) (mfderiv 𝓘(ℝ, V) I u x w) (mfderiv 𝓘(ℝ, V) I u x z) =
      g.inner (v x) (mfderiv 𝓘(ℝ, V) I v x w) (mfderiv 𝓘(ℝ, V) I v x z) +
        inner ℝ (fderiv ℝ a x w) (fderiv ℝ a x z) := by
  let L₁ : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I u x
  let L₂ : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I v x
  let A := fderiv ℝ a x
  let B₁ : E →L[ℝ] E →L[ℝ] ℝ := g.inner (u x)
  let B₂ : E →L[ℝ] E →L[ℝ] ℝ := g.inner (v x)
  have hdiag (q : V) : B₁ (L₁ q) (L₁ q) = B₂ (L₂ q) (L₂ q) + inner ℝ (A q) (A q) :=
    inner_self_mfderiv_eq_of_l2_dist_sq g hr hnorm hu hv ha hdist q
  have hw := hdiag w
  have hz := hdiag z
  have hsum := hdiag (w + z)
  have hsym₁ : B₁ (L₁ z) (L₁ w) = B₁ (L₁ w) (L₁ z) := g.symm (u x) _ _
  have hsym₂ : B₂ (L₂ z) (L₂ w) = B₂ (L₂ w) (L₂ z) := g.symm (v x) _ _
  simp only [map_add, add_apply, inner_add_left, inner_add_right, hsym₁, hsym₂,
    real_inner_comm (A z) (A w)] at hsum
  change B₁ (L₁ w) (L₁ z) = B₂ (L₂ w) (L₂ z) + inner ℝ (A w) (A z)
  have hsymA : inner ℝ (A z) (A w) = inner ℝ (A w) (A z) := real_inner_comm _ _
  linarith only [hw, hz, hsum, hsymA]

open DifferentialGeometry.Geometry.ExactSplitting in
theorem real_l2_metric_differential (x w z : ℝ) :
    realFrameMetric.inner x w z = realFrameMetric.inner 0 0 0 + inner ℝ w z := by
  have hn : ∀ (p : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner p v v)) := by
    intro p v
    change ‖(v : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : ℝ) v))
    rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]
  have hd : ∀ᶠ y in 𝓝 x,
      dist (id x) (id y) ^ 2 = dist (0 : ℝ) 0 ^ 2 + dist (id x) (id y) ^ 2 := by
    filter_upwards with y
    simp only [dist_self, zero_pow (by decide : 2 ≠ 0), zero_add]
  have h := inner_mfderiv_eq_of_l2_dist_sq (r := 2) realFrameMetric le_rfl hn
    (u := id) (v := fun _p : ℝ => 0) (a := id) (x := x)
    mdifferentiableAt_id mdifferentiableAt_const differentiableAt_id hd w z
  simp only [id_eq, mfderiv_id, mfderiv_const, fderiv_id] at h
  change realFrameMetric.inner x w z = realFrameMetric.inner 0 0 0 + inner ℝ w z at h
  exact h

end DifferentialGeometry.Geometry.FiniteMetricDistance
