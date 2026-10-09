import DifferentialGeometry.Geometry.Collapse.RankOneSmoothingDerivative
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartDistanceDini
import DifferentialGeometry.Analysis.Calculus.DistanceSmoothing.SeminormMollification

/-!
# Integrating a minimizing-direction test along a curve (the Riemannian step of FC16)

Let `η` be differentiable along a curve `c` of speed at most one avoiding `q`, and suppose that
at every point of the curve EVERY minimizing unit direction `w` toward `q` satisfies
`|dη(X) - g(w, X)| ≤ K |X|`. Then `η + d_q` changes by at most `K` times the parameter length.

Only the UPPER first variation of the distance is used: the smooth upper support
`infDist_upper_support_of_isClosed` at each point of the curve, once along the curve and once
along its reversal. No differentiability of the distance (and no Rademacher theorem) is used.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The local step: at a point of the curve, `η + d_q` is dominated near the point by a
function differentiable at the point with derivative of absolute value at most `K`. -/
private theorem local_direction_test_step (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {q : M} {η : M → ℝ} {c : ℝ → M} {t K : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hη : MDifferentiableAt I 𝓘(ℝ, ℝ) η (c t))
    (hspeed : g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) (mfderiv 𝓘(ℝ, ℝ) I c t 1) ≤ 1)
    (hq : c t ≠ q)
    (htest : ∀ w ∈ minimizingDirectionsTo g hEnorm {q} (c t), ∀ X : TangentSpace I (c t),
      |mvfderiv (I := I) η (c t) X - g.inner (c t) w X| ≤ K * Real.sqrt (g.inner (c t) X X)) :
    ∃ ψ : ℝ → ℝ, ∃ D : ℝ, HasDerivAt ψ D t ∧ |D| ≤ K ∧
      ∀ᶠ s in 𝓝 t, (η (c s) + dist (c s) q) - (η (c t) + dist (c t) q) ≤ ψ s - ψ t := by
  have hpos : 0 < Metric.infDist (c t) ({q} : Set M) := by
    rw [Metric.infDist_singleton]
    exact dist_pos.mpr hq
  obtain ⟨ρ, u, hρ, hval, hupper, hu, hgrad⟩ :=
    infDist_upper_support_of_isClosed g hEnorm isClosed_singleton (singleton_nonempty q) hpos
  set V : TangentSpace I (c t) := mfderiv 𝓘(ℝ, ℝ) I c t 1 with hV
  have hηl := hasDerivAt_comp_mfderiv_along I η c t hη hc
  have hρl := hasDerivAt_comp_mfderiv_along I ρ c t (hρ.mdifferentiableAt (by simp)) hc
  change HasDerivAt (fun s => η (c s)) (mvfderiv (I := I) η (c t) V) t at hηl
  change HasDerivAt (fun s => ρ (c s)) (mvfderiv (I := I) ρ (c t) V) t at hρl
  have hρV : mvfderiv (I := I) ρ (c t) V = -g.inner (c t) u V := by
    rw [← inner_gradientFun, hgrad, map_neg]
    rfl
  have hK : 0 ≤ K := by
    have h := htest u hu u
    rw [hu.1, Real.sqrt_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hsq : Real.sqrt (g.inner (c t) V V) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hspeed
  have hsum : HasDerivAt (fun s => η (c s) + ρ (c s))
      (mvfderiv (I := I) η (c t) V + mvfderiv (I := I) ρ (c t) V) t := hηl.add hρl
  rw [hρV, ← sub_eq_add_neg] at hsum
  refine ⟨fun s => η (c s) + ρ (c s), mvfderiv (I := I) η (c t) V - g.inner (c t) u V,
    hsum, ?_, ?_⟩
  · exact (htest u hu V).trans ((mul_le_mul_of_nonneg_left hsq hK).trans (by rw [mul_one]))
  · have hct : Tendsto c (𝓝 t) (𝓝 (c t)) := hc.continuousAt.tendsto
    filter_upwards [hct.eventually hupper] with s hs
    rw [Metric.infDist_singleton] at hs hval
    linarith

private theorem increment_lt_of_hasDerivAt {ψ : ℝ → ℝ} {D c t : ℝ}
    (hψ : HasDerivAt ψ D t) (hDc : D < c) :
    ∀ᶠ s in 𝓝[>] t, ψ s - ψ t < c * (s - t) := by
  have h := hψ.hasDerivWithinAt.limsup_slope_le' (s := Ioi t) (lt_irrefl t) hDc
  filter_upwards [h, self_mem_nhdsWithin] with s hs hst
  have hpos : 0 < s - t := sub_pos.mpr hst
  rw [slope_def_field, div_lt_iff₀ hpos] at hs
  exact hs

/-- **Integration of a minimizing-direction test (the Riemannian step of FC16).** Along a curve
of speed at most one on `[a, b]` avoiding `q`, if EVERY minimizing unit direction `w` toward `q`
at every point satisfies `|dη(X) - g(w, X)| ≤ K |X|_g`, then `η + d_q` changes by at most
`K (b - a)`. -/
theorem abs_sub_le_of_minimizingDirection_test (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {q : M} {η : M → ℝ} {c : ℝ → M} {a b K : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hη : ∀ t ∈ Icc a b, MDifferentiableAt I 𝓘(ℝ, ℝ) η (c t))
    (hspeed : ∀ t ∈ Icc a b,
      g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) (mfderiv 𝓘(ℝ, ℝ) I c t 1) ≤ 1)
    (hq : ∀ t ∈ Icc a b, c t ≠ q)
    (htest : ∀ t ∈ Icc a b, ∀ w ∈ minimizingDirectionsTo g hEnorm {q} (c t),
      ∀ X : TangentSpace I (c t),
      |mvfderiv (I := I) η (c t) X - g.inner (c t) w X| ≤ K * Real.sqrt (g.inner (c t) X X)) :
    |(η (c b) + dist (c b) q) - (η (c a) + dist (c a) q)| ≤ K * (b - a) := by
  set φ : ℝ → ℝ := fun s => η (c s) + dist (c s) q with hφ
  have hφc : ContinuousOn φ (Icc a b) := by
    intro t ht
    exact (((hη t ht).continuousAt.comp (hc t ht).continuousAt).add
      ((hc t ht).continuousAt.dist continuousAt_const)).continuousWithinAt
  have hstep (t : ℝ) (ht : t ∈ Icc a b) := local_direction_test_step g hEnorm (hc t ht)
    (hη t ht) (hspeed t ht) (hq t ht) (htest t ht)
  have hupper : φ b - φ a ≤ K * (b - a) := by
    refine sub_le_mul_sub_of_eventually_increment_le hab hφc fun t ht c' hc' => ?_
    obtain ⟨ψ, D, hψ, hD, hdom⟩ := hstep t (Ico_subset_Icc_self ht)
    filter_upwards [increment_lt_of_hasDerivAt hψ ((le_abs_self D).trans hD |>.trans_lt hc'),
      nhdsWithin_le_nhds hdom] with s hs hds
    exact hds.trans hs.le
  have hlower : φ a - φ b ≤ K * (b - a) := by
    set φr : ℝ → ℝ := fun τ => φ (a + b - τ) with hφr
    have hmaps : MapsTo (fun τ : ℝ => a + b - τ) (Icc a b) (Icc a b) := by
      intro τ hτ
      exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hφrc : ContinuousOn φr (Icc a b) :=
      hφc.comp (by fun_prop) hmaps
    have h := sub_le_mul_sub_of_eventually_increment_le (φ := φr) (B := K) hab hφrc ?_
    · simpa only [hφr, add_sub_cancel_right, add_sub_cancel_left] using h
    intro τ hτ c' hc'
    have ht : a + b - τ ∈ Icc a b := hmaps (Ico_subset_Icc_self hτ)
    obtain ⟨ψ, D, hψ, hD, hdom⟩ := hstep (a + b - τ) ht
    have hrev : HasDerivAt (fun τ' : ℝ => a + b - τ') (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub (a + b)
    have hψr : HasDerivAt (fun τ' => ψ (a + b - τ')) (D * -1) τ := hψ.comp τ hrev
    have hDr : D * -1 < c' := by
      have := neg_abs_le D
      linarith
    have htend : Tendsto (fun τ' : ℝ => a + b - τ') (𝓝 τ) (𝓝 (a + b - τ)) :=
      ((continuous_const.sub continuous_id).tendsto τ)
    filter_upwards [increment_lt_of_hasDerivAt hψr hDr,
      nhdsWithin_le_nhds (htend.eventually hdom)] with s hs hds
    exact hds.trans hs.le
  exact abs_le.mpr ⟨by linarith, hupper⟩

end DifferentialGeometry.Geometry.Collapse
