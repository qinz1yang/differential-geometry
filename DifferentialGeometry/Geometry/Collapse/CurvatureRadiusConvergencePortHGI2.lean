import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBoundsHGI2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

open Filter DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u v w

private theorem exists_inverse_sqrt_pinching {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ δ > 0, δ < κ ∧
      |1 / Real.sqrt (κ + δ) - 1 / Real.sqrt κ| < ε ∧
      |1 / Real.sqrt (κ - δ) - 1 / Real.sqrt κ| < ε := by
  have hcont : ContinuousAt (fun r : ℝ => 1 / Real.sqrt r) κ :=
    continuousAt_const.div₀ continuousAt_id.sqrt (Real.sqrt_pos.mpr hκ).ne'
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  let δ := min η κ / 2
  have hδ : 0 < δ := half_pos (lt_min hη hκ)
  have hδη : δ < η := (half_lt_self (lt_min hη hκ)).trans_le (min_le_left _ _)
  have hδκ : δ < κ := (half_lt_self (lt_min hη hκ)).trans_le (min_le_right _ _)
  refine ⟨δ, hδ, hδκ, ?_, ?_⟩
  · have hdist : dist (κ + δ) κ < η := by
      simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ] using hδη
    simpa only [Real.dist_eq] using hclose hdist
  · have hdist : dist (κ - δ) κ < η := by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
      exact hδη
    simpa only [Real.dist_eq] using hclose hdist

theorem exists_sectional_tolerance_curvatureRadius_close
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ δ > 0, δ < κ ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] (H : Type v) [TopologicalSpace H]
        (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M] (g : SmoothRiemannianMetric I M) (p : M),
        (∀ q ∈ riemannianBallOf g p (1 / Real.sqrt κ),
          SectionalBoundedBelowAt g q (-(κ + δ))) →
        (∃ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] ∧
          sectionalCurvature g p v w ≤ -(κ - δ)) →
        curvatureRadius g p ≠ ⊤ ∧
          |(curvatureRadius g p).toReal - 1 / Real.sqrt κ| < ε := by
  obtain ⟨δ, hδ, hδκ, hleft, hright⟩ := exists_inverse_sqrt_pinching hκ hε
  refine ⟨δ, hδ, hδκ, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ g p hlower
  rintro ⟨v, w, hvw, hupper⟩
  have hplus : 0 < κ + δ := add_pos hκ hδ
  have hminus : 0 < κ - δ := sub_pos.mpr hδκ
  have hleftpos : 0 < 1 / Real.sqrt (κ + δ) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr hplus)
  have hrightpos : 0 < 1 / Real.sqrt (κ - δ) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr hminus)
  have hradius : 1 / Real.sqrt (κ + δ) ≤ 1 / Real.sqrt κ :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hκ)
      (Real.sqrt_le_sqrt (le_add_of_nonneg_right hδ.le))
  have hsec : ∀ q ∈ riemannianBallOf g p (1 / Real.sqrt (κ + δ)),
      SectionalBoundedBelowAt g q (-((1 / Real.sqrt (κ + δ)) ^ 2)⁻¹) := by
    intro q hq
    simpa only [one_div, inv_pow, inv_inv, Real.sq_sqrt hplus.le]
      using hlower q (riemannianBallOf_mono g p hradius hq)
  have hlo : ENNReal.ofReal (1 / Real.sqrt (κ + δ)) ≤ curvatureRadius g p := by
    unfold curvatureRadius
    exact le_iSup_of_le (1 / Real.sqrt (κ + δ))
      (le_iSup_of_le hleftpos (le_iSup_of_le hsec le_rfl))
  have hhi : curvatureRadius g p ≤ ENNReal.ofReal (1 / Real.sqrt (κ - δ)) := by
    apply curvatureRadius_le_of_sectionalCurvature_le g hrightpos
      (by rw [riemannianEDistOf_self]; exact bot_le) v w hvw
    simpa only [one_div, inv_pow, inv_inv, Real.sq_sqrt hminus.le] using hupper
  have hfinite : curvatureRadius g p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hloreal := ENNReal.toReal_mono hfinite hlo
  have hhireal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hhi
  rw [ENNReal.toReal_ofReal hleftpos.le] at hloreal
  rw [ENNReal.toReal_ofReal hrightpos.le] at hhireal
  refine ⟨hfinite, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have := (abs_lt.mp hleft).1
    linarith
  · have := (abs_lt.mp hright).2
    linarith

theorem tendsto_curvatureRadius_of_uniform_sectional_pinching
    {ι α : Type*} {l : Filter ι} {s : Set α} {κ : ℝ} (hκ : 0 < κ)
    {E : ι → Type u} [∀ t, NormedAddCommGroup (E t)] [∀ t, NormedSpace ℝ (E t)]
    [∀ t, FiniteDimensional ℝ (E t)] {H : ι → Type v} [∀ t, TopologicalSpace (H t)]
    (I : ∀ t, ModelWithCorners ℝ (E t) (H t)) [∀ t, (I t).Boundaryless]
    {M : ι → Type w} [∀ t, TopologicalSpace (M t)] [∀ t, ChartedSpace (H t) (M t)]
    [∀ t, IsManifold (I t) ∞ (M t)] [∀ t, T2Space (M t)]
    (g : ∀ t, SmoothRiemannianMetric (I t) (M t)) (p : ∀ t, α → M t)
    (hpinch : ∀ δ > 0, δ < κ → ∀ᶠ t in l, ∀ x ∈ s,
      (∀ q ∈ riemannianBallOf (g t) (p t x) (1 / Real.sqrt κ),
        SectionalBoundedBelowAt (g t) q (-(κ + δ))) ∧
      ∃ v w : TangentSpace (I t) (p t x), LinearIndependent ℝ ![v, w] ∧
        sectionalCurvature (g t) (p t x) v w ≤ -(κ - δ)) :
    Tendsto (fun z : ι × α => curvatureRadius (g z.1) (p z.1 z.2))
      (l ×ˢ 𝓟 s) (𝓝 (ENNReal.ofReal (1 / Real.sqrt κ))) := by
  have hclose : ∀ ε > 0, ∀ᶠ t in l, ∀ x ∈ s,
      curvatureRadius (g t) (p t x) ≠ ⊤ ∧
        |(curvatureRadius (g t) (p t x)).toReal - 1 / Real.sqrt κ| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδκ, hδclose⟩ :=
      exists_sectional_tolerance_curvatureRadius_close hκ hε
    filter_upwards [hpinch δ hδ hδκ] with t ht
    intro x hx
    exact hδclose (E t) (H t) (I t) (M t) (g t) (p t x) (ht x hx).1 (ht x hx).2
  have hreal : TendstoUniformlyOn (fun t x => (curvatureRadius (g t) (p t x)).toReal)
      (fun _ => 1 / Real.sqrt κ) l s := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hclose ε hε] with t ht
    intro x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact (ht x hx).2
  have hlim : Tendsto (fun z : ι × α => (curvatureRadius (g z.1) (p z.1 z.2)).toReal)
      (l ×ˢ 𝓟 s) (𝓝 (1 / Real.sqrt κ)) := tendsto_prod_principal_iff.mpr hreal
  have hofReal : Tendsto
      (fun z : ι × α => ENNReal.ofReal (curvatureRadius (g z.1) (p z.1 z.2)).toReal)
      (l ×ˢ 𝓟 s) (𝓝 (ENNReal.ofReal (1 / Real.sqrt κ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  apply hofReal.congr'
  change ∀ᶠ z : ι × α in l ×ˢ 𝓟 s,
    ENNReal.ofReal (curvatureRadius (g z.1) (p z.1 z.2)).toReal =
      curvatureRadius (g z.1) (p z.1 z.2)
  rw [eventually_prod_principal_iff]
  filter_upwards [hclose 1 zero_lt_one] with t ht
  intro x hx
  exact ENNReal.ofReal_toReal (ht x hx).1

end DifferentialGeometry.Geometry.Collapse
