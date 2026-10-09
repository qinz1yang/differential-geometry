import DifferentialGeometry.Geometry.Metric.Approximation.ZeroStratumSmallCoreCover
import DifferentialGeometry.Geometry.Metric.Approximation.MultipleEndsBlowdown
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# Multiple-ended models and the selected model with at most one end (LC75, LC77)

Blueprint `master207A.tex`, LC75 (`lem:collapse-model-line-cone`, lines 24436–24478) and LC77
(`thm:collapse-selected-model-one-end`, lines 24531–24557).

* LC75 (adapter): a proper geodesic space with nonnegative four-point comparison and two
  distinct unbounded components outside a compact set is isometric to `ℝ × Y` with `Y` compact
  (the zero slice meeting the compact set), and the SAME supplied LC21 cone, approximated by
  the globally rescaled model at every large scale, is pointed isometric to `(ℝ, 0)`. Both
  kernels already exist (`exists_isometryEquiv_real_prod_compact_of_unbounded_components`,
  `exists_isometryEquiv_real_of_rescaled_approximations`); the adapter states the row as one
  theorem.
* LC77 (metric kernel, per selected center): for every `0 < β₁ < 1` there are `δℓ, Λℓ > 0`
  such that, at a center `i` whose ball `B(i, r_i)` meets the LC16 zero stratum and on which the
  scale ratio `r_i / ρ(q)` is at least `Λℓ`, with LC76's curvature data at scale `r_i` and an
  actual pointed `δ`-map (`δ < δℓ`) from `(X, r_i⁻¹ d, i)` to the SAME supplied cone of a
  nonnegatively curved proper geodesic model `N`, the model `N` has at most one end. The
  selection version takes the LC64 selection, where LC62 supplies the scale ratio from
  `T ≥ 20 Λℓ`.
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w

/-- **LC75 (adapter).** A multiple-ended nonnegatively curved proper geodesic model splits off
a line with compact factor, and its supplied LC21 cone is pointed isometric to the real line. -/
theorem multiple_ends_model_splits_and_cone_is_line
    {N : Type w} {C : Type v} [mN : MetricSpace N] [ProperSpace N] [MetricSpace C] [ProperSpace C]
    (n₀ : N) (o : C)
    (hcone : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
      R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox N C
        (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n₀ o δ))
    (hcomp : fourPointComparison 0 (univ : Set N))
    (hsegments : ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {K : Set N} (hK : IsCompact K) {a b : N}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b))
    (hab : connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) :
    (∃ (Y : Type w) (m : MetricSpace Y), letI := m
      ∃ (y₀ : Y) (e : N ≃ᵢ WithLp 2 (ℝ × Y)),
        CompactSpace Y ∧ fourPointComparison 0 (univ : Set Y) ∧
        e.symm (WithLp.toLp 2 (0, y₀)) ∈ K) ∧
      ∃ e : C ≃ᵢ ℝ, e o = 0 := by
  obtain ⟨Y, mY, y₀, e, hY, hYcomp, hK0, -⟩ :=
    exists_isometryEquiv_real_prod_compact_of_unbounded_components hcomp hsegments hK ha hb hab
  exact ⟨⟨Y, mY, y₀, e, hY, hYcomp, hK0⟩,
    exists_isometryEquiv_real_of_rescaled_approximations n₀ o hcone hcomp hsegments hK ha hb hab⟩

/-- **LC77 (metric kernel, one selected center).** -/
theorem exists_selected_model_one_end_parameter {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompleteSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (i : X) {ri : ℝ} (hri : 0 < ri),
      dimH (ball i (2 * ri)) ≤ 3 →
      fourPointComparison ((1 / 60) ^ 2 * ri⁻¹ ^ 2) (ball i (21 * ri)) →
      (∀ q, dist i q < ri → Λℓ ≤ ri / ρ q) →
      (ball i ri ∩ {q | @splittingRank.{u, 0} X
          (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}).Nonempty →
      ∀ (N : Type w) [mN : MetricSpace N] [ProperSpace N] (n₀ : N)
        (C : Type v) [MetricSpace C] [ProperSpace C] (o : C),
      fourPointComparison 0 (univ : Set N) →
      (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
        R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox N C
          (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n₀ o δ)) →
      ∀ {δ : ℝ}, δ < δℓ →
      Nonempty (@KleinerLottApprox X C (m.rescale ri⁻¹ (inv_pos.mpr hri)) _ i o δ) →
      ∀ K : Set N, IsCompact K → ∀ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  obtain ⟨δℓ, Λℓ, hδℓ, hΛℓ, hLC76⟩ :=
    exists_line_unit_ball_splitting_parameter.{u} (n := 3) (by norm_num) hβ hβone
  refine ⟨δℓ, Λℓ, hδℓ, hΛℓ, ?_⟩
  intro X m _ hsegments ρ hρpos i ri hri hdim hcomp1 hscale hZ N mN _ n₀ C _ _ o hNcomp hNseg
    hcone δ hδ ⟨φ⟩ K hK a b ha hb
  have hcomp := hcomp1.forall_ge (by positivity)
  by_contra hab
  obtain ⟨e, he⟩ :=
    exists_isometryEquiv_real_of_rescaled_approximations n₀ o hcone hNcomp hNseg hK ha hb hab
  have hri' : 0 < ri⁻¹ := inv_pos.mpr hri
  let F := @KleinerLottApprox.mapTargetIsometryAt X C ℝ (m.rescale ri⁻¹ hri') _ _ i o δ φ e 0
    he
  obtain ⟨q, hqball, hqZ⟩ := hZ
  have hqi : dist i q < ri := by rw [dist_comm]; exact hqball
  have hρq := hρpos q
  have hcomplete : @CompleteSpace X (m.rescale ri⁻¹ hri').toUniformSpace :=
    (MetricSpace.rescale_completeSpace_iff m ri⁻¹ hri').mpr inferInstance
  have hball (s : ℝ) : @ball X (m.rescale ri⁻¹ hri').toPseudoMetricSpace i s =
      ball i (ri * s) := by
    have h := MetricSpace.rescale_ball m ri⁻¹ hri' i (ri * s)
    have hc : ri⁻¹ * (ri * s) = s := by field_simp
    rwa [hc] at h
  have hdim' : @dimH X (m.rescale ri⁻¹ hri').toEMetricSpace
      (@ball X (m.rescale ri⁻¹ hri').toPseudoMetricSpace i 2) ≤ (3 : ℕ) := by
    rw [hball, MetricSpace.rescale_dimH, mul_comm]
    exact_mod_cast hdim
  have hcomp' : ∀ K' : ℝ, (1 / 60) ^ 2 ≤ K' → @fourPointComparison X (m.rescale ri⁻¹ hri') K'
      (@ball X (m.rescale ri⁻¹ hri').toPseudoMetricSpace i 7) := by
    intro K' hK'
    rw [hball, fourPointComparison_rescale_iff (m := m) hri' (by linarith [sq_nonneg (1 / 60 : ℝ)])]
    apply (hcomp _ _).mono
    · exact ball_subset_ball (by nlinarith)
    · exact mul_le_mul_of_nonneg_right hK' (by positivity)
  have hq1 : q ∈ @ball X (m.rescale ri⁻¹ hri').toPseudoMetricSpace i 1 := by
    rw [hball, mul_one]
    exact hqball
  have hlam : 0 < (ρ q / ri)⁻¹ := inv_pos.mpr (div_pos hρq hri)
  have hΛ : Λℓ ≤ (ρ q / ri)⁻¹ := by
    rw [inv_div]
    exact hscale q hqi
  have hsplit := @hLC76 X (m.rescale ri⁻¹ hri') hcomplete (rescale_segments m hri' hsegments) i
    hdim' (hcomp' _ le_rfl) δ 0 F hδ q hq1 (ρ q / ri)⁻¹ hlam hΛ
  rw [MetricSpace.rescale_inv_ratio m hri hρq] at hsplit
  have hrank := @le_splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr hρq)) q β 3 1
    (by norm_num) hsplit
  have hq0 : @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr hρq)) q β 3 = 0 := hqZ
  omega

end GC.MetricGeometry
