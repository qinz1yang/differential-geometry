import DifferentialGeometry.Geometry.Metric.Approximation.SelectedModelOneEnd
import DifferentialGeometry.Geometry.Comparison.OutwardPrefixCalibration

/-!
# The zero-stratum local export, partial form (LC80 items 1, 3 without adaptedness, 4)

Blueprint `master207A.tex`, LC80 (`prop:collapse-zero-export`, lines 24719–24757). This module
is the consumer of LC64, LC65, LC66, LC69, LC75, LC76 and LC77.

* `zero_stratum_partial_export`: one choice of constants `δ' = min`, `Λ' = max` of LC66's and
  LC77's thresholds, imposed BEFORE the selection; families of models `N`, cones `C` with
  `RadialConeData`, maps and errors fixed before the selection; the LC64 selection of maximal
  candidates for the LC16 zero stratum `Z`; under the joint data at every selected center
  (curvature at scale `r(i)`, the cone `C_i` proper and the supplied LC21 cone of the SAME
  nonnegative model `N_i`, and an actual pointed map of error below `δ'` from
  `(X, r(i)⁻¹ d, i)` to `C_i`), it exports: finitely many disjoint balls each meeting `Z` (item 1),
  the open tenth-radius cover of `Z` (item 1), a normalized one-splitting at every point of
  every CLOSED shell (item 3, without the adapted-coordinate clause, which needs LC70–LC73),
  and at most one end for every attached model (item 4).
* `annular_strainer_outward_anchor_calibration`: LC69 applied to LC65's own construction: the
  outward anchor `b` at distance `s = σ⁻¹/λ` from `q` satisfies
  `0 ≤ d(p,q) + s - d(p,b) < 2 s (1 - cos θ)` for the original center `p`.

Item 2 (core/interior identification, LC61) and the adapted radial coordinate of item 3
(LC70–LC73) are not part of this export.
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

/-- **LC80, partial export (items 1, 3 without adaptedness, 4).** The attached models, cones,
cone data, maps and errors form families indexed by all points, fixed before the selection;
their properties are required at the selected centers only. -/
theorem zero_stratum_partial_export {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompactSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ 3 →
      ∀ (N C : X → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) → ∀ (δ : X → ℝ),
      ∀ (r ρ : X → ℝ), Continuous ρ → ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → T ≤ U → ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ I : Set X, I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ I, (ball i (r i) ∩
          {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty) ∧
        ((∀ i ∈ I, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧ Nonempty (@KleinerLottApprox X (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i))) →
          (∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1)) ∧
          {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ I, ball i (r i / 10) ∧
          ∀ i ∈ I, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨δ₁, Λ₁, hδ₁, hΛ₁, h66⟩ := exists_zero_stratum_small_core_cover.{u, v} hβ hβone
  obtain ⟨δ₂, Λ₂, hδ₂, hΛ₂, h77⟩ := exists_selected_model_one_end_parameter.{u, v, v} hβ hβone
  refine ⟨min δ₁ δ₂, max Λ₁ Λ₂, lt_min hδ₁ hδ₂, lt_max_of_lt_left hΛ₁, ?_⟩
  intro X m _ hsegments hdim N C mN _ mC _ n₀ o H δ r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  obtain ⟨I, hfin, hmax, hdisj, hloc, -, hcond⟩ := h66 X hsegments hdim r ρ hρ hρpos hT
    ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hTΛ) hTU hlower hupper
  refine ⟨I, hfin, hdisj, fun i hi => (hmax i hi).1, fun hdata => ?_⟩
  obtain ⟨hshell, hcover⟩ := hcond fun i hi => by
    obtain ⟨hcomp, -, -, -, hδ, hφ⟩ := hdata i hi
    exact ⟨hcomp, C i, mC i, o i, ⟨H i⟩, δ i, hδ.trans_le (min_le_left _ _), hφ⟩
  refine ⟨fun i hi q hq1 hq2 => (hshell i hi q hq1 hq2).1, hcover, ?_⟩
  intro i hi
  obtain ⟨hcomp, hNcomp, hNseg, hcone, hδ, hφ⟩ := hdata i hi
  have hri : 0 < r i := (mul_pos hT (hρpos i)).trans_le (hlower i)
  have hT2 : 20 * Λ₂ ≤ T := (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hTΛ
  exact h77 X hsegments ρ hρpos i hri ((dimH_mono (subset_univ _)).trans hdim) hcomp
    (fun q hq => by have := (hloc i hi q (by linarith)).2; linarith) (hmax i hi).1
    (N i) (n₀ i) (C i) (o i) hNcomp hNseg hcone (hδ.trans_le (min_le_right _ _)) hφ

/-- **LC69 on LC65's construction.** The outward anchor of the exact-scale strainer is
calibrated by the original center. -/
theorem annular_strainer_outward_anchor_calibration {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ δσ Λσ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < δσ ∧ 0 < Λσ ∧
      ∀ (X : Type u) (C : Type v) [MetricSpace X] [MetricSpace C],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (p : X) (o : C), RadialConeData o → ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < δσ → fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam : ℝ, Λσ ≤ lam →
      ∃ b : X, dist q b = σ⁻¹ / lam ∧
        0 ≤ dist p q + dist q b - dist p b ∧
        dist p q + dist q b - dist p b < 2 * dist q b * (1 - cos θ) := by
  obtain ⟨θ, δσ, Λσ, hθ, hθone, hδσ, hΛσ, h65⟩ := exists_annular_exact_scale_strainer.{u, v} hσ hσone
  refine ⟨θ, δσ, Λσ, hθ, hθone, hδσ, hΛσ, ?_⟩
  intro X C _ _ hsegments p o H δ φ hδ hcomp q hq1 hq2 lam hlam
  obtain ⟨-, b, z, hqz, hex, hangle, -, hqb, -, hbz, -⟩ :=
    h65 X C hsegments p o H φ hδ hcomp q hq1 hq2 lam hlam
  have hqp : dist q p = dist p q := dist_comm q p
  have hσlam : 0 < σ⁻¹ / lam := div_pos (inv_pos.mpr hσ) (hΛσ.trans_le hlam)
  have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
  have hqB : q ∈ ball p 21 := by change dist q p < 21; linarith
  have hpz_up : dist p z ≤ 2 * dist p q := by
    have h := dist_triangle p q z
    linarith
  have hzB : z ∈ ball p 21 := by change dist z p < 21; rw [dist_comm]; linarith
  have hbz' : dist b z = dist q z - dist q b := by linarith
  have hbB : b ∈ ball p 21 := by
    change dist b p < 21
    have h := dist_triangle b q p
    rw [dist_comm b q] at h
    have hz0 : 0 ≤ dist b z := dist_nonneg
    linarith
  have h := outward_prefix_calibration (κ := 1 / 60) (θ := θ) (by norm_num) hcomp hpB hqB hzB hbB
    (by rw [hqz, hqp]) (by rw [hqp]; linarith) hθ (by linarith [one_le_pi_div_two])
    hangle (by rw [hqb]; exact hσlam) hbz
  rw [hqp] at h
  exact ⟨b, hqb, h⟩

end GC.MetricGeometry
