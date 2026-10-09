import DifferentialGeometry.Geometry.Metric.Approximation.LineUnitBallSplitting
import DifferentialGeometry.Topology.MetricSpace.ZeroSetSmallCoreCover

/-!
# Annular one-splitting and the selected small-core cover (LC66, metric kernel)

Blueprint `master207A.tex`, LC66 (`thm:collapse-annular-splitting-cover`, lines 23841–23897).
On a compact geodesic space of Hausdorff dimension at most three, with a positive continuous
scale `ρ`, a radius assignment `T ρ ≤ r ≤ U ρ` fixed once and the LC16 zero stratum
`Z = {q | splittingRank (X, ρ(q)⁻¹ d, q) β 3 = 0}`, the LC64 selection `I` is taken first. If
every selected center carries the LC65 data at its own scale `r(i)` (curvature at least
`-(1/60)²` for `r(i)⁻¹ d` on the `21`-ball, and a pointed
Kleiner–Lott map of error below `δ'` from `(X, r(i)⁻¹ d, i)` to a cone with `RadialConeData`),
then every point `q` of every CLOSED shell `r(i)/10 ≤ d(i,q) ≤ 10 r(i)` admits a normalized
`(1, β₁)`-splitting of `(X, ρ(q)⁻¹ d, q)`, is not in `Z`, and the selected open tenth-radius
balls cover `Z`. The constants `δ', Λ'` depend only on `β₁`, and `T ≥ 20 Λ'` is imposed before the
selection.

Proof: LC62's neighboring bound (exported by LC64) gives `λ = r(i)/ρ(q) ≥ T/20 ≥ Λ'`; LC65 in
the distance `r(i)⁻¹ d` gives an exact-scale one-strainer for `λ r(i)⁻¹ d = ρ(q)⁻¹ d`; AC55
(`hasEuclideanSplitting_one_of_rescaled_strainer`) gives the splitting; LC16 excludes the shell
from `Z`; LC64's conditional clause gives the cover. The curvature data are stated in the
original distance: comparison at curvature `-(1/60)² r(i)⁻²` on `B(i, 21 r(i))` is comparison at
`-(1/60)²` for `r(i)⁻¹ d` (`fourPointComparison_rescale_iff`); the weaker levels consumed by AC55
come from `fourPointComparison.forall_ge` (lane MON).
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

/-- Segments survive a rescaling of the distance. -/
theorem rescale_segments {X : Type*} (m : MetricSpace X) {c : ℝ} (hc : 0 < c)
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t) :
    ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      @Continuous _ _ _ (m.rescale c hc).toUniformSpace.toTopologicalSpace f ∧
        f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, @dist X (m.rescale c hc).toDist (f s) (f t) =
          @dist X (m.rescale c hc).toDist x y * dist s t := by
  intro x y
  obtain ⟨f, hf, h0, h1, hd⟩ := hsegments x y
  refine ⟨f, hf, h0, h1, fun s t => ?_⟩
  simp only [MetricSpace.rescale_dist, hd]
  ring

/-- **LC66 (metric kernel).** -/
theorem exists_zero_stratum_small_core_cover {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompactSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ 3 →
      ∀ (r ρ : X → ℝ), Continuous ρ → ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → T ≤ U → ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ I : Set X, I.Finite ∧
        (∀ i ∈ I, (ball i (r i) ∩
            {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty ∧
          ∀ q, (ball q (r q) ∩ {q | @splittingRank.{u, 0} X
              (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}).Nonempty →
            ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
        I.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
          ⋃ i ∈ I, ball i (5 * r i) ∧
        ((∀ i ∈ I, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) ∧
            ∃ (C : Type v) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ∃ δ : ℝ,
              δ < δ' ∧ Nonempty (@KleinerLottApprox X C
                (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
                mC i o δ)) →
          (∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1) ∧
            @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ I, ball i (r i / 10)) := by
  obtain ⟨σ, hσ, hσone, hAC55⟩ :=
    exists_prescribed_splitting_parameter.{u} (n := 3) (by norm_num) hβ hβone
  obtain ⟨θ, δσ, Λσ, -, -, hδσ, hΛσ, hLC65⟩ :=
    exists_annular_exact_scale_strainer.{u, v} hσ hσone
  refine ⟨δσ, max Λσ σ⁻¹, hδσ, lt_max_of_lt_left hΛσ, ?_⟩
  intro X m _ hsegments hdim r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  set Z : Set X := {q | @splittingRank.{u, 0} X
    (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} with hZ
  have hrpos (p : X) : 0 < r p := (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨I, hfin, hmax, hdisj, hlocal, hcover, hsmall⟩ :=
    Metric.exists_zero_set_small_core_cover Z r ρ hρ hρpos hT
      hTU hlower hupper
  refine ⟨I, hfin, hmax, hdisj, hlocal, hcover, fun hdata => ?_⟩
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hshell : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      @HasEuclideanSplitting.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1) := by
    intro i hi q hq1 hq2
    obtain ⟨hcomp1, C, mC, o, ⟨H⟩, δ, hδ, ⟨φ⟩⟩ := hdata i hi
    have hcomp := hcomp1.forall_ge (by positivity)
    have hri := hrpos i
    have hri' : 0 < (r i)⁻¹ := inv_pos.mpr hri
    have hρq := hρpos q
    have hlampos : 0 < r i / ρ q := div_pos hri hρq
    have hlamT : T / 20 ≤ r i / ρ q := (hlocal i hi q hq2).2
    have hlamΛ : max Λσ σ⁻¹ ≤ r i / ρ q := by linarith
    have hlamΛσ : Λσ ≤ r i / ρ q := (le_max_left _ _).trans hlamΛ
    have hlamσ : σ⁻¹ ≤ r i / ρ q := (le_max_right _ _).trans hlamΛ
    -- LC65 in the distance `r(i)⁻¹ d`.
    have hcomp21 : @fourPointComparison X (m.rescale (r i)⁻¹ hri') ((1 / 60) ^ 2)
        (@ball X (m.rescale (r i)⁻¹ hri').toPseudoMetricSpace i 21) := by
      have hb := MetricSpace.rescale_ball m (r i)⁻¹ hri' i (21 * r i)
      have hc : (r i)⁻¹ * (21 * r i) = 21 := by field_simp
      rw [hc] at hb
      rw [hb, fourPointComparison_rescale_iff (m := m) hri' (by positivity)]
      exact hcomp _ le_rfl
    have hd1 : 1 / 10 ≤ @dist X (m.rescale (r i)⁻¹ hri').toDist i q := by
      rw [MetricSpace.rescale_dist, le_inv_mul_iff₀ hri]
      linarith
    have hd2 : @dist X (m.rescale (r i)⁻¹ hri').toDist i q ≤ 10 := by
      rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hri]
      linarith
    obtain ⟨a, b, -, -, -, -, hqa, hqb, -, -, hangle⟩ :=
      @hLC65 X C (m.rescale (r i)⁻¹ hri') mC (rescale_segments m hri' hsegments) i o H δ φ hδ
        hcomp21 q hd1 hd2 (r i / ρ q) hlamΛσ
    simp only [MetricSpace.rescale_dist] at hqa hqb hangle
    have hconv (x y : X) : r i / ρ q * ((r i)⁻¹ * dist x y) = (ρ q)⁻¹ * dist x y := by
      field_simp
    rw [hconv, hconv, hconv] at hangle
    have hρq' : 0 < (ρ q)⁻¹ := inv_pos.mpr hρq
    have hσρ : σ⁻¹ / (ρ q)⁻¹ ≤ r i := by
      rw [div_inv_eq_mul]
      have := (le_div_iff₀ hρq).mp hlamσ
      linarith
    have hK : (1 / 60) ^ 2 * (r i)⁻¹ ^ 2 ≤ σ * (ρ q)⁻¹ ^ 2 := by
      have hρr : (ρ q)⁻¹ = r i / ρ q * (r i)⁻¹ := by field_simp
      have h1 : 1 ≤ σ * (r i / ρ q) := by
        have := mul_le_mul_of_nonneg_left hlamσ hσ.le
        rwa [mul_inv_cancel₀ hσ.ne'] at this
      have h2 : 1 ≤ σ * (r i / ρ q) ^ 2 := by nlinarith
      rw [hρr, mul_pow, ← mul_assoc]
      have h3 : 0 ≤ (r i)⁻¹ ^ 2 := by positivity
      nlinarith
    refine hasEuclideanSplitting_one_of_rescaled_strainer hσ hAC55 (by norm_num) hcurves hρq'
      ((dimH_mono (subset_univ _)).trans (by exact_mod_cast hdim)) isOpen_ball
      (fun w hw => ?_) (hcomp _ hK) ?_ ?_ hangle
    · have hw' : dist w q < σ⁻¹ / (ρ q)⁻¹ := hw
      change dist w i < 21 * r i
      have ht := dist_triangle w q i
      rw [dist_comm q i] at ht
      linarith
    · rw [mul_comm, ← div_eq_mul_inv, div_eq_iff hρq.ne']
      have := (eq_div_iff hlampos.ne').mp hqa
      field_simp at this ⊢
      linarith
    · rw [mul_comm, ← div_eq_mul_inv, div_eq_iff hρq.ne']
      have := (eq_div_iff hlampos.ne').mp hqb
      field_simp at this ⊢
      linarith
  have hrank : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0 := by
    intro i hi q hq1 hq2
    have h := @le_splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 1
      (by norm_num) (hshell i hi q hq1 hq2)
    omega
  refine ⟨fun i hi q hq1 hq2 => ⟨hshell i hi q hq1 hq2, hrank i hi q hq1 hq2⟩, ?_⟩
  apply hsmall
  intro i hi z hz hshellz
  exact hrank i hi z hshellz.1 hshellz.2 hz

end GC.MetricGeometry
