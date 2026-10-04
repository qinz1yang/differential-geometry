import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialStrainer
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialAnchors

/-!
# Annular splitting with the original radial function

LC70 preserves the signed centered distance to the original cone center on every source point.
The thresholds are uniform in the geometry and allow every larger normalization factor.
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem exists_original_radial_splitting_parameter {n : ℕ} (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    ∃ δstar Λstar : ℝ, 0 < δstar ∧ 0 < Λstar ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompleteSpace X],
      (∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
        Continuous c ∧ c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (c s) (c t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ n →
      ∀ (C : Type v) [MetricSpace C] (p : X) (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δstar →
      fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : @KleinerLottApprox X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
          inferInstance q (WithLp.toLp 2 (0, z)) β),
          ∀ x : X, (@KleinerLottApprox.toFun X
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
            inferInstance q (WithLp.toLp 2 (0, z)) β F x).fst = WithLp.toLp 2
            (Function.const (Fin 1) (lam * (dist p x - dist p q))) := by
  obtain ⟨σ, hσ, hσone, hproduce⟩ :=
    exists_original_radial_strainer_parameter.{u} hn hβ hβone
  obtain ⟨θ, δσ, Λσ, hθ, hθone, hθσ, hδσ, hΛσ, hanchors⟩ :=
    exists_original_radial_exact_scale_anchors.{u, v} hσ hσone
  refine ⟨δσ, max Λσ σ⁻¹, hδσ, hΛσ.trans_le (le_max_left _ _), ?_⟩
  intro X m hcomplete hsegments hdim C mC p o H δ F hδ hcomp q hqlo hqhi lam hlam hΛ
  have hΛa : Λσ ≤ lam := (le_max_left _ _).trans hΛ
  have hΛs : σ⁻¹ ≤ lam := (le_max_right _ _).trans hΛ
  obtain ⟨a, b, z, hqz, hexcess, hangle, hqa, hqb, hap, hbz, hopp⟩ :=
    hanchors X C hsegments p o H F hδ hcomp q hqlo hqhi lam hΛa
  have hsone : σ⁻¹ / lam ≤ 1 := (div_le_one₀ hlam).mpr hΛs
  have hball : @ball X (m.rescale lam hlam).toPseudoMetricSpace q σ⁻¹ =
      ball q (σ⁻¹ / lam) := by
    have hh := MetricSpace.rescale_ball m lam hlam q (σ⁻¹ / lam)
    have heq : lam * (σ⁻¹ / lam) = σ⁻¹ := by field_simp
    rwa [heq] at hh
  have hsub : ball q (σ⁻¹ / lam) ⊆ ball p 21 := by
    intro w hw
    have ht := dist_triangle w q p
    rw [dist_comm q p] at ht
    change dist w p < 21
    change dist w q < σ⁻¹ / lam at hw
    linarith
  have hcompLarge : fourPointComparison (σ * lam ^ 2) (ball p 21) := by
    apply hcomp.forall_ge (by positivity)
    have hσlam : 1 ≤ σ * lam := by
      have hh := mul_le_mul_of_nonneg_left hΛs hσ.le
      rw [mul_inv_cancel₀ hσ.ne'] at hh
      exact hh
    have hlamone : 1 ≤ lam := by
      have hinv : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσone.le
      exact hinv.trans hΛs
    nlinarith only [hσlam, hlamone]
  have hcompScaled := (fourPointComparison_rescale_iff (m := m) hlam hσ.le).mpr hcompLarge
  have hdimScaled : @dimH X (m.rescale lam hlam).toEMetricSpace
      (@ball X (m.rescale lam hlam).toPseudoMetricSpace q σ⁻¹) ≤ n := by
    rw [hball, MetricSpace.rescale_dimH]
    exact (dimH_mono (subset_univ _)).trans hdim
  have hcompleteScaled : @CompleteSpace X (m.rescale lam hlam).toUniformSpace :=
    (MetricSpace.rescale_completeSpace_iff m lam hlam).mpr hcomplete
  have ha : lam * dist q b = σ⁻¹ := by rw [hqb]; field_simp
  have hb : lam * dist q a = σ⁻¹ := by rw [hqa]; field_simp
  have hangle' : π - σ ≤ comparisonAngleNegCurvature σ
      (lam * dist q b) (lam * dist q a) (lam * dist b a) := by
    rw [comparisonAngleNegCurvature_comm, dist_comm b a]
    exact hopp.le
  have hbudget : 2 * (1 - cos θ) ≤ σ := by
    have hc := one_sub_sq_div_two_le_cos (x := θ)
    nlinarith only [hc, hθ.le, hθσ, hσ, hσone]
  have hrad : ∀ w, dist q w + dist w b = dist q b →
      dist q w - σ * dist q w ≤ dist p w - dist p q := by
    intro w hw
    have hwqb : dist q w ≤ dist q b := by linarith only [hw, dist_nonneg (x := w) (y := b)]
    have hwz : dist q w + dist w z = dist q z := by
      have h1 := dist_triangle w b z
      have h2 := dist_triangle q w z
      linarith only [hw, hbz, h1, h2]
    have hwB : w ∈ ball p 21 := by
      have h1 := dist_triangle w q p
      rw [dist_comm w q, dist_comm q p] at h1
      change dist w p < 21
      linarith only [h1, hwqb, hqb, hsone, hqhi]
    have hqB : q ∈ ball p 21 := by change dist q p < 21; rw [dist_comm]; linarith
    have hzB : z ∈ ball p 21 := by
      have h1 := dist_triangle z q p
      rw [dist_comm z q, hqz, dist_comm q p] at h1
      change dist z p < 21
      linarith only [h1, hqhi]
    by_cases hzero : dist q w = 0
    · have heq : q = w := dist_eq_zero.mp hzero
      subst w
      simp only [dist_self, mul_zero, sub_self, le_refl]
    · have hpos : 0 < dist q w := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
      have hh := outward_prefix_calibration (κ := 1 / 60) (by norm_num) hcomp
        (mem_ball_self (by norm_num)) hqB hzB hwB (by rw [dist_comm q p]; exact hqz)
        (by rw [dist_comm]; linarith only [hqhi]) hθ
        (hθone.trans (by linarith [two_le_pi])) hangle hpos hwz
      have he := mul_le_mul_of_nonneg_left hbudget hpos.le
      rw [dist_comm q p] at hh
      nlinarith only [hh.2, he]
  obtain ⟨Z, mZ, z0, G, hG⟩ := @hproduce X (m.rescale lam hlam) hcompleteScaled q p b a
    (fun x y η hη => MetricSpace.rescale_arbitrarily_short_curves
      (arbitrarily_short_curves_of_metric_segments hsegments) lam hlam x y hη)
    hdimScaled
    (fun w hw => ⟨ball p 21, isOpen_ball, hcompScaled, by rw [hball] at hw; exact hsub hw⟩)
    ha hb (by simpa only [MetricSpace.rescale_dist] using hangle')
    (fun w hw => by
      simp only [MetricSpace.rescale_dist] at hw ⊢
      have heq : dist q w + dist w b = dist q b := by nlinarith only [hw, hlam]
      have hh := mul_le_mul_of_nonneg_left (hrad w heq) hlam.le
      nlinarith only [hh])
    (by simpa only [MetricSpace.rescale_dist, mul_add] using congrArg (lam * ·) hap)
  refine ⟨Z, mZ, z0, G, ?_⟩
  intro x
  simpa only [MetricSpace.rescale_dist, ← mul_sub] using hG x

end GC.MetricGeometry
