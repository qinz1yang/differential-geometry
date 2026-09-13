import DifferentialGeometry.Analysis.Elliptic.Euclidean.GradientEstimate
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp

open Filter Set InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

open Parabolic.Euclidean

private theorem norm_lapEval_le
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V →L[ℝ] F) :
    ‖lapEval A‖ ≤ Module.finrank ℝ V * ‖A‖ := by
  have h := lapEval_dist_le A 0
  have hd : dist A 0 = ‖A‖ := dist_zero_right A
  rw [map_zero, dist_zero_right, hd] at h
  exact h

private theorem norm_laplacian_ballCutoff_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {c : V} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ‖Laplacian.laplacian (ballCutoff c r R) x‖ ≤
      Module.finrank ℝ V * ballCutoffFDeriv2Bound r R := by
  have he : Laplacian.laplacian (ballCutoff c r R) x =
      lapEval (ballCutoffFDeriv2 c r R x) := by
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      fderiv_ballCutoff, fderiv_ballCutoffFDeriv, lapEval_apply]
  have hl : ‖lapEval (ballCutoffFDeriv2 c r R x)‖ ≤
      Module.finrank ℝ V * ‖ballCutoffFDeriv2 c r R x‖ :=
    norm_lapEval_le (ballCutoffFDeriv2 c r R x)
  rw [he]
  exact hl.trans (mul_le_mul_of_nonneg_left (norm_ballCutoffFDeriv2_le hr hrR x)
    (Nat.cast_nonneg _))

private theorem exists_weighted_max_ball
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {u : X → ℝ} {c : X} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (Metric.closedBall c R)) (hc : 0 < u c) :
    ∃ q ∈ Metric.ball c R, 0 < u q ∧
      R * u c ≤ (R - dist q c) * u q ∧
      ∀ y ∈ Metric.ball q ((R - dist q c) / 2),
        y ∈ Metric.ball c R ∧ u y ≤ 2 * u q := by
  have hcont : ContinuousOn (fun x => (R - dist x c) * u x) (Metric.closedBall c R) :=
    (continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn).mul hu
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c, Metric.mem_closedBall_self hR.le⟩ hcont
  have hmaxc : R * u c ≤ (R - dist q c) * u q := by
    have h := hmax (Metric.mem_closedBall_self hR.le)
    change (R - dist c c) * u c ≤ (R - dist q c) * u q at h
    simpa only [dist_self, sub_zero] using h
  have hpos : 0 < (R - dist q c) * u q := (mul_pos hR hc).trans_le hmaxc
  have hdist : dist q c ≤ R := Metric.mem_closedBall.mp hq
  have hρ : 0 < R - dist q c := by
    by_contra hn
    have he : R - dist q c = 0 := by linarith
    rw [he, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have huq : 0 < u q := (mul_pos_iff_of_pos_left hρ).mp hpos
  refine ⟨q, Metric.mem_ball.mpr (by linarith), huq, hmaxc, ?_⟩
  intro y hy
  have hyq : dist y q < (R - dist q c) / 2 := Metric.mem_ball.mp hy
  have hyc : dist y c < R := by linarith [dist_triangle y q c]
  refine ⟨Metric.mem_ball.mpr hyc, ?_⟩
  have hm : (R - dist y c) * u y ≤ (R - dist q c) * u q :=
    hmax (Metric.mem_closedBall.mpr hyc.le)
  have hweight : (R - dist q c) / 2 ≤ R - dist y c := by
    linarith [dist_triangle y q c]
  by_cases hy0 : 0 ≤ u y
  · have hm' := mul_le_mul_of_nonneg_right hweight hy0
    nlinarith [hm]
  · linarith

private theorem not_le_of_large_gradient
    {A n x s : ℝ} (hA : 1 ≤ A) (hn : 0 ≤ n)
    (hx : 65536 * A * (n + 1) ≤ x) (hs : s ≤ 1 / 8) :
    ¬ (1 ≤ 1 / 8 + s + 1024 * A / x + 2560 * A * n / x ^ 2) := by
  have hAn : 0 ≤ A * n := mul_nonneg (by linarith) hn
  have hx1 : 1 ≤ x := by nlinarith only [hA, hAn, hx]
  have hx0 : 0 < x := by linarith
  have h1 : 1024 * A / x ≤ 1 / 8 := by
    rw [div_le_iff₀ hx0]
    nlinarith only [hA, hAn, hx]
  have hx2 : x ≤ x ^ 2 := by nlinarith only [hx1]
  have h2 : 2560 * A * n / x ^ 2 ≤ 1 / 8 := by
    rw [div_le_iff₀ (sq_pos_of_pos hx0)]
    nlinarith only [hA, hAn, hx, hx2]
  intro h
  linarith

private theorem gradient_normalization
    {a δ L ρ : ℝ} (ha : a ≠ 0) (hδ : δ ≠ 0) (hL : L ≠ 0) (hρ : ρ ≠ 0)
    (C β k n : ℝ) :
    (((8 * a * δ / L)⁻¹ * C * δ +
      2 * (4 * β * L ^ 2 + 2 * (32 * k / (3 * ρ)) * (2 * L) +
        n * (1408 * k / (9 * ρ ^ 2)) * δ) * C * (8 * a * δ / L)) / L) =
      C / (8 * a) + 64 * a * C * β * δ +
        (2048 / 3) * a * C * k / (ρ * L / δ) +
        (22528 / 9) * a * C * n * k / (ρ * L / δ) ^ 2 := by
  field_simp
  ring

private theorem ballCutoffFDerivBound_eighth {ρ : ℝ} (hρ : ρ ≠ 0) :
    ballCutoffFDerivBound (ρ / 8) (ρ / 4) = 32 * CutoffProfile.derivBound / (3 * ρ) := by
  unfold ballCutoffFDerivBound
  field_simp
  ring

private theorem ballCutoffFDeriv2Bound_eighth {ρ : ℝ} (hρ : ρ ≠ 0) :
    ballCutoffFDeriv2Bound (ρ / 8) (ρ / 4) = 1408 * CutoffProfile.derivBound / (9 * ρ ^ 2) := by
  unfold ballCutoffFDeriv2Bound
  field_simp
  ring

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem norm_fderiv_center_le_of_laplacian_bound
    {f : V → F} {c : V} {R t M D B : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Metric.ball c R))
    (hM : ∀ x ∈ Metric.ball c R, ‖f x‖ ≤ M)
    (hD : ∀ x ∈ Metric.ball c R, ‖fderiv ℝ f x‖ ≤ D)
    (hB : ∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian f x‖ ≤ B) :
    ‖fderiv ℝ f c‖ ≤ (Real.sqrt t)⁻¹ * heatC1 V * M +
      2 * (B + 2 * ballCutoffFDerivBound (R / 4) (R / 2) * D +
        Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) * M) *
        heatC1 V * Real.sqrt t := by
  let χ := ballCutoff c (R / 4) (R / 2)
  let g : V → F := fun x => χ x • f x
  have hr : 0 ≤ R / 4 := by positivity
  have hrR : R / 4 < R / 2 := by linarith
  have hχ : ContDiff ℝ 2 χ := (ballCutoff_contDiff c (R / 4) (R / 2)).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hsupp : tsupport g ⊆ Metric.closedBall c (R / 2) :=
    (tsupport_smul_subset_left χ f).trans (ballCutoff_tsupport_subset_closedBall hr hrR)
  have hsupp' : tsupport g ⊆ Metric.ball c R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hsupp hx)).trans_lt (by linarith))
  have hg : ContDiff ℝ 2 g :=
    (hχ.contDiffOn.smul hf).contDiff_of_tsupport_subset Metric.isOpen_ball hsupp'
  have hgcs : HasCompactSupport g := (ballCutoff_hasCompactSupport hr hrR).smul_right
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c hc)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ f c)).trans (hD c hc)
  have hB0 : 0 ≤ B := (norm_nonneg (Laplacian.laplacian f c)).trans (hB c hc)
  have hK1 := ballCutoffFDerivBound_nonneg hr hrR
  have hK2 := ballCutoffFDeriv2Bound_nonneg hr hrR
  have hχnorm (x : V) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc c (R / 4) (R / 2) x).1]
    exact (ballCutoff_mem_Icc c (R / 4) (R / 2) x).2
  have hgnorm (x : V) : ‖g x‖ ≤ M := by
    by_cases hx : x ∈ Metric.ball c R
    · calc
        ‖g x‖ = ‖χ x‖ * ‖f x‖ := norm_smul _ _
        _ ≤ 1 * M := mul_le_mul (hχnorm x) (hM x hx) (norm_nonneg _) (by norm_num)
        _ = M := one_mul M
    · have he : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp' h))
      simpa only [he, norm_zero] using hM0
  have hχD (x : V) : ‖fderiv ℝ χ x‖ ≤ ballCutoffFDerivBound (R / 4) (R / 2) := by
    rw [show χ = ballCutoff c (R / 4) (R / 2) from rfl, fderiv_ballCutoff]
    exact norm_ballCutoffFDeriv_le hr hrR x
  have hχB (x : V) : ‖Laplacian.laplacian χ x‖ ≤
      Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) :=
    norm_laplacian_ballCutoff_le hr hrR x
  have hgB (x : V) : ‖Laplacian.laplacian g x‖ ≤
      B + 2 * ballCutoffFDerivBound (R / 4) (R / 2) * D +
        Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) * M := by
    by_cases hx : x ∈ Metric.ball c R
    · have hh := hχ.contDiffAt.norm_laplacian_fun_smul_le
        ((hf x hx).contDiffAt (Metric.isOpen_ball.mem_nhds hx))
      have hm := mul_le_mul (hχnorm x) (hB x hx) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hd := mul_le_mul (hχD x) (hD x hx) (norm_nonneg _) hK1
      have hb := mul_le_mul (hχB x) (hM x hx) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hK2)
      dsimp [g] at *
      nlinarith only [hh, hm, hd, hb]
    · have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp
        (fun h => hx (hsupp' h))
      have he := (laplacian_congr_nhds hz).self_of_nhds
      rw [he]
      change ‖Laplacian.laplacian (fun _ : V => (0 : F)) x‖ ≤ _
      simp only [laplacian_const, Pi.zero_apply, norm_zero]
      positivity
  have heq : g =ᶠ[𝓝 c] f := by
    filter_upwards [Metric.ball_mem_nhds c (by positivity : 0 < R / 4)] with x hx
    dsimp [g, χ]
    rw [ballCutoff_eq_one_of_mem_closedBall hr hrR (Metric.ball_subset_closedBall hx), one_smul]
  rw [← heq.fderiv_eq]
  exact norm_fderiv_le_of_laplacian_bound hg hgcs ht hgnorm hgB c


omit [MeasurableSpace V] [BorelSpace V] in
theorem exists_pos_norm_fderiv_le_of_quadratic_laplacian_bound :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (f : V → F) (c : V) (R β δ : ℝ), 0 < R → 0 ≤ β → β * δ ≤ ε →
        ContDiffOn ℝ 2 f (Metric.ball c R) →
        (∀ x ∈ Metric.ball c R, ‖f x‖ ≤ δ) →
        (∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian f x‖ ≤ β * ‖fderiv ℝ f x‖ ^ 2) →
        R * ‖fderiv ℝ f c‖ ≤ C * δ := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let a : ℝ := heatC1 V + 1
  let k : ℝ := CutoffProfile.derivBound + 1
  let n : ℝ := Module.finrank ℝ V
  let A : ℝ := a ^ 2 * k
  let T : ℝ := 65536 * A * (n + 1)
  have hC0 := heatC1_nonneg (V := V)
  have hk0 := CutoffProfile.derivBound_nonneg
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hk : 1 ≤ k := by dsimp [k]; linarith
  have ha0 : 0 < a := by linarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg (a - 1)]
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨(512 * a ^ 2)⁻¹, by positivity, 2 * T, by positivity, ?_⟩
  intro f c R β δ hR hβ hsmall hf hbound hΔ
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hδ0 : 0 ≤ δ := (norm_nonneg (f c)).trans (hbound c hc)
  by_cases hδzero : δ = 0
  · have he : f =ᶠ[𝓝 c] 0 := by
      filter_upwards [Metric.ball_mem_nhds c hR] with x hx
      exact norm_le_zero_iff.mp (by simpa [hδzero] using hbound x hx)
    have hd : fderiv ℝ f c = 0 := by
      rw [he.fderiv_eq]
      exact fderiv_const_apply (0 : F)
    simp [hd, hδzero]
  have hδ : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδzero)
  by_contra hbad
  have hbad' : 2 * T * δ < R * ‖fderiv ℝ f c‖ := lt_of_not_ge hbad
  have hdc : 0 < ‖fderiv ℝ f c‖ := by nlinarith [mul_pos hT hδ]
  have hu : ContinuousOn (fun x => ‖fderiv ℝ f x‖) (Metric.closedBall c (R / 2)) := by
    intro x hx
    have hxb : x ∈ Metric.ball c R := Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    exact (((hf x hxb).contDiffAt (Metric.isOpen_ball.mem_nhds hxb)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨q, hq, hL, hmax, hnear⟩ := exists_weighted_max_ball
    (R := R / 2) (by positivity) hu hdc
  let ρ : ℝ := R / 2 - dist q c
  let L : ℝ := ‖fderiv ℝ f q‖
  have hρ : 0 < ρ := sub_pos.mpr (Metric.mem_ball.mp hq)
  have hL0 : 0 < L := hL
  have hmax' : T * δ ≤ ρ * L := by dsimp [ρ, L]; nlinarith only [hmax, hbad']
  have hsub : Metric.ball q (ρ / 2) ⊆ Metric.ball c R := by
    intro y hy
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp (hnear y hy).1).trans (by linarith))
  have hD : ∀ y ∈ Metric.ball q (ρ / 2), ‖fderiv ℝ f y‖ ≤ 2 * L :=
    fun y hy => (hnear y hy).2
  have hB : ∀ y ∈ Metric.ball q (ρ / 2),
      ‖Laplacian.laplacian f y‖ ≤ 4 * β * L ^ 2 := by
    intro y hy
    have hs : ‖fderiv ℝ f y‖ ^ 2 ≤ (2 * L) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hD y hy)
    have hm := mul_le_mul_of_nonneg_left hs hβ
    exact (hΔ y (hsub hy)).trans (by nlinarith only [hm])
  let τ : ℝ := 8 * a * δ / L
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hg := norm_fderiv_center_le_of_laplacian_bound
    (c := q) (R := ρ / 2) (t := τ ^ 2) (M := δ) (D := 2 * L) (B := 4 * β * L ^ 2)
    (by positivity) (sq_pos_of_pos hτ) (hf.mono hsub)
    (fun y hy => hbound y (hsub hy)) hD hB
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hτ] at hg
  have hk1 : ballCutoffFDerivBound ((ρ / 2) / 4) ((ρ / 2) / 2) =
      32 * CutoffProfile.derivBound / (3 * ρ) := by
    simpa only [div_div, show (2 * 4 : ℝ) = 8 by norm_num,
      show (2 * 2 : ℝ) = 4 by norm_num] using ballCutoffFDerivBound_eighth hρ.ne'
  have hk2 : ballCutoffFDeriv2Bound ((ρ / 2) / 4) ((ρ / 2) / 2) =
      1408 * CutoffProfile.derivBound / (9 * ρ ^ 2) := by
    simpa only [div_div, show (2 * 4 : ℝ) = 8 by norm_num,
      show (2 * 2 : ℝ) = 4 by norm_num] using ballCutoffFDeriv2Bound_eighth hρ.ne'
  rw [hk1, hk2] at hg
  let x : ℝ := ρ * L / δ
  have hx : 0 < x := by dsimp [x]; positivity
  have hxT : 65536 * A * (n + 1) ≤ x := (le_div_iff₀ hδ).2 hmax'
  have hg' : 1 ≤ heatC1 V / (8 * a) + 64 * a * heatC1 V * β * δ +
      (2048 / 3) * a * heatC1 V * CutoffProfile.derivBound / x +
      (22528 / 9) * a * heatC1 V * n * CutoffProfile.derivBound / x ^ 2 := by
    have hh : 1 ≤ (τ⁻¹ * heatC1 V * δ +
        2 * (4 * β * L ^ 2 + 2 * (32 * CutoffProfile.derivBound / (3 * ρ)) * (2 * L) +
          n * (1408 * CutoffProfile.derivBound / (9 * ρ ^ 2)) * δ) * heatC1 V * τ) / L :=
      (le_div_iff₀ hL0).2 (by simpa only [one_mul] using hg)
    exact hh.trans_eq (gradient_normalization ha0.ne' hδ.ne' hL0.ne' hρ.ne'
      (heatC1 V) β CutoffProfile.derivBound n)
  have hCa : heatC1 V ≤ a := by dsimp [a]; linarith
  have hka : CutoffProfile.derivBound ≤ k := by dsimp [k]; linarith
  have hac : a * heatC1 V ≤ a ^ 2 := by nlinarith
  have hak : a * heatC1 V * CutoffProfile.derivBound ≤ A :=
    mul_le_mul hac hka hk0 (sq_nonneg a)
  have hlead : heatC1 V / (8 * a) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * a)]
    linarith
  have hquad : 64 * a * heatC1 V * β * δ ≤ 64 * a ^ 2 * β * δ := by
    have hh := mul_le_mul_of_nonneg_right hac (mul_nonneg hβ hδ.le)
    nlinarith only [hh]
  have hcross : (2048 / 3) * a * heatC1 V * CutoffProfile.derivBound / x ≤
      1024 * A / x := by
    apply div_le_div_of_nonneg_right _ hx.le
    nlinarith only [hak, hA]
  have hlast : (22528 / 9) * a * heatC1 V * n * CutoffProfile.derivBound / x ^ 2 ≤
      2560 * A * n / x ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg x)
    have hh := mul_le_mul_of_nonneg_right hak hn
    have hAn := mul_nonneg (by linarith : 0 ≤ A) hn
    nlinarith only [hh, hAn]
  have hs : 64 * a ^ 2 * β * δ ≤ 1 / 8 := by
    rw [← one_div] at hsmall
    have hh := (le_div_iff₀ (by positivity : 0 < 512 * a ^ 2)).mp hsmall
    nlinarith only [hh]
  apply not_le_of_large_gradient hA hn hxT hs
  linarith only [hg', hlead, hquad, hcross, hlast]

end DifferentialGeometry.Analysis
