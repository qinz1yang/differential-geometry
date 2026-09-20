import DifferentialGeometry.Analysis.Asymptotics.GeometricDecay
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Set Metric Filter MeasureTheory

namespace DifferentialGeometry.Analysis

private theorem dist_normalize_of_norm_le_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : V} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    dist x (NormedSpace.normalize x) = 1 - ‖x‖ := by
  have he : x - NormedSpace.normalize x = (‖x‖ - 1) • NormedSpace.normalize x := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx,
    mul_one, abs_of_nonpos (by linarith)]
  ring

theorem exists_uniform_cap_power_bound_of_boundary_bound_of_half_contraction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] {μ : Measure V} {f : V → ℝ}
    (hfi : IntegrableOn f (ball (0 : V) 1) μ)
    (hf0 : ∀ᵐ z ∂μ.restrict (ball (0 : V) 1), 0 ≤ f z)
    {β Kb δb δi θ : ℝ} (hβ : 0 < β) (hKb : 0 ≤ Kb)
    (hδb : 0 < δb) (hδi : 0 < δi) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hboundary : ∀ c ∈ sphere (0 : V) 1, ∀ s : ℝ, 0 < s → s ≤ δb →
      (∫ z in ball (0 : V) 1 ∩ ball c s, f z ∂μ) ≤ Kb * s ^ β)
    (hstep : ∀ (x : V) (s : ℝ), 0 < s → s ≤ δi → ‖x‖ + s < 1 →
      (∫ z in ball x (s / 2), f z ∂μ) ≤ θ * ∫ z in ball x s, f z ∂μ) :
    ∃ p δ K : ℝ, 0 < p ∧ p ≤ β ∧ p ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ K ∧
      ∀ x ∈ closedBall (0 : V) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        (∫ z in ball (0 : V) 1 ∩ ball x s, f z ∂μ) ≤ K * s ^ p := by
  obtain ⟨α, hα, hα1, hpower⟩ := exists_power_bound_of_half_contraction hθ hθ1
  let pI : ℝ := 2 * α
  have hpI : 0 < pI := mul_pos (by norm_num) hα
  let p := min β pI
  have hp : 0 < p := lt_min hβ hpI
  have hpβ : p ≤ β := min_le_left _ _
  have hppI : p ≤ pI := min_le_right _ _
  have hp2 : p ≤ 2 := hppI.trans (by dsimp only [pI]; linarith)
  let δ := min δi (min (δb / 4) (1 / 8))
  have hδ : 0 < δ := lt_min hδi (lt_min (by positivity) (by norm_num))
  have hδi' : δ ≤ δi := min_le_left _ _
  have hδb' : δ ≤ δb / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ8 : δ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let M := ∫ z in ball (0 : V) 1, f z ∂μ
  have hM : 0 ≤ M := integral_nonneg_of_ae hf0
  let Kb' := Kb * (3 : ℝ) ^ β
  have hKb' : 0 ≤ Kb' := mul_nonneg hKb (Real.rpow_nonneg (by norm_num) β)
  let M₀ := Kb' + M / δ ^ p
  have hM₀ : 0 ≤ M₀ := add_nonneg hKb' (div_nonneg hM (Real.rpow_nonneg hδ.le p))
  have hKM : Kb' ≤ M₀ := le_add_of_nonneg_right (by positivity)
  let K := (1 + (2 : ℝ) ^ pI) * M₀
  have hK : 0 ≤ K := mul_nonneg (by positivity) hM₀
  have hM₀K : M₀ ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) pI) hM₀]
  have hmono {S T : Set V} (hST : S ⊆ T) (hTD : T ⊆ ball (0 : V) 1) :
      (∫ z in S, f z ∂μ) ≤ ∫ z in T, f z ∂μ :=
    setIntegral_mono_set (hfi.mono_set hTD)
      (hf0.filter_mono (ae_mono (Measure.restrict_mono hTD le_rfl)))
      (Eventually.of_forall hST)
  have hnear (x : V) (hx : x ∈ closedBall (0 : V) 1)
      (s : ℝ) (hs : 0 < s) (hsδ : s ≤ δ) (hclose : 1 - ‖x‖ ≤ 2 * s) :
      (∫ z in ball (0 : V) 1 ∩ ball x s, f z ∂μ) ≤ Kb' * s ^ p := by
    have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, norm_zero] at hclose
      linarith [hδ8]
    let c := NormedSpace.normalize x
    have hc : c ∈ sphere (0 : V) 1 := by
      rw [mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize hx0
    have hxc : dist x c = 1 - ‖x‖ := dist_normalize_of_norm_le_one hx0 hx1
    have hcap : ball (0 : V) 1 ∩ ball x s ⊆ ball (0 : V) 1 ∩ ball c (3 * s) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hdist := dist_triangle z x c
      rw [hxc] at hdist
      change dist z c < 3 * s
      have hzx : dist z x < s := hz.2
      linarith
    have h3s : 3 * s ≤ δb := by linarith [hδb']
    have hβp : s ^ β ≤ s ^ p :=
      Real.rpow_le_rpow_of_exponent_ge hs (by linarith [hδ8]) hpβ
    calc
      (∫ z in ball (0 : V) 1 ∩ ball x s, f z ∂μ) ≤
          ∫ z in ball (0 : V) 1 ∩ ball c (3 * s), f z ∂μ := hmono hcap inter_subset_left
      _ ≤ Kb * (3 * s) ^ β := hboundary c hc (3 * s) (by positivity) h3s
      _ = Kb' * s ^ β := by
        rw [Real.mul_rpow (by norm_num) hs.le]
        dsimp only [Kb']
        ring
      _ ≤ Kb' * s ^ p := mul_le_mul_of_nonneg_left hβp hKb'
  refine ⟨p, δ, K, hp, hpβ, hp2, hδ, hδ8, hK, ?_⟩
  intro x hx s hs hsδ
  by_cases hclose : 1 - ‖x‖ ≤ 2 * s
  · exact (hnear x hx s hs hsδ hclose).trans
      (mul_le_mul_of_nonneg_right (hKM.trans hM₀K) (Real.rpow_nonneg hs.le p))
  have hd : 0 < 1 - ‖x‖ := by linarith
  let R := min δ ((1 - ‖x‖) / 2)
  have hR : 0 < R := lt_min hδ (by linarith)
  have hRδ : R ≤ δ := min_le_left _ _
  have hRd : R ≤ (1 - ‖x‖) / 2 := min_le_right _ _
  have hsR : s ≤ R := le_min hsδ (by linarith)
  have hxR : ‖x‖ + R < 1 := by linarith
  have hball {t : ℝ} (ht : t ≤ R) : ball x t ⊆ ball (0 : V) 1 :=
    ball_subset_ball' (by rw [dist_zero_right]; linarith)
  have hbase : (∫ z in ball x R, f z ∂μ) ≤ M₀ * R ^ p := by
    by_cases hdist : 1 - ‖x‖ ≤ 2 * δ
    · have hReq : R = (1 - ‖x‖) / 2 := min_eq_right (by linarith)
      have hn := hnear x hx R hR hRδ (by rw [hReq]; linarith)
      rw [inter_eq_right.mpr (hball le_rfl)] at hn
      exact hn.trans (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg hR.le p))
    · have hReq : R = δ := min_eq_left (by linarith)
      have hm : (∫ z in ball x R, f z ∂μ) ≤ M := hmono (hball le_rfl) Subset.rfl
      apply hm.trans
      rw [hReq]
      calc
        M = (M / δ ^ p) * δ ^ p := by
          rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hδ p).ne']
        _ ≤ M₀ * δ ^ p :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKb')
            (Real.rpow_nonneg hδ.le p)
  let Energy : ℝ → ℝ := fun t => ∫ z in ball x t, f z ∂μ
  have hmonotone : MonotoneOn Energy (Ioc (0 : ℝ) R) := by
    intro a ha b hb hab
    exact hmono (ball_subset_ball hab) (hball hb.2)
  have hrec (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) R) : Energy (t / 2) ≤ θ * Energy t :=
    hstep x t ht.1 (ht.2.trans (hRδ.trans hδi')) (by linarith [ht.2])
  have hpow := hpower Energy R (M₀ * R ^ p) hR
    (mul_nonneg hM₀ (Real.rpow_nonneg hR.le p)) hbase hmonotone hrec s ⟨hs, hsR⟩
  have hratio : (s / R) ^ pI ≤ (s / R) ^ p :=
    Real.rpow_le_rpow_of_exponent_ge (div_pos hs hR) ((div_le_one hR).mpr hsR) hppI
  have hscaled : ((2 : ℝ) ^ pI * (M₀ * R ^ p) / R ^ pI) * s ^ pI ≤
      ((2 : ℝ) ^ pI * M₀) * s ^ p := by
    calc
      _ = ((2 : ℝ) ^ pI * M₀ * R ^ p) * (s / R) ^ pI := by
        rw [Real.div_rpow hs.le hR.le]
        ring
      _ ≤ ((2 : ℝ) ^ pI * M₀ * R ^ p) * (s / R) ^ p :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ((2 : ℝ) ^ pI * M₀) * s ^ p := by
        rw [Real.div_rpow hs.le hR.le]
        field_simp [(Real.rpow_pos_of_pos hR p).ne']
  have hfactor : (2 : ℝ) ^ pI * M₀ ≤ K := by
    dsimp only [K]
    nlinarith
  rw [inter_eq_right.mpr (hball hsR)]
  exact (hpow.trans hscaled).trans
    (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hs.le p))

end DifferentialGeometry.Analysis

end
