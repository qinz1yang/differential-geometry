import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_mem_Ioo_scalar_metric_close {t₀ ζ d : ℝ} (ht₀ : t₀ ∈ Ioo a s) (hζ : 0 < ζ)
    (hd : 0 < d) :
    ∃ σ : ℝ, σ ∈ Ioo a t₀ ∧ t₀ - d ≤ σ ∧ ∀ x : P.Carrier,
      |G.flow.scalar σ x - G.flow.scalar t₀ x| ≤ ζ ∧
      ∀ v : TangentSpace ThreeModel x,
        (G.flow.base.metric σ).inner x v v ≤ (1 + ζ) * (G.flow.base.metric t₀).inner x v v := by
  obtain ⟨δ, hδ, -, h⟩ := G.exists_forall_Icc_scalar_riemannNorm_metric_close
    ⟨ht₀.1.le, ht₀.2⟩ hζ
  set e : ℝ := min (min δ d) ((t₀ - a) / 2) with hedef
  have he : 0 < e := lt_min (lt_min hδ hd) (by linarith [ht₀.1])
  have heδ : e ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hed : e ≤ d := (min_le_left _ _).trans (min_le_right _ _)
  have hea : e ≤ (t₀ - a) / 2 := min_le_right _ _
  have hσ : t₀ - e ∈ Icc (max a (t₀ - δ)) (t₀ + δ) :=
    ⟨max_le (by linarith) (by linarith), by linarith⟩
  have h₀ : t₀ ∈ Icc (max a (t₀ - δ)) (t₀ + δ) :=
    ⟨max_le ht₀.1.le (by linarith), by linarith⟩
  refine ⟨t₀ - e, ⟨by linarith, by linarith⟩, by linarith, fun x => ?_⟩
  obtain ⟨h1, -, h3⟩ := h (t₀ - e) hσ t₀ h₀ x
  exact ⟨h1, h3⟩

theorem exists_earlier_slice_scalar_ball_transfer {t₀ t q ρ Cq Λ A θ S : ℝ} (y : P.Carrier)
    (hat₀ : a < t₀) (ht₀t : t₀ ≤ t) (hts : t < s) (hq : 0 < q)
    (hqy : q ≤ Cq * G.flow.scalar t y) (hΛ : 0 < Λ) (hΛR : Λ ≤ G.flow.scalar t y)
    (hΛt : Λ ≤ G.flow.scalar t y * t₀)
    (hclose : ∀ x, |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ G.flow.scalar t y / 4)
    (hmet : ∀ x (v : TangentSpace ThreeModel x),
      (G.flow.base.metric t₀).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t).inner x v v)
    (hρ : Λ ≤ ρ * Real.sqrt (G.flow.scalar t y)) (hA : 0 < A) (hθ : 0 < θ) (hS : 0 < S) :
    ∃ σ : ℝ, a < σ ∧ σ < t₀ ∧ S * (t₀ - σ) ≤ θ / 2 ∧
      q ≤ 2 * Cq * G.flow.scalar σ y ∧ Λ / 4 ≤ G.flow.scalar σ y ∧
      Λ / 4 ≤ G.flow.scalar σ y * σ ∧ Λ / 4 ≤ ρ * Real.sqrt (G.flow.scalar σ y) ∧
      ∀ Q : ℝ, 0 ≤ Q →
        (∀ z ∈ riemannianBallOf (G.flow.base.metric σ) y
          (2 * Real.sqrt (Real.exp 1) * A / Real.sqrt (G.flow.scalar σ y)),
          G.flow.scalar σ z ≤ Q * G.flow.scalar σ y) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ (2 * Q + 1) * G.flow.scalar t y := by
  set R := G.flow.scalar t y with hRdef
  have hR : 0 < R := hΛ.trans_le hΛR
  have ht₀pos : 0 < t₀ := by
    by_contra hneg
    have : R * t₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR.le (not_lt.mp hneg)
    linarith
  have hCq : 0 ≤ Cq := by
    by_contra hneg
    have : Cq * R < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hR
    linarith
  have hρpos : 0 < ρ := by
    by_contra hneg
    have : ρ * Real.sqrt R ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
    linarith
  obtain ⟨σ, hσ, hσd, hσx⟩ := G.exists_mem_Ioo_scalar_metric_close ⟨hat₀, ht₀t.trans_lt hts⟩
    (lt_min (by linarith : 0 < R / 4) one_pos) (lt_min (half_pos ht₀pos) (div_pos hθ
      (mul_pos two_pos hS)))
  have hζR : min (R / 4) 1 ≤ R / 4 := min_le_left _ _
  have hζ1 : min (R / 4) 1 ≤ 1 := min_le_right _ _
  have hσ2 : t₀ / 2 ≤ σ := by
    linarith [min_le_left (t₀ / 2) (θ / (2 * S))]
  have hσS : S * (t₀ - σ) ≤ θ / 2 := by
    have h1 : t₀ - σ ≤ θ / (2 * S) := by linarith [min_le_right (t₀ / 2) (θ / (2 * S))]
    rw [le_div_iff₀ (mul_pos two_pos hS)] at h1
    linarith
  have hdiff : ∀ x, |G.flow.scalar σ x - G.flow.scalar t x| ≤ R / 2 := by
    intro x
    have h1 := (hσx x).1
    have h2 := hclose x
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hy := abs_le.mp (hdiff y)
  have hRσl : R / 2 ≤ G.flow.scalar σ y := by linarith [hy.1]
  have hRσu : G.flow.scalar σ y ≤ 3 * R / 2 := by linarith [hy.2]
  set Rσ := G.flow.scalar σ y with hRσdef
  have hRσ : 0 < Rσ := by linarith
  have hmetσ : ∀ x (v : TangentSpace ThreeModel x),
      (G.flow.base.metric σ).inner x v v ≤ 2 * (G.flow.base.metric t₀).inner x v v := by
    intro x v
    have hnn := metric_inner_self_nonneg (G.flow.base.metric t₀) x v
    have := (hσx x).2 v
    nlinarith
  have hsqrtR : Real.sqrt R / 2 ≤ Real.sqrt Rσ := by
    have h4 : Real.sqrt (R / 4) = Real.sqrt R / 2 := by
      rw [Real.sqrt_div' R (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨σ, hσ.1, hσ.2, hσS, ?_, by linarith, ?_, ?_, fun Q hQ hball z hz => ?_⟩
  · calc q ≤ Cq * R := hqy
      _ ≤ Cq * (2 * Rσ) := mul_le_mul_of_nonneg_left (by linarith) hCq
      _ = 2 * Cq * Rσ := by ring
  · have h1 : R / 2 * (t₀ / 2) ≤ Rσ * σ :=
      mul_le_mul hRσl hσ2 (by linarith) hRσ.le
    nlinarith
  · have h1 : ρ * (Real.sqrt R / 2) ≤ ρ * Real.sqrt Rσ :=
      mul_le_mul_of_nonneg_left hsqrtR hρpos.le
    nlinarith
  · have hsub1 := DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul
      (G.flow.base.metric t) (G.flow.base.metric t₀) y (r := A / Real.sqrt R) (Real.exp_pos 1)
      (fun x _ v => hmet x v)
    have hsub2 := DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul
      (G.flow.base.metric t₀) (G.flow.base.metric σ) y
      (r := Real.sqrt (Real.exp 1) * (A / Real.sqrt R)) two_pos (fun x _ v => hmetσ x v)
    have hz' := hsub2 (hsub1 hz)
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
    have hsRσ : 0 < Real.sqrt Rσ := Real.sqrt_pos.mpr hRσ
    have hs2 : Real.sqrt 2 * Real.sqrt Rσ ≤ 2 * Real.sqrt R := by
      rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * Real.sqrt R = Real.sqrt (4 * R) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hrad : Real.sqrt 2 * (Real.sqrt (Real.exp 1) * (A / Real.sqrt R)) ≤
        2 * Real.sqrt (Real.exp 1) * A / Real.sqrt Rσ := by
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hsR hsRσ]
      have hk : 0 < Real.sqrt (Real.exp 1) * A := mul_pos (Real.sqrt_pos.mpr (Real.exp_pos 1)) hA
      nlinarith [mul_le_mul_of_nonneg_left hs2 hk.le]
    have hzσ := hball z (DifferentialGeometry.riemannianBallOf_mono _ _ hrad hz')
    have hzd := abs_le.mp (hdiff z)
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
