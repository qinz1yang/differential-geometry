import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHalfPlaneModel
import DifferentialGeometry.Geometry.Metric.Approximation.PaddedStripBoundary

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry.KleinerLottApprox

universe u v
variable {X : Type u} [mX : MetricSpace X]

theorem model_height_lt_of_rescaled_edgePoint {T : Set ℝ} {o : T}
    {p z : X} {e Δ b s c R S r t C K : ℝ}
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hT : Icc 0 C ⊆ T) (hmark : |o.val| ≤ K)
    (hc : 0 < c) (ht : 0 < t)
    (hzedge : @isEdgePoint.{u, v} X (mX.rescale c hc) z Δ b s)
    (hstrong : S < e⁻¹)
    (hweak : c * r + 10 * (b + s) < min b⁻¹ s⁻¹)
    (hbuffer : R + 8 * e + t < S) (htop : R + K + 4 * e + t < C)
    (hlocal : t + 12 * e < r) (hsmall : 20 * e + (b + s) / c ≤ t / 1000)
    (hz : z ∈ ball p R) : (H.toFun z).snd.val < t := by
  have he := H.error_pos
  have hbs : 0 < b + s := by
    let : MetricSpace X := mX.rescale c hc
    obtain ⟨Y, mY, q, D, hD, _, ⟨F⟩, ⟨G⟩⟩ := hzedge
    let := mY
    exact add_pos F.error_pos G.error_pos
  let J : WithLp 2 (ℝ × T) → WithLp 2 (ℝ × ℝ) :=
    fun y => WithLp.toLp 2 (y.fst, y.snd.val)
  have hJ : Isometry J := isometry_id.withLpProdMap 2 isometry_subtype_coe
  let Q : X → WithLp 2 (ℝ × ℝ) := fun x => J (H.toFun x)
  have hQp : Q p = WithLp.toLp 2 ((0 : ℝ), o.val) := by
    dsimp [Q]
    rw [H.basepoint]
    rfl
  have hnormp : ‖Q p‖ ≤ K := by
    rw [hQp]
    have hh := (WithLp.isometry_prodMk_left (Y := ℝ) (0 : ℝ)).dist_eq o.val 0
    have hzero : WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) = 0 := rfl
    rw [hzero, dist_zero_right, Real.dist_eq, sub_zero] at hh
    rwa [hh]
  obtain ⟨W, hWz, hWheight, hWdist⟩ := hzedge.exists_local_half_plane_model_rescale hc hweak
  apply strip_height_lt_of_local_half_plane_model_of_bounded_mark
    (R := R) (S := S) (r := r) (δ := 4 * e) (ε := (b + s) / c) (C := C) (K := K)
    ht (by positivity) (by positivity) (by linarith) htop (by linarith) (by linarith)
    Q W hnormp hWz ?_ ?_ (fun x _ => hWheight x) hWdist hz
  · intro x hx y hy
    have hd := H.distortion x (lt_trans hx hstrong) y (lt_trans hy hstrong)
    change |dist (J (H.toFun x)) (J (H.toFun y)) - dist x y| ≤ 4 * e
    rw [hJ.dist_eq]
    exact hd.trans (by linarith)
  · intro y hy hr
    let y' : WithLp 2 (ℝ × T) := WithLp.toLp 2 (y.fst, ⟨y.snd, hT hy⟩)
    have hy' : J y' = y := rfl
    have hd : dist y' (WithLp.toLp 2 ((0 : ℝ), o)) = dist y (Q p) := by
      rw [← hJ.dist_eq, hy']
      congr 1
      exact (congrArg J H.basepoint).symm
    obtain ⟨x, _, hxy, hrad⟩ := H.coverage_witness_radius y' (by rw [hd]; linarith)
    have hx : x ∈ ball p S := by change dist x p < S; rw [hd] at hrad; linarith
    have herr : dist y (Q x) < 2 * e := by
      change dist y (J (H.toFun x)) < 2 * e
      rw [← hy', hJ.dist_eq]
      exact hxy
    exact (infDist_le_dist_of_mem (show Q x ∈ Q '' ball p S from ⟨x, hx, rfl⟩)).trans
      (herr.le.trans (by linarith))


theorem model_height_lt_of_weak_edge {T : Set ℝ} {o : T}
    {p z : X} {e Δ b s : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hT : Icc 0 (500 * Δ) ⊆ T) (hmark : |o.val| ≤ Δ / 2)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1) (hρz : 0 < ρ z)
    (hΔ : 1 ≤ Δ) (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (he : e < 1 / 100000000) (heΔ : e ≤ 1 / (1000 * Δ))
    (hb : b < 1 / 100000000) (hs : s < 1 / 100000000)
    (hzedge : @isEdgePoint.{u, v} X (mX.rescale (ρ z)⁻¹ (inv_pos.mpr hρz)) z Δ b s)
    (hz : z ∈ ball p (10 * Δ)) : (H.toFun z).snd.val < 1 / 20 := by
  have hepos := H.error_pos
  have hwpos : 0 < b ∧ 0 < s := by
    let : MetricSpace X := mX.rescale (ρ z)⁻¹ (inv_pos.mpr hρz)
    obtain ⟨Y, mY, q, D, hD, _, ⟨F⟩, ⟨G⟩⟩ := hzedge
    let := mY
    exact ⟨F.error_pos, G.error_pos⟩
  have hΔpos : 0 < Δ := by linarith only [hΔ]
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hclose : |ρ z - 1| ≤ (Λ : ℝ) * (10 * Δ) := by
    have hh := hρ.dist_le_mul z p
    rw [Real.dist_eq, hρp] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (le_of_lt hz) Λ.coe_nonneg)
  have hrholower : 1 / 2 < ρ z := by nlinarith only [hΛΔ, (abs_le.mp hclose).1]
  have hrhoupper : ρ z < 2 := by nlinarith only [hΛΔ, (abs_le.mp hclose).2]
  have hinv : (ρ z)⁻¹ < 2 := by
    rw [← one_div]
    exact (div_lt_iff₀ hρz).mpr (by linarith only [hrholower])
  have hstrong : 20 * Δ < e⁻¹ := by
    have hprod : e * (1000 * Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp heΔ
    rw [← one_div]
    apply (lt_div_iff₀ hepos).mpr
    nlinarith only [hprod]
  have hweakb : (ρ z)⁻¹ * (1 / 2) + 10 * (b + s) < b⁻¹ := by
    have hdom : 2 < b⁻¹ := by
      rw [← one_div]
      apply (lt_div_iff₀ hwpos.1).mpr
      linarith only [hb]
    linarith only [hinv, hb, hs, hdom]
  have hweaks : (ρ z)⁻¹ * (1 / 2) + 10 * (b + s) < s⁻¹ := by
    have hdom : 2 < s⁻¹ := by
      rw [← one_div]
      apply (lt_div_iff₀ hwpos.2).mpr
      linarith only [hs]
    linarith only [hinv, hb, hs, hdom]
  have herr : (b + s) / (ρ z)⁻¹ ≤ 2 * (b + s) := by
    rw [div_inv_eq_mul]
    simpa only [mul_comm (b + s) 2] using
      mul_le_mul_of_nonneg_left hrhoupper.le (add_pos hwpos.1 hwpos.2).le
  exact H.model_height_lt_of_rescaled_edgePoint (R := 10 * Δ) (S := 20 * Δ)
    (r := 1 / 2) hT hmark (inv_pos.mpr hρz) (by norm_num) hzedge hstrong
    (lt_min hweakb hweaks) (by linarith only [hΔ, he]) (by linarith only [hΔ, he])
    (by linarith only [he]) (by linarith only [herr, he, hb, hs]) hz

end GC.MetricGeometry.KleinerLottApprox
