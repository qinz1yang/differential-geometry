import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHalfPlaneModel
import DifferentialGeometry.Geometry.Metric.Approximation.PaddedStripBoundary
import DifferentialGeometry.Geometry.Metric.Scaling.LipschitzScale

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry.KleinerLottApprox

universe u v w
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p z : X} {q : Y} {C b s : ℝ} {hC : 0 ≤ C}

theorem strip_height_lt_of_rescaled_edgePoint {Δ b' s' c R S r t : ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hc : 0 < c) (ht : 0 < t)
    (hzedge : @isEdgePoint.{u, w} X (mX.rescale c hc) z Δ b' s')
    (hstrong : S + 10 * (b + s) < min b⁻¹ s⁻¹)
    (hweak : c * r + 10 * (b' + s') < min b'⁻¹ s'⁻¹)
    (hbuffer : R + 8 * (b + s) + t < S)
    (htop : R + 4 * (b + s) + t < C)
    (hlocal : t + 12 * (b + s) < r)
    (hsmall : 20 * (b + s) + (b' + s') / c ≤ t / 1000)
    (hz : z ∈ ball p R) : (F.stripMap G z).snd < t := by
  have hwpos : 0 < b' + s' := by
    let : MetricSpace X := mX.rescale c hc
    obtain ⟨Z, mZ, qZ, CZ, hCZ, _, ⟨FZ⟩, ⟨GZ⟩⟩ := hzedge
    let := mZ
    exact add_pos FZ.error_pos GZ.error_pos
  obtain ⟨W, hWz, hWheight, hWdist⟩ := hzedge.exists_local_half_plane_model_rescale hc hweak
  obtain ⟨hQdist, hcover⟩ := F.stripMap_estimates (hC := hC) G hstrong
  have hbs : 0 < b + s := add_pos F.error_pos G.error_pos
  apply strip_height_lt_of_local_half_plane_model (R := R) (S := S) (r := r) (C := C) ht (by positivity : 0 < 4 * (b + s))
    (by positivity : 0 ≤ (b' + s') / c) (by linarith) htop (by linarith) (by linarith)
    (F.stripMap G) W (F.stripMap_basepoint (hC := hC) G) hWz ?_ ?_ (fun x _ => hWheight x) hWdist hz
  · intro x hx y hy
    exact (hQdist x hx y hy).trans (by linarith)
  · intro y hy hnorm
    obtain ⟨x, hx, hxy, _⟩ := hcover y hy hnorm.le
    have hxy' : dist y (F.stripMap G x) ≤ 4 * (b + s) := by rw [dist_comm]; linarith
    exact (infDist_le_dist_of_mem (show F.stripMap G x ∈ F.stripMap G '' ball p S from
      ⟨x, hx, rfl⟩)).trans hxy'

theorem strip_height_lt_of_weak_edge {Δ τ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1) (hρz : 0 < ρ z)
    (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hss' : s < s' / 100000) (hbs : b < s / 100000) (hlength : 200 * Δ ≤ C)
    (hzedge : @isEdgePoint.{u, w} X (mX.rescale (ρ z)⁻¹ (inv_pos.mpr hρz)) z Δ b' s')
    (hz : z ∈ ball p (191 * Δ)) : (F.stripMap G z).snd < τ * Δ / 2 := by
  have hb := F.error_pos
  have hs := G.error_pos
  have hwpos : 0 < b' ∧ 0 < s' := by
    let : MetricSpace X := mX.rescale (ρ z)⁻¹ (inv_pos.mpr hρz)
    obtain ⟨Z, mZ, qZ, CZ, hCZ, _, ⟨FZ⟩, ⟨GZ⟩⟩ := hzedge
    let := mZ
    exact ⟨FZ.error_pos, GZ.error_pos⟩
  have hΔpos : 0 < Δ := by linarith
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hbpΔ : b' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hb'domain
  have hspΔ : s' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hs'domain
  have hclose : |ρ z - 1| ≤ (Λ : ℝ) * (191 * Δ) := by
    have hh := hρ.dist_le_mul z p
    rw [Real.dist_eq, hρp] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (le_of_lt hz) Λ.coe_nonneg)
  have hrholower : 1 / 2 < ρ z := by nlinarith only [hΛΔ, (abs_le.mp hclose).1]
  have hrhoupper : ρ z < 2 := by nlinarith only [hΛΔ, (abs_le.mp hclose).2]
  have hinv : (ρ z)⁻¹ < 2 := by
    rw [← one_div]
    exact (div_lt_iff₀ hρz).mpr (by linarith)
  have hbp1 : b' < 1 / 1000000 := by nlinarith only [hbpΔ, hΔ, hwpos.1]
  have hsp1 : s' < 1 / 1000000 := by nlinarith only [hspΔ, hΔ, hwpos.2]
  have hbs1 : b + s < 1 / 1000000 := by linarith only [hbs, hss', hsp1]
  have hsΔ : s * Δ < 1 / 100000000000 := by
    nlinarith only [hspΔ, mul_lt_mul_of_pos_right hss' hΔpos]
  have hbΔ : b * Δ < 1 / 100000000000 := by
    nlinarith only [hsΔ, mul_lt_mul_of_pos_right hbs hΔpos]
  have hstrongb : 200 * Δ + 10 * (b + s) < b⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hb).mpr
    have hδb : 10 * (b + s) * b < 1 / 1000000 := by
      nlinarith only [mul_lt_mul_of_pos_right hbs1 hb, hbs1, hs]
    nlinarith only [hbΔ, hδb]
  have hstrongs : 200 * Δ + 10 * (b + s) < s⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hs).mpr
    have hδs : 10 * (b + s) * s < 1 / 1000000 := by
      nlinarith only [mul_lt_mul_of_pos_right hbs1 hs, hbs1, hb]
    nlinarith only [hsΔ, hδs]
  have hweakb : (ρ z)⁻¹ * Δ + 10 * (b' + s') < b'⁻¹ := by
    conv_rhs => rw [← one_div]
    apply (lt_div_iff₀ hwpos.1).mpr
    have hh : (ρ z)⁻¹ * Δ < 2 * Δ := mul_lt_mul_of_pos_right hinv hΔpos
    have hh' := mul_lt_mul_of_pos_right hh hwpos.1
    have hδ : 10 * (b' + s') * b' < 1 / 1000000 := by
      nlinarith only [mul_lt_mul_of_pos_right (add_lt_add hbp1 hsp1) hwpos.1, hbp1]
    nlinarith only [hh', hbpΔ, hδ]
  have hweaks : (ρ z)⁻¹ * Δ + 10 * (b' + s') < s'⁻¹ := by
    conv_rhs => rw [← one_div]
    apply (lt_div_iff₀ hwpos.2).mpr
    have hh : (ρ z)⁻¹ * Δ < 2 * Δ := mul_lt_mul_of_pos_right hinv hΔpos
    have hh' := mul_lt_mul_of_pos_right hh hwpos.2
    have hδ : 10 * (b' + s') * s' < 1 / 1000000 := by
      nlinarith only [mul_lt_mul_of_pos_right (add_lt_add hbp1 hsp1) hwpos.2, hsp1]
    nlinarith only [hh', hspΔ, hδ]
  have htΔ : τ * Δ < Δ / 10000 := by nlinarith only [mul_lt_mul_of_pos_right hτsmall hΔpos]
  have herr : (b' + s') / (ρ z)⁻¹ ≤ 2 * (b' + s') := by
    rw [div_inv_eq_mul]
    simpa only [mul_comm (b' + s') 2] using
      mul_le_mul_of_nonneg_left hrhoupper.le (add_pos hwpos.1 hwpos.2).le
  exact F.strip_height_lt_of_rescaled_edgePoint (hC := hC) (Δ := Δ) (R := 191 * Δ)
    (S := 200 * Δ) (r := Δ) (t := τ * Δ / 2) G (inv_pos.mpr hρz) (by positivity) hzedge
    (lt_min hstrongb hstrongs) (lt_min hweakb hweaks)
    (by linarith only [hΔ, hbs1, htΔ]) (by linarith only [hΔ, hbs1, htΔ, hlength])
    (by linarith only [hΔ, hbs1, htΔ]) (by linarith only [herr, hb'error, hs'error, hss', hbs, mul_pos hτ hΔpos]) hz

end GC.MetricGeometry.KleinerLottApprox
