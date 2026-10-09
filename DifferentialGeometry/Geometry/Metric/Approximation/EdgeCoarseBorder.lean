import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHeight
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderLifts
import DifferentialGeometry.Geometry.Metric.CoarseClosure

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry.KleinerLottApprox

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {C b s : ℝ} {hC : 0 ≤ C}

theorem coarse_border_of_lipschitz_scale {Δ τ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000)
    (hbs : b < s / 100000) (hlength : 200 * Δ ≤ C) :
    let E : Set X := {x | @isEdgePoint.{u, v} X
      (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
    IsClosed (closure E) ∧ p ∈ closure E ∧ F.stripMap G p = 0 ∧
      (∀ x, 0 ≤ (F.stripMap G x).snd) ∧
      (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
        |dist (F.stripMap G x) (F.stripMap G y) - dist x y| ≤ τ * Δ) ∧
      (∀ y : WithLp 2 (ℝ × ℝ), |y.fst| ≤ 100 * Δ → y.snd ∈ Icc 0 (100 * Δ) →
        ∃ x ∈ ball p (200 * Δ), dist (F.stripMap G x) y < τ * Δ) ∧
      (∀ a ∈ closure E ∩ ball p (190 * Δ), (F.stripMap G a).snd ≤ τ * Δ) ∧
      ∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ E ∩ ball p (190 * Δ),
        dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) < τ * Δ := by
  let E : Set X := {x | @isEdgePoint.{u, v} X
    (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
  have hb := F.error_pos
  have hs := G.error_pos
  have hb' : 0 < b' := by linarith only [hs, hsb']
  have hs' : 0 < s' := by linarith only [hs, hss']
  have hbb' : b < b' / 100000 := (show b < s by linarith only [hbs, hs]).trans hsb'
  have hΔpos : 0 < Δ := by linarith
  have hτΔ : 0 < τ * Δ := mul_pos hτ hΔpos
  have hbpΔ : b' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hb'domain
  have hspΔ : s' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hs'domain
  have hbp1 : b' < 1 / 1000000 := by nlinarith only [hbpΔ, hΔ, hb']
  have hsp1 : s' < 1 / 1000000 := by nlinarith only [hspΔ, hΔ, hs']
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
  obtain ⟨hQdist, hQcover⟩ := F.stripMap_estimates (hC := hC) G (lt_min hstrongb hstrongs)
  have hsmallb' : b' < 1 / 10000 := by linarith only [hbp1]
  have hsmalls' : s' < 1 / 10000 := by linarith only [hsp1]
  have hpweak : p ∈ E := isEdgePoint_of_lipschitz_scale hρ hρp (hρpos p) hΔ hC F G
    hb' hs' hsmallb' hsmalls' hscale hend hb'domain hsb' hss' hbs hbb' hlength
    (by simp only [dist_self]; positivity)
    (by rw [F.basepoint]; simpa only [WithLp.toLp_snd, dist_self] using (show 0 < 2 * b by positivity))
  refine ⟨isClosed_closure, subset_closure hpweak, F.stripMap_basepoint (hC := hC) G,
    fun x => (F.stripMap_height (hC := hC) G x).1, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact (hQdist x hx y hy).trans (by linarith only [hτΔ, hs'error, hss', hbs])
  · intro y hyfst hysnd
    have hnorm : ‖y‖ ≤ 150 * Δ := by
      apply (sq_le_sq₀ (norm_nonneg y) (by positivity)).mp
      rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      have hfst := (sq_le_sq₀ (abs_nonneg y.fst) (by positivity : 0 ≤ 100 * Δ)).mpr hyfst
      rw [sq_abs] at hfst
      have hsnd := (sq_le_sq₀ hysnd.1 (by positivity : 0 ≤ 100 * Δ)).mpr hysnd.2
      nlinarith only [hfst, hsnd, sq_nonneg Δ]
    obtain ⟨x, hx, hxy, _⟩ := hQcover y ⟨hysnd.1, by linarith only [hysnd.2, hlength, hΔ]⟩
      (by linarith only [hnorm, hΔ, hbs1])
    exact ⟨x, hx, hxy.trans (by linarith only [hτΔ, hs'error, hss', hbs])⟩
  · intro a ha
    have hweak : ∀ x ∈ E ∩ ball p (191 * Δ), (F.stripMap G x).snd ≤ τ * Δ / 2 := by
      intro x hx
      exact (F.strip_height_lt_of_weak_edge (hC := hC) G hρ hρp (hρpos x) hΔ hτ hτsmall
        hscale hb'domain hs'domain hb'error hs'error hss' hbs hlength hx.1 hx.2).le
    have hcoarse : ∀ x ∈ ball p (191 * Δ), ∀ y ∈ ball p (191 * Δ),
        |(F.stripMap G x).snd - (F.stripMap G y).snd| ≤ dist x y + (b + s) := by
      intro x hx y hy
      have hx' : x ∈ ball p (200 * Δ) := (show dist x p < 191 * Δ from hx).trans (by linarith)
      have hy' : y ∈ ball p (200 * Δ) := (show dist y p < 191 * Δ from hy).trans (by linarith)
      have hcoord := WithLp.dist_snd_le (F.stripMap G x) (F.stripMap G y)
      rw [Real.dist_eq] at hcoord
      have hdist := (abs_le.mp (hQdist x hx' y hy')).2
      linarith only [hcoord, hdist]
    have hheight := le_on_closure_of_coarse_bound isOpen_ball hweak hcoarse
      ⟨ha.1, (show dist a p < 190 * Δ from ha.2).trans (by linarith)⟩
    exact hheight.trans (by linarith only [hτΔ, hs'error, hss', hbs])
  · intro t ht
    obtain ⟨a, ha, haw, hQa⟩ := F.exists_weak_edge_strip_border_lift hρ hρpos hρp hΔ hC G
      hb' hs' hsmallb' hsmalls' hscale hend hb'domain hsb' hss' hbs hbb' hlength t ht
    exact ⟨a, ⟨haw, ha.trans (by linarith)⟩,
      hQa.trans (by linarith only [hτΔ, hs'error, hss', hbs])⟩

end GC.MetricGeometry.KleinerLottApprox
