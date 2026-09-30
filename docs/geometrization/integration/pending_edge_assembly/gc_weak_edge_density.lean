import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeLifts
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedModelHeight

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

private theorem nearby_of_model_border_lifts {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {p z : X} {o o₀ : Y} {e Δ : ℝ} {Λ : NNReal} {ρ : X → ℝ} {P : X → Prop}
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1) (hΔ : 1 ≤ Δ)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (he : e < 1 / 100000000) (heΔ : e ≤ 1 / (1000 * Δ))
    (hz : z ∈ ball p (10 * Δ)) (hheight : dist (H.toFun z).snd o₀ < 1 / 20)
    (hlifts : ∀ t : ℝ, |t| ≤ 12 * Δ →
      ∃ a : X, dist a p < 13 * Δ ∧ P a ∧
        dist (H.toFun a) (WithLp.toLp 2 (t, o₀)) < 2 * e) :
    ∃ a : X, P a ∧ dist z a < ρ a := by
  have hepos := H.error_pos
  have hΔpos : 0 < Δ := by linarith only [hΔ]
  have hprod : e * (1000 * Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp heΔ
  have hsource : 13 * Δ < e⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hepos).mpr
    nlinarith only [hprod]
  have hzsource : z ∈ ball p e⁻¹ := (show dist z p < 10 * Δ from hz).trans (by linarith)
  have ht : |(H.toFun z).fst| ≤ 12 * Δ := by
    have hd := (abs_le.mp (H.radial_error z hzsource)).2
    have hf := WithLp.dist_fst_le (H.toFun z) (WithLp.toLp 2 ((0 : ℝ), o))
    change dist (H.toFun z).fst (0 : ℝ) ≤ _ at hf
    rw [Real.dist_eq, sub_zero] at hf
    change dist z p < 10 * Δ at hz
    linarith only [hd, hf, hz, he, hΔ]
  obtain ⟨a, ha, hP, hclose⟩ := hlifts (H.toFun z).fst ht
  have hasource : a ∈ ball p e⁻¹ := ha.trans hsource
  have hmodel : dist (H.toFun z) (WithLp.toLp 2 ((H.toFun z).fst, o₀)) =
      dist (H.toFun z).snd o₀ :=
    (WithLp.isometry_prodMk_left (H.toFun z).fst).dist_eq (H.toFun z).snd o₀
  have hdist : dist z a < 1 / 10 := by
    have hd := (abs_le.mp (H.distortion z hzsource a hasource)).1
    have htri := dist_triangle (H.toFun z) (WithLp.toLp 2 ((H.toFun z).fst, o₀)) (H.toFun a)
    rw [hmodel] at htri
    have hclose' : dist (WithLp.toLp 2 ((H.toFun z).fst, o₀)) (H.toFun a) < 2 * e := by
      simpa only [dist_comm] using hclose
    linarith only [hd, htri, hheight, hclose', he]
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hrho : |ρ a - 1| ≤ (Λ : ℝ) * (13 * Δ) := by
    have hd := hρ.dist_le_mul a p
    rw [Real.dist_eq, hρp] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left ha.le Λ.coe_nonneg)
  have hlower : 1 / 2 < ρ a := by nlinarith only [hΛΔ, (abs_le.mp hrho).1]
  exact ⟨a, hP, hdist.trans (by linarith only [hlower])⟩

universe u v w
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p z : X} {q : Y} {Δ β βE s η e θ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}

theorem exists_strong_edge_near_weak_interval_model {C : ℝ} {o : Icc (0 : ℝ) C}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hC : 500 * Δ < C) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (heprec : e < 1 / 100000000) (hb' : b' < 1 / 100000000) (hs' : s' < 1 / 100000000)
    (hzedge : @isEdgePoint.{u, w} X (mX.rescale (ρ z)⁻¹ (inv_pos.mpr (hρpos z))) z Δ b' s')
    (hz : z ∈ ball p (10 * Δ)) :
    ∃ a : X, (@isEdgePoint.{u, v} X
      (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist z a < ρ a := by
  let o₀ : Icc (0 : ℝ) C := ⟨0, by constructor <;> linarith [hΔ]⟩
  have hheight : dist (H.toFun z).snd o₀ < 1 / 20 := by
    have hh := H.model_height_lt_of_weak_edge (Δ := Δ)
      (fun x hx => ⟨hx.1, hx.2.trans hC.le⟩)
      (by rwa [abs_of_nonneg o.property.1]) hρ hρp (hρpos z) hΔ hscale heprec heΔ hb' hs' hzedge hz
    simpa only [Subtype.dist_eq, Real.dist_eq, o₀, sub_zero,
      abs_of_nonneg (H.toFun z).snd.property.1] using hh
  apply nearby_of_model_border_lifts H hρ hρp hΔ hscale heprec heΔ hz hheight
  intro t ht
  obtain ⟨a, hrad, hed, hclose⟩ := exists_strong_edge_interval_lift F G H hρ hρpos hρp
    hΔ hC hβE hβsmall hβdomain hs hssmall hηs hηΔ he heΔ hθ hscale ho hcompat t ht
  refine ⟨a, ?_, hed, hclose⟩
  linarith only [hrad, ht, ho, heprec, hΔ]

theorem exists_strong_edge_near_weak_ray_model {o : Ici (0 : ℝ)}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (heprec : e < 1 / 100000000) (hb' : b' < 1 / 100000000) (hs' : s' < 1 / 100000000)
    (hzedge : @isEdgePoint.{u, w} X (mX.rescale (ρ z)⁻¹ (inv_pos.mpr (hρpos z))) z Δ b' s')
    (hz : z ∈ ball p (10 * Δ)) :
    ∃ a : X, (@isEdgePoint.{u, v} X
      (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist z a < ρ a := by
  let o₀ : Ici (0 : ℝ) := ⟨0, by norm_num⟩
  have hheight : dist (H.toFun z).snd o₀ < 1 / 20 := by
    have hh := H.model_height_lt_of_weak_edge (Δ := Δ)
      (fun x hx => hx.1)
      (by rwa [abs_of_nonneg o.property]) hρ hρp (hρpos z) hΔ hscale heprec heΔ hb' hs' hzedge hz
    simpa only [Subtype.dist_eq, Real.dist_eq, o₀, sub_zero,
      abs_of_nonneg (show 0 ≤ (H.toFun z).snd.val from (H.toFun z).snd.property)] using hh
  apply nearby_of_model_border_lifts H hρ hρp hΔ hscale heprec heΔ hz hheight
  intro t ht
  obtain ⟨a, hrad, hed, hclose⟩ := exists_strong_edge_ray_lift F G H hρ hρpos hρp
    hΔ hβE hβsmall hβdomain hs hssmall hηs hηΔ he heΔ hθ hscale ho hcompat t ht
  refine ⟨a, ?_, hed, hclose⟩
  linarith only [hrad, ht, ho, heprec, hΔ]

end GC.MetricGeometry
