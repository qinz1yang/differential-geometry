import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Metric Set

namespace GC.MetricGeometry

variable {Z E X Y : Type*} [MetricSpace Z] [MetricSpace E] [MetricSpace X] [MetricSpace Y]

private theorem factor_lift (p : Z) (u : E) (x₀ : X) {b R : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (u, x₀)) b)
    (hR : R ≤ b⁻¹ - b) :
    ∃ a : X → Z, a x₀ = p ∧ ∀ x, dist x x₀ < R →
      dist (a x) p < dist x x₀ + 3 * b ∧
      dist (f.toFun (a x)) (WithLp.toLp 2 (u, x)) < 2 * b ∧
      a x ∈ ball p b⁻¹ := by
  classical
  have hex (x : X) : ∃ z : Z, (x = x₀ → z = p) ∧ (dist x x₀ < R →
      dist z p < dist x x₀ + 3 * b ∧
      dist (f.toFun z) (WithLp.toLp 2 (u, x)) < 2 * b ∧ z ∈ ball p b⁻¹) := by
    by_cases h : x = x₀
    · subst x
      refine ⟨p, fun _ => rfl, fun _ => ?_⟩
      simp only [dist_self, f.basepoint, zero_add]
      exact ⟨by linarith [f.error_pos], by linarith [f.error_pos],
        mem_ball_self (inv_pos.mpr f.error_pos)⟩
    · by_cases hx : dist x x₀ < R
      · have ht : dist (WithLp.toLp 2 (u, x)) (WithLp.toLp 2 (u, x₀)) < b⁻¹ - b := by
          rw [(WithLp.isometry_prodMk_left u).dist_eq x x₀]
          exact hx.trans_le hR
        obtain ⟨z, hz, hd⟩ := f.coverage_witness (WithLp.toLp 2 (u, x)) ht
        have hr := (abs_le.mp (f.radial_error z hz)).1
        have htri := dist_triangle (f.toFun z) (WithLp.toLp 2 (u, x))
          (WithLp.toLp 2 (u, x₀))
        rw [(WithLp.isometry_prodMk_left u).dist_eq x x₀] at htri
        rw [dist_comm] at hd
        exact ⟨z, fun he => (h he).elim, fun _ => ⟨by linarith, hd, hz⟩⟩
      · exact ⟨p, fun he => (h he).elim, fun he => (hx he).elim⟩
  choose a ha hb using hex
  exact ⟨a, ha x₀ rfl, hb⟩


private theorem product_dist_le_sum {A B : Type*} [MetricSpace A] [MetricSpace B]
    (x y : WithLp 2 (A × B)) :
    dist x y ≤ dist x.fst y.fst + dist x.snd y.snd := by
  nlinarith [WithLp.prod_dist_sq_eq_add_sq x y, dist_nonneg (x := x) (y := y),
    dist_nonneg (x := x.fst) (y := y.fst), dist_nonneg (x := x.snd) (y := y.snd),
    mul_nonneg (dist_nonneg (x := x.fst) (y := y.fst))
      (dist_nonneg (x := x.snd) (y := y.snd))]

theorem exists_factor_approximation_of_common_coordinate
    {L η θ : ℝ}
    (hL : 1 ≤ L) (hη : 0 < η) (hη1 : η < 1) (hθ : 0 < θ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {Z E X Y : Type*} [MetricSpace Z] [MetricSpace E] [MetricSpace X] [MetricSpace Y]
        (p : Z) (u : E) (x₀ : X) (y₀ : Y) (b e : ℝ), b < ε → e < ε →
      ∀ (f : KleinerLottApprox p (WithLp.toLp 2 (u, x₀)) b)
        (g : KleinerLottApprox p (WithLp.toLp 2 (u, y₀)) e),
        (∀ z, (f.toFun z).fst = (g.toFun z).fst) →
        ∃ G : KleinerLottApprox x₀ y₀ η, ∀ z ∈ ball p L,
          dist (G.toFun (f.toFun z).snd) (g.toFun z).snd < θ := by
  classical
  let R := 4 * (L + η⁻¹ + 1)
  have hi : 0 < η⁻¹ := inv_pos.mpr hη
  have hR : 8 < R := by dsimp [R]; linarith
  let ε := min (η / 100) (min (1 / (100 * R)) (min (θ ^ 2 / (100 * (L + 1))) (1 / 100)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  intro Z E X Y _ _ _ _ p u x₀ y₀ b e hb he f g hcoord
  have hb0 := f.error_pos
  have he0 := g.error_pos
  have hbη : b < η / 100 := hb.trans_le (min_le_left _ _)
  have heη : e < η / 100 := he.trans_le (min_le_left _ _)
  have hbR : b < 1 / (100 * R) := hb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heR : e < 1 / (100 * R) := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbθ : b < θ ^ 2 / (100 * (L + 1)) :=
    hb.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heθ : e < θ ^ 2 / (100 * (L + 1)) :=
    he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb1 : b < 1 / 100 :=
    hb.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he1 : e < 1 / 100 :=
    he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hRb : 2 * R < b⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hb0).mpr
    have ht := (lt_div_iff₀ (show 0 < 100 * R by positivity)).mp hbR
    nlinarith
  have hRe : 2 * R < e⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ he0).mpr
    have ht := (lt_div_iff₀ (show 0 < 100 * R by positivity)).mp heR
    nlinarith
  obtain ⟨a, ha0, ha⟩ := factor_lift p u x₀ f (R := R) (by linarith)
  have hag (x : X) (hx : dist x x₀ < R) : a x ∈ ball p e⁻¹ := by
    have := (ha x hx).1
    change dist (a x) p < e⁻¹
    linarith
  let G : X → Y := fun x => (g.toFun (a x)).snd
  have hG0 : G x₀ = y₀ := by simp [G, ha0, g.basepoint]
  have hfirst (x : X) (hx : dist x x₀ < R) : dist (f.toFun (a x)).fst u < 2 * b :=
    (WithLp.dist_fst_le _ _).trans_lt (ha x hx).2.1
  have hdist (x x' : X) (hx : dist x x₀ < R) (hx' : dist x' x₀ < R) :
      |dist (G x) (G x') - dist x x'| < e + 9 * b := by
    have hfd := abs_le.mp (f.distortion (a x) (ha x hx).2.2 (a x') (ha x' hx').2.2)
    have hgd := abs_le.mp (g.distortion (a x) (hag x hx) (a x') (hag x' hx'))
    have ht := dist_dist_dist_le (f.toFun (a x)) (f.toFun (a x'))
      (WithLp.toLp 2 (u, x)) (WithLp.toLp 2 (u, x'))
    rw [Real.dist_eq, (WithLp.isometry_prodMk_left u).dist_eq x x'] at ht
    have ht' := abs_le.mp ht
    have hc : dist (g.toFun (a x)).fst (g.toFun (a x')).fst < 4 * b := by
      rw [← hcoord, ← hcoord]
      have := dist_triangle_right (f.toFun (a x)).fst (f.toFun (a x')).fst u
      linarith [hfirst x hx, hfirst x' hx']
    have hu := product_dist_le_sum (g.toFun (a x)) (g.toFun (a x'))
    have hl := WithLp.dist_snd_le (g.toFun (a x)) (g.toFun (a x'))
    change |dist (g.toFun (a x)).snd (g.toFun (a x')).snd - dist x x'| < _
    exact abs_lt.mpr ⟨by linarith [(ha x hx).2.1, (ha x' hx').2.1],
      by linarith [(ha x hx).2.1, (ha x' hx').2.1]⟩
  have hηR : η⁻¹ < R := by dsimp [R]; linarith
  have hcoverage : ∀ y : Y, dist y y₀ < η⁻¹ - η →
      ∃ x ∈ ball x₀ η⁻¹, dist y (G x) < η := by
    intro y hy
    have hyt : dist (WithLp.toLp 2 (u, y)) (WithLp.toLp 2 (u, y₀)) < e⁻¹ - e := by
      rw [(WithLp.isometry_prodMk_left u).dist_eq y y₀]
      linarith
    obtain ⟨z, hze, hz⟩ := g.coverage_witness (WithLp.toLp 2 (u, y)) hyt
    have hzr : dist z p < dist y y₀ + 3 * e := by
      have hr := (abs_le.mp (g.radial_error z hze)).1
      have ht := dist_triangle (g.toFun z) (WithLp.toLp 2 (u, y))
        (WithLp.toLp 2 (u, y₀))
      rw [(WithLp.isometry_prodMk_left u).dist_eq y y₀] at ht
      rw [dist_comm] at hz
      linarith
    have hzb : z ∈ ball p b⁻¹ := by change dist z p < b⁻¹; linarith
    let x := (f.toFun z).snd
    have hxr : dist x x₀ < dist y y₀ + 3 * e + b := by
      have hr := (abs_le.mp (f.radial_error z hzb)).2
      have := WithLp.dist_snd_le (f.toFun z) (WithLp.toLp 2 (u, x₀))
      change dist x x₀ ≤ _ at this
      linarith
    have hxi : dist x x₀ < η⁻¹ := by linarith
    have hxR : dist x x₀ < R := hxi.trans hηR
    have hzc : dist (f.toFun z).fst u < 2 * e := by
      rw [hcoord, dist_comm]
      exact (WithLp.dist_fst_le (WithLp.toLp 2 (u, y)) (g.toFun z)).trans_lt hz
    have hza : dist z (a x) < 2 * e + 3 * b := by
      have ht := dist_triangle (f.toFun z) (WithLp.toLp 2 (u, x)) (f.toFun (a x))
      have hsame : dist (f.toFun z) (WithLp.toLp 2 (u, x)) = dist (f.toFun z).fst u := by
        exact (WithLp.isometry_prodMk_right x).dist_eq (f.toFun z).fst u
      rw [hsame, dist_comm (WithLp.toLp 2 (u, x))] at ht
      have hd := (abs_le.mp (f.distortion z hzb (a x) (ha x hxR).2.2)).1
      linarith [(ha x hxR).2.1]
    have hgy := WithLp.dist_snd_le (WithLp.toLp 2 (u, y)) (g.toFun z)
    simp only [WithLp.toLp_snd] at hgy
    have hga := WithLp.dist_snd_le (g.toFun z) (g.toFun (a x))
    have hd := (abs_le.mp (g.distortion z hze (a x) (hag x hxR))).2
    have ht := dist_triangle y (g.toFun z).snd (g.toFun (a x)).snd
    refine ⟨x, hxi, ?_⟩
    change dist y (g.toFun (a x)).snd < η
    linarith
  let F : KleinerLottApprox x₀ y₀ η :=
    ⟨hη, hη1, G, hG0,
      fun x hx x' hx' => (hdist x x' (hx.trans hηR) (hx'.trans hηR)).le.trans (by linarith),
      fun y hy => by
        obtain ⟨x, hx, hd⟩ := hcoverage y hy
        exact (infDist_le_dist_of_mem (show G x ∈ G '' ball x₀ η⁻¹ from ⟨x, hx, rfl⟩)).trans hd.le⟩
  refine ⟨F, ?_⟩
  intro z hz
  have hzL : dist z p < L := hz
  have hzb : z ∈ ball p b⁻¹ := by change dist z p < b⁻¹; dsimp [R] at hRb; linarith
  have hze : z ∈ ball p e⁻¹ := by change dist z p < e⁻¹; dsimp [R] at hRe; linarith
  let x := (f.toFun z).snd
  have hxr : dist x x₀ < L + b := by
    have hr := (abs_le.mp (f.radial_error z hzb)).2
    have := WithLp.dist_snd_le (f.toFun z) (WithLp.toLp 2 (u, x₀))
    change dist x x₀ ≤ _ at this
    linarith
  have hxR : dist x x₀ < R := by dsimp [R]; linarith
  have hza : dist z (a x) < dist (f.toFun z).fst (f.toFun (a x)).fst + 3 * b := by
    have hsum := product_dist_le_sum (f.toFun z) (f.toFun (a x))
    have hs := WithLp.dist_snd_le (f.toFun (a x)) (WithLp.toLp 2 (u, x))
    have hd := (abs_le.mp (f.distortion z hzb (a x) (ha x hxR).2.2)).1
    rw [dist_comm (f.toFun (a x)).snd] at hs
    change dist (f.toFun z).snd (f.toFun (a x)).snd ≤ _ at hs
    linarith [(ha x hxR).2.1]
  have hU : dist (f.toFun z).fst (f.toFun (a x)).fst < L + 3 * b := by
    have hc := WithLp.dist_fst_le (f.toFun z) (WithLp.toLp 2 (u, x₀))
    simp only [WithLp.toLp_fst] at hc
    have hr := (abs_le.mp (f.radial_error z hzb)).2
    have ht := dist_triangle_right (f.toFun z).fst (f.toFun (a x)).fst u
    linarith [hfirst x hxR]
  have hprod : dist (g.toFun z) (g.toFun (a x)) <
      dist (g.toFun z).fst (g.toFun (a x)).fst + (e + 3 * b) := by
    have hd := (abs_le.mp (g.distortion z hze (a x) (hag x hxR))).2
    rw [hcoord, hcoord] at hza
    linarith
  have hsq := WithLp.prod_dist_sq_eq_add_sq (g.toFun z) (g.toFun (a x))
  have hsmall : (2 * L + 8) * (e + 3 * b) < θ ^ 2 := by
    have hp : 0 < 100 * (L + 1) := by linarith
    have hbt := (lt_div_iff₀ hp).mp hbθ
    have het := (lt_div_iff₀ hp).mp heθ
    nlinarith
  rw [hcoord, hcoord] at hU
  have hd0 := dist_nonneg (x := (g.toFun z)) (y := g.toFun (a x))
  have hu0 := dist_nonneg (x := (g.toFun z).fst) (y := (g.toFun (a x)).fst)
  have hprodSq := (sq_lt_sq₀ hd0 (by positivity : 0 ≤
    dist (g.toFun z).fst (g.toFun (a x)).fst + (e + 3 * b))).mpr hprod
  have hUbound := mul_lt_mul_of_pos_right hU (by linarith : 0 < e + 3 * b)
  have herr : (e + 3 * b) ^ 2 < (e + 3 * b) := by nlinarith
  change dist (g.toFun (a x)).snd (g.toFun z).snd < θ
  rw [dist_comm]
  nlinarith [sq_nonneg (dist (g.toFun z).snd (g.toFun (a x)).snd - θ)]

end GC.MetricGeometry
