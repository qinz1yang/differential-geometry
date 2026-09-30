import DifferentialGeometry.Geometry.Metric.Approximation.StripChart
import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry.KleinerLottApprox

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {C b s : ℝ}

theorem exists_strip_border_lift (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (t : ℝ) (hbuffer : |t| + 3 * b < min b⁻¹ s⁻¹) :
    ∃ a : X, dist a p < |t| + 3 * b ∧ dist (F.toFun a).snd q < 2 * b ∧
      dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) < 2 * b + s := by
  have hb := F.error_pos
  have htb := hbuffer.trans_le (min_le_left _ _)
  have hts := hbuffer.trans_le (min_le_right _ _)
  let z := WithLp.toLp 2 (t, q)
  have hz : dist z (WithLp.toLp 2 ((0 : ℝ), q)) = |t| := by
    change dist (WithLp.toLp 2 (t, q)) (WithLp.toLp 2 ((0 : ℝ), q)) = |t|
    exact ((WithLp.isometry_prodMk_right (E := ℝ) q).dist_eq t 0).trans (by simp)
  obtain ⟨a, ha, hFa⟩ := F.coverage_witness z (by rw [hz]; linarith)
  have hrad : dist a p < |t| + 3 * b := by
    have hh := (abs_le.mp (F.radial_error a ha)).1
    have ht := dist_triangle (F.toFun a) z (WithLp.toLp 2 ((0 : ℝ), q))
    rw [hz, dist_comm (F.toFun a) z] at ht
    linarith
  have hfactor : dist (F.toFun a).snd q < 2 * b := by
    have hh := WithLp.dist_snd_le (F.toFun a) z
    change dist (F.toFun a).snd q ≤ dist (F.toFun a) z at hh
    exact hh.trans_lt (by simpa only [dist_comm] using hFa)
  have hfactorball : (F.toFun a).snd ∈ ball q s⁻¹ := by
    change dist (F.toFun a).snd q < s⁻¹
    linarith [abs_nonneg t]
  have hG := G.radial_error (F.toFun a).snd hfactorball
  have hG' : |dist (G.toFun (F.toFun a).snd).val (0 : ℝ) - dist (F.toFun a).snd q| ≤ s := hG
  have hp := WithLp.prod_dist_dist_sub_le (F.toFun a).fst t
    (G.toFun (F.toFun a).snd).val (0 : ℝ) (F.toFun a).snd q
  have hd := (abs_le.mp (hp.trans hG')).2
  change dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) - dist (F.toFun a) z ≤ s at hd
  rw [dist_comm (F.toFun a) z] at hd
  exact ⟨a, hrad, hfactor, by linarith⟩

theorem exists_weak_edge_strip_border_lift {Δ b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hb' : 0 < b') (hs' : 0 < s')
    (hsmallb' : b' < 1 / 10000) (hsmalls' : s' < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hbΔ : b' < 1 / (1000000 * Δ))
    (hsb : s < b' / 100000) (hss : s < s' / 100000)
    (hbs : b < s / 100000) (hbb : b < b' / 100000)
    (hlength : 200 * Δ ≤ C) (t : ℝ) (ht : |t| ≤ 100 * Δ) :
    ∃ a : X, dist a p < 101 * Δ ∧
      (@isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b' s') ∧
      dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) < 2 * b + s := by
  have hb := F.error_pos
  have hs := G.error_pos
  have hΔ0 : 0 < Δ := by linarith
  have hbΔ' : b' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hbΔ
  have hbs' : b < s := by linarith
  have hsΔ : 101 * Δ * s < 1 := by nlinarith
  have hbΔ'' : 101 * Δ * b < 1 := by nlinarith
  have hdom : 101 * Δ < min b⁻¹ s⁻¹ := by
    apply lt_min
    · simpa only [one_div] using (lt_div_iff₀ hb).mpr hbΔ''
    · simpa only [one_div] using (lt_div_iff₀ hs).mpr hsΔ
  have hrad : |t| + 3 * b < 101 * Δ := by linarith [G.error_lt_one]
  obtain ⟨a, ha, hqa, hQa⟩ := F.exists_strip_border_lift hC G t (hrad.trans hdom)
  refine ⟨a, ha.trans hrad, ?_, hQa⟩
  exact isEdgePoint_of_lipschitz_scale hρ hρp (hρpos a) hΔ hC F G hb' hs'
    hsmallb' hsmalls' hscale hend hbΔ hsb hss hbs hbb hlength (ha.trans hrad).le hqa

end GC.MetricGeometry.KleinerLottApprox
