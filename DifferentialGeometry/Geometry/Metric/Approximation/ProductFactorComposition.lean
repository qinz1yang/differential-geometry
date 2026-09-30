import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.ProductApproximation

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X E Y W : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y] [MetricSpace W]
variable {p : X} {u : E} {q : Y} {o : W} {b s S : ℝ}

theorem product_factor_composition_estimates
    (f : KleinerLottApprox p (WithLp.toLp 2 (u, q)) b)
    (g : KleinerLottApprox q o s)
    (hbuffer : S + 10 * (b + s) < min b⁻¹ s⁻¹) :
    let Q : X → WithLp 2 (E × W) := fun x =>
      WithLp.toLp 2 ((f.toFun x).fst, g.toFun (f.toFun x).snd)
    (∀ x ∈ ball p S, ∀ x' ∈ ball p S, |dist (Q x) (Q x') - dist x x'| ≤ b + s) ∧
      ∀ z : WithLp 2 (E × W), dist z (WithLp.toLp 2 (u, o)) ≤ S - 4 * (b + s) →
        ∃ x ∈ ball p S, dist (Q x) z < 3 * (b + s) ∧
          dist x p < dist z (WithLp.toLp 2 (u, o)) + 3 * (b + s) := by
  intro Q
  have hb := f.error_pos
  have hs := g.error_pos
  have hSb := hbuffer.trans_le (min_le_left _ _)
  have hSs := hbuffer.trans_le (min_le_right _ _)
  have hin (x : X) (hx : x ∈ ball p S) : x ∈ ball p b⁻¹ := by
    change dist x p < b⁻¹
    change dist x p < S at hx
    linarith
  have hfactor (x : X) (hx : x ∈ ball p S) : (f.toFun x).snd ∈ ball q s⁻¹ := by
    have hr := (abs_le.mp (f.radial_error x (hin x hx))).2
    have hp := WithLp.dist_snd_le (f.toFun x) (WithLp.toLp 2 (u, q))
    change dist (f.toFun x).snd q ≤ _ at hp
    change dist (f.toFun x).snd q < s⁻¹
    change dist x p < S at hx
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx x' hx'
    have hg := g.distortion (f.toFun x).snd (hfactor x hx)
      (f.toFun x').snd (hfactor x' hx')
    have hp := WithLp.prod_dist_dist_sub_le (f.toFun x).fst (f.toFun x').fst
      (g.toFun (f.toFun x).snd) (g.toFun (f.toFun x').snd)
      (f.toFun x).snd (f.toFun x').snd
    have hq : |dist (Q x) (Q x') - dist (f.toFun x) (f.toFun x')| ≤ s := hp.trans hg
    have hf := f.distortion x (hin x hx) x' (hin x' hx')
    have hq' := abs_le.mp hq
    have hf' := abs_le.mp hf
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro z hz
    have hzs : dist z.snd o < s⁻¹ - s := by
      have hp := WithLp.dist_snd_le z (WithLp.toLp 2 (u, o))
      change dist z.snd o ≤ _ at hp
      linarith
    obtain ⟨y, hy, hgy⟩ := g.coverage_witness z.snd hzs
    have hyr : |dist y q - dist z.snd o| < 3 * s := by
      have h₁ := abs_le.mp (g.radial_error y hy)
      have h₂ := abs_le.mp (abs_dist_sub_le z.snd (g.toFun y) o)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    let t := WithLp.toLp 2 (z.fst, y)
    have htr : dist t (WithLp.toLp 2 (u, q)) <
        dist z (WithLp.toLp 2 (u, o)) + 3 * s := by
      have h := WithLp.prod_dist_dist_sub_le z.fst u y q z.snd o
      have h'' := h.trans_lt hyr
      change |dist t (WithLp.toLp 2 (u, q)) - dist z (WithLp.toLp 2 (u, o))| < 3 * s at h''
      linarith [(abs_lt.mp h'').2]
    obtain ⟨x, hx, hfx⟩ := f.coverage_witness t (by linarith)
    have hxr : dist x p < dist z (WithLp.toLp 2 (u, o)) + 3 * (b + s) := by
      have hr := (abs_le.mp (f.radial_error x hx)).1
      have ht := dist_triangle (f.toFun x) t (WithLp.toLp 2 (u, q))
      rw [dist_comm (f.toFun x) t] at ht
      linarith
    have hxS : x ∈ ball p S := by change dist x p < S; linarith
    have hg := g.distortion (f.toFun x).snd (hfactor x hxS) y hy
    have hp := WithLp.prod_dist_dist_sub_le (f.toFun x).fst z.fst
      (g.toFun (f.toFun x).snd) (g.toFun y) (f.toFun x).snd y
    have hp' := abs_le.mp (hp.trans hg)
    have ht := dist_triangle (Q x) (WithLp.toLp 2 (z.fst, g.toFun y)) z
    have hsame : dist (WithLp.toLp 2 (z.fst, g.toFun y)) z = dist (g.toFun y) z.snd :=
      (WithLp.isometry_prodMk_left z.fst).dist_eq (g.toFun y) z.snd
    rw [hsame, dist_comm (g.toFun y) z.snd] at ht
    have hf' : dist (f.toFun x) t < 2 * b := by simpa only [dist_comm] using hfx
    refine ⟨x, hxS, ?_, hxr⟩
    have hpp := hp'.2
    change dist (Q x) (WithLp.toLp 2 (z.fst, g.toFun y)) - dist (f.toFun x) t ≤ s at hpp
    linarith

end GC.MetricGeometry.KleinerLottApprox
