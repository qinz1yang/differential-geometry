import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Topology.MetricSpace.CoarseGap
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {Z E X Y : Type*} [MetricSpace Z] [MetricSpace E] [MetricSpace X] [MetricSpace Y]

theorem exists_restricted_factor_approximation
    {p : Z} {u : E} {x₀ : X} {y₀ : Y} {b η A B D : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (u, x₀)) b)
    (g : KleinerLottApprox x₀ y₀ η)
    (hsegments : ∀ x y : Z, ∃ c : Icc (0 : ℝ) 1 → Z,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ D)
    (hA : 0 < A) (hDA : D + η < A) (hAB : b < B - A) (hB : B < η⁻¹) :
    ∃ F : KleinerLottApprox p (WithLp.toLp 2 (u, (⟨x₀, mem_ball_self hA⟩ : ball x₀ A))) b,
      (∀ z, (F.toFun z).fst = (f.toFun z).fst) ∧
      (∀ z ∈ ball p b⁻¹, ((F.toFun z).snd : X) = (f.toFun z).snd) ∧
      Bornology.IsBounded (univ : Set (ball x₀ A)) ∧
      diam (univ : Set (ball x₀ A)) ≤ D + η := by
  classical
  have hb0 := f.error_pos
  have hAB' : A < B := by linarith
  have havoid (x : X) : dist x x₀ < A ∨ B < dist x x₀ := by
    by_cases hl : dist x x₀ < A
    · exact Or.inl hl
    · right
      by_contra! hr
      have hx : x ∈ ball x₀ η⁻¹ := hr.trans_lt hB
      have hg := (abs_le.mp (g.radial_error x hx)).1
      have hd := (dist_le_diam_of_mem hY (mem_univ (g.toFun x)) (mem_univ y₀)).trans hD
      linarith
  have hrange (z : Z) (hz : z ∈ ball p b⁻¹) : (f.toFun z).snd ∈ ball x₀ A := by
    obtain ⟨c, hc0, hc1, hc⟩ := hsegments p z
    have hcin (t : Icc (0 : ℝ) 1) : c t ∈ ball p b⁻¹ := by
      have hd := hc t ⟨0, by norm_num⟩
      rw [hc0, Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] at hd
      change dist (c t) p < b⁻¹
      have hz' : dist p z < b⁻¹ := by simpa [dist_comm] using hz
      have hm := mul_le_mul_of_nonneg_left t.property.2 (dist_nonneg (x := p) (y := z))
      linarith
    let r : Icc (0 : ℝ) 1 → ℝ := fun t => dist (f.toFun (c t)).snd x₀
    have hd (s t : Icc (0 : ℝ) 1) :
        |r s - r t| ≤ dist p z * dist s t + b := by
      have h₁ := abs_dist_sub_le (f.toFun (c s)).snd (f.toFun (c t)).snd x₀
      have h₂ := WithLp.dist_snd_le (f.toFun (c s)) (f.toFun (c t))
      have h₃ := (abs_le.mp (f.distortion (c s) (hcin s) (c t) (hcin t))).2
      rw [hc] at h₃
      exact h₁.trans (h₂.trans (by linarith))
    have hconn : IsPreconnected (univ : Set (Icc (0 : ℝ) 1)) := isPreconnected_univ
    have ht := hconn.lt_iff_lt_of_coarse_bound r hAB (fun s _ t _ => hd s t)
      (fun t _ => havoid (f.toFun (c t)).snd)
      (x := ⟨0, by norm_num⟩) (y := ⟨1, by norm_num⟩) (mem_univ _) (mem_univ _)
    have hr0 : r ⟨0, by norm_num⟩ < A := by
      change dist (f.toFun (c ⟨0, by norm_num⟩)).snd x₀ < A
      rw [hc0, f.basepoint]
      simpa using hA
    change dist (f.toFun z).snd x₀ < A
    simpa only [r, hc1] using ht.mp hr0
  let q : ball x₀ A := ⟨x₀, mem_ball_self hA⟩
  let F' : Z → WithLp 2 (E × ball x₀ A) := fun z =>
    WithLp.toLp 2 ((f.toFun z).fst,
      if hz : z ∈ ball p b⁻¹ then ⟨(f.toFun z).snd, hrange z hz⟩ else q)
  let j : WithLp 2 (E × ball x₀ A) → WithLp 2 (E × X) :=
    WithLp.map 2 (Prod.map id Subtype.val)
  have hj : Isometry j := Isometry.withLpProdMap 2 isometry_id isometry_subtype_coe
  have htest (z : Z) (hz : z ∈ ball p b⁻¹) : j (F' z) = f.toFun z := by
    simp only [j, F', dite_eq_left hz, WithLp.map,
      Prod.map_apply, id_eq]
    rfl
  have hq : j (WithLp.toLp 2 (u, q)) = WithLp.toLp 2 (u, x₀) := rfl
  have hbase : F' p = WithLp.toLp 2 (u, q) := by
    apply hj.injective
    rw [htest p (mem_ball_self (inv_pos.mpr hb0)), hq, f.basepoint]
  have himage : j '' (F' '' ball p b⁻¹) = f.toFun '' ball p b⁻¹ := by
    rw [image_image]
    apply image_congr
    exact htest
  let F : KleinerLottApprox p (WithLp.toLp 2 (u, q)) b :=
    ⟨f.error_pos, f.error_lt_one, F', hbase,
      fun z hz z' hz' => by
        rw [← hj.dist_eq, htest z hz, htest z' hz']
        exact f.distortion z hz z' hz',
      fun y hy => by
        have hd : dist (j y) (WithLp.toLp 2 (u, x₀)) < b⁻¹ - b := by
          rw [← hq, hj.dist_eq]
          exact hy
        have h := f.coverage (j y) hd
        rw [← himage, Metric.infDist_image hj] at h
        exact h⟩
  have hpair (x x' : ball x₀ A) : dist x x' ≤ D + η := by
    have hd := (abs_le.mp (g.distortion x.val (x.property.trans (hAB'.trans hB))
      x'.val (x'.property.trans (hAB'.trans hB)))).1
    have hb := (dist_le_diam_of_mem hY (mem_univ (g.toFun x.val))
      (mem_univ (g.toFun x'.val))).trans hD
    change dist x.val x'.val ≤ _
    linarith
  refine ⟨F, fun _ => rfl, ?_, ?_, ?_⟩
  · intro z hz
    change (if hz' : z ∈ ball p b⁻¹ then
      (⟨(f.toFun z).snd, hrange z hz'⟩ : ball x₀ A) else q).val = _
    simp only [dite_eq_left hz]
  · exact Metric.isBounded_iff.mpr ⟨D + η, fun x _ x' _ => hpair x x'⟩
  · exact diam_le_of_forall_dist_le_of_nonempty ⟨q, mem_univ q⟩
      (fun x _ x' _ => hpair x x')


theorem exists_factor_approximation_of_bounded_target
    {p : Z} {u : E} {x₀ : X} {y₀ : Y} {b η Δ : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (u, x₀)) b)
    (g : KleinerLottApprox x₀ y₀ η)
    (hsegments : ∀ x y : Z, ∃ c : Icc (0 : ℝ) 1 → Z,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ 500 * Δ)
    (hΔ : 1 ≤ Δ) (hη : 900 * Δ < η⁻¹) :
    ∃ F : KleinerLottApprox p
      (WithLp.toLp 2 (u, (⟨x₀, mem_ball_self (by linarith)⟩ : ball x₀ (600 * Δ)))) b,
      (∀ z, (F.toFun z).fst = (f.toFun z).fst) ∧
      (∀ z ∈ ball p b⁻¹, ((F.toFun z).snd : X) = (f.toFun z).snd) ∧
      Bornology.IsBounded (univ : Set (ball x₀ (600 * Δ))) ∧
      diam (univ : Set (ball x₀ (600 * Δ))) < 1000 * Δ := by
  have he := g.error_lt_one
  have hb := f.error_lt_one
  obtain ⟨F, hfst, hsnd, hbound, hdiam⟩ := exists_restricted_factor_approximation f g
    hsegments hY hD (A := 600 * Δ) (B := 900 * Δ)
    (by linarith) (by linarith) (by linarith) hη
  exact ⟨F, hfst, hsnd, hbound, by linarith⟩

end GC.MetricGeometry
