import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelRegion

/-!
# Every pants point lies on a circle of the nested family

Lane N2f, side model, step 6 (cover, planar part). For a point `z` of the pants and the host chart
coordinate `w = hostInv l z`, `w` lies in the closed disc of the host circle
(`norm_hostInv_le`) and outside the circle of the port of side `t` (`le_norm_sub_famC_of_mem`, the
converse of `circleSign_port_aux`). By the intermediate value theorem `w` is a point of the nested
circle family of side `t` at a parameter `ρ ∈ [3/2, 3]` (`exists_point_eq`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

theorem circleSign_nonneg_of_mem {z : ℂ} (hz : z ∈ planarModel 3) (p : Fin 3) :
    0 ≤ circleSign p z :=
  planarSign_mul_nonneg p hz

theorem hostInv_ne_zero_of_mem (l : Fin 3) {z : ℂ} (hz : z ∈ planarModel 3) :
    l.val ≠ 0 → hostInv l z ≠ 0 := by
  intro hl
  have h := circleSign_nonneg_of_mem hz l
  simp only [circleSign, planarSign, planarRadius, hl, ↓reduceIte, one_mul] at h
  rw [hostInv_of_ne hl]
  exact inv_ne_zero (norm_pos_iff.mp (by linarith))

theorem norm_hostInv_le (l : Fin 3) {z : ℂ} (hz : z ∈ planarModel 3) :
    ‖hostInv l z‖ ≤ hostRadius l.val 0 := by
  have h := circleSign_nonneg_of_mem hz l
  by_cases hl : l.val = 0
  · simp only [circleSign, planarSign, planarRadius, hl, ↓reduceIte, planarCenter_zero hl,
      Complex.ofReal_zero, sub_zero] at h
    rw [hostInv_of_zero hl]
    simp only [hostRadius, hl, ↓reduceIte]
    linarith
  · simp only [circleSign, planarSign, planarRadius, hl, ↓reduceIte, one_mul] at h
    rw [hostInv_of_ne hl, norm_inv]
    simp only [hostRadius, hl, ↓reduceIte]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith

theorem le_norm_sub_famC_of_circleSign (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h : 0 ≤ circleSign (sidePort l t) (hostChart l w)) :
    (sideData l t).famR 3 ≤ ‖w - (sideData l t).famC 3‖ := by
  by_contra hc
  push Not at hc
  rw [famC_three, famR_three] at hc
  unfold sideData at hc
  split_ifs at hc with hl hp
  · simp only [zeroData] at hc
    have hp0 : (sidePort l t).val ≠ 0 := by fin_cases l <;> cases t <;> simp_all [sidePort]
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖w - planarCenter 3 (sidePort l t)‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp0, ↓reduceIte, hostChart, hl, one_mul]
    rw [e] at h
    norm_num at hc
    linarith
  · simp only [outerData] at hc
    have hA2 : (planarCenter 3 (sidePort l t) - planarCenter 3 l) ^ 2 = 9 / 4 := by
      rw [← sq_abs, abs_sidePort_outer hl hp]; norm_num
    set A := planarCenter 3 (sidePort l t) - planarCenter 3 l with hAdef
    have hcl : planarCenter 3 l = -A := by
      rw [hAdef, planarCenter_zero hp]; ring
    have hw0 := hw hl
    have hA2c : (A : ℂ) ^ 2 = 9 / 4 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hA2
      push_cast at this
      exact this
    norm_num at hc
    rw [hA2] at hc
    norm_num at hc
    try rw [hA2c] at hc
    have hR : ‖w - ((-(4 / 27) * A : ℝ) : ℂ)‖ < 4 / 9 := by
      convert (show ‖w - ((A / (9 / 4 - 9) : ℝ) : ℂ)‖ < 4 / 9 by
        push_cast at hc ⊢; linarith) using 4
      ring
    have hn : Complex.normSq (w - ((-(4 / 27) * A : ℝ) : ℂ)) < (4 / 9) ^ 2 := by
      rw [← Complex.sq_norm]
      exact pow_lt_pow_left₀ hR (norm_nonneg _) two_ne_zero
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        3 - ‖((planarCenter 3 l : ℝ) : ℂ) + w⁻¹‖ := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl,
        planarCenter_zero hp, Complex.ofReal_zero, sub_zero]
      ring
    rw [e, hcl] at h
    have hns := Complex.normSq_nonneg w
    have := lt_norm_add_inv_of (-A) 3 hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
    push_cast at this h
    linarith
  · simp only [innerData] at hc
    have hA2 : (planarCenter 3 (sidePort l t) - planarCenter 3 l) ^ 2 = 9 := by
      rw [← sq_abs, abs_sidePort_inner hl hp]; norm_num
    set A := planarCenter 3 (sidePort l t) - planarCenter 3 l with hAdef
    have hw0 := hw hl
    have hA2c : (A : ℂ) ^ 2 = 9 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hA2
      push_cast at this
      exact this
    norm_num at hc
    rw [hA2] at hc
    norm_num at hc
    try rw [hA2c] at hc
    have hR : ‖w - (((4 / 35) * A : ℝ) : ℂ)‖ < 2 / 35 := by
      convert (show ‖w - ((A / (9 - 1 / 4) : ℝ) : ℂ)‖ < 2 / 35 by
        push_cast at hc ⊢; linarith) using 4
      ring
    have hn : Complex.normSq (w - (((4 / 35) * A : ℝ) : ℂ)) < (2 / 35) ^ 2 := by
      rw [← Complex.sq_norm]
      exact pow_lt_pow_left₀ hR (norm_nonneg _) two_ne_zero
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖((-A : ℝ) : ℂ) + w⁻¹‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl, one_mul]
      congr 2
      rw [hAdef]
      push_cast
      ring
    rw [e] at h
    have hns := Complex.normSq_nonneg w
    have := norm_add_inv_lt_of (-A) (1 / 2) hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
    linarith

theorem le_norm_sub_famC_of_mem (l : Fin 3) (t : Bool) {z : ℂ} (hz : z ∈ planarModel 3) :
    (sideData l t).famR 3 ≤ ‖hostInv l z - (sideData l t).famC 3‖ := by
  refine le_norm_sub_famC_of_circleSign l t (hostInv_ne_zero_of_mem l hz) ?_
  rw [hostChart_hostInv]
  exact circleSign_nonneg_of_mem hz _

theorem vRadius_three (l : Fin 3) : vRadius l 3 = hostRadius l.val 0 := by
  have h := famR_three_halves (sideData l false)
  rw [(sideData l false).famR_of_le (by norm_num)] at h
  rw [← h]
  norm_num

theorem exists_point_eq (l : Fin 3) (t : Bool) {z : ℂ} (hz : z ∈ planarModel 3) :
    ∃ q : Circle × ℝ, q.2 ∈ Icc (3 / 2 : ℝ) 3 ∧ (sideData l t).point q = hostInv l z := by
  set D := sideData l t
  have hw := norm_hostInv_le l hz
  have h0 : ‖hostInv l z - D.famC 0‖ ≤ D.famR 0 := by
    rw [D.famC_of_le (by norm_num), D.famR_of_le (by norm_num), sub_zero, mul_zero]
    refine hw.trans ?_
    rw [← vRadius_three]
    exact ((strictAntiOn_vRadius l) (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by norm_num))
      (by norm_num : (0 : ℝ) < 3)).le
  obtain ⟨q, hq, he⟩ := exists_nestedPoint_eq (μ := D.famMu) D.continuousOn_famC
    D.continuousOn_famR (fun ρ hρ => D.famR_pos hρ) (fun ρ hρ => D.famA_lt' hρ) h0
    (le_norm_sub_famC_of_mem l t hz)
  refine ⟨q, ⟨?_, hq.2⟩, he⟩
  by_contra hlt
  push Not at hlt
  have hp : D.point q = (vRadius l (2 * q.2) : ℂ) * (q.1 : ℂ) := D.point_of_le_two (by linarith)
  have h2v : 2 ≤ vRadius l (2 * q.2) := two_le_vRadius l (by linarith [hq.1]) (by linarith)
  have hn : ‖D.point q‖ = vRadius l (2 * q.2) := by
    rw [hp, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hlt' : hostRadius l.val 0 < vRadius l (2 * q.2) := by
    rw [← vRadius_three]
    exact (strictAntiOn_vRadius l) (mem_Ici.mpr (by linarith [hq.1]))
      (mem_Ici.mpr (by norm_num)) (by linarith)
  have : ‖D.point q‖ = ‖hostInv l z‖ := by rw [show D.point q = hostInv l z from he]
  linarith

end GC.Seifert.SplitTube
