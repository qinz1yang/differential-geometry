/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundedSurfaceComponent
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def triodHalfPlane (i : Fin 3) : Set E3 :=
  (![{w : E3 | w 1 = 0 ∧ 0 ≤ w 0},
    {w : E3 | w 1 = 0 ∧ w 0 ≤ 0},
    {w : E3 | w 0 = 0 ∧ 0 ≤ w 1}] : Fin 3 → Set E3) i

@[simp] lemma triodHalfPlane_zero :
    triodHalfPlane 0 = {w : E3 | w 1 = 0 ∧ 0 ≤ w 0} := rfl

@[simp] lemma triodHalfPlane_one :
    triodHalfPlane 1 = {w : E3 | w 1 = 0 ∧ w 0 ≤ 0} := rfl

@[simp] lemma triodHalfPlane_two :
    triodHalfPlane 2 = {w : E3 | w 0 = 0 ∧ 0 ≤ w 1} := rfl

lemma convex_setOf_coord_lt (i : Fin 3) (c : ℝ) :
    Convex ℝ {w : E3 | w i < c} := by
  intro x (hx : x i < c) y (hy : y i < c) a b ha hb hab
  change (a • x + b • y) i < c
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hab
    subst hab
    rw [zero_smul, zero_add, one_smul]
    exact hy
  · by_cases hb0 : b = 0
    · subst hb0
      simp only [add_zero] at hab
      subst hab
      rw [zero_smul, add_zero, one_smul]
      exact hx
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have h1 : a * x i < a * c := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * y i < b * c := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : (a • x + b • y) i = a * x i + b * y i := rfl
      rw [h3]
      calc a * x i + b * y i < a * c + b * c := add_lt_add h1 h2
      _ = (a + b) * c := (add_mul a b c).symm
      _ = c := by rw [hab, one_mul]

lemma convex_setOf_coord_gt (i : Fin 3) (c : ℝ) :
    Convex ℝ {w : E3 | c < w i} := by
  intro x (hx : c < x i) y (hy : c < y i) a b ha hb hab
  change c < (a • x + b • y) i
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hab
    subst hab
    rw [zero_smul, zero_add, one_smul]
    exact hy
  · by_cases hb0 : b = 0
    · subst hb0
      simp only [add_zero] at hab
      subst hab
      rw [zero_smul, add_zero, one_smul]
      exact hx
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have h1 : a * c < a * x i := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * c < b * y i := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : (a • x + b • y) i = a * x i + b * y i := rfl
      rw [h3]
      calc c = (a + b) * c := by rw [hab, one_mul]
      _ = a * c + b * c := add_mul a b c
      _ < a * x i + b * y i := add_lt_add h1 h2

lemma isConnected_ball_inter_halfspace_lt (i : Fin 3) (c : ℝ) {r : ℝ}
    (w : E3) (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw_coord : w i < c) :
    IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | w i < c}) := by
  have hconv : Convex ℝ (Metric.ball (0 : E3) r ∩ {w : E3 | w i < c}) :=
    (convex_ball (0 : E3) r).inter (convex_setOf_coord_lt i c)
  exact ⟨⟨w, hw_ball, hw_coord⟩, hconv.isPreconnected⟩

lemma isConnected_ball_inter_halfspace_gt (i : Fin 3) (c : ℝ) {r : ℝ}
    (w : E3) (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw_coord : c < w i) :
    IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | c < w i}) := by
  have hconv : Convex ℝ (Metric.ball (0 : E3) r ∩ {w : E3 | c < w i}) :=
    (convex_ball (0 : E3) r).inter (convex_setOf_coord_gt i c)
  exact ⟨⟨w, hw_ball, hw_coord⟩, hconv.isPreconnected⟩

lemma norm_vec_zero (a : ℝ) (ha : 0 ≤ a) : ‖(!₂[a, 0, 0] : E3)‖ = a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 3, ‖(!₂[a, 0, 0] : E3) i‖ ^ 2) = a ^ 2 := by
    rw [Fin.sum_univ_three]
    simp
  rw [hsum, Real.sqrt_sq ha]

lemma norm_vec_one (a : ℝ) (ha : 0 ≤ a) : ‖(!₂[0, a, 0] : E3)‖ = a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 3, ‖(!₂[0, a, 0] : E3) i‖ ^ 2) = a ^ 2 := by
    rw [Fin.sum_univ_three]
    simp
  rw [hsum, Real.sqrt_sq ha]

lemma norm_vec_neg_zero (a : ℝ) (ha : 0 ≤ a) : ‖(!₂[-a, 0, 0] : E3)‖ = a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 3, ‖(!₂[-a, 0, 0] : E3) i‖ ^ 2) = a ^ 2 := by
    rw [Fin.sum_univ_three]
    simp
  rw [hsum, Real.sqrt_sq ha]

lemma norm_vec_neg_one (a : ℝ) (ha : 0 ≤ a) : ‖(!₂[0, -a, 0] : E3)‖ = a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 3, ‖(!₂[0, -a, 0] : E3) i‖ ^ 2) = a ^ 2 := by
    rw [Fin.sum_univ_three]
    simp
  rw [hsum, Real.sqrt_sq ha]

lemma mem_closure_symm_of_mem_closure {e : OpenPartialHomeomorph E3 E3}
    {s : Set E3} {w : E3} (hw : w ∈ closure s) (hw_target : w ∈ e.target) :
    e.symm w ∈ closure (e.symm '' s) := by
  have hcont : ContinuousAt e.symm w :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hw_target)
  exact mem_closure_image hcont hw

lemma mem_closure_ball_inter_coord_lt_one {r : ℝ} (w : E3)
    (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw1 : w 1 = 0) :
    w ∈ closure (Metric.ball (0 : E3) r ∩ {y : E3 | y 1 < 0}) := by
  rw [_root_.mem_closure_iff]
  intro t ht hwt
  have htopen : IsOpen (Metric.ball (0 : E3) r ∩ t) := isOpen_ball.inter ht
  have hwt_in : w ∈ Metric.ball (0 : E3) r ∩ t := ⟨hw_ball, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp htopen w hwt_in
  let y : E3 := w - (ε / 2) • !₂[0, 1, 0]
  have hdist : dist y w < ε := by
    rw [dist_eq_norm]
    have : y - w = (- (ε / 2)) • !₂[0, 1, 0] := by
      simp [y]
    rw [this, norm_smul, norm_vec_one 1 (by norm_num), mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  have hy_in_t : y ∈ Metric.ball (0 : E3) r ∩ t := hεsub (Metric.mem_ball.mpr hdist)
  have hy1 : y 1 < 0 := by
    have : y 1 = w 1 - ε / 2 := by simp [y]
    rw [this, hw1, zero_sub]
    linarith
  exact ⟨y, hy_in_t.2, hy_in_t.1, hy1⟩

lemma mem_closure_ball_inter_quadrant_first_y {r : ℝ} (w : E3)
    (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw0 : 0 < w 0) (hw1 : w 1 = 0) :
    w ∈ closure (Metric.ball (0 : E3) r ∩ {y : E3 | 0 < y 0 ∧ 0 < y 1}) := by
  rw [_root_.mem_closure_iff]
  intro t ht hwt
  have htopen : IsOpen (Metric.ball (0 : E3) r ∩ t) := isOpen_ball.inter ht
  have hwt_in : w ∈ Metric.ball (0 : E3) r ∩ t := ⟨hw_ball, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp htopen w hwt_in
  let y : E3 := w + (ε / 2) • !₂[0, 1, 0]
  have hdist : dist y w < ε := by
    rw [dist_eq_norm]
    have : y - w = (ε / 2) • !₂[0, 1, 0] := by simp [y]
    rw [this, norm_smul, norm_vec_one 1 (by norm_num), mul_one,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hy_in_t : y ∈ Metric.ball (0 : E3) r ∩ t := hεsub (Metric.mem_ball.mpr hdist)
  have hy0 : 0 < y 0 := by
    have : y 0 = w 0 := by simp [y]
    rw [this]
    exact hw0
  have hy1 : 0 < y 1 := by
    have : y 1 = w 1 + ε / 2 := by simp [y]
    rw [this, hw1, zero_add]
    linarith
  exact ⟨y, hy_in_t.2, hy_in_t.1, hy0, hy1⟩

lemma mem_closure_ball_inter_quadrant_first_x {r : ℝ} (w : E3)
    (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw0 : w 0 = 0) (hw1 : 0 < w 1) :
    w ∈ closure (Metric.ball (0 : E3) r ∩ {y : E3 | 0 < y 0 ∧ 0 < y 1}) := by
  rw [_root_.mem_closure_iff]
  intro t ht hwt
  have htopen : IsOpen (Metric.ball (0 : E3) r ∩ t) := isOpen_ball.inter ht
  have hwt_in : w ∈ Metric.ball (0 : E3) r ∩ t := ⟨hw_ball, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp htopen w hwt_in
  let y : E3 := w + (ε / 2) • !₂[1, 0, 0]
  have hdist : dist y w < ε := by
    rw [dist_eq_norm]
    have : y - w = (ε / 2) • !₂[1, 0, 0] := by simp [y]
    rw [this, norm_smul, norm_vec_zero 1 (by norm_num), mul_one,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hy_in_t : y ∈ Metric.ball (0 : E3) r ∩ t := hεsub (Metric.mem_ball.mpr hdist)
  have hy0 : 0 < y 0 := by
    have : y 0 = w 0 + ε / 2 := by simp [y]
    rw [this, hw0, zero_add]
    linarith
  have hy1 : 0 < y 1 := by
    have : y 1 = w 1 := by simp [y]
    rw [this]
    exact hw1
  exact ⟨y, hy_in_t.2, hy_in_t.1, hy0, hy1⟩

lemma mem_closure_ball_inter_quadrant_second_y {r : ℝ} (w : E3)
    (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw0 : w 0 < 0) (hw1 : w 1 = 0) :
    w ∈ closure (Metric.ball (0 : E3) r ∩ {y : E3 | y 0 < 0 ∧ 0 < y 1}) := by
  rw [_root_.mem_closure_iff]
  intro t ht hwt
  have htopen : IsOpen (Metric.ball (0 : E3) r ∩ t) := isOpen_ball.inter ht
  have hwt_in : w ∈ Metric.ball (0 : E3) r ∩ t := ⟨hw_ball, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp htopen w hwt_in
  let y : E3 := w + (ε / 2) • !₂[0, 1, 0]
  have hdist : dist y w < ε := by
    rw [dist_eq_norm]
    have : y - w = (ε / 2) • !₂[0, 1, 0] := by simp [y]
    rw [this, norm_smul, norm_vec_one 1 (by norm_num), mul_one,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hy_in_t : y ∈ Metric.ball (0 : E3) r ∩ t := hεsub (Metric.mem_ball.mpr hdist)
  have hy0 : y 0 < 0 := by
    have : y 0 = w 0 := by simp [y]
    rw [this]
    exact hw0
  have hy1 : 0 < y 1 := by
    have : y 1 = w 1 + ε / 2 := by simp [y]
    rw [this, hw1, zero_add]
    linarith
  exact ⟨y, hy_in_t.2, hy_in_t.1, hy0, hy1⟩

lemma mem_closure_ball_inter_quadrant_second_x {r : ℝ} (w : E3)
    (hw_ball : w ∈ Metric.ball (0 : E3) r) (hw0 : w 0 = 0) (hw1 : 0 < w 1) :
    w ∈ closure (Metric.ball (0 : E3) r ∩ {y : E3 | y 0 < 0 ∧ 0 < y 1}) := by
  rw [_root_.mem_closure_iff]
  intro t ht hwt
  have htopen : IsOpen (Metric.ball (0 : E3) r ∩ t) := isOpen_ball.inter ht
  have hwt_in : w ∈ Metric.ball (0 : E3) r ∩ t := ⟨hw_ball, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp htopen w hwt_in
  let y : E3 := w - (ε / 2) • !₂[1, 0, 0]
  have hdist : dist y w < ε := by
    rw [dist_eq_norm]
    have : y - w = (- (ε / 2)) • !₂[1, 0, 0] := by simp [y]
    rw [this, norm_smul, norm_vec_zero 1 (by norm_num), mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  have hy_in_t : y ∈ Metric.ball (0 : E3) r ∩ t := hεsub (Metric.mem_ball.mpr hdist)
  have hy0 : y 0 < 0 := by
    have : y 0 = w 0 - ε / 2 := by simp [y]
    rw [this, hw0, zero_sub]
    linarith
  have hy1 : 0 < y 1 := by
    have : y 1 = w 1 := by simp [y]
    rw [this]
    exact hw1
  exact ⟨y, hy_in_t.2, hy_in_t.1, hy0, hy1⟩

lemma exists_frontier_pair_witnesses_of_sector
    (S : Fin 3 → Set E3) (B : Set E3)
    (hinter : ∀ i j, i ≠ j → S i ∩ S j = B)
    (hpair : ∀ i j, i ≠ j → ∃ K : Geometry.SimplicialComplex ℝ E3,
      K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
        K.space = S i ∪ S j)
    (e : OpenPartialHomeomorph E3 E3) {p x : E3}
    (hp : p ∈ B) (hpsource : p ∈ e.source) (hep : e p = 0)
    (htrace : ∀ i, ∀ z ∈ e.source, z ∈ S i ↔ e z ∈ triodHalfPlane i)
    {r : ℝ} (hr : 0 < r) (hrsub : Metric.ball (0 : E3) r ⊆ e.target)
    (hx : x ∉ ⋃ i, S i)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (_hjk : j ≠ k)
    (Sec Out : Set E3)
    (hSecConn : IsConnected Sec)
    (hOutConn : IsConnected Out)
    (hSecSub : Sec ⊆ (triodHalfPlane 0 ∪ triodHalfPlane 1 ∪ triodHalfPlane 2)ᶜ)
    (hSecBall : Sec ⊆ Metric.ball (0 : E3) r)
    (hOutBall : Out ⊆ Metric.ball (0 : E3) r)
    (hPart : (triodHalfPlane i ∪ triodHalfPlane j)ᶜ ∩ Metric.ball (0 : E3) r = Sec ∪ Out)
    {w_u w_v w_w : E3}
    (hu_clos : w_u ∈ closure Sec)
    (hu_ball : w_u ∈ Metric.ball (0 : E3) r)
    (hu_i : w_u ∈ triodHalfPlane i)
    (hu_not_j : w_u ∉ triodHalfPlane j)
    (hv_clos : w_v ∈ closure Sec)
    (hv_ball : w_v ∈ Metric.ball (0 : E3) r)
    (hv_j : w_v ∈ triodHalfPlane j)
    (hv_not_i : w_v ∉ triodHalfPlane i)
    (hw_out : w_w ∈ Out)
    (hw_k : w_w ∈ triodHalfPlane k)
    (hw_not_ij : w_w ∉ triodHalfPlane i ∪ triodHalfPlane j)
    (hSecMeet : (e '' (connectedComponentIn (⋃ l, S l)ᶜ x ∩ e.source) ∩ Sec).Nonempty) :
    (∃ u ∈ S i \ B, u ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
    (∃ v ∈ S j \ B, v ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
    ∃ w ∈ S k \ B, w ∉ connectedComponentIn (S i ∪ S j)ᶜ x := by
  let U := connectedComponentIn (⋃ l, S l)ᶜ x
  have hSec_sub_target : Sec ⊆ e.target := hSecBall.trans hrsub
  have hSec_compl : e.symm '' Sec ⊆ (⋃ l, S l)ᶜ := by
    rintro z ⟨w, hwSec, rfl⟩
    rw [mem_compl_iff, mem_iUnion]
    rintro ⟨l, hl⟩
    have hw_source : e.symm w ∈ e.source := e.map_target (hSec_sub_target hwSec)
    have htrace_l := (htrace l (e.symm w) hw_source).mp hl
    rw [e.right_inv (hSec_sub_target hwSec)] at htrace_l
    have hnot := hSecSub hwSec
    rw [mem_compl_iff, mem_union, mem_union] at hnot
    fin_cases l
    · exact hnot (Or.inl (Or.inl htrace_l))
    · exact hnot (Or.inl (Or.inr htrace_l))
    · exact hnot (Or.inr htrace_l)
  have hSec_conn_image : IsConnected (e.symm '' Sec) :=
    ⟨hSecConn.nonempty.image _,
      hSecConn.isPreconnected.image _ (e.continuousOn_symm.mono hSec_sub_target)⟩
  obtain ⟨w_meet, ⟨⟨z_meet, ⟨hzU, hzs⟩, rfl⟩, hwSec_meet⟩⟩ := hSecMeet
  have hzSec : z_meet ∈ e.symm '' Sec := ⟨e z_meet, hwSec_meet, e.left_inv hzs⟩
  have hSecU : e.symm '' Sec ⊆ U := by
    have heq : U = connectedComponentIn (⋃ l, S l)ᶜ z_meet := connectedComponentIn_eq hzU
    rw [heq]
    exact hSec_conn_image.isPreconnected.subset_connectedComponentIn hzSec hSec_compl
  have hu_target : w_u ∈ e.target := hrsub hu_ball
  let u := e.symm w_u
  have hu_source : u ∈ e.source := e.map_target hu_target
  have heu : e u = w_u := e.right_inv hu_target
  have hu_Si : u ∈ S i := (htrace i u hu_source).mpr (heu.symm ▸ hu_i)
  have hu_not_B : u ∉ B := by
    intro huB
    have hu_Sj : u ∈ S j := by
      have : u ∈ S i ∩ S j := (hinter i j hij).symm ▸ huB
      exact this.2
    have hw_j : w_u ∈ triodHalfPlane j := by
      rw [← heu]
      exact (htrace j u hu_source).mp hu_Sj
    exact hu_not_j hw_j
  have hu_in_clos : u ∈ closure U := by
    have h1 : u ∈ closure (e.symm '' Sec) :=
      mem_closure_symm_of_mem_closure hu_clos hu_target
    exact closure_mono hSecU h1
  have hu_not_U : u ∉ U := by
    intro huU
    have : u ∈ (⋃ l, S l)ᶜ := connectedComponentIn_subset _ _ huU
    exact this (mem_iUnion.mpr ⟨i, hu_Si⟩)
  have hu_front : u ∈ frontier U := ⟨hu_in_clos, fun h => hu_not_U (interior_subset h)⟩
  have hv_target : w_v ∈ e.target := hrsub hv_ball
  let v := e.symm w_v
  have hv_source : v ∈ e.source := e.map_target hv_target
  have hev : e v = w_v := e.right_inv hv_target
  have hv_Sj : v ∈ S j := (htrace j v hv_source).mpr (hev.symm ▸ hv_j)
  have hv_not_B : v ∉ B := by
    intro hvB
    have hv_Si : v ∈ S i := by
      have : v ∈ S i ∩ S j := (hinter i j hij).symm ▸ hvB
      exact this.1
    have hw_i : w_v ∈ triodHalfPlane i := by
      rw [← hev]
      exact (htrace i v hv_source).mp hv_Si
    exact hv_not_i hw_i
  have hv_in_clos : v ∈ closure U := by
    have h1 : v ∈ closure (e.symm '' Sec) :=
      mem_closure_symm_of_mem_closure hv_clos hv_target
    exact closure_mono hSecU h1
  have hv_not_U : v ∉ U := by
    intro hvU
    have : v ∈ (⋃ l, S l)ᶜ := connectedComponentIn_subset _ _ hvU
    exact this (mem_iUnion.mpr ⟨j, hv_Sj⟩)
  have hv_front : v ∈ frontier U := ⟨hv_in_clos, fun h => hv_not_U (interior_subset h)⟩
  refine ⟨⟨u, ⟨hu_Si, hu_not_B⟩, hu_front⟩, ⟨v, ⟨hv_Sj, hv_not_B⟩, hv_front⟩, ?_⟩
  have hw_target : w_w ∈ e.target := hrsub (hOutBall hw_out)
  let w := e.symm w_w
  have hw_source : w ∈ e.source := e.map_target hw_target
  have hew : e w = w_w := e.right_inv hw_target
  have hw_Sk : w ∈ S k := (htrace k w hw_source).mpr (hew.symm ▸ hw_k)
  have hw_not_B : w ∉ B := by
    intro hwB
    have hw_Si : w ∈ S i := by
      have : w ∈ S k ∩ S i := (hinter k i hik.symm).symm ▸ hwB
      exact this.2
    have : w_w ∈ triodHalfPlane i := by
      rw [← hew]
      exact (htrace i w hw_source).mp hw_Si
    exact hw_not_ij (Or.inl this)
  refine ⟨w, ⟨hw_Sk, hw_not_B⟩, ?_⟩
  obtain ⟨K, hKfin, hK, hKconn, hKspace⟩ := hpair i j hij
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨a, ha, b, hb, -, hdis, hcover, -, hfrontA, hfrontB⟩ :=
    hK.exists_bounded_connectedComponentIn_pair_compl K (by simp) hKconn
  let A := connectedComponentIn K.spaceᶜ a
  let B' := connectedComponentIn K.spaceᶜ b
  have hKcomp : K.spaceᶜ = (S i ∪ S j)ᶜ := by rw [hKspace]
  have hx_compl : x ∈ K.spaceᶜ := by
    rw [hKspace]
    intro h
    rcases h with hi | hj
    · exact hx (mem_iUnion.mpr ⟨i, hi⟩)
    · exact hx (mem_iUnion.mpr ⟨j, hj⟩)
  have hx_cases : x ∈ A ∨ x ∈ B' := hcover.symm.subset hx_compl
  have hOut_sub_target : Out ⊆ e.target := hOutBall.trans hrsub
  have hOut_compl_plane : Out ⊆ (triodHalfPlane i ∪ triodHalfPlane j)ᶜ := by
    intro w' hw'
    have : w' ∈ Sec ∪ Out := Or.inr hw'
    rw [← hPart] at this
    exact this.1
  have hOut_compl : e.symm '' Out ⊆ K.spaceᶜ := by
    rw [hKspace]
    rintro z ⟨w', hw'Out, rfl⟩ (hzi | hzj)
    · have hw'_target : w' ∈ e.target := hOut_sub_target hw'Out
      have hw'_i : w' ∈ triodHalfPlane i := by
        rw [← e.right_inv hw'_target]
        exact (htrace i (e.symm w') (e.map_target hw'_target)).mp hzi
      exact (hOut_compl_plane hw'Out) (Or.inl hw'_i)
    · have hw'_target : w' ∈ e.target := hOut_sub_target hw'Out
      have hw'_j : w' ∈ triodHalfPlane j := by
        rw [← e.right_inv hw'_target]
        exact (htrace j (e.symm w') (e.map_target hw'_target)).mp hzj
      exact (hOut_compl_plane hw'Out) (Or.inr hw'_j)
  have hOut_conn_image : IsConnected (e.symm '' Out) :=
    ⟨hOutConn.nonempty.image _,
      hOutConn.isPreconnected.image _ (e.continuousOn_symm.mono hOut_sub_target)⟩
  have hV_open : IsOpen (e.source ∩ e ⁻¹' (Metric.ball (0 : E3) r)) :=
    e.isOpen_inter_preimage isOpen_ball
  have hp_in_V : p ∈ e.source ∩ e ⁻¹' (Metric.ball (0 : E3) r) := by
    refine ⟨hpsource, ?_⟩
    simp only [mem_preimage, hep, mem_ball_self hr]
  rcases hx_cases with hxA | hxB
  · have hX_eq : connectedComponentIn (S i ∪ S j)ᶜ x = A := by
      rw [← hKcomp]
      exact (connectedComponentIn_eq hxA).symm
    have hUA : U ⊆ A := by
      have hsub : (⋃ l, S l)ᶜ ⊆ (S i ∪ S j)ᶜ := by
        rintro y hy (hyi | hyj)
        · exact hy (mem_iUnion.mpr ⟨i, hyi⟩)
        · exact hy (mem_iUnion.mpr ⟨j, hyj⟩)
      exact hX_eq ▸ connectedComponentIn_mono x hsub
    have hSecA : e.symm '' Sec ⊆ A := hSecU.trans hUA
    have hSec_disj_B' : Disjoint (e.symm '' Sec) B' := Disjoint.mono_left hSecA hdis
    have hp_frontB : p ∈ frontier B' := by
      rw [hfrontB, hKspace]
      have : p ∈ S i ∩ S j := hinter i j hij ▸ hp
      exact Or.inl this.1
    have hp_closB : p ∈ closure B' := frontier_subset_closure hp_frontB
    obtain ⟨y, hy_B', hy_source, hy_ball⟩ :=
      (closure_inter_open_nonempty_iff hV_open).mp ⟨p, hp_closB, hp_in_V⟩
    have hy_K : y ∈ K.spaceᶜ := connectedComponentIn_subset _ _ hy_B'
    rw [hKspace] at hy_K
    have hey_not_i : e y ∉ triodHalfPlane i :=
      fun h => hy_K (Or.inl ((htrace i y hy_source).mpr h))
    have hey_not_j : e y ∉ triodHalfPlane j :=
      fun h => hy_K (Or.inr ((htrace j y hy_source).mpr h))
    have hey_part : e y ∈ (triodHalfPlane i ∪ triodHalfPlane j)ᶜ ∩ Metric.ball (0 : E3) r :=
      ⟨fun h => h.elim hey_not_i hey_not_j, hy_ball⟩
    rw [hPart] at hey_part
    have hey_Out : e y ∈ Out := by
      rcases hey_part with hey_Sec | hey_Out
      · have hy_Sec : y ∈ e.symm '' Sec := ⟨e y, hey_Sec, e.left_inv hy_source⟩
        exact (disjoint_left.mp hSec_disj_B' hy_Sec hy_B').elim
      · exact hey_Out
    have hy_in_Out : y ∈ e.symm '' Out := ⟨e y, hey_Out, e.left_inv hy_source⟩
    have hOut_sub_B' : e.symm '' Out ⊆ B' := by
      have heq : B' = connectedComponentIn K.spaceᶜ y := connectedComponentIn_eq hy_B'
      rw [heq]
      exact hOut_conn_image.isPreconnected.subset_connectedComponentIn hy_in_Out hOut_compl
    have hw_in_B' : w ∈ B' := hOut_sub_B' ⟨w_w, hw_out, rfl⟩
    intro hwA
    rw [hX_eq] at hwA
    exact disjoint_left.mp hdis hwA hw_in_B'
  · have hX_eq : connectedComponentIn (S i ∪ S j)ᶜ x = B' := by
      rw [← hKcomp]
      exact (connectedComponentIn_eq hxB).symm
    have hUB : U ⊆ B' := by
      have hsub : (⋃ l, S l)ᶜ ⊆ (S i ∪ S j)ᶜ := by
        rintro y hy (hyi | hyj)
        · exact hy (mem_iUnion.mpr ⟨i, hyi⟩)
        · exact hy (mem_iUnion.mpr ⟨j, hyj⟩)
      exact hX_eq ▸ connectedComponentIn_mono x hsub
    have hSecB : e.symm '' Sec ⊆ B' := hSecU.trans hUB
    have hSec_disj_A : Disjoint (e.symm '' Sec) A :=
      Disjoint.mono_left hSecB (Disjoint.symm hdis)
    have hp_frontA : p ∈ frontier A := by
      rw [hfrontA, hKspace]
      have : p ∈ S i ∩ S j := hinter i j hij ▸ hp
      exact Or.inl this.1
    have hp_closA : p ∈ closure A := frontier_subset_closure hp_frontA
    obtain ⟨y, hy_A, hy_source, hy_ball⟩ :=
      (closure_inter_open_nonempty_iff hV_open).mp ⟨p, hp_closA, hp_in_V⟩
    have hy_K : y ∈ K.spaceᶜ := connectedComponentIn_subset _ _ hy_A
    rw [hKspace] at hy_K
    have hey_not_i : e y ∉ triodHalfPlane i :=
      fun h => hy_K (Or.inl ((htrace i y hy_source).mpr h))
    have hey_not_j : e y ∉ triodHalfPlane j :=
      fun h => hy_K (Or.inr ((htrace j y hy_source).mpr h))
    have hey_part : e y ∈ (triodHalfPlane i ∪ triodHalfPlane j)ᶜ ∩ Metric.ball (0 : E3) r :=
      ⟨fun h => h.elim hey_not_i hey_not_j, hy_ball⟩
    rw [hPart] at hey_part
    have hey_Out : e y ∈ Out := by
      rcases hey_part with hey_Sec | hey_Out
      · have hy_Sec : y ∈ e.symm '' Sec := ⟨e y, hey_Sec, e.left_inv hy_source⟩
        exact (disjoint_left.mp hSec_disj_A hy_Sec hy_A).elim
      · exact hey_Out
    have hy_in_Out : y ∈ e.symm '' Out := ⟨e y, hey_Out, e.left_inv hy_source⟩
    have hOut_sub_A : e.symm '' Out ⊆ A := by
      have heq : A = connectedComponentIn K.spaceᶜ y := connectedComponentIn_eq hy_A
      rw [heq]
      exact hOut_conn_image.isPreconnected.subset_connectedComponentIn hy_in_Out hOut_compl
    have hw_in_A : w ∈ A := hOut_sub_A ⟨w_w, hw_out, rfl⟩
    intro hwB'
    rw [hX_eq] at hwB'
    exact disjoint_left.mp hdis hw_in_A hwB'

lemma exists_frontier_pair_witnesses_of_sector_C
    (S : Fin 3 → Set E3) (B : Set E3)
    (hinter : ∀ i j, i ≠ j → S i ∩ S j = B)
    (hpair : ∀ i j, i ≠ j → ∃ K : Geometry.SimplicialComplex ℝ E3,
      K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
        K.space = S i ∪ S j)
    (e : OpenPartialHomeomorph E3 E3) {p x : E3}
    (hp : p ∈ B) (hpsource : p ∈ e.source) (hep : e p = 0)
    (htrace : ∀ i, ∀ z ∈ e.source, z ∈ S i ↔ e z ∈ triodHalfPlane i)
    {r : ℝ} (hr : 0 < r) (hrsub : Metric.ball (0 : E3) r ⊆ e.target)
    (hx : x ∉ ⋃ i, S i)
    {z : E3} (hzU : z ∈ connectedComponentIn (⋃ l, S l)ᶜ x)
    (hzs : z ∈ e.source) (hzball : e z ∈ Metric.ball (0 : E3) r)
    (hz_neg : e z 1 < 0) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∃ u ∈ S i \ B, u ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      (∃ v ∈ S j \ B, v ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      ∃ w ∈ S k \ B, w ∉ connectedComponentIn (S i ∪ S j)ᶜ x := by
  let Sec : Set E3 := Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0}
  let Out : Set E3 := Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 1}
  have hSecConn : IsConnected Sec :=
    isConnected_ball_inter_halfspace_lt 1 0 (!₂[0, - (r / 2), 0])
      (Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_neg_one (r / 2) (by linarith)]; linarith))
      (by simp; linarith)
  have hOutConn : IsConnected Out :=
    isConnected_ball_inter_halfspace_gt 1 0 (!₂[0, r / 2, 0])
      (Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_one (r / 2) (by linarith)]; linarith))
      (by simp; linarith)
  have hSecSub : Sec ⊆ (triodHalfPlane 0 ∪ triodHalfPlane 1 ∪ triodHalfPlane 2)ᶜ := by
    rintro w ⟨-, (hw1 : w 1 < 0)⟩
    simp only [mem_compl_iff, mem_union, triodHalfPlane_zero, triodHalfPlane_one,
      triodHalfPlane_two]
    rintro ((⟨h0, -⟩ | ⟨h1, -⟩) | ⟨-, h2⟩)
    · linarith
    · linarith
    · linarith
  have hSecBall : Sec ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hOutBall : Out ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hPart : (triodHalfPlane 0 ∪ triodHalfPlane 1)ᶜ ∩ Metric.ball (0 : E3) r = Sec ∪ Out := by
    ext w
    simp only [mem_inter_iff, mem_union, mem_compl_iff, triodHalfPlane_zero, triodHalfPlane_one,
      Sec, Out]
    constructor
    · rintro ⟨hnot, hball⟩
      have h1ne : w 1 ≠ 0 := by
        intro hw10
        rcases le_total 0 (w 0) with h0 | h0
        · exact hnot (Or.inl ⟨hw10, h0⟩)
        · exact hnot (Or.inr ⟨hw10, h0⟩)
      rcases lt_or_gt_of_ne h1ne with hlt | hgt
      · exact Or.inl ⟨hball, hlt⟩
      · exact Or.inr ⟨hball, hgt⟩
    · rintro (⟨hball, hw1⟩ | ⟨hball, hw1⟩)
      · dsimp at hw1
        refine ⟨?_, hball⟩
        rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
      · dsimp at hw1
        refine ⟨?_, hball⟩
        rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
  let w_u : E3 := !₂[r / 2, 0, 0]
  have hu_ball : w_u ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_zero (r / 2) (by linarith)]; linarith)
  have hu_clos : w_u ∈ closure Sec :=
    mem_closure_ball_inter_coord_lt_one w_u hu_ball (by simp [w_u])
  have hu_i : w_u ∈ triodHalfPlane 0 := ⟨by simp [w_u], by simp [w_u]; linarith⟩
  have hu_not_j : w_u ∉ triodHalfPlane 1 := by
    intro h
    have : w_u 0 ≤ 0 := h.2
    simp [w_u] at this
    linarith
  let w_v : E3 := !₂[- (r / 2), 0, 0]
  have hv_ball : w_v ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_neg_zero (r / 2) (by linarith)]; linarith)
  have hv_clos : w_v ∈ closure Sec :=
    mem_closure_ball_inter_coord_lt_one w_v hv_ball (by simp [w_v])
  have hv_j : w_v ∈ triodHalfPlane 1 := ⟨by simp [w_v], by simp [w_v]; linarith⟩
  have hv_not_i : w_v ∉ triodHalfPlane 0 := by
    intro h
    have : 0 ≤ w_v 0 := h.2
    simp [w_v] at this
    linarith
  let w_w : E3 := !₂[0, r / 2, 0]
  have hw_out : w_w ∈ Out :=
    ⟨Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_one (r / 2) (by linarith)]; linarith),
      by simp [w_w]; linarith⟩
  have hw_k : w_w ∈ triodHalfPlane 2 := ⟨by simp [w_w], by simp [w_w]; linarith⟩
  have hw_not_ij : w_w ∉ triodHalfPlane 0 ∪ triodHalfPlane 1 := by
    rintro (⟨h, -⟩ | ⟨h, -⟩) <;> { simp [w_w] at h; linarith }
  have hSecMeet : (e '' (connectedComponentIn (⋃ l, S l)ᶜ x ∩ e.source) ∩ Sec).Nonempty :=
    ⟨e z, ⟨z, ⟨hzU, hzs⟩, rfl⟩, ⟨hzball, hz_neg⟩⟩
  obtain ⟨hu, hv, hw⟩ :=
    exists_frontier_pair_witnesses_of_sector S B hinter hpair e hp hpsource hep htrace hr hrsub
      hx 0 1 2 (by decide) (by decide) (by decide) Sec Out hSecConn hOutConn hSecSub hSecBall
      hOutBall hPart hu_clos hu_ball hu_i hu_not_j hv_clos hv_ball hv_j hv_not_i hw_out hw_k
      hw_not_ij hSecMeet
  exact ⟨0, 1, 2, by decide, by decide, by decide, hu, hv, hw⟩

lemma exists_frontier_pair_witnesses_of_sector_A
    (S : Fin 3 → Set E3) (B : Set E3)
    (hinter : ∀ i j, i ≠ j → S i ∩ S j = B)
    (hpair : ∀ i j, i ≠ j → ∃ K : Geometry.SimplicialComplex ℝ E3,
      K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
        K.space = S i ∪ S j)
    (e : OpenPartialHomeomorph E3 E3) {p x : E3}
    (hp : p ∈ B) (hpsource : p ∈ e.source) (hep : e p = 0)
    (htrace : ∀ i, ∀ z ∈ e.source, z ∈ S i ↔ e z ∈ triodHalfPlane i)
    {r : ℝ} (hr : 0 < r) (hrsub : Metric.ball (0 : E3) r ⊆ e.target)
    (hx : x ∉ ⋃ i, S i)
    {z : E3} (hzU : z ∈ connectedComponentIn (⋃ l, S l)ᶜ x)
    (hzs : z ∈ e.source) (hzball : e z ∈ Metric.ball (0 : E3) r)
    (hz_pos1 : 0 < e z 1) (hz_pos0 : 0 < e z 0) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∃ u ∈ S i \ B, u ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      (∃ v ∈ S j \ B, v ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      ∃ w ∈ S k \ B, w ∉ connectedComponentIn (S i ∪ S j)ᶜ x := by
  let Sec : Set E3 := Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 0 ∧ 0 < w 1}
  let Out : Set E3 := Metric.ball (0 : E3) r ∩ ({w : E3 | w 0 < 0} ∪ {w : E3 | w 1 < 0})
  have hSecConn : IsConnected Sec := by
    have hconv : Convex ℝ Sec := by
      have h1 : Convex ℝ {w : E3 | 0 < w 0 ∧ 0 < w 1} :=
        (convex_setOf_coord_gt 0 0).inter (convex_setOf_coord_gt 1 0)
      exact (convex_ball (0 : E3) r).inter h1
    exact ⟨⟨e z, hzball, hz_pos0, hz_pos1⟩, hconv.isPreconnected⟩
  have hOutConn : IsConnected Out := by
    have hO1 : IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | w 0 < 0}) :=
      isConnected_ball_inter_halfspace_lt 0 0 (!₂[- (r / 2), 0, 0])
        (Metric.mem_ball.mpr
          (by rw [dist_zero_right, norm_vec_neg_zero (r / 2) (by linarith)]; linarith))
        (by simp; linarith)
    have hO2 : IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0}) :=
      isConnected_ball_inter_halfspace_lt 1 0 (!₂[0, - (r / 2), 0])
        (Metric.mem_ball.mpr
          (by rw [dist_zero_right, norm_vec_neg_one (r / 2) (by linarith)]; linarith))
        (by simp; linarith)
    have hm1 : (!₂[- (r / 2), 0, 0] : E3) ∈ Metric.ball 0 r :=
      Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_neg_zero (r / 2) (by linarith)]; linarith)
    have hm2 : (!₂[0, - (r / 2), 0] : E3) ∈ Metric.ball 0 r :=
      Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_neg_one (r / 2) (by linarith)]; linarith)
    let m : E3 := (1/2 : ℝ) • !₂[- (r / 2), 0, 0] + (1/2 : ℝ) • !₂[0, - (r / 2), 0]
    have hm_ball : m ∈ Metric.ball (0 : E3) r :=
      convex_ball (0 : E3) r hm1 hm2 (by linarith) (by linarith) (by norm_num)
    have hm0 : m 0 < 0 := by
      have : m 0 = - (r / 4) := by simp [m]; ring
      rw [this]; linarith
    have hm1' : m 1 < 0 := by
      have : m 1 = - (r / 4) := by simp [m]; ring
      rw [this]; linarith
    have hmeet : ((Metric.ball (0 : E3) r ∩ {w : E3 | w 0 < 0}) ∩
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0})).Nonempty :=
      ⟨m, ⟨hm_ball, hm0⟩, ⟨hm_ball, hm1'⟩⟩
    have hunion : IsConnected ((Metric.ball (0 : E3) r ∩ {w : E3 | w 0 < 0}) ∪
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0})) :=
      IsConnected.union hmeet hO1 hO2
    have heq : Out = (Metric.ball (0 : E3) r ∩ {w : E3 | w 0 < 0}) ∪
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0}) :=
      inter_union_distrib_left (Metric.ball (0 : E3) r) {w : E3 | w 0 < 0} {w : E3 | w 1 < 0}
    exact heq ▸ hunion
  have hSecSub : Sec ⊆ (triodHalfPlane 0 ∪ triodHalfPlane 1 ∪ triodHalfPlane 2)ᶜ := by
    rintro w ⟨-, (hw0 : 0 < w 0), (hw1 : 0 < w 1)⟩
    simp only [mem_compl_iff, mem_union, triodHalfPlane_zero, triodHalfPlane_one,
      triodHalfPlane_two]
    rintro ((⟨h0, -⟩ | ⟨h1, -⟩) | ⟨h2, -⟩)
    · linarith
    · linarith
    · linarith
  have hSecBall : Sec ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hOutBall : Out ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hPart : (triodHalfPlane 0 ∪ triodHalfPlane 2)ᶜ ∩ Metric.ball (0 : E3) r = Sec ∪ Out := by
    ext w
    simp only [mem_inter_iff, mem_union, mem_compl_iff, triodHalfPlane_zero, triodHalfPlane_two,
      Sec, Out]
    constructor
    · rintro ⟨hnot, hball⟩
      by_cases h0 : 0 < w 0
      · by_cases h1 : 0 < w 1
        · exact Or.inl ⟨hball, h0, h1⟩
        · have h1le : w 1 ≤ 0 := le_of_not_gt h1
          rcases lt_or_eq_of_le h1le with hlt | heq
          · exact Or.inr ⟨hball, Or.inr hlt⟩
          · exfalso; exact hnot (Or.inl ⟨heq, le_of_lt h0⟩)
      · have h0le : w 0 ≤ 0 := le_of_not_gt h0
        rcases lt_or_eq_of_le h0le with hlt | heq
        · exact Or.inr ⟨hball, Or.inl hlt⟩
        · have hw1 : w 1 < 0 := by
            by_contra! hge
            exact hnot (Or.inr ⟨heq, hge⟩)
          exact Or.inr ⟨hball, Or.inr hw1⟩
    · rintro (⟨hball, hw0, hw1⟩ | ⟨hball, hw0 | hw1⟩)
      · refine ⟨?_, hball⟩
        rintro (⟨h0, -⟩ | ⟨h2, -⟩) <;> linarith
      · dsimp at hw0
        refine ⟨?_, hball⟩
        rintro (⟨-, h0⟩ | ⟨h2, -⟩) <;> linarith
      · dsimp at hw1
        refine ⟨?_, hball⟩
        rintro (⟨h0, -⟩ | ⟨-, h2⟩) <;> linarith
  let w_u : E3 := !₂[r / 2, 0, 0]
  have hu_ball : w_u ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_zero (r / 2) (by linarith)]; linarith)
  have hu_clos : w_u ∈ closure Sec :=
    mem_closure_ball_inter_quadrant_first_y w_u hu_ball (by simp [w_u]; linarith) (by simp [w_u])
  have hu_i : w_u ∈ triodHalfPlane 0 := ⟨by simp [w_u], by simp [w_u]; linarith⟩
  have hu_not_j : w_u ∉ triodHalfPlane 2 := by
    intro h
    have : w_u 0 = 0 := h.1
    simp [w_u] at this
    linarith
  let w_v : E3 := !₂[0, r / 2, 0]
  have hv_ball : w_v ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_one (r / 2) (by linarith)]; linarith)
  have hv_clos : w_v ∈ closure Sec :=
    mem_closure_ball_inter_quadrant_first_x w_v hv_ball (by simp [w_v]) (by simp [w_v]; linarith)
  have hv_j : w_v ∈ triodHalfPlane 2 := ⟨by simp [w_v], by simp [w_v]; linarith⟩
  have hv_not_i : w_v ∉ triodHalfPlane 0 := by
    intro h
    have : w_v 1 = 0 := h.1
    simp [w_v] at this
    linarith
  let w_w : E3 := !₂[- (r / 2), 0, 0]
  have hw_out : w_w ∈ Out :=
    ⟨Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_neg_zero (r / 2) (by linarith)]; linarith),
      Or.inl (by simp [w_w]; linarith)⟩
  have hw_k : w_w ∈ triodHalfPlane 1 := ⟨by simp [w_w], by simp [w_w]; linarith⟩
  have hw_not_ij : w_w ∉ triodHalfPlane 0 ∪ triodHalfPlane 2 := by
    rintro (⟨-, h0⟩ | ⟨h2, -⟩) <;> { simp [w_w] at *; linarith }
  have hSecMeet : (e '' (connectedComponentIn (⋃ l, S l)ᶜ x ∩ e.source) ∩ Sec).Nonempty :=
    ⟨e z, ⟨z, ⟨hzU, hzs⟩, rfl⟩, ⟨hzball, hz_pos0, hz_pos1⟩⟩
  obtain ⟨hu, hv, hw⟩ :=
    exists_frontier_pair_witnesses_of_sector S B hinter hpair e hp hpsource hep htrace hr hrsub
      hx 0 2 1 (by decide) (by decide) (by decide) Sec Out hSecConn hOutConn hSecSub hSecBall
      hOutBall hPart hu_clos hu_ball hu_i hu_not_j hv_clos hv_ball hv_j hv_not_i hw_out hw_k
      hw_not_ij hSecMeet
  exact ⟨0, 2, 1, by decide, by decide, by decide, hu, hv, hw⟩

lemma exists_frontier_pair_witnesses_of_sector_B
    (S : Fin 3 → Set E3) (B : Set E3)
    (hinter : ∀ i j, i ≠ j → S i ∩ S j = B)
    (hpair : ∀ i j, i ≠ j → ∃ K : Geometry.SimplicialComplex ℝ E3,
      K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
        K.space = S i ∪ S j)
    (e : OpenPartialHomeomorph E3 E3) {p x : E3}
    (hp : p ∈ B) (hpsource : p ∈ e.source) (hep : e p = 0)
    (htrace : ∀ i, ∀ z ∈ e.source, z ∈ S i ↔ e z ∈ triodHalfPlane i)
    {r : ℝ} (hr : 0 < r) (hrsub : Metric.ball (0 : E3) r ⊆ e.target)
    (hx : x ∉ ⋃ i, S i)
    {z : E3} (hzU : z ∈ connectedComponentIn (⋃ l, S l)ᶜ x)
    (hzs : z ∈ e.source) (hzball : e z ∈ Metric.ball (0 : E3) r)
    (hz_pos1 : 0 < e z 1) (hz_neg0 : e z 0 < 0) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∃ u ∈ S i \ B, u ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      (∃ v ∈ S j \ B, v ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      ∃ w ∈ S k \ B, w ∉ connectedComponentIn (S i ∪ S j)ᶜ x := by
  let Sec : Set E3 := Metric.ball (0 : E3) r ∩ {w : E3 | w 0 < 0 ∧ 0 < w 1}
  let Out : Set E3 := Metric.ball (0 : E3) r ∩ ({w : E3 | 0 < w 0} ∪ {w : E3 | w 1 < 0})
  have hSecConn : IsConnected Sec := by
    have hconv : Convex ℝ Sec := by
      have h1 : Convex ℝ {w : E3 | w 0 < 0 ∧ 0 < w 1} :=
        (convex_setOf_coord_lt 0 0).inter (convex_setOf_coord_gt 1 0)
      exact (convex_ball (0 : E3) r).inter h1
    exact ⟨⟨e z, hzball, hz_neg0, hz_pos1⟩, hconv.isPreconnected⟩
  have hOutConn : IsConnected Out := by
    have hO1 : IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 0}) :=
      isConnected_ball_inter_halfspace_gt 0 0 (!₂[r / 2, 0, 0])
        (Metric.mem_ball.mpr
          (by rw [dist_zero_right, norm_vec_zero (r / 2) (by linarith)]; linarith))
        (by simp; linarith)
    have hO2 : IsConnected (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0}) :=
      isConnected_ball_inter_halfspace_lt 1 0 (!₂[0, - (r / 2), 0])
        (Metric.mem_ball.mpr
          (by rw [dist_zero_right, norm_vec_neg_one (r / 2) (by linarith)]; linarith))
        (by simp; linarith)
    have hm1 : (!₂[r / 2, 0, 0] : E3) ∈ Metric.ball 0 r :=
      Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_zero (r / 2) (by linarith)]; linarith)
    have hm2 : (!₂[0, - (r / 2), 0] : E3) ∈ Metric.ball 0 r :=
      Metric.mem_ball.mpr
        (by rw [dist_zero_right, norm_vec_neg_one (r / 2) (by linarith)]; linarith)
    let m : E3 := (1/2 : ℝ) • !₂[r / 2, 0, 0] + (1/2 : ℝ) • !₂[0, - (r / 2), 0]
    have hm_ball : m ∈ Metric.ball (0 : E3) r :=
      convex_ball (0 : E3) r hm1 hm2 (by linarith) (by linarith) (by norm_num)
    have hm0 : 0 < m 0 := by
      have : m 0 = r / 4 := by simp [m]; ring
      rw [this]; linarith
    have hm1' : m 1 < 0 := by
      have : m 1 = - (r / 4) := by simp [m]; ring
      rw [this]; linarith
    have hmeet : ((Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 0}) ∩
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0})).Nonempty :=
      ⟨m, ⟨hm_ball, hm0⟩, ⟨hm_ball, hm1'⟩⟩
    have hunion : IsConnected ((Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 0}) ∪
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0})) :=
      IsConnected.union hmeet hO1 hO2
    have heq : Out = (Metric.ball (0 : E3) r ∩ {w : E3 | 0 < w 0}) ∪
        (Metric.ball (0 : E3) r ∩ {w : E3 | w 1 < 0}) :=
      inter_union_distrib_left (Metric.ball (0 : E3) r) {w : E3 | 0 < w 0} {w : E3 | w 1 < 0}
    exact heq ▸ hunion
  have hSecSub : Sec ⊆ (triodHalfPlane 0 ∪ triodHalfPlane 1 ∪ triodHalfPlane 2)ᶜ := by
    rintro w ⟨-, (hw0 : w 0 < 0), (hw1 : 0 < w 1)⟩
    simp only [mem_compl_iff, mem_union, triodHalfPlane_zero, triodHalfPlane_one,
      triodHalfPlane_two]
    rintro ((⟨h0, -⟩ | ⟨h1, -⟩) | ⟨h2, -⟩)
    · linarith
    · linarith
    · linarith
  have hSecBall : Sec ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hOutBall : Out ⊆ Metric.ball (0 : E3) r := inter_subset_left
  have hPart : (triodHalfPlane 1 ∪ triodHalfPlane 2)ᶜ ∩ Metric.ball (0 : E3) r = Sec ∪ Out := by
    ext w
    simp only [mem_inter_iff, mem_union, mem_compl_iff, triodHalfPlane_one, triodHalfPlane_two,
      Sec, Out]
    constructor
    · rintro ⟨hnot, hball⟩
      by_cases h0 : w 0 < 0
      · by_cases h1 : 0 < w 1
        · exact Or.inl ⟨hball, h0, h1⟩
        · have h1le : w 1 ≤ 0 := le_of_not_gt h1
          rcases lt_or_eq_of_le h1le with hlt | heq
          · exact Or.inr ⟨hball, Or.inr hlt⟩
          · exfalso; exact hnot (Or.inl ⟨heq, le_of_lt h0⟩)
      · have h0ge : 0 ≤ w 0 := le_of_not_gt h0
        rcases h0ge.lt_or_eq with hgt | heq
        · exact Or.inr ⟨hball, Or.inl hgt⟩
        · have hw1 : w 1 < 0 := by
            by_contra! hge
            exact hnot (Or.inr ⟨heq.symm, hge⟩)
          exact Or.inr ⟨hball, Or.inr hw1⟩
    · rintro (⟨hball, hw0, hw1⟩ | ⟨hball, hw0 | hw1⟩)
      · refine ⟨?_, hball⟩
        rintro (⟨h1, -⟩ | ⟨h2, -⟩) <;> linarith
      · dsimp at hw0
        refine ⟨?_, hball⟩
        rintro (⟨-, h1⟩ | ⟨h2, -⟩) <;> linarith
      · dsimp at hw1
        refine ⟨?_, hball⟩
        rintro (⟨h1, -⟩ | ⟨-, h2⟩) <;> linarith
  let w_u : E3 := !₂[- (r / 2), 0, 0]
  have hu_ball : w_u ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_neg_zero (r / 2) (by linarith)]; linarith)
  have hu_clos : w_u ∈ closure Sec :=
    mem_closure_ball_inter_quadrant_second_y w_u hu_ball (by simp [w_u]; linarith) (by simp [w_u])
  have hu_i : w_u ∈ triodHalfPlane 1 := ⟨by simp [w_u], by simp [w_u]; linarith⟩
  have hu_not_j : w_u ∉ triodHalfPlane 2 := by
    intro h
    have : w_u 0 = 0 := h.1
    simp [w_u] at this
    linarith
  let w_v : E3 := !₂[0, r / 2, 0]
  have hv_ball : w_v ∈ Metric.ball (0 : E3) r :=
    Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_one (r / 2) (by linarith)]; linarith)
  have hv_clos : w_v ∈ closure Sec :=
    mem_closure_ball_inter_quadrant_second_x w_v hv_ball (by simp [w_v]) (by simp [w_v]; linarith)
  have hv_j : w_v ∈ triodHalfPlane 2 := ⟨by simp [w_v], by simp [w_v]; linarith⟩
  have hv_not_i : w_v ∉ triodHalfPlane 1 := by
    intro h
    have : w_v 1 = 0 := h.1
    simp [w_v] at this
    linarith
  let w_w : E3 := !₂[r / 2, 0, 0]
  have hw_out : w_w ∈ Out :=
    ⟨Metric.mem_ball.mpr
      (by rw [dist_zero_right, norm_vec_zero (r / 2) (by linarith)]; linarith),
      Or.inl (by simp [w_w]; linarith)⟩
  have hw_k : w_w ∈ triodHalfPlane 0 := ⟨by simp [w_w], by simp [w_w]; linarith⟩
  have hw_not_ij : w_w ∉ triodHalfPlane 1 ∪ triodHalfPlane 2 := by
    rintro (⟨-, h1⟩ | ⟨h2, -⟩) <;> { simp [w_w] at *; linarith }
  have hSecMeet : (e '' (connectedComponentIn (⋃ l, S l)ᶜ x ∩ e.source) ∩ Sec).Nonempty :=
    ⟨e z, ⟨z, ⟨hzU, hzs⟩, rfl⟩, ⟨hzball, hz_neg0, hz_pos1⟩⟩
  obtain ⟨hu, hv, hw⟩ :=
    exists_frontier_pair_witnesses_of_sector S B hinter hpair e hp hpsource hep htrace hr hrsub
      hx 1 2 0 (by decide) (by decide) (by decide) Sec Out hSecConn hOutConn hSecSub hSecBall
      hOutBall hPart hu_clos hu_ball hu_i hu_not_j hv_clos hv_ball hv_j hv_not_i hw_out hw_k
      hw_not_ij hSecMeet
  exact ⟨1, 2, 0, by decide, by decide, by decide, hu, hv, hw⟩

theorem exists_frontier_pair_witnesses_of_triod_chart
    (S : Fin 3 → Set E3) (B : Set E3)
    (hinter : ∀ i j, i ≠ j → S i ∩ S j = B)
    (hpair : ∀ i j, i ≠ j → ∃ K : Geometry.SimplicialComplex ℝ E3,
      K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
        K.space = S i ∪ S j)
    (e : OpenPartialHomeomorph E3 E3) {p x : E3}
    (hp : p ∈ B) (hpsource : p ∈ e.source) (hep : e p = 0)
    (he : IsPLHomeomorphOn e e.source e.target)
    (htrace : ∀ i, ∀ z ∈ e.source, z ∈ S i ↔
      e z ∈ (![{w : E3 | w 1 = 0 ∧ 0 ≤ w 0},
        {w : E3 | w 1 = 0 ∧ w 0 ≤ 0},
        {w : E3 | w 0 = 0 ∧ 0 ≤ w 1}] : Fin 3 → Set E3) i)
    (hx : x ∉ ⋃ i, S i)
    (hpfront : p ∈ frontier (connectedComponentIn (⋃ i, S i)ᶜ x)) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∃ u ∈ S i \ B, u ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      (∃ v ∈ S j \ B, v ∈ frontier (connectedComponentIn (⋃ l, S l)ᶜ x)) ∧
      ∃ w ∈ S k \ B, w ∉ connectedComponentIn (S i ∪ S j)ᶜ x := by
  let _ := he
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target 0 (hep ▸ e.map_source hpsource)
  have hV_open : IsOpen (e.source ∩ e ⁻¹' (Metric.ball (0 : E3) r)) :=
    e.isOpen_inter_preimage isOpen_ball
  have hp_in_V : p ∈ e.source ∩ e ⁻¹' (Metric.ball (0 : E3) r) := by
    refine ⟨hpsource, ?_⟩
    simp only [mem_preimage, hep, Metric.mem_ball_self hr]
  have hp_clos : p ∈ closure (connectedComponentIn (⋃ i, S i)ᶜ x) :=
    frontier_subset_closure hpfront
  obtain ⟨z, hz_U, hzs, hz_ball⟩ :=
    (closure_inter_open_nonempty_iff hV_open).mp ⟨p, hp_clos, hp_in_V⟩
  have htrace' : ∀ i, ∀ z' ∈ e.source, z' ∈ S i ↔ e z' ∈ triodHalfPlane i := by
    intro i z' hz'
    exact htrace i z' hz'
  have hz_not_S : ∀ i, z ∉ S i := by
    intro i hi
    have : z ∈ (⋃ l, S l)ᶜ := connectedComponentIn_subset _ _ hz_U
    exact this (mem_iUnion.mpr ⟨i, hi⟩)
  have hz_not_plane : ∀ i, e z ∉ triodHalfPlane i := by
    intro i hi
    exact hz_not_S i ((htrace' i z hzs).mpr hi)
  have hz1_ne : e z 1 ≠ 0 := by
    intro h0
    rcases le_total 0 (e z 0) with hge | hle
    · exact hz_not_plane 0 ⟨h0, hge⟩
    · exact hz_not_plane 1 ⟨h0, hle⟩
  rcases lt_or_gt_of_ne hz1_ne with hlt1 | hgt1
  · exact exists_frontier_pair_witnesses_of_sector_C S B hinter hpair e hp hpsource hep
      htrace' hr hrsub hx hz_U hzs hz_ball hlt1
  · have hz0_ne : e z 0 ≠ 0 := by
      intro h0
      exact hz_not_plane 2 ⟨h0, le_of_lt hgt1⟩
    rcases lt_or_gt_of_ne hz0_ne with hlt0 | hgt0
    · exact exists_frontier_pair_witnesses_of_sector_B S B hinter hpair e hp hpsource hep
        htrace' hr hrsub hx hz_U hzs hz_ball hgt1 hlt0
    · exact exists_frontier_pair_witnesses_of_sector_A S B hinter hpair e hp hpsource hep
        htrace' hr hrsub hx hz_U hzs hz_ball hgt1 hgt0

end DifferentialGeometry.Topology.PiecewiseLinear
