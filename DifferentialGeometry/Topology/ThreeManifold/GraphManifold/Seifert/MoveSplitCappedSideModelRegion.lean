import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelLift

/-!
# Regions of the host chart swept by the nested circles

Lane N2d, side model, step 4 (regions). A point `w` of the host chart of the seam circle `l`
lies in the closed round pants after `hostChart l` (resp. in its interior) as soon as it is
inside the seam circle `‖w‖ ≤ hostRadius l 0` (`circleSign_seam`), outside the image of the port
circle of side `t` (`circleSign_port`, the circle `‖w - C‖ = R` of the nested family at
`ρ = 3`), and on the right side of the other port, `-3 < sgnR t · stripLevel l w`
(`circleSign_other`, from the collar avoidance of step 1); see `hostChart_mem_planarModel` and
`hostChart_mem_pantsInterior`. The nested circles of `sideData l t` stay inside the seam circle
beyond `ρ = 3/2` and outside the port circle before `ρ = 3` (`norm_point_le`,
`le_norm_point_sub`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

open GC.GraphManifold

theorem normSq_add_inv_mul (c : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Complex.normSq ((c : ℂ) + w⁻¹) * Complex.normSq w =
      c ^ 2 * Complex.normSq w + 2 * c * w.re + 1 := by
  have h1 : (c : ℂ) + w⁻¹ = ((c : ℂ) * w + 1) / w := by field_simp
  rw [h1, Complex.normSq_div, div_mul_cancel₀ _ (Complex.normSq_pos.mpr hw).ne']
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.one_re, Complex.add_im, Complex.mul_im, add_zero, Complex.one_im]
  ring

theorem normSq_sub_ofReal (w : ℂ) (C : ℝ) :
    Complex.normSq (w - C) = Complex.normSq w - 2 * C * w.re + C ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

theorem norm_add_inv_le_of (c k : ℝ) {w : ℂ} (hw : w ≠ 0) (hk : 0 ≤ k)
    (h : c ^ 2 * Complex.normSq w + 2 * c * w.re + 1 ≤ k ^ 2 * Complex.normSq w) :
    ‖(c : ℂ) + w⁻¹‖ ≤ k := by
  have hn := Complex.normSq_pos.mpr hw
  have e := normSq_add_inv_mul c hw
  have h2 : Complex.normSq ((c : ℂ) + w⁻¹) ≤ k ^ 2 := by
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc hn
    linarith
  rw [← Complex.sq_norm] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hk two_ne_zero).mp h2

theorem le_norm_add_inv_of (c k : ℝ) {w : ℂ} (hw : w ≠ 0) (hk : 0 ≤ k)
    (h : k ^ 2 * Complex.normSq w ≤ c ^ 2 * Complex.normSq w + 2 * c * w.re + 1) :
    k ≤ ‖(c : ℂ) + w⁻¹‖ := by
  have hn := Complex.normSq_pos.mpr hw
  have e := normSq_add_inv_mul c hw
  have h2 : k ^ 2 ≤ Complex.normSq ((c : ℂ) + w⁻¹) := by
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc hn
    linarith
  rw [← Complex.sq_norm] at h2
  exact (pow_le_pow_iff_left₀ hk (norm_nonneg _) two_ne_zero).mp h2

theorem lt_norm_add_inv_of (c k : ℝ) {w : ℂ} (hw : w ≠ 0) (hk : 0 ≤ k)
    (h : k ^ 2 * Complex.normSq w < c ^ 2 * Complex.normSq w + 2 * c * w.re + 1) :
    k < ‖(c : ℂ) + w⁻¹‖ := by
  have hn := Complex.normSq_pos.mpr hw
  have e := normSq_add_inv_mul c hw
  have h2 : k ^ 2 < Complex.normSq ((c : ℂ) + w⁻¹) := by
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_right hc hn.le
    linarith
  rw [← Complex.sq_norm] at h2
  exact (pow_lt_pow_iff_left₀ hk (norm_nonneg _) two_ne_zero).mp h2

theorem norm_add_inv_lt_of (c k : ℝ) {w : ℂ} (hw : w ≠ 0) (hk : 0 ≤ k)
    (h : c ^ 2 * Complex.normSq w + 2 * c * w.re + 1 < k ^ 2 * Complex.normSq w) :
    ‖(c : ℂ) + w⁻¹‖ < k := by
  have hn := Complex.normSq_pos.mpr hw
  have e := normSq_add_inv_mul c hw
  have h2 : Complex.normSq ((c : ℂ) + w⁻¹) < k ^ 2 := by
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_right hc hn.le
    linarith
  rw [← Complex.sq_norm] at h2
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hk two_ne_zero).mp h2

theorem normSq_ge_of_norm_ge {x : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : r ≤ ‖x‖) :
    r ^ 2 ≤ Complex.normSq x := by
  rw [← Complex.sq_norm]; exact pow_le_pow_left₀ hr h 2

theorem normSq_gt_of_norm_gt {x : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : r < ‖x‖) :
    r ^ 2 < Complex.normSq x := by
  rw [← Complex.sq_norm]; exact pow_lt_pow_left₀ h hr two_ne_zero

def circleSign (p : Fin 3) (z : ℂ) : ℝ := planarSign p * (‖z - planarCenter 3 p‖ - planarRadius p)

theorem mem_planarModel_of_circleSign {z : ℂ} (h : ∀ p : Fin 3, 0 ≤ circleSign p z) :
    z ∈ planarModel 3 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [circleSign, planarSign, planarRadius, planarCenter] at h0 h1 h2
  norm_num at h0 h1 h2
  rw [mem_planarModel_three]
  refine ⟨by linarith, ?_, ?_⟩
  · convert h1 using 2
    push_cast
    ring
  · convert h2 using 2
    push_cast
    ring

theorem mem_pantsInterior_of_circleSign {z : ℂ} (h : ∀ p : Fin 3, 0 < circleSign p z) :
    z ∈ pantsInterior := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [circleSign, planarSign, planarRadius, planarCenter] at h0 h1 h2
  norm_num at h0 h1 h2
  refine ⟨by linarith, ?_, ?_⟩
  · convert h1 using 2
    push_cast
    ring
  · convert h2 using 2
    push_cast
    ring

theorem circleSign_seam (l : Fin 3) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h : ‖w‖ ≤ hostRadius l.val 0) : 0 ≤ circleSign l (hostChart l w) := by
  unfold circleSign
  by_cases hl : l.val = 0
  · simp only [hostChart, hl, ↓reduceIte, planarSign, planarRadius, planarCenter_zero hl,
      Complex.ofReal_zero, sub_zero]
    simp only [hostRadius, hl, ↓reduceIte] at h
    linarith
  · simp only [hostChart, hl, ↓reduceIte, planarSign, planarRadius, add_sub_cancel_left,
      norm_inv, one_mul]
    simp only [hostRadius, hl, ↓reduceIte] at h
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (hw hl)
    rw [sub_nonneg, le_inv_comm₀ (by norm_num) hw0]
    linarith

theorem circleSign_seam_lt (l : Fin 3) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h : ‖w‖ < hostRadius l.val 0) : 0 < circleSign l (hostChart l w) := by
  unfold circleSign
  by_cases hl : l.val = 0
  · simp only [hostChart, hl, ↓reduceIte, planarSign, planarRadius, planarCenter_zero hl,
      Complex.ofReal_zero, sub_zero]
    simp only [hostRadius, hl, ↓reduceIte] at h
    linarith
  · simp only [hostChart, hl, ↓reduceIte, planarSign, planarRadius, add_sub_cancel_left,
      norm_inv, one_mul]
    simp only [hostRadius, hl, ↓reduceIte] at h
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (hw hl)
    rw [sub_pos, lt_inv_comm₀ (by norm_num) hw0]
    linarith

theorem circleSign_other (l : Fin 3) (t : Bool) {w : ℂ}
    (h : -3 < sgnR t * stripLevel l w) : 1 / 8 < circleSign (sidePort l (!t)) (hostChart l w) := by
  by_contra hc
  push Not at hc
  have hm := (lt_sgnR_mul_stripLevel l (!t) (z := hostChart l w) hc).2
  rw [hostInv_hostChart] at hm
  have : sgnR (!t) = -sgnR t := by cases t <;> simp [sgnR]
  rw [this] at hm
  linarith

theorem famC_three {l : Fin 3} (D : CollarData l) : D.famC 3 = D.C 3 := by
  simp [CollarData.famC, sideBlend_of_ge (by norm_num : (5 / 2 : ℝ) ≤ 3)]

theorem famR_three {l : Fin 3} (D : CollarData l) : D.famR 3 = D.R 3 := by
  simp [CollarData.famR, sideBlend_of_ge (by norm_num : (5 / 2 : ℝ) ≤ 3)]

theorem circleSign_port_aux (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0) {k : ℝ}
    (hk : 0 ≤ k) (h : k ≤ ‖w - (sideData l t).famC 3‖ - (sideData l t).famR 3) :
    k * (if l.val = 0 then 1 else 0) ≤ circleSign (sidePort l t) (hostChart l w) ∧
      (k = 0 → 0 ≤ circleSign (sidePort l t) (hostChart l w)) ∧
      (0 < k → 0 < circleSign (sidePort l t) (hostChart l w)) := by
  rw [famC_three, famR_three] at h
  unfold sideData at h
  split_ifs at h with hl hp
  · simp only [zeroData] at h
    have hp0 : (sidePort l t).val ≠ 0 := by fin_cases l <;> cases t <;> simp_all [sidePort]
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖w - planarCenter 3 (sidePort l t)‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp0, ↓reduceIte, hostChart, hl, one_mul]
    rw [e]
    norm_num at h
    simp only [hl, ↓reduceIte, mul_one]
    refine ⟨by linarith, fun _ => by linarith, fun hk' => by linarith⟩
  · simp only [outerData] at h
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
    norm_num at h
    rw [hA2] at h
    norm_num at h
    try rw [hA2c] at h
    have hR : (4 / 9 : ℝ) + k ≤ ‖w - ((-(4 / 27) * A : ℝ) : ℂ)‖ := by
      convert (show 4 / 9 + k ≤ ‖w - ((A / (9 / 4 - 9) : ℝ) : ℂ)‖ by
        push_cast at h ⊢; linarith) using 4
      ring
    have hn := normSq_ge_of_norm_ge (by positivity) hR
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        3 - ‖((planarCenter 3 l : ℝ) : ℂ) + w⁻¹‖ := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl,
        planarCenter_zero hp, Complex.ofReal_zero, sub_zero]
      ring
    rw [e, hcl]
    simp only [hl, ↓reduceIte, mul_zero]
    have hns := Complex.normSq_nonneg w
    refine ⟨?_, ?_, ?_⟩
    · have := norm_add_inv_le_of (-A) 3 hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      push_cast at this ⊢
      linarith
    · intro _
      have := norm_add_inv_le_of (-A) 3 hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      push_cast at this ⊢
      linarith
    · intro hk'
      have := norm_add_inv_lt_of (-A) 3 hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      push_cast at this ⊢
      linarith
  · simp only [innerData] at h
    have hA2 : (planarCenter 3 (sidePort l t) - planarCenter 3 l) ^ 2 = 9 := by
      rw [← sq_abs, abs_sidePort_inner hl hp]; norm_num
    set A := planarCenter 3 (sidePort l t) - planarCenter 3 l with hAdef
    have hw0 := hw hl
    have hA2c : (A : ℂ) ^ 2 = 9 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hA2
      push_cast at this
      exact this
    norm_num at h
    rw [hA2] at h
    norm_num at h
    try rw [hA2c] at h
    have hR : (2 / 35 : ℝ) + k ≤ ‖w - (((4 / 35) * A : ℝ) : ℂ)‖ := by
      convert (show 2 / 35 + k ≤ ‖w - ((A / (9 - 1 / 4) : ℝ) : ℂ)‖ by
        push_cast at h ⊢; linarith) using 4
      ring
    have hn := normSq_ge_of_norm_ge (by positivity) hR
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖((-A : ℝ) : ℂ) + w⁻¹‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl, one_mul]
      congr 2
      rw [hAdef]
      push_cast
      ring
    rw [e]
    simp only [hl, ↓reduceIte, mul_zero]
    have hns := Complex.normSq_nonneg w
    refine ⟨?_, ?_, ?_⟩
    · have := le_norm_add_inv_of (-A) (1 / 2) hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      linarith
    · intro _
      have := le_norm_add_inv_of (-A) (1 / 2) hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      linarith
    · intro hk'
      have := lt_norm_add_inv_of (-A) (1 / 2) hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
      linarith

theorem fin3_cases (l : Fin 3) (t : Bool) (p : Fin 3) :
    p = l ∨ p = sidePort l t ∨ p = sidePort l (!t) := by
  fin_cases l <;> cases t <;> fin_cases p <;> simp [sidePort]

theorem hostChart_mem_planarModel (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h1 : ‖w‖ ≤ hostRadius l.val 0) (h2 : (sideData l t).famR 3 ≤ ‖w - (sideData l t).famC 3‖)
    (h3 : -3 < sgnR t * stripLevel l w) : hostChart l w ∈ planarModel 3 := by
  refine mem_planarModel_of_circleSign fun p => ?_
  rcases fin3_cases l t p with rfl | rfl | rfl
  · exact circleSign_seam _ hw h1
  · exact (circleSign_port_aux l t hw le_rfl (by linarith)).2.1 rfl
  · linarith [circleSign_other l t h3]

theorem hostChart_mem_pantsInterior (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h1 : ‖w‖ < hostRadius l.val 0) (h2 : (sideData l t).famR 3 < ‖w - (sideData l t).famC 3‖)
    (h3 : -3 < sgnR t * stripLevel l w) : hostChart l w ∈ pantsInterior := by
  refine mem_pantsInterior_of_circleSign fun p => ?_
  rcases fin3_cases l t p with rfl | rfl | rfl
  · exact circleSign_seam_lt _ hw h1
  · exact (circleSign_port_aux l t hw (k := ‖w - (sideData l t).famC 3‖ - (sideData l t).famR 3)
      (by linarith) le_rfl).2.2 (by linarith)
  · linarith [circleSign_other l t h3]

theorem norm_nestedPoint_sub_le {c : ℝ → ℂ} {r : ℝ → ℝ} {μ : ℝ → Circle} {a : ℝ → ℝ}
    (hn : NestedOn c r (Icc 0 3)) {ρ₁ : ℝ} (hρ₁ : ρ₁ ∈ Icc (0 : ℝ) 3) {q : Circle × ℝ}
    (hq : q.2 ∈ Icc (0 : ℝ) 3) (hle : ρ₁ ≤ q.2) (hr : 0 ≤ r q.2) :
    ‖nestedPoint c r μ a q - c ρ₁‖ ≤ r ρ₁ ∧ (ρ₁ < q.2 → ‖nestedPoint c r μ a q - c ρ₁‖ < r ρ₁) := by
  have hp := norm_nestedPoint_sub (c := c) (μ := μ) (a := a) hr
  have key : ρ₁ < q.2 → ‖nestedPoint c r μ a q - c ρ₁‖ < r ρ₁ := by
    intro hlt
    have hnest := hn ρ₁ hρ₁ q.2 hq hlt
    have h4 := norm_sub_le_norm_sub_add_norm_sub (nestedPoint c r μ a q) (c q.2) (c ρ₁)
    linarith
  refine ⟨?_, key⟩
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [he]; exact hp.le
  · exact (key hlt).le

theorem le_norm_nestedPoint_sub {c : ℝ → ℂ} {r : ℝ → ℝ} {μ : ℝ → Circle} {a : ℝ → ℝ}
    (hn : NestedOn c r (Icc 0 3)) {q : Circle × ℝ} (hq : q.2 ∈ Icc (0 : ℝ) 3) (hr : 0 ≤ r q.2) :
    r 3 ≤ ‖nestedPoint c r μ a q - c 3‖ ∧ (q.2 < 3 → r 3 < ‖nestedPoint c r μ a q - c 3‖) := by
  have hp := norm_nestedPoint_sub (c := c) (μ := μ) (a := a) hr
  have key : q.2 < 3 → r 3 < ‖nestedPoint c r μ a q - c 3‖ := by
    intro hlt
    have hnest := hn q.2 hq 3 ⟨by norm_num, le_rfl⟩ hlt
    have h4 := norm_sub_le_norm_sub_add_norm_sub (nestedPoint c r μ a q) (c 3) (c q.2)
    have h5 : ‖c 3 - c q.2‖ = ‖c 3 - c q.2‖ := rfl
    linarith
  refine ⟨?_, key⟩
  rcases eq_or_lt_of_le hq.2 with he | hlt
  · rw [he] at hp; exact hp.ge
  · exact (key hlt).le

theorem famC_three_halves {l : Fin 3} (D : CollarData l) : D.famC (3 / 2) = 0 :=
  D.famC_of_le (by norm_num)

theorem famR_three_halves {l : Fin 3} (D : CollarData l) : D.famR (3 / 2) = hostRadius l.val 0 := by
  rw [D.famR_of_le (by norm_num), vRadius_of_two_le l (by norm_num)]
  norm_num

theorem norm_point_le (l : Fin 3) (t : Bool) {q : Circle × ℝ} (h1 : 3 / 2 ≤ q.2) (h3 : q.2 ≤ 3) :
    ‖(sideData l t).point q‖ ≤ hostRadius l.val 0 ∧
      (3 / 2 < q.2 → ‖(sideData l t).point q‖ < hostRadius l.val 0) := by
  have h := norm_nestedPoint_sub_le (μ := (sideData l t).famMu) (a := (sideData l t).famA)
    (sideData l t).nestedOn_fam (ρ₁ := 3 / 2) ⟨by norm_num, by norm_num⟩ (q := q)
    ⟨by linarith, h3⟩ h1 ((sideData l t).famR_pos ⟨by linarith, h3⟩).le
  rw [famC_three_halves, famR_three_halves, sub_zero] at h
  exact h

theorem le_norm_point_sub (l : Fin 3) (t : Bool) {q : Circle × ℝ} (h0 : 0 ≤ q.2) (h3 : q.2 ≤ 3) :
    (sideData l t).famR 3 ≤ ‖(sideData l t).point q - (sideData l t).famC 3‖ ∧
      (q.2 < 3 → (sideData l t).famR 3 < ‖(sideData l t).point q - (sideData l t).famC 3‖) :=
  le_norm_nestedPoint_sub (sideData l t).nestedOn_fam ⟨h0, h3⟩
    ((sideData l t).famR_pos ⟨h0, h3⟩).le

theorem stripLevel_zero (l : Fin 3) : stripLevel l 0 = stripCenter l / tubeSlope := by
  have hB : stripBump 0 = 1 := stripBump_of_le_half (by norm_num)
  have hW : stripWidth 0 = 1 := by rw [stripWidth, hB]; norm_num
  rw [stripLevel_eq]
  simp [hB, hW]

theorem ne_zero_of_level (l : Fin 3) (t : Bool) (hl : l.val ≠ 0) {w : ℂ}
    (h3 : -3 < sgnR t * stripLevel l w)
    (h2 : (sideData l t).famR 3 ≤ ‖w - (sideData l t).famC 3‖) : w ≠ 0 := by
  rintro rfl
  rw [stripLevel_zero] at h3
  rw [famC_three, famR_three, zero_sub, norm_neg] at h2
  unfold sideData at h2
  simp only [hl, ↓reduceDIte] at h2
  fin_cases l
  · exact absurd rfl hl
  · cases t
    · simp only [sidePort, outerData, planarCenter] at h2
      norm_num at h2
    · simp only [sgnR, stripCenter, tubeSlope] at h3
      norm_num at h3
  · cases t
    · simp only [sgnR, stripCenter, tubeSlope] at h3
      norm_num at h3
    · simp only [sidePort, outerData, planarCenter] at h2
      norm_num at h2

end GC.Seifert.SplitTube
