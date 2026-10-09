/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeArc

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_param_of_mem_segment_affine {p d x : E3} {lo hi : ℝ} (hlh : lo ≤ hi)
    (hx : x ∈ segment ℝ (p + lo • d) (p + hi • d)) : ∃ s ∈ Icc lo hi, x = p + s • d := by
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  refine ⟨lo + t * (hi - lo), ⟨by nlinarith, by nlinarith⟩, ?_⟩
  have : p + hi • d - (p + lo • d) = (hi - lo) • d := by rw [sub_smul]; abel
  change p + lo • d + t • (p + hi • d - (p + lo • d)) = p + (lo + t * (hi - lo)) • d
  rw [this, smul_smul, add_smul, add_assoc]

theorem segment_affine_subset {p d : E3} {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ 1) : segment ℝ (p + lo • d) (p + hi • d) ⊆ segment ℝ p (p + d) := by
  intro x hx
  obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := exists_param_of_mem_segment_affine hlh hx
  rw [segment_eq_image']
  refine ⟨s, ⟨by linarith, by linarith⟩, ?_⟩
  change p + s • (p + d - p) = p + s • d
  rw [add_sub_cancel_left]

theorem isPLBall_sdiff_interior_tube_of_crossing {X W O U : Set E3} (hX : IsPLBall 3 X)
    (hW : IsPLBall 3 W) (hXW : X ⊆ interior W) (hO : IsOpen O) (hU : IsOpen U) (hWU : W ⊆ U)
    {w : ℕ → E3} {N j k : ℕ} {ta tb ρa ρb : ℝ} {na nb : E3}
    (hjk : j ≤ k) (hkN : k < N) (hta0 : 0 < ta) (hta1 : ta < 1) (htb0 : 0 < tb)
    (htb1 : tb < 1) (hkj : k = j → ta < tb)
    (hafter : ∀ s, ta < s → s ≤ 1 → w j + s • (w (j + 1) - w j) ∉ X)
    (hlater : ∀ i, j < i → i < N → ∀ s ∈ Icc (0 : ℝ) 1, w i + s • (w (i + 1) - w i) ∉ X)
    (hbefore : ∀ s, (if k = j then ta else 0) ≤ s → s < tb →
      w k + s • (w (k + 1) - w k) ∈ interior W)
    (hmid : ∀ i, j ≤ i → i < k → ∀ s, (if i = j then ta else 0) ≤ s → s ≤ 1 →
      w i + s • (w (i + 1) - w i) ∈ interior W)
    (hρa : 0 < ρa) (hna : 0 < inner ℝ na (w (j + 1) - w j))
    (hflatX : X ∩ ball (w j + ta • (w (j + 1) - w j)) ρa =
      {x | inner ℝ na (x - (w j + ta • (w (j + 1) - w j))) ≤ 0} ∩
        ball (w j + ta • (w (j + 1) - w j)) ρa)
    (hρb : 0 < ρb) (hnb : 0 < inner ℝ nb (w (k + 1) - w k))
    (hflatW : W ∩ ball (w k + tb • (w (k + 1) - w k)) ρb =
      {x | inner ℝ nb (x - (w k + tb • (w (k + 1) - w k))) ≤ 0} ∩
        ball (w k + tb • (w (k + 1) - w k)) ρb)
    (hsegO : ∀ i < N, segment ℝ (w i) (w (i + 1)) ⊆ O) (hwne : ∀ i < N, w i ≠ w (i + 1))
    (hnonadj : ∀ i i', i' < N → i + 1 < i' →
      Disjoint (segment ℝ (w i) (w (i + 1))) (segment ℝ (w i') (w (i' + 1))))
    (hadj : ∀ i, i + 1 < N →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w (i + 1)) (w (i + 2)) ⊆ {w (i + 1)})
    (hncol : ∀ i, 0 < i → i < N → w (i + 1) ∉ affineSpan ℝ ({w (i - 1), w i} : Set E3)) :
    ∃ Nt : Set E3, IsCompact Nt ∧ Nt ⊆ O ∩ U ∧ IsPLBall 3 (W \ interior (X ∪ Nt)) := by
  classical
  set d : ℕ → E3 := fun i => w (i + 1) - w i with hd
  have hwd : ∀ i, w (i + 1) = w i + (1 : ℝ) • d i := fun i => by
    rw [one_smul]
    exact (add_sub_cancel (w i) (w (i + 1))).symm
  set b := w k + tb • d k with hbdef
  have hbW : b ∈ W := by
    have := (hflatW.symm.subset ⟨by simp, mem_ball_self hρb⟩).1
    exact this
  obtain ⟨rU, hrU, hrUsub⟩ := Metric.isOpen_iff.mp hU b (hWU hbW)
  set r := min ρb rU with hr
  have hr0 : 0 < r := lt_min hρb hrU
  set μ := min ((1 - tb) / 2) (r / (2 * (‖d k‖ + 1))) with hμ
  have hμ0 : 0 < μ := lt_min (by linarith) (div_pos hr0 (by positivity))
  have hμ1 : μ ≤ (1 - tb) / 2 := min_le_left _ _
  have hμ2 : μ * ‖d k‖ < r := by
    calc μ * ‖d k‖ ≤ r / (2 * (‖d k‖ + 1)) * ‖d k‖ := by
          gcongr
          exact min_le_right _ _
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (d k)]
  set tp := tb + μ with htp
  have htp1 : tp < 1 := by linarith
  set m := k - j with hm
  have hjm : j + m = k := by omega
  set lo : ℕ → ℝ := fun i => if i = 0 then ta else 0 with hlo
  set hi : ℕ → ℝ := fun i => if i = m then tp else 1 with hhi
  set u' : ℕ → E3 := fun i => if i ≤ m then w (j + i) + lo i • d (j + i)
    else w k + tp • d k with hu'
  have hu'i : ∀ i ≤ m, u' i = w (j + i) + lo i • d (j + i) := fun i hi' => by
    simp only [hu', ite_eq_left hi']
  have hu'succ : ∀ i ≤ m, u' (i + 1) = w (j + i) + hi i • d (j + i) := by
    intro i hi'
    rcases Nat.lt_or_ge i m with him | him
    · have hle : i + 1 ≤ m := him
      rw [hu'i (i + 1) hle]
      simp only [hlo, hhi, ite_eq_right (Nat.succ_ne_zero i), ite_eq_right (Nat.ne_of_lt him), zero_smul,
        add_zero]
      rw [show j + (i + 1) = j + i + 1 by omega, hwd]
    · have him' : i = m := le_antisymm hi' him
      subst him'
      simp only [hu', hhi, ite_eq_right (Nat.not_succ_le_self m), ite_eq_left rfl]
      rw [hjm]
  have hlohi : ∀ i ≤ m, 0 ≤ lo i ∧ lo i < hi i ∧ hi i ≤ 1 := by
    intro i hi'
    simp only [hlo, hhi]
    refine ⟨by split_ifs <;> linarith, ?_, by split_ifs <;> linarith⟩
    split_ifs with h0 hm'
    · have hk : k = j := by omega
      have := hkj hk
      linarith
    · linarith
    · linarith
    · linarith
  have hseg' : ∀ i ≤ m, segment ℝ (u' i) (u' (i + 1)) ⊆ segment ℝ (w (j + i)) (w (j + i + 1)) := by
    intro i hi'
    rw [hu'i i hi', hu'succ i hi', hwd, one_smul]
    exact segment_affine_subset (hlohi i hi').1 (hlohi i hi').2.1.le (hlohi i hi').2.2
  have hdir : ∀ i ≤ m, u' (i + 1) - u' i = (hi i - lo i) • d (j + i) := by
    intro i hi'
    rw [hu'i i hi', hu'succ i hi', sub_smul]
    abel
  have hloj : ∀ i, (if j + i = j then ta else 0) = lo i := by
    intro i
    by_cases h : i = 0
    · subst h
      simp [hlo]
    · rw [ite_eq_right (by omega)]
      simp only [hlo, ite_eq_right h]
  have hlok : (if k = j then ta else 0) = lo m := by
    by_cases h : m = 0
    · rw [ite_eq_left (by omega)]
      simp only [hlo, ite_eq_left h]
    · rw [ite_eq_right (by omega)]
      simp only [hlo, ite_eq_right h]
  have hhim : hi m = tp := by simp only [hhi, ite_eq_left rfl]
  have hhilt : ∀ i < m, hi i = 1 := fun i him => by simp only [hhi, ite_eq_right (Nat.ne_of_lt him)]
  set ν : ℕ → E3 := fun i => if i = 0 then na else
    ‖d (j + i)‖⁻¹ • d (j + i) + ‖d (j + i - 1)‖⁻¹ • d (j + i - 1) with hνdef
  have hbis : ∀ i, 1 ≤ i → i ≤ m →
      0 < inner ℝ (ν i) (d (j + i)) ∧ 0 < inner ℝ (ν i) (d (j + i - 1)) := by
    intro i hi1 him
    have hjiN : j + i < N := by omega
    have hidx : j + i - 1 + 1 = j + i := by omega
    have h1 := hwne (j + i - 1) (by omega)
    rw [hidx] at h1
    have hx : d (j + i - 1) ≠ 0 := by
      simp only [hd, hidx]
      exact sub_ne_zero.mpr (Ne.symm h1)
    have hy : d (j + i) ≠ 0 := by
      simp only [hd]
      exact sub_ne_zero.mpr (Ne.symm (hwne (j + i) hjiN))
    have hxy : ‖d (j + i - 1)‖ • d (j + i) + ‖d (j + i)‖ • d (j + i - 1) ≠ 0 := by
      have := bisector_ne_zero_of_notMem_affineSpan h1 (hncol (j + i) (by omega) hjiN)
      simpa only [hd, hidx] using this
    have := inner_bisector_pos hx hy hxy
    simp only [hνdef, ite_eq_right (by omega : i ≠ 0)]
    exact this
  have hu0 : u' 0 = w j + ta • (w (j + 1) - w j) := by
    rw [hu'i 0 (Nat.zero_le _)]
    simp [hlo, hd]
  have hum : u' m = w k + lo m • d k := by rw [hu'i m le_rfl, hjm]
  have hum1 : u' (m + 1) = w k + tp • d k := by rw [hu'succ m le_rfl, hhim, hjm]
  have hlom : lo m < tb := by
    by_cases h : m = 0
    · simp only [hlo, ite_eq_left h]
      exact hkj (by omega)
    · simp only [hlo, ite_eq_right h]
      exact htb0
  have hlo0 : 0 ≤ lo m := (hlohi m le_rfl).1
  have hcsegO : ∀ i ≤ m, segment ℝ (u' i) (u' (i + 1)) ⊆ O ∩ U := by
    intro i hi' x hx
    refine ⟨hsegO (j + i) (by omega) (hseg' i hi' hx), ?_⟩
    rw [hu'i i hi', hu'succ i hi'] at hx
    obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := exists_param_of_mem_segment_affine (hlohi i hi').2.1.le hx
    rcases Nat.lt_or_ge i m with him | him
    · rw [hhilt i him] at hs2
      exact hWU (interior_subset (hmid (j + i) (by omega) (by omega) s (by rw [hloj]; exact hs1)
        hs2))
    · have him' : i = m := le_antisymm hi' him
      subst him'
      rw [hjm]
      rw [hhim] at hs2
      by_cases hsb : s < tb
      · exact hWU (interior_subset (hbefore s (by rw [hlok]; exact hs1) hsb))
      · push Not at hsb
        apply hrUsub
        rw [mem_ball, dist_eq_norm, hbdef]
        have : w k + s • d k - (w k + tb • d k) = (s - tb) • d k := by rw [sub_smul]; abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have : (s - tb) * ‖d k‖ ≤ μ * ‖d k‖ := by gcongr; linarith
        have := min_le_right ρb rU
        linarith
  have hcsegW : ∀ i < m, segment ℝ (u' i) (u' (i + 1)) ⊆ interior W := by
    intro i him x hx
    rw [hu'i i him.le, hu'succ i him.le, hhilt i him] at hx
    obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := exists_param_of_mem_segment_affine
      (by have := hlohi i him.le; rw [hhilt i him] at this; exact this.2.1.le) hx
    exact hmid (j + i) (by omega) (by omega) s (by rw [hloj]; exact hs1) hs2
  have hcb : b ∈ openSegment ℝ (u' m) (u' (m + 1)) := by
    rw [hum, hum1, openSegment_eq_image']
    refine ⟨(tb - lo m) / (tp - lo m), ⟨div_pos (by linarith) (by linarith),
      (div_lt_one (by linarith)).mpr (by linarith)⟩, ?_⟩
    change w k + lo m • d k + ((tb - lo m) / (tp - lo m)) •
      (w k + tp • d k - (w k + lo m • d k)) = b
    have : w k + tp • d k - (w k + lo m • d k) = (tp - lo m) • d k := by rw [sub_smul]; abel
    rw [this, smul_smul, div_mul_cancel₀ _ (by linarith : tp - lo m ≠ 0), hbdef, add_assoc,
      ← add_smul]
    congr 2
    ring
  have hcsegW' : ∀ x ∈ segment ℝ (u' m) (u' (m + 1)), x ∈ frontier W → x = b := by
    intro x hx hxW
    rw [hum, hum1] at hx
    obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := exists_param_of_mem_segment_affine (by linarith) hx
    rcases lt_trichotomy s tb with hsb | hsb | hsb
    · exact absurd (hbefore s (by rw [hlok]; exact hs1) hsb) hxW.2
    · rw [hsb]
    · exfalso
      have hxball : w k + s • d k ∈ ball b ρb := by
        rw [mem_ball, dist_eq_norm, hbdef]
        have : w k + s • d k - (w k + tb • d k) = (s - tb) • d k := by rw [sub_smul]; abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have : (s - tb) * ‖d k‖ ≤ μ * ‖d k‖ := by gcongr; linarith
        have := min_le_left ρb rU
        linarith
      have hle := (hflatW.subset ⟨hW.isPolyhedron.isClosed.frontier_subset hxW, hxball⟩).1
      change inner ℝ nb (w k + s • d k - (w k + tb • d k)) ≤ 0 at hle
      have : w k + s • d k - (w k + tb • d k) = (s - tb) • d k := by rw [sub_smul]; abel
      rw [this, real_inner_smul_right] at hle
      have := mul_pos (by linarith : 0 < s - tb) hnb
      linarith
  have hcν : ∀ i ≤ m, 0 < inner ℝ (ν i) (u' (i + 1) - u' i) := by
    intro i hi'
    rw [hdir i hi', real_inner_smul_right]
    refine mul_pos (by linarith [(hlohi i hi').2.1]) ?_
    by_cases h : i = 0
    · subst h
      simpa [hνdef, hd] using hna
    · exact (hbis i (by omega) hi').1
  have hcν' : ∀ i < m, 0 < inner ℝ (ν (i + 1)) (u' (i + 1) - u' i) := by
    intro i him
    rw [hdir i him.le, real_inner_smul_right]
    refine mul_pos (by linarith [(hlohi i him.le).2.1]) ?_
    have := (hbis (i + 1) (by omega) him).2
    rwa [show j + (i + 1) - 1 = j + i by omega] at this
  have hcXA : ∀ i ≤ m, ∀ x ∈ segment ℝ (u' i) (u' (i + 1)), x ∈ X → x = u' 0 := by
    intro i hi' x hx hxX
    rw [hu'i i hi', hu'succ i hi'] at hx
    obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := exists_param_of_mem_segment_affine (hlohi i hi').2.1.le hx
    by_cases h : i = 0
    · subst h
      simp only [hlo, ite_eq_left rfl, add_zero] at hs1 ⊢
      rcases hs1.lt_or_eq with hlt | heq
      · exact absurd hxX (hafter s hlt (hs2.trans (hlohi 0 hi').2.2))
      · rw [hu0, ← heq]
    · exfalso
      exact hlater (j + i) (by omega) (by omega) s ⟨(hlohi i hi').1.trans hs1,
        hs2.trans (hlohi i hi').2.2⟩ hxX
  have hcdisj : ∀ i i', i' ≤ m → i + 1 < i' →
      Disjoint (segment ℝ (u' i) (u' (i + 1))) (segment ℝ (u' i') (u' (i' + 1))) := by
    intro i i' hi' hii'
    exact (hnonadj (j + i) (j + i') (by omega) (by omega)).mono (hseg' i (by omega))
      (hseg' i' hi')
  have hcadj : ∀ i < m, segment ℝ (u' i) (u' (i + 1)) ∩ segment ℝ (u' (i + 1)) (u' (i + 2)) ⊆
      {u' (i + 1)} := by
    intro i him x hx
    have h1 := hseg' i him.le hx.1
    have h2 := hseg' (i + 1) him hx.2
    rw [show j + (i + 1) = j + i + 1 by omega] at h2
    have := hadj (j + i) (by omega) ⟨h1, h2⟩
    rw [mem_singleton_iff] at this ⊢
    rw [this, hu'i (i + 1) him, show j + (i + 1) = j + i + 1 by omega]
    simp [hlo]
  have hcnb : 0 < inner ℝ nb (u' (m + 1) - u' m) := by
    rw [hum1, hum]
    have : w k + tp • d k - (w k + lo m • d k) = (tp - lo m) • d k := by rw [sub_smul]; abel
    rw [this, real_inner_smul_right]
    exact mul_pos (by linarith) hnb
  have hcflat : X ∩ ball (u' 0) ρa = {x | inner ℝ (ν 0) (x - u' 0) ≤ 0} ∩ ball (u' 0) ρa := by
    rw [hu0]
    simpa [hνdef] using hflatX
  exact isPLBall_sdiff_interior_union_prismChain (m := m) (u := u') (ν := ν) (b := b)
    (nb := nb) (ρ := ρa) (ρb := ρb) (O := O ∩ U) hX hW hXW (hO.inter hU) hρa hcflat hρb hflatW
    hcsegO hcsegW hcb hcsegW' hcν hcν' hcnb hcXA hcdisj hcadj

theorem disjoint_convexHull_of_card_le_two {A : Set E3} {σ : Finset E3} (hne : σ.Nonempty)
    (hσ : σ.card ≤ 2) (h : ∀ e₁ ∈ σ, ∀ e₂ ∈ σ, Disjoint A (segment ℝ e₁ e₂)) :
    Disjoint A (convexHull ℝ (σ : Set E3)) := by
  have hpos := hne.card_pos
  rcases (show σ.card = 1 ∨ σ.card = 2 by omega) with h1 | h2
  · obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h1
    have := h e (Finset.mem_singleton_self e) e (Finset.mem_singleton_self e)
    rwa [segment_same, ← convexHull_singleton (𝕜 := ℝ), ← Finset.coe_singleton] at this
  · obtain ⟨e₁, e₂, -, rfl⟩ := Finset.card_eq_two.mp h2
    have := h e₁ (Finset.mem_insert_self _ _) e₂
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rwa [← convexHull_pair (𝕜 := ℝ), ← Finset.coe_pair] at this

theorem exists_isPLBall_sdiff_interior_tube {X W K U : Set E3} (S : Finset (E3 × E3))
    (hX : IsPLBall 3 X) (hW : IsPLBall 3 W) (hXW : X ⊆ interior W) (hK : IsClosed K)
    (hU : IsOpen U) (hWU : W ⊆ U) {p q : E3} (hp : p ∈ interior X) (hq : q ∉ W)
    (hpq : JoinedIn Kᶜ p q) :
    ∃ N : Set E3, IsCompact N ∧ N ⊆ U ∧ Disjoint N K ∧
      (∀ e ∈ S, Disjoint N (segment ℝ e.1 e.2)) ∧ IsPLBall 3 (W \ interior (X ∪ N)) := by
  classical
  have hXc : IsClosed X := hX.isPolyhedron.isClosed
  have hWc : IsClosed W := hW.isPolyhedron.isClosed
  obtain ⟨LX, hLXf, hLX⟩ := hX.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  obtain ⟨LW, hLWf, hLW⟩ := hW.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  have : Finite LX.faces := hLXf.to_subtype
  have : Finite LW.faces := hLWf.to_subtype
  have hex : ∀ τ : Finset E3, ∃ n g : E3, τ.card = 3 → n ≠ 0 ∧
      ∀ x ∈ convexHull ℝ (τ : Set E3), inner ℝ n (x - g) = 0 := by
    intro τ
    by_cases h : τ.card = 3
    · obtain ⟨n, g, hn, hng⟩ := exists_unit_normal_of_card_eq_three h
      refine ⟨n, g, fun _ => ⟨fun h0 => ?_, hng⟩⟩
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose nrm g hnrm using hex
  set F : Finset E3 := hLXf.toFinset.biUnion id ∪ hLWf.toFinset.biUnion id ∪
    S.image Prod.fst ∪ S.image Prod.snd with hF
  set ℋ : Set (Set E3) := (fun τ : Finset E3 => {x : E3 | inner ℝ (nrm τ) x =
    inner ℝ (nrm τ) (g τ)}) '' {τ | (τ ∈ LX.faces ∨ τ ∈ LW.faces) ∧ τ.card = 3} with hℋ
  have hℋf : ℋ.Finite := ((hLXf.union hLWf).subset fun τ hτ => hτ.1).image _
  have hℋc : ∀ B ∈ ℋ, IsClosed B := by
    rintro _ ⟨τ, -, rfl⟩
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hℋi : ∀ B ∈ ℋ, interior B = ∅ := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact interior_setOf_inner_eq_eq_empty (hnrm τ hτ.2).1 _
  obtain ⟨N, w, hN0, hw0, hwN, hsegK, hwℋ, hgen⟩ := exists_generic_polygonal_path hK
    isOpen_interior hWc.isOpen_compl hp hq hpq F hℋf hℋc hℋi
  obtain ⟨hFd, hnonadj, hadj, hncol⟩ := generic_polygonal_path_facts hgen
  have hnotconv : ∀ k ≤ N, ∀ σ : Finset E3, σ ⊆ F → σ.card ≤ 3 →
      w k ∉ convexHull ℝ (σ : Set E3) := fun k hk σ hσ hc hmem =>
    hgen k hk σ (hσ.trans Finset.subset_union_left) hc (convexHull_subset_affineSpan _ hmem)
  have hfX : ∀ σ ∈ LX.faces, σ ⊆ F := fun σ hσ =>
    (Finset.subset_biUnion_of_mem id (hLXf.mem_toFinset.mpr hσ)).trans
      (Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  have hfW : ∀ σ ∈ LW.faces, σ ⊆ F := fun σ hσ =>
    (Finset.subset_biUnion_of_mem id (hLWf.mem_toFinset.mpr hσ)).trans
      (Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  have hcX : ∀ σ ∈ LX.faces, σ.card ≤ 3 := fun σ hσ =>
    card_le_three_of_interior_eq_empty LX (by rw [hLX]; exact interior_frontier hXc) hσ
  have hcW : ∀ σ ∈ LW.faces, σ.card ≤ 3 := fun σ hσ =>
    card_le_three_of_interior_eq_empty LW (by rw [hLW]; exact interior_frontier hWc) hσ
  have hvX : ∀ k ≤ N, w k ∉ frontier X := fun k hk hkX => by
    rw [← hLX] at hkX
    obtain ⟨σ, hσ, hkσ⟩ := LX.mem_space_iff.mp hkX
    exact hnotconv k hk σ (hfX σ hσ) (hcX σ hσ) hkσ
  have hvW : ∀ k ≤ N, w k ∉ frontier W := fun k hk hkW => by
    rw [← hLW] at hkW
    obtain ⟨σ, hσ, hkσ⟩ := LW.mem_space_iff.mp hkW
    exact hnotconv k hk σ (hfW σ hσ) (hcW σ hσ) hkσ
  have hwne : ∀ i < N, w i ≠ w (i + 1) := by
    intro i hi h
    apply hgen (i + 1) hi {w i} (by
      intro e he
      rw [Finset.mem_singleton.mp he]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr
        (Nat.lt_succ_self i), rfl⟩)) (by simp)
    rw [← h, Finset.coe_singleton]
    exact mem_affineSpan ℝ (mem_singleton _)
  have hedge : ∀ i < N, ∀ (L : Geometry.SimplicialComplex ℝ E3), (∀ σ ∈ L.faces, σ ⊆ F) →
      ∀ σ ∈ L.faces, σ.card ≤ 2 →
        Disjoint (segment ℝ (w i) (w (i + 1))) (convexHull ℝ (σ : Set E3)) :=
    fun i hi L hLF σ hσ hc => disjoint_convexHull_of_card_le_two (L.nonempty_of_mem_faces hσ)
      hc fun e₁ he₁ e₂ he₂ => hFd i hi e₁ (hLF σ hσ he₁) e₂ (hLF σ hσ he₂)
  have hoff : ∀ k ≤ N, ∀ τ, (τ ∈ LX.faces ∨ τ ∈ LW.faces) → τ.card = 3 →
      inner ℝ (nrm τ) (w k - g τ) ≠ 0 := by
    intro k hk τ hτ hτ3 h0
    apply hwℋ k hk _ ⟨τ, ⟨hτ, hτ3⟩, rfl⟩
    change inner ℝ (nrm τ) (w k) = inner ℝ (nrm τ) (g τ)
    rw [inner_sub_right] at h0
    linarith
  obtain ⟨j, k, ta, tb, hjk, hkN, hta0, hta1, htb0, htb1, hkj, hafr, hafter, hlater, hbfr,
    hbefore, hmid⟩ := exists_crossing_params hXc hWc hXW hN0 (interior_subset hw0) hwN hvX hvW
  obtain ⟨ρa, hρa, na, hna, hflatX⟩ := exists_flat_of_mem_frontier_of_mem_segment hX LX hLX
    (nrm := nrm) (g := g) (fun τ _ hτ3 => hnrm τ hτ3) hta0 hta1 hafr
    (hedge j (by omega) LX hfX) (fun τ hτ hτ3 => hoff j (by omega) τ (Or.inl hτ) hτ3)
    (Or.inl ⟨1 - ta, by linarith, fun s hs1 hs2 => hafter s hs1 (by linarith)⟩)
  have hlow : (if k = j then ta else 0) < tb := by
    split_ifs with h
    · exact hkj h
    · exact htb0
  obtain ⟨ρb, hρb, nb, hnb, hflatW⟩ := exists_flat_of_mem_frontier_of_mem_segment hW LW hLW
    (nrm := nrm) (g := g) (fun τ _ hτ3 => hnrm τ hτ3) htb0 htb1 hbfr
    (hedge k hkN LW hfW) (fun τ hτ hτ3 => hoff k (by omega) τ (Or.inr hτ) hτ3)
    (Or.inr ⟨tb - (if k = j then ta else 0), by linarith, fun s hs1 hs2 =>
      hbefore s (by linarith) hs2⟩)
  set O := Kᶜ ∩ (⋃ e ∈ S, segment ℝ e.1 e.2)ᶜ with hOdef
  have hO : IsOpen O := hK.isOpen_compl.inter
    ((S.finite_toSet.isClosed_biUnion fun e _ =>
      (isCompact_segment_euclidean e.1 e.2).isClosed).isOpen_compl)
  have hsegO : ∀ i < N, segment ℝ (w i) (w (i + 1)) ⊆ O := by
    intro i hi x hx
    refine ⟨hsegK i hi hx, fun hxS => ?_⟩
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxS
    have he1 : e.1 ∈ F := Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ he))
    have he2 : e.2 ∈ F := Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    exact Set.disjoint_left.mp (hFd i hi e.1 he1 e.2 he2) hx hxe
  obtain ⟨Nt, hNtc, hNtOU, hball⟩ := isPLBall_sdiff_interior_tube_of_crossing hX hW hXW hO hU
    hWU hjk hkN hta0 hta1 htb0 htb1 hkj hafter hlater hbefore hmid hρa hna hflatX hρb hnb
    hflatW hsegO hwne hnonadj hadj hncol
  refine ⟨Nt, hNtc, fun x hx => (hNtOU hx).2, Set.disjoint_left.mpr fun x hx hxK =>
    (hNtOU hx).1.1 hxK, fun e he => Set.disjoint_left.mpr fun x hx hxe =>
    (hNtOU hx).1.2 (mem_iUnion₂.mpr ⟨e, he, hxe⟩), hball⟩

end DifferentialGeometry.Topology.PiecewiseLinear
