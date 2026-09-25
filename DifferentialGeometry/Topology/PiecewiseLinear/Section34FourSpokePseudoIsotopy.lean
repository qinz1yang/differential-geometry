import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSectorFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CellularDiskPseudoIsotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

private theorem image_arc_eq_of_preserves_fixed_pairs
    {S A : Set Plane} (hS : IsPLSphere 1 S) {p q : Plane}
    (hA : IsArcBetween A p q) (hAS : A ⊆ S) {u : Plane → Plane}
    (hu : PreservesArcsAtFixedPairs S u) (hp : u p = p) (hq : u q = q) :
    u '' A = A := by
  obtain ⟨B, hcut, hAb, hBb⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hS hA hAS
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hAb hA
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hBb hcut.snd
  exact hu A B γ δ hγ hδ (hδ0.trans hγ0.symm) (hδ1.trans hγ1.symm)
    hcut.union_eq (by simpa only [hγ0, hγ1] using hcut.inter_eq)
    (by simpa only [hγ0] using hp) (by simpa only [hγ1] using hq)

private theorem image_disk_eq_of_preserves_frontier
    {D S : Set Plane} {u : Plane → Plane} (hu : IsPLHomeomorphOn u D D)
    (hS : IsPLBall 2 S) (hSD : S ⊆ D) (hfront : u '' frontier S = frontier S) :
    u '' S = S := by
  obtain ⟨r, hr⟩ := hS
  have hru := hr.trans (hu.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hSD)
  have himage : IsPLBall 2 (u '' S) := ⟨u ∘ r, hru⟩
  have hfr : frontier (u '' S) = frontier S := by
    rw [← hru.image_stdSimplexBoundary_eq_frontier, image_comp,
      hr.image_stdSimplexBoundary_eq_frontier, hfront]
  calc
    u '' S = closure (inside (frontier (u '' S))) := by
      rw [← himage.interior_eq_inside_frontier, himage.closure_interior]
    _ = S := by
      rw [hfr, ← (show IsPLBall 2 S from ⟨r, hr⟩).interior_eq_inside_frontier,
        (show IsPLBall 2 S from ⟨r, hr⟩).closure_interior]

private theorem four_boundary_arcs_inter
    {D A₁ A₂ : Set Plane} {v : Fin 4 → Plane} {α : Fin 4 → Set Plane}
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (h01 : α 0 ∪ α 1 = A₁) (h01i : α 0 ∩ α 1 = {v 1})
    (h23 : α 2 ∪ α 3 = A₂) (h23i : α 2 ∩ α 3 = {v 3}) :
    ∀ i j, i ≠ j → α i ∩ α j ⊆ {v i, v (i + 1)} := by
  have hcross : (α 0 ∪ α 1) ∩ (α 2 ∪ α 3) = {v 0, v 2} := by
    rw [h01, h23, hcut.inter_eq]
  have h0 : v 0 ∈ α 0 := (hα 0).left_mem
  have h1 : v 1 ∈ α 0 := (hα 0).right_mem
  have h2 : v 2 ∈ α 1 := (hα 1).right_mem
  have h2' : v 2 ∈ α 2 := (hα 2).left_mem
  have h3 : v 3 ∈ α 2 := (hα 2).right_mem
  have h4 : v 0 ∈ α 3 := (hα 3).right_mem
  intro i j hij x hx
  have h01x : x ∈ α 0 → x ∈ α 1 → x = v 1 := fun h k => h01i.subset ⟨h, k⟩
  have h23x : x ∈ α 2 → x ∈ α 3 → x = v 3 := fun h k => h23i.subset ⟨h, k⟩
  have hcx : (x ∈ α 0 ∨ x ∈ α 1) → (x ∈ α 2 ∨ x ∈ α 3) →
      x = v 0 ∨ x = v 2 := fun h k => hcross.subset ⟨h, k⟩
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  all_goals norm_num only [Fin.reduceAdd, mem_insert_iff, mem_singleton_iff]
  all_goals
    simp only [mem_inter_iff] at hx
    aesop

theorem exists_PL_four_spoke_disk_pseudoisotopy
    {D A₁ A₂ : Set Plane} {c : Plane} {T : Fin 4 → Set Plane} {v : Fin 4 → Plane}
    (hD : IsPLBall 2 D) (hT : ∀ i, IsPLBall 1 (T i))
    (harc : ∀ i, IsArcBetween (T i) c (v i)) (hTD : ∀ i, T i ⊆ D)
    (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    {u : Plane → Plane} (hu : IsPLHomeomorphOn u D D)
    (huT : ∀ i, u '' T i = T i) (huv : ∀ i, u (v i) = v i) :
    ∃ Φ : Plane × ℝ → Plane × ℝ,
      IsPLHomeomorphOn Φ (D ×ˢ Icc (0 : ℝ) 1) (D ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ D, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ D, Φ (x, 1) = (u x, 1)) ∧
      (∀ i, Φ '' (T i ×ˢ Icc (0 : ℝ) 1) = T i ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (c, t) = (c, t)) ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, Φ (v i, t) = (v i, t) := by
  classical
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij heq
    have hm : v i ∈ T i ∩ T j :=
      ⟨(harc i).right_mem, heq ▸ (harc j).right_mem⟩
    exact ne_of_isArcBetween (harc i) ((hTT i j hij).subset hm).symm
  have huc : u c = c := by
    apply (hTT 0 1 (by decide)).subset
    exact ⟨(huT 0).subset ⟨c, (harc 0).left_mem, rfl⟩,
      (huT 1).subset ⟨c, (harc 1).left_mem, rfl⟩⟩
  have hvf (i : Fin 4) : v i ∈ frontier D := ((hTf i).symm.subset rfl).2
  have huf : u '' frontier D = frontier D := by
    obtain ⟨r, hr⟩ := hD
    rw [← hr.image_stdSimplexBoundary_eq_frontier, ← image_comp]
    exact (hr.trans hu).image_stdSimplexBoundary_congr hr
  have hpres : PreservesArcsAtFixedPairs (frontier D) u :=
    preservesArcsAtFixedPairs_of_three_fixed
      (by
        simpa only [huf] using hu.restrict hD.isPLSphere_frontier.isPolyhedron
          hD.isPolyhedron.isCompact.isClosed.frontier_subset)
      (hvf 0) (hvf 1) (hvf 2) (hvne 0 1 (by decide))
      (hvne 0 2 (by decide)) (hvne 1 2 (by decide)) (huv 0) (huv 1) (huv 2)
  obtain ⟨α, hα, h01, h01i, h23, h23i⟩ :=
    exists_boundary_arcs_of_isCutPair hcut hv1 hv3 hvne
  have hαf (i : Fin 4) : α i ⊆ frontier D := by
    fin_cases i
    · exact (h01 ▸ subset_union_left).trans hcut.fst_subset
    · exact (h01 ▸ subset_union_right).trans hcut.fst_subset
    · exact (h23 ▸ subset_union_left).trans hcut.snd_subset
    · exact (h23 ▸ subset_union_right).trans hcut.snd_subset
  have hαb (i : Fin 4) : IsPLBall 1 (α i) :=
    isPLBall_of_isArc_subset_isPLSphere hD.isPLSphere_frontier (hα i).isArc (hαf i)
  have huα (i : Fin 4) : u '' α i = α i :=
    image_arc_eq_of_preserves_fixed_pairs hD.isPLSphere_frontier (hα i) (hαf i)
      hpres (huv i) (huv (i + 1))
  obtain ⟨hS, hcover, hinter⟩ := fourSpokeSector_spec hD hT harc hTD hTf hTT
    hcut hv1 hv3 hα h01 h01i h23 h23i
  have hfour (B : Fin 4 → Set Plane) : (⋃ i, B i) = B 0 ∪ B 1 ∪ (B 2 ∪ B 3) := by
    ext x
    simp [Fin.exists_fin_succ, or_assoc]
  have hSD : (⋃ i, fourSpokeSector T α i) = D := (hfour _).trans hcover
  have hsub (i : Fin 4) : fourSpokeSector T α i ⊆ D :=
    hSD ▸ subset_iUnion (fourSpokeSector T α) i
  have huS (i : Fin 4) : u '' fourSpokeSector T α i = fourSpokeSector T α i := by
    apply image_disk_eq_of_preserves_frontier hu (hS i).1 (hsub i)
    rw [(hS i).2, image_union, image_union, huT, huT, huα]
  have hthin : interior (⋃ i, T i) = ∅ :=
    interior_iUnion_eq_empty_of_finite (fun i => (hT i).isPolyhedron.isClosed)
      fun i => (hT i).interior_eq_empty_of_lt_finrank (by simp)
  have hSinter (i j : Fin 4) (hij : i ≠ j) :
      fourSpokeSector T α i ∩ fourSpokeSector T α j ⊆ frontier (fourSpokeSector T α i) := by
    have hempty : interior (fourSpokeSector T α i) ∩
        interior (fourSpokeSector T α j) = ∅ := by
      rw [← interior_inter]
      exact subset_empty_iff.mp (hthin ▸ interior_mono (hinter i j hij))
    intro x hx
    refine ⟨subset_closure hx.1, fun hxi => ?_⟩
    have hxcl := isOpen_interior.inter_closure
      ⟨hxi, (hS j).1.closure_interior.symm ▸ hx.2⟩
    simp only [hempty, closure_empty, mem_empty_iff_false] at hxcl
  choose r hr using fun i => (hS i).1
  choose γ hγ hγ0 hγ1 using fun i =>
    exists_isPLHomeomorphOn_Icc_of_isArcBetween (hT i) (harc i)
  choose δ hδ hδ0 hδ1 using fun i =>
    exists_isPLHomeomorphOn_Icc_of_isArcBetween (hαb i) (hα i)
  let A : Fin 4 ⊕ Fin 4 → Set Plane := Sum.elim T α
  let ε : Fin 4 ⊕ Fin 4 → ℝ → Plane := Sum.elim γ δ
  have hε : ∀ e, IsPLHomeomorphOn (ε e) (Icc 0 1) (A e) := by
    intro e
    cases e with
    | inl i => exact hγ i
    | inr i => exact hδ i
  have hAf (i j : Fin 4) : T i ∩ α j ⊆ {v i} := by
    intro x hx
    exact (hTf i).subset ⟨hx.1, hαf j hx.2⟩
  have hαinter := four_boundary_arcs_inter hcut hα h01 h01i h23 h23i
  have hAinter : ∀ e f, e ≠ f → A e ∩ A f ⊆ {ε e 0, ε e 1} := by
    intro e f hef
    cases e with
    | inl i =>
      cases f with
      | inl j =>
        change T i ∩ T j ⊆ {γ i 0, γ i 1}
        rw [hγ0, hγ1, hTT i j (fun h => hef (congrArg Sum.inl h))]
        exact singleton_subset_iff.mpr (by simp)
      | inr j =>
        change T i ∩ α j ⊆ {γ i 0, γ i 1}
        rw [hγ0, hγ1]
        exact (hAf i j).trans (singleton_subset_iff.mpr (by simp))
    | inr i =>
      cases f with
      | inl j =>
        change α i ∩ T j ⊆ {δ i 0, δ i 1}
        rw [hδ0, hδ1]
        intro x hx
        have hxv : x = v j := hAf j i ⟨hx.2, hx.1⟩
        by_cases hij : i = j
        · exact Or.inl (hxv.trans (congrArg v hij.symm))
        · have hxαj : x ∈ α j := hxv ▸ (hα j).left_mem
          exact hαinter i j hij ⟨hx.1, hxαj⟩
      | inr j =>
        change α i ∩ α j ⊆ {δ i 0, δ i 1}
        rw [hδ0, hδ1]
        exact hαinter i j (fun h => hef (congrArg Sum.inr h))
  let edges (i : Fin 4) : Finset (Fin 4 ⊕ Fin 4) :=
    {Sum.inl i, Sum.inr i, Sum.inl (i + 1)}
  have hboundary (i : Fin 4) :
      r i '' stdSimplexBoundary 2 = ⋃ e ∈ edges i, A e := by
    rw [(hr i).image_stdSimplexBoundary_eq_frontier, (hS i).2]
    simp only [edges, Finset.set_biUnion_insert, Finset.set_biUnion_singleton,
      A, Sum.elim_inl, Sum.elim_inr, union_assoc]
  have hincident (e : Fin 4 ⊕ Fin 4) : ∃ i, e ∈ edges i := by
    cases e with
    | inl i => exact ⟨i, by simp [edges]⟩
    | inr i => exact ⟨i, by simp [edges]⟩
  have huA (e : Fin 4 ⊕ Fin 4) : IsPLHomeomorphOn u (A e) (A e) := by
    cases e with
    | inl i => simpa only [A, Sum.elim_inl, huT] using hu.restrict (hT i).isPolyhedron (hTD i)
    | inr i =>
      simpa only [A, Sum.elim_inr, huα] using hu.restrict (hαb i).isPolyhedron
        ((hαf i).trans hD.isPolyhedron.isClosed.frontier_subset)
  have hzero (e : Fin 4 ⊕ Fin 4) : u (ε e 0) = ε e 0 := by
    cases e with
    | inl i => simpa only [ε, Sum.elim_inl, hγ0] using huc
    | inr i => simpa only [ε, Sum.elim_inr, hδ0] using huv i
  have hone (e : Fin 4 ⊕ Fin 4) : u (ε e 1) = ε e 1 := by
    cases e with
    | inl i => simpa only [ε, Sum.elim_inl, hγ1] using huv i
    | inr i => simpa only [ε, Sum.elim_inr, hδ1] using huv (i + 1)
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, -, hΦA, hΦends⟩ :=
    exists_PL_cellular_disk_pseudoisotopy hr
      (fun i j hij => (hr i).image_stdSimplexBoundary_eq_frontier.symm ▸ hSinter i j hij)
      hε hAinter edges hboundary hincident
      (fun i => by simpa only [huS] using hu.restrict (hS i).1.isPolyhedron (hsub i))
      huA hzero hone
  rw [hSD] at hΦ hΦ0 hΦ1
  refine ⟨Φ, hΦ, hΦ0, hΦ1, fun i => hΦA (Sum.inl i), ?_, ?_⟩
  · intro t ht
    simpa only [ε, Sum.elim_inl, hγ0] using (hΦends (Sum.inl 0) t ht).1
  · intro i t ht
    simpa only [ε, Sum.elim_inl, hγ1] using (hΦends (Sum.inl i) t ht).2

end DifferentialGeometry.Topology.PiecewiseLinear
