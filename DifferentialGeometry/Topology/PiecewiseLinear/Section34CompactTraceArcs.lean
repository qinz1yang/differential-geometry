/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.isPLCellOn_inter_vertexBallImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {s : Section34CompactSimplexIndex K 3} {J F : Set E3} (hJ : IsPLSphere 1 J) (hJF : J ⊆ F)
    (hF : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 s.1 →
      F ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (hJU : J ⊆ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hJE : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
      ∃ p, J ∩ section34CompactSplitDiskImage srcBd f₁ e = {p})
    (hJV : ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 →
      ¬ J ⊆ section34CompactVertexBallImage src f₁ w)
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 s.1) :
    IsPLCellOn 1 (J ∩ section34CompactVertexBallImage src f₁ w)
      (J ∩ section34CompactVertexBallImage src f₁ w ∩
        ⋃ e, section34CompactSplitDiskImage src f₁ e) := by
  classical
  obtain ⟨-, -, hK'fin, -, hsub, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have hVc : ∀ u : Section34CompactVertexIndex K K',
      IsClosed (section34CompactVertexBallImage src f₁ u) :=
    fun u => (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hUc : IsClosed (⋃ u, section34CompactVertexBallImage src f₁ u) :=
    isClosed_iUnion_of_finite hVc
  have hJUsub : J ⊆ ⋃ u, section34CompactVertexBallImage src f₁ u :=
    hJU.trans hUc.frontier_subset
  have hinc : ∀ (u : Section34CompactVertexIndex K K') (x : E3), x ∈ J →
      x ∈ section34CompactVertexBallImage src f₁ u → Section34Incident u.1 s.1 := by
    intro u x hxJ hxu
    by_contra hn
    have hx : x ∈ F ∩ section34CompactVertexBallImage src f₁ u := ⟨hJF hxJ, hxu⟩
    rw [hF u hn] at hx
    exact hx
  have hEinc : ∀ (e : Section34CompactEdgeIndex K K') (x : E3), x ∈ J →
      x ∈ section34CompactSplitDiskImage src f₁ e → Section34Incident e.1 s.1 := by
    intro e x hxJ hxe
    obtain ⟨u, u', -, heu, hEeq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    rw [hEeq] at hxe
    change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [heu]
    exact union_subset (hinc u x hxJ hxe.1) (hinc u' x hxJ hxe.2)
  have hJEbd : ∀ (e : Section34CompactEdgeIndex K K') (x : E3), x ∈ J →
      x ∈ section34CompactSplitDiskImage src f₁ e →
        x ∈ section34CompactSplitDiskImage srcBd f₁ e := by
    intro e x hxJ hxe
    by_contra hxb
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hxe, hxb⟩) (hJU hxJ)
  have hEbdE : ∀ e : Section34CompactEdgeIndex K K',
      section34CompactSplitDiskImage srcBd f₁ e ⊆ section34CompactSplitDiskImage src f₁ e :=
    fun e => (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  choose pt hpt using fun e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1} =>
    hJE e.1 e.2
  have hptJ : ∀ e, pt e ∈ J ∧ pt e ∈ section34CompactSplitDiskImage srcBd f₁ e.1 := by
    intro e
    have h : pt e ∈ J ∩ section34CompactSplitDiskImage srcBd f₁ e.1 := by
      rw [hpt e]
      exact mem_singleton _
    exact h
  have hmemE : ∀ (e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}) (x : E3),
      x ∈ J → x ∈ section34CompactSplitDiskImage src f₁ e.1 → x = pt e := by
    intro e x hxJ hxe
    have hx : x ∈ J ∩ section34CompactSplitDiskImage srcBd f₁ e.1 := ⟨hxJ, hJEbd e.1 x hxJ hxe⟩
    rw [hpt e] at hx
    exact hx
  have hpig : ∀ {β : Type} (a b x y z : β), (x = a ∨ x = b) → (y = a ∨ y = b) →
      (z = a ∨ z = b) → x = y ∨ x = z ∨ y = z := by
    intro β a b x y z hx hy hz
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
      first
        | exact Or.inl (hx.trans hy.symm)
        | exact Or.inr (Or.inl (hx.trans hz.symm))
        | exact Or.inr (Or.inr (hy.trans hz.symm))
  have hcover : J ⊆ ⋃ u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1},
      J ∩ section34CompactVertexBallImage src f₁ u.1 := by
    intro x hx
    obtain ⟨u, hxu⟩ := mem_iUnion.mp (hJUsub hx)
    exact mem_iUnion.mpr ⟨⟨u, hinc u x hx hxu⟩, hx, hxu⟩
  have hXne : ∀ u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1},
      J ∩ section34CompactVertexBallImage src f₁ u.1 ≠ J := by
    intro u h
    exact hJV u.1 u.2 (h.symm.subset.trans inter_subset_right)
  have hp : Function.Injective pt := by
    intro e e' h
    by_contra hee
    have hne : e.1 ≠ e'.1 := fun h' => hee (Subtype.ext h')
    exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁ hne) (hEbdE e.1 (hptJ e).2)
      (h ▸ hEbdE e'.1 (hptJ e').2)
  have hpX : ∀ (u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1})
      (e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}),
      pt e ∈ J ∩ section34CompactVertexBallImage src f₁ u.1 ↔ u.1.1 ⊆ e.1.1 := by
    intro u e
    constructor
    · intro h
      exact hcut.subset_of_mem_splitDiskImage hf₁ (hEbdE e.1 (hptJ e).2) h.2
    · intro h
      refine ⟨(hptJ e).1, ?_⟩
      obtain ⟨a, b, -, hab, hEeq⟩ := hcut.splitDiskImage_eq_inter hf₁ e.1
      have hpe := hEbdE e.1 (hptJ e).2
      rw [hEeq] at hpe
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e.1 hab h with h' | h'
      · rw [h']
        exact hpe.1
      · rw [h']
        exact hpe.2
  have hmeet : ∀ u u' : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1},
      u ≠ u' → ∀ x ∈ (J ∩ section34CompactVertexBallImage src f₁ u.1) ∩
        (J ∩ section34CompactVertexBallImage src f₁ u'.1),
      ∃ e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1},
        u.1.1 ⊆ e.1.1 ∧ u'.1.1 ⊆ e.1.1 ∧ x = pt e := by
    intro u u' huu x hx
    have hne : u.1 ≠ u'.1 := fun h => huu (Subtype.ext h)
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hne hx.1.2 hx.2.2
    have he := hEinc e x hx.1.1 hxe
    exact ⟨⟨e, he⟩, hcut.subset_of_mem_splitDiskImage hf₁ hxe hx.1.2,
      hcut.subset_of_mem_splitDiskImage hf₁ hxe hx.2.2, hmemE ⟨e, he⟩ x hx.1.1 hxe⟩
  have hdeg : ∀ u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1},
      ∃ e₁ e₂ : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1},
        e₁ ≠ e₂ ∧ u.1.1 ⊆ e₁.1.1 ∧ u.1.1 ⊆ e₂.1.1 := by
    intro u
    obtain ⟨e₁, e₂, hne, hi₁, hi₂, hw₁, hw₂, -⟩ :=
      exists_section34CompactEdgeIndex_pair_of_incident hsub hK'fin s u.1 u.2
    exact ⟨⟨e₁, hi₁⟩, ⟨e₂, hi₂⟩, fun h => hne (congrArg Subtype.val h), hw₁, hw₂⟩
  have hdeg₃ : ∀ (u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1})
      (g₁ g₂ g₃ : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}),
      u.1.1 ⊆ g₁.1.1 → u.1.1 ⊆ g₂.1.1 → u.1.1 ⊆ g₃.1.1 → g₁ = g₂ ∨ g₁ = g₃ ∨ g₂ = g₃ := by
    intro u g₁ g₂ g₃ h₁ h₂ h₃
    obtain ⟨e₁, e₂, -, -, -, -, -, huniq⟩ :=
      exists_section34CompactEdgeIndex_pair_of_incident hsub hK'fin s u.1 u.2
    rcases hpig e₁ e₂ g₁.1 g₂.1 g₃.1 (huniq g₁.1 g₁.2 h₁) (huniq g₂.1 g₂.2 h₂)
      (huniq g₃.1 g₃.2 h₃) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hend : ∀ e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1},
      ∃ u u' : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1},
        u ≠ u' ∧ u.1.1 ⊆ e.1.1 ∧ u'.1.1 ⊆ e.1.1 := by
    intro e
    obtain ⟨a, b, hab, heab, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e.1
    have ha : (a.1 : Set E3) ⊆ e.1.1 := heab ▸ subset_union_left
    have hb : (b.1 : Set E3) ⊆ e.1.1 := heab ▸ subset_union_right
    exact ⟨⟨a, ha.trans e.2⟩, ⟨b, hb.trans e.2⟩, fun h => hab (congrArg Subtype.val h),
      Finset.coe_subset.mp ha, Finset.coe_subset.mp hb⟩
  have hend₃ : ∀ (e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1})
      (u₁ u₂ u₃ : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1}),
      u₁.1.1 ⊆ e.1.1 → u₂.1.1 ⊆ e.1.1 → u₃.1.1 ⊆ e.1.1 → u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
    intro e u₁ u₂ u₃ h₁ h₂ h₃
    obtain ⟨a, b, -, hab, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e.1
    rcases hpig a b u₁.1 u₂.1 u₃.1 (eq_or_eq_of_section34CompactVertexIndex_subset e.1 hab h₁)
      (eq_or_eq_of_section34CompactVertexIndex_subset e.1 hab h₂)
      (eq_or_eq_of_section34CompactVertexIndex_subset e.1 hab h₃) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  obtain ⟨e₁, e₂, hne, hi₁, hi₂, hw₁, hw₂, huniq⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident hsub hK'fin s w hw
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := hJ.exists_isPLHomeomorphOn_Icc_of_cycle
    (X := fun u : {u : Section34CompactVertexIndex K K' // Section34Incident u.1 s.1} =>
      J ∩ section34CompactVertexBallImage src f₁ u.1)
    (inc := fun u e => u.1.1 ⊆ e.1.1)
    (fun u => hJ.isPolyhedron.isClosed.inter (hVc u.1)) (fun _ => inter_subset_left) hcover
    hXne hp hpX hmeet hdeg hdeg₃ hend hend₃ (u := ⟨w, hw⟩) (e₁ := ⟨e₁, hi₁⟩)
    (e₂ := ⟨e₂, hi₂⟩) (fun h => hne (congrArg Subtype.val h)) hw₁ hw₂
  have hcell := isPLCellOn_one_of_isPLHomeomorphOn_Icc hγ
  have hbd : J ∩ section34CompactVertexBallImage src f₁ w ∩
      ⋃ e, section34CompactSplitDiskImage src f₁ e = {γ 0, γ 1} := by
    rw [hγ0, hγ1]
    apply Subset.antisymm
    · rintro x ⟨⟨hxJ, hxw⟩, hxE⟩
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hxE
      have he := hEinc e x hxJ hxe
      have hx := hmemE ⟨e, he⟩ x hxJ hxe
      rcases huniq e he (hcut.subset_of_mem_splitDiskImage hf₁ hxe hxw) with h | h
      · subst h
        exact Or.inl hx
      · subst h
        exact Or.inr hx
    · rintro x (rfl | rfl)
      · exact ⟨(hpX ⟨w, hw⟩ ⟨e₁, hi₁⟩).mpr hw₁,
          mem_iUnion.mpr ⟨e₁, hEbdE e₁ (hptJ ⟨e₁, hi₁⟩).2⟩⟩
      · exact ⟨(hpX ⟨w, hw⟩ ⟨e₂, hi₂⟩).mpr hw₂,
          mem_iUnion.mpr ⟨e₂, hEbdE e₂ (hptJ ⟨e₂, hi₂⟩).2⟩⟩
  rw [hbd]
  exact hcell

end DifferentialGeometry.Topology.PiecewiseLinear
