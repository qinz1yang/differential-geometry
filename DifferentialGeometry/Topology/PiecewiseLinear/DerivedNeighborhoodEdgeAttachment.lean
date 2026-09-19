/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodEdge
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellBoundary
import DifferentialGeometry.Topology.Attachment.Union

/-! Actual prism attachments in finite graph neighborhoods. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_derivedNeighborhoodCell_edge_attachment
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {a b : E} (hab : a ≠ b)
    (he : {a, b} ∈ K.faces) (d : Finset (Finset E))
    (hd : ∀ s ∈ d, s ∈ K.faces ∧ s.card ≤ 2) (hed : {a, b} ∉ d)
    (ha : {a} ∈ d) (hb : {b} ∈ d) :
    let D := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
    let A : Set D := {z | z.val.2 = 0 ∨ z.val.2 = 1}
    let U := ⋃ s ∈ d, (derivedNeighborhoodCell K s).space
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g D (derivedNeighborhoodCell K {a, b}).space ∧
      ∃ φ : A → U, IsClosedEmbedding φ ∧
        (∀ z, (φ z : E) = g z.val.val) ∧
        ∃ e : AdjunctionSpace (Subtype.val : A → D) φ ≃ₜ
            (⋃ s ∈ insert {a, b} d, (derivedNeighborhoodCell K s).space),
          (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
          ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  classical
  dsimp only
  let D := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
  let A : Set D := {z | z.val.2 = 0 ∨ z.val.2 = 1}
  let U := ⋃ s ∈ d, (derivedNeighborhoodCell K s).space
  obtain ⟨g, hg, hg0, hg1⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_edge K hK hab he
  have hmeet := derivedNeighborhoodCell_edge_inter_iUnion K hab he d hd hed ha hb
  have hpre (z : (Fin 3 → ℝ) × ℝ) (hz : z ∈ D) :
      g z ∈ U ↔ z.2 = 0 ∨ z.2 = 1 := by
    constructor
    · intro hzU
      have hz' : g z ∈ (derivedNeighborhoodCell K {a, b}).space ∩ U :=
        ⟨hg.bijOn.mapsTo hz, hzU⟩
      rw [hmeet] at hz'
      rcases hz' with hz0 | hz1
      · rw [← hg0] at hz0
        obtain ⟨w, hw, hwz⟩ := hz0
        have hwD : w ∈ D := ⟨hw.1, hw.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
        have heq := hg.bijOn.injOn hwD hz hwz
        exact Or.inl ((congrArg Prod.snd heq).symm.trans hw.2)
      · rw [← hg1] at hz1
        obtain ⟨w, hw, hwz⟩ := hz1
        have hwD : w ∈ D := ⟨hw.1, hw.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
        have heq := hg.bijOn.injOn hwD hz hwz
        exact Or.inr ((congrArg Prod.snd heq).symm.trans hw.2)
    · intro hzA
      have hz' : g z ∈ (derivedNeighborhoodCell K {a, b}).space ∩ U := by
        rw [hmeet]
        rcases hzA with hz0 | hz1
        · exact Or.inl (hg0 ▸ mem_image_of_mem g ⟨hz.1, hz0⟩)
        · exact Or.inr (hg1 ▸ mem_image_of_mem g ⟨hz.1, hz1⟩)
      exact hz'.2
  let c : D → E := fun z => g z.val
  have hc : Continuous c :=
    continuousOn_iff_continuous_domRestrict.mp hg.isPiecewiseAffineOn.continuousOn
  have hci : Function.Injective c := fun x y h =>
    Subtype.ext (hg.bijOn.injOn x.property y.property h)
  let φ : A → U := fun z => ⟨g z.val.val, (hpre z.val.val z.val.property).mpr z.property⟩
  have hφcont : Continuous φ := (hc.comp continuous_subtype_val).subtype_mk _
  have hφinj : Function.Injective φ := fun x y h =>
    Subtype.ext (hci (congrArg Subtype.val h))
  let _ : CompactSpace D := isCompact_iff_compactSpace.mp
    ((isCompact_stdSimplex ℝ (Fin 3)).prod isCompact_Icc)
  have hA : IsClosed A :=
    (isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const).union
      (isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const)
  let _ : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have hboundary (z : D) (hz : c z ∈ U) : z ∈ range (Subtype.val : A → D) :=
    ⟨⟨z, (hpre z.val z.property).mp hz⟩, rfl⟩
  have hclosed : IsClosed U := d.finite_toSet.isClosed_biUnion fun s hs =>
    (hK.isPLBall_derivedNeighborhoodCell (hd s hs).1).isPolyhedron.isClosed
  let e := adjunctionHomeomorphUnionImage (Subtype.val : A → D) φ c
    (fun _ => rfl) hci hc hboundary hclosed
  have hrange : range c = (derivedNeighborhoodCell K {a, b}).space := by
    apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      exact hg.bijOn.mapsTo z.property
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := hg.bijOn.surjOn hy
      exact ⟨⟨z, hz⟩, hzy⟩
  have htarget : U ∪ range c =
      ⋃ s ∈ insert {a, b} d, (derivedNeighborhoodCell K s).space := by
    rw [hrange]
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, U, union_comm]
  refine ⟨g, hg, φ, hφcont.isClosedEmbedding hφinj, fun _ => rfl,
    e.trans (Homeomorph.setCongr htarget), ?_, ?_⟩
  · intro x
    change (e (adjunctionLower φ x)).val = x.val
    exact congrArg Subtype.val
      (adjunctionHomeomorphUnionImage_lower _ φ c (fun _ => rfl) hci hc hboundary hclosed x)
  · intro z
    rfl

open Classical in
theorem exists_derivedNeighborhood_edge_attachment
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ s ∈ L.faces, s.card ≤ 2) {a b : E} (hab : a ≠ b)
    (he : {a, b} ∈ K.faces) (heL : {a, b} ∉ L.faces)
    (ha : {a} ∈ L.faces) (hb : {b} ∈ L.faces) :
    let D := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
    let A : Set D := {z | z.val.2 = 0 ∨ z.val.2 = 1}
    let N := derivedNeighborhood K L
    IsCombinatorialManifoldWithBoundary 3 N ∧
      ∃ g : (Fin 3 → ℝ) × ℝ → E,
        IsPLHomeomorphOn g D (derivedNeighborhoodCell K {a, b}).space ∧
        ∃ φ : A → N.space, IsClosedEmbedding φ ∧
          (∀ z, (φ z : E) = g z.val.val) ∧
          (∀ z, (φ z : E) ∈ (boundaryComplex 3 N).space) ∧
          ∃ e : AdjunctionSpace (Subtype.val : A → D) φ ≃ₜ
              (derivedNeighborhood K
                (subcomplexGeneratedBy K (insert {a, b} L.faces))).space,
            (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
            ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  classical
  dsimp only
  have hfin : L.faces.Finite := (Set.toFinite K.faces).subset hLK
  let d := hfin.toFinset
  have h := exists_derivedNeighborhoodCell_edge_attachment K hK hab he d
    (fun s hs => ⟨hLK (hfin.mem_toFinset.mp hs), hL s (hfin.mem_toFinset.mp hs)⟩)
    (fun hs => heL (hfin.mem_toFinset.mp hs))
    (hfin.mem_toFinset.mpr ha) (hfin.mem_toFinset.mpr hb)
  dsimp only [d] at h
  have hU : (⋃ s ∈ hfin.toFinset, (derivedNeighborhoodCell K s).space) =
      (derivedNeighborhood K L).space := by
    change (⋃ s ∈ (hfin.toFinset : Set (Finset E)),
      (derivedNeighborhoodCell K s).space) = _
    rw [hfin.coe_toFinset]
    exact iUnion_derivedNeighborhoodCell_space K L hLK
  have hI : (⋃ s ∈ insert {a, b} hfin.toFinset, (derivedNeighborhoodCell K s).space) =
      (derivedNeighborhoodCell K {a, b}).space ∪ (derivedNeighborhood K L).space := by
    rw [← hU]
    ext x
    simp only [mem_iUnion, Finset.mem_insert, mem_union]
    aesop
  rw [hU, hI] at h
  obtain ⟨g, hg, φ, hφ, hφg, e, he0, he1⟩ := h
  have hnext := derivedNeighborhood_space_of_insert_face K L hLK he
    (fun t ht hts => by
      have htcard : t.card = 1 := by
        have hlt := Finset.card_lt_card hts
        have hpos := Finset.card_pos.mpr ht
        rw [Finset.card_pair hab] at hlt
        omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp htcard
      have hv : v = a ∨ v = b := by simpa using hts.le (Finset.mem_singleton_self v)
      rcases hv with rfl | rfl <;> assumption)
  let e' := e.trans (Homeomorph.setCongr hnext.symm)
  refine ⟨hK.derivedNeighborhood L, g, hg, φ, hφ, hφg, ?_, e', ?_, ?_⟩
  · intro z
    apply derivedNeighborhoodCell_inter_subset_boundary_derivedNeighborhood K L hK hLK he heL
    refine ⟨?_, (φ z).property⟩
    rw [hφg]
    exact hg.bijOn.mapsTo z.val.property
  · exact he0
  · exact he1

end DifferentialGeometry.Topology.PiecewiseLinear
