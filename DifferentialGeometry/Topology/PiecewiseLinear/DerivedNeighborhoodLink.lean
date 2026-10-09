/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights
import DifferentialGeometry.Topology.PiecewiseLinear.JoinInternal
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : Geometry.SimplicialComplex ℝ E)

theorem centroid_injOn_barycentricSubdivision {e e' : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (he' : e' ∈ (barycentricSubdivision K).faces)
    (h : e.centroid ℝ id = e'.centroid ℝ id) : e = e' :=
  injOn_faces_of_mem_openSimplex (barycentricSubdivision K)
    (centroid_mem_openSimplex_of_mem_faces _) he he' h

theorem subset_mem_barycentricSubdivision {e s : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hs : s ⊆ e) (hne : s.Nonempty) :
    s ∈ (barycentricSubdivision K).faces :=
  (barycentricSubdivision K).down_closed he hs hne

theorem isFlag_of_subsets_of_chain {e : Finset E} (he : e ∈ (barycentricSubdivision K).faces)
    {d : Finset (Finset E)} (hd : ∀ s ∈ d, s.Nonempty ∧ s ⊆ e)
    (hchain : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s) : IsFlag (barycentricSubdivision K) d :=
  ⟨fun s hs => subset_mem_barycentricSubdivision K he (hd s hs).2 (hd s hs).1, hchain⟩

theorem image_centroid_erase {D : Finset (Finset E)} (hD : IsFlag (barycentricSubdivision K) D)
    {e : Finset E} (he : e ∈ (barycentricSubdivision K).faces) :
    ((D.image fun s => s.centroid ℝ id).erase (e.centroid ℝ id)) =
      (D.erase e).image fun s => s.centroid ℝ id := by
  ext z
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hz, s, hs, rfl⟩
    exact ⟨s, ⟨fun h => hz (h ▸ rfl), hs⟩, rfl⟩
  · rintro ⟨s, ⟨hse, hs⟩, rfl⟩
    refine ⟨fun h => hse (centroid_injOn_barycentricSubdivision K (hD.mem_faces hs) he h),
      s, hs, rfl⟩

theorem centroid_notMem_image_of_ssubset {D : Finset (Finset E)}
    (hD : IsFlag (barycentricSubdivision K) D) {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hD' : ∀ s ∈ D, s ≠ e) :
    e.centroid ℝ id ∉ D.image fun s => s.centroid ℝ id := by
  intro h
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp h
  exact hD' s hs (centroid_injOn_barycentricSubdivision K (hD.mem_faces hs) he heq)

theorem mem_of_centroid_mem_image {D : Finset (Finset E)}
    (hD : IsFlag (barycentricSubdivision K) D) {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces)
    (h : e.centroid ℝ id ∈ D.image fun s => s.centroid ℝ id) : e ∈ D := by
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp h
  exact (centroid_injOn_barycentricSubdivision K (hD.mem_faces hs) he heq) ▸ hs

variable (L : Geometry.SimplicialComplex ℝ E)

open Classical in
theorem mem_filter_centroid_iff {e s : Finset E} (hs : s ⊆ e) :
    (s ∩ e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v).Nonempty ↔
      ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ s := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨hvs, hvf⟩ := Finset.mem_inter.mp hv
    obtain ⟨-, σ, hσ, rfl⟩ := Finset.mem_filter.mp hvf
    exact ⟨σ, hσ, hvs⟩
  · rintro ⟨σ, hσ, hσs⟩
    exact ⟨σ.centroid ℝ id, Finset.mem_inter.mpr ⟨hσs, Finset.mem_filter.mpr ⟨hs hσs, σ, hσ, rfl⟩⟩⟩

open Classical in
theorem mem_geometricLink_faceNeighborhood_iff {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e)
    {s : Finset E} :
    s ∈ (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces ↔
      ∃ D₁ : Finset (Finset E), IsFlag (barycentricSubdivision K) D₁ ∧ D₁.Nonempty ∧
        (∀ x ∈ D₁, x ⊂ e) ∧ (∀ x ∈ D₁, ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ x) ∧
        s = D₁.image fun x => x.centroid ℝ id := by
  rw [SimplicialComplex.mem_geometricLink_singleton, mem_faceNeighborhood_faces_iff]
  constructor
  · rintro ⟨hsne, hcs, d, hd, hchain, -, hdf, hins⟩
    have hdflag := isFlag_of_subsets_of_chain K he hd hchain
    have hed : e ∈ d := mem_of_centroid_mem_image K hdflag he (hins ▸ Finset.mem_insert_self _ _)
    refine ⟨d.erase e, hdflag.mono (Finset.erase_subset e d), ?_, ?_, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hsne
      have hz' : z ∈ (d.image fun x => x.centroid ℝ id).erase (e.centroid ℝ id) := by
        rw [Finset.mem_erase, ← hins]
        exact ⟨fun h => hcs (h ▸ hz), Finset.mem_insert_of_mem hz⟩
      rw [image_centroid_erase K hdflag he] at hz'
      obtain ⟨x, hx, -⟩ := Finset.mem_image.mp hz'
      exact ⟨x, hx⟩
    · intro x hx
      exact Finset.ssubset_iff_subset_ne.mpr ⟨(hd x (Finset.mem_of_mem_erase hx)).2,
        (Finset.mem_erase.mp hx).1⟩
    · intro x hx
      exact (mem_filter_centroid_iff L (hd x (Finset.mem_of_mem_erase hx)).2).mp
        (hdf x (Finset.mem_of_mem_erase hx))
    · rw [← image_centroid_erase K hdflag he, ← hins, Finset.erase_insert hcs]
  · rintro ⟨D₁, hD₁, hne, hlt, hL, rfl⟩
    refine ⟨hne.image _, centroid_notMem_image_of_ssubset K hD₁ he fun x hx => (hlt x hx).ne, ?_⟩
    refine ⟨insert e D₁, ?_, ?_, Finset.insert_nonempty e D₁, ?_, by rw [Finset.image_insert]⟩
    · rw [Finset.forall_mem_insert]
      exact ⟨⟨(barycentricSubdivision K).nonempty_of_mem_faces he, subset_rfl⟩, fun x hx =>
        ⟨(barycentricSubdivision K).nonempty_of_mem_faces (hD₁.mem_faces hx), (hlt x hx).subset⟩⟩
    · rw [Finset.forall_mem_insert]
      refine ⟨?_, fun x hx => ?_⟩
      · rw [Finset.forall_mem_insert]
        exact ⟨Or.inl subset_rfl, fun y hy => Or.inr (hlt y hy).subset⟩
      · rw [Finset.forall_mem_insert]
        exact ⟨Or.inl (hlt x hx).subset, fun y hy => hD₁.subset_or_subset hx hy⟩
    · rw [Finset.forall_mem_insert]
      exact ⟨(mem_filter_centroid_iff L subset_rfl).mpr hef, fun x hx =>
        (mem_filter_centroid_iff L (hlt x hx).subset).mpr (hL x hx)⟩

open Classical in
theorem geometricLink_derivedNeighborhood_eq_internalJoin {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces)
    (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e)
    (hA : (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces ⊆
        (secondDerived K).faces)
    (hB : (upperLink (barycentricSubdivision K) e).faces ⊆ (secondDerived K).faces)
    (hunion : ∀ s ∈ (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces,
      ∀ t ∈ (upperLink (barycentricSubdivision K) e).faces, s ∪ t ∈ (secondDerived K).faces) :
    SimplicialComplex.geometricLink (derivedNeighborhood K L) {e.centroid ℝ id} =
      internalJoin (secondDerived K)
        (SimplicialComplex.geometricLink
          (faceNeighborhood e ((barycentricSubdivision K).indep he)
            (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id})
        (upperLink (barycentricSubdivision K) e) hA hB hunion := by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton, mem_derivedNeighborhood_faces_iff,
    mem_internalJoin_faces_iff]
  constructor
  · rintro ⟨htne, hct, D, hD, -, hDL, hins⟩
    have heD : e ∈ D := mem_of_centroid_mem_image K hD he (hins ▸ Finset.mem_insert_self _ _)
    have ht : t = (D.erase e).image fun s => s.centroid ℝ id := by
      rw [← image_centroid_erase K hD he, ← hins, Finset.erase_insert hct]
    have hsplit : D.erase e = D.filter (· ⊂ e) ∪ D.filter (e ⊂ ·) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hxe, hx⟩
        rcases hD.subset_or_subset hx heD with h | h
        · exact Or.inl ⟨hx, Finset.ssubset_iff_subset_ne.mpr ⟨h, hxe⟩⟩
        · exact Or.inr ⟨hx, Finset.ssubset_iff_subset_ne.mpr ⟨h, fun h' => hxe h'.symm⟩⟩
      · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
        · exact ⟨h.ne, hx⟩
        · exact ⟨fun h' => h.ne h'.symm, hx⟩
    rw [ht, hsplit, Finset.image_union]
    refine ⟨_, _, ?_, ?_, ?_, rfl⟩
    · rcases (D.filter (· ⊂ e)).eq_empty_or_nonempty with h | h
      · rw [h, Finset.image_empty]
        exact Or.inl rfl
      · refine Or.inr ((mem_geometricLink_faceNeighborhood_iff K L he hef).mpr
          ⟨_, hD.mono (Finset.filter_subset _ _), h, fun x hx => (Finset.mem_filter.mp hx).2,
            fun x hx => hDL x (Finset.mem_of_mem_filter x hx), rfl⟩)
    · rcases (D.filter (e ⊂ ·)).eq_empty_or_nonempty with h | h
      · rw [h, Finset.image_empty]
        exact Or.inl rfl
      · exact Or.inr ⟨_, hD.mono (Finset.filter_subset _ _), h,
          fun x hx => (Finset.mem_filter.mp hx).2, rfl⟩
    · obtain ⟨z, hz⟩ := htne
      rw [ht, hsplit, Finset.image_union] at hz
      rcases Finset.mem_union.mp hz with h | h
      · exact Or.inl ⟨z, h⟩
      · exact Or.inr ⟨z, h⟩
  · rintro ⟨s, r, hs, hr, hne, rfl⟩
    obtain ⟨D₁, hD₁, hlt, hL₁, rfl⟩ : ∃ D₁ : Finset (Finset E),
        IsFlag (barycentricSubdivision K) D₁ ∧ (∀ x ∈ D₁, x ⊂ e) ∧
        (∀ x ∈ D₁, ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ x) ∧
        s = D₁.image fun x => x.centroid ℝ id := by
      rcases hs with rfl | hs
      · exact ⟨∅, ⟨fun x hx => absurd hx (Finset.notMem_empty x),
          fun x hx => absurd hx (Finset.notMem_empty x)⟩, fun x hx => absurd hx (Finset.notMem_empty
              x),
          fun x hx => absurd hx (Finset.notMem_empty x), by rw [Finset.image_empty]⟩
      · obtain ⟨D₁, hD₁, -, hlt, hL₁, rfl⟩ :=
          (mem_geometricLink_faceNeighborhood_iff K L he hef).mp hs
        exact ⟨D₁, hD₁, hlt, hL₁, rfl⟩
    obtain ⟨D₂, hD₂, hgt, rfl⟩ : ∃ D₂ : Finset (Finset E),
        IsFlag (barycentricSubdivision K) D₂ ∧ (∀ x ∈ D₂, e ⊂ x) ∧
        r = D₂.image fun x => x.centroid ℝ id := by
      rcases hr with rfl | hr
      · exact ⟨∅, ⟨fun x hx => absurd hx (Finset.notMem_empty x),
          fun x hx => absurd hx (Finset.notMem_empty x)⟩, fun x hx => absurd hx (Finset.notMem_empty
              x),
          by rw [Finset.image_empty]⟩
      · obtain ⟨D₂, hD₂, -, hgt, rfl⟩ := (mem_upperLink_faces_iff _ _).mp hr
        exact ⟨D₂, hD₂, hgt, rfl⟩
    have hflag : IsFlag (barycentricSubdivision K) (insert e (D₁ ∪ D₂)) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.forall_mem_insert]
        refine ⟨he, fun x hx => ?_⟩
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hD₁.mem_faces hx
        · exact hD₂.mem_faces hx
      · rw [Finset.forall_mem_insert]
        refine ⟨?_, fun x hx => ?_⟩
        · rw [Finset.forall_mem_insert]
          refine ⟨Or.inl subset_rfl, fun y hy => ?_⟩
          rcases Finset.mem_union.mp hy with hy | hy
          · exact Or.inr (hlt y hy).subset
          · exact Or.inl (hgt y hy).subset
        · rw [Finset.forall_mem_insert]
          refine ⟨?_, fun y hy => ?_⟩
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact Or.inl (hlt x hx).subset
            · exact Or.inr (hgt x hx).subset
          · rcases Finset.mem_union.mp hx with hx | hx
            · rcases Finset.mem_union.mp hy with hy | hy
              · exact hD₁.subset_or_subset hx hy
              · exact Or.inl ((hlt x hx).subset.trans (hgt y hy).subset)
            · rcases Finset.mem_union.mp hy with hy | hy
              · exact Or.inr ((hlt y hy).subset.trans (hgt x hx).subset)
              · exact hD₂.subset_or_subset hx hy
    refine ⟨?_, ?_, insert e (D₁ ∪ D₂), hflag, Finset.insert_nonempty _ _, ?_, ?_⟩
    · rcases hne with h | h
      · exact h.mono Finset.subset_union_left
      · exact h.mono Finset.subset_union_right
    · rw [← Finset.image_union]
      exact centroid_notMem_image_of_ssubset K (hflag.mono (Finset.subset_insert _ _)) he
        fun x hx => by
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (hlt x hx).ne
          · exact fun h => (hgt x hx).ne h.symm
    · rw [Finset.forall_mem_insert]
      refine ⟨hef, fun x hx => ?_⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hL₁ x hx
      · obtain ⟨σ, hσ, hσe⟩ := hef
        exact ⟨σ, hσ, (hgt x hx).subset hσe⟩
    · rw [Finset.image_insert, Finset.image_union]

theorem faceNeighborhood_faces_subset_secondDerived {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (f : Finset E) :
    (faceNeighborhood e ((barycentricSubdivision K).indep he) f).faces ⊆ (secondDerived K).faces :=
        by
  rintro u ⟨d, hd, hchain, hne, -, rfl⟩
  exact ⟨d, isFlag_of_subsets_of_chain K he hd hchain, hne, rfl⟩

open Classical in
theorem geometricLink_faceNeighborhood_faces_subset_secondDerived {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) :
    (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces ⊆
      (secondDerived K).faces :=
  (SimplicialComplex.geometricLink_le _ _).trans (faceNeighborhood_faces_subset_secondDerived K he
      _)

open Classical in
theorem union_mem_secondDerived_of_lower_upper {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) :
    ∀ s ∈ (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces,
      ∀ t ∈ (upperLink (barycentricSubdivision K) e).faces, s ∪ t ∈ (secondDerived K).faces := by
  intro s hs t ht
  obtain ⟨D₁, hD₁, hne₁, hlt, -, rfl⟩ := (mem_geometricLink_faceNeighborhood_iff K L he hef).mp hs
  obtain ⟨D₂, hD₂, -, hgt, rfl⟩ := (mem_upperLink_faces_iff _ _).mp ht
  refine ⟨D₁ ∪ D₂, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, hne₁.mono Finset.subset_union_left,
    by rw [Finset.image_union]⟩
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact hD₁.mem_faces hx
    · exact hD₂.mem_faces hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact hD₁.subset_or_subset hx hy
      · exact Or.inl ((hlt x hx).subset.trans (hgt y hy).subset)
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact Or.inr ((hlt y hy).subset.trans (hgt x hx).subset)
      · exact hD₂.subset_or_subset hx hy

open Classical in
theorem disjoint_lower_upper {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) :
    ∀ s ∈ (SimplicialComplex.geometricLink
      (faceNeighborhood e ((barycentricSubdivision K).indep he)
        (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id}).faces,
      ∀ t ∈ (upperLink (barycentricSubdivision K) e).faces, Disjoint s t := by
  intro s hs t ht
  obtain ⟨D₁, hD₁, -, hlt, -, rfl⟩ := (mem_geometricLink_faceNeighborhood_iff K L he hef).mp hs
  obtain ⟨D₂, hD₂, -, hgt, rfl⟩ := (mem_upperLink_faces_iff _ _).mp ht
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz₁
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hz₂
  have hxy := centroid_injOn_barycentricSubdivision K (hD₂.mem_faces hy) (hD₁.mem_faces hx) heq
  exact (hlt x hx).ne (Finset.Subset.antisymm (hlt x hx).subset (hxy ▸ (hgt y hy).subset))

open Classical in
theorem geometricLink_derivedNeighborhood_eq {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) (hef : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) :
    SimplicialComplex.geometricLink (derivedNeighborhood K L) {e.centroid ℝ id} =
      internalJoin (secondDerived K)
        (SimplicialComplex.geometricLink
          (faceNeighborhood e ((barycentricSubdivision K).indep he)
            (e.filter fun v => ∃ σ ∈ L.faces, σ.centroid ℝ id = v)) {e.centroid ℝ id})
        (upperLink (barycentricSubdivision K) e)
        (geometricLink_faceNeighborhood_faces_subset_secondDerived K L he)
        (upperLink_faces_subset _ _) (union_mem_secondDerived_of_lower_upper K L he hef) :=
  geometricLink_derivedNeighborhood_eq_internalJoin K L he hef _ _ _

theorem geometricLink_derivedNeighborhood_eq_of_subset {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces)
    (hsub : ∀ v ∈ e, ∃ σ ∈ L.faces, σ.centroid ℝ id = v) :
    SimplicialComplex.geometricLink (derivedNeighborhood K L) {e.centroid ℝ id} =
      SimplicialComplex.geometricLink (secondDerived K) {e.centroid ℝ id} := by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton, SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨htne, hct, hins⟩
    exact ⟨htne, hct, derivedNeighborhood_faces_subset K L hins⟩
  · rintro ⟨htne, hct, D, hD, hne, hins⟩
    have heD : e ∈ D := mem_of_centroid_mem_image K hD he (hins ▸ Finset.mem_insert_self _ _)
    refine ⟨htne, hct, D, hD, hne, fun e' he' => ?_, hins⟩
    obtain ⟨v, hv⟩ := (barycentricSubdivision K).nonempty_of_mem_faces (hD.mem_faces he')
    rcases hD.subset_or_subset he' heD with h | h
    · obtain ⟨σ, hσ, hσv⟩ := hsub v (h hv)
      exact ⟨σ, hσ, hσv ▸ hv⟩
    · obtain ⟨w, hw⟩ := (barycentricSubdivision K).nonempty_of_mem_faces he
      obtain ⟨σ, hσ, hσw⟩ := hsub w hw
      exact ⟨σ, hσ, hσw ▸ h hw⟩

theorem exists_eq_centroid_of_singleton_mem_barycentricSubdivision {v : E}
    (hv : {v} ∈ (barycentricSubdivision K).faces) : ∃ e ∈ K.faces, e.centroid ℝ id = v := by
  obtain ⟨d, hd, hne, hdv⟩ := hv
  obtain ⟨e, he⟩ := hne
  have : e.centroid ℝ id ∈ ({v} : Finset E) := by
    rw [hdv]
    exact Finset.mem_image_of_mem _ he
  exact ⟨e, hd.mem_faces he, Finset.mem_singleton.mp this⟩

theorem internalJoin_eq_left_of_faces_eq_empty {A B : Geometry.SimplicialComplex ℝ E}
    (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    (hunion : ∀ s ∈ A.faces, ∀ t ∈ B.faces, s ∪ t ∈ K.faces) (hBe : B.faces = ∅) :
    internalJoin K A B hA hB hunion = A := by
  ext u
  rw [mem_internalJoin_faces_iff]
  constructor
  · rintro ⟨s, t, hs, ht, hne, rfl⟩
    rcases ht with rfl | ht
    · rw [Finset.union_empty]
      rcases hs with rfl | hs
      · rcases hne with h | h
        · exact absurd h Finset.not_nonempty_empty
        · exact absurd h Finset.not_nonempty_empty
      · exact hs
    · rw [hBe] at ht
      exact absurd ht (Set.notMem_empty t)
  · intro hu
    exact ⟨u, ∅, Or.inr hu, Or.inl rfl, Or.inl (A.nonempty_of_mem_faces hu), by rw
        [Finset.union_empty]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
