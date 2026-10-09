/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodSurgery
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeOuterTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_sdiff_eq_of_sdiff_eq {Y : Type*} [TopologicalSpace Y] {s t Z : Set Y}
    (hZ : IsClosed Z) (h : s \ Z = t \ Z) : frontier s \ Z = frontier t \ Z := by
  have h' : s ∩ Zᶜ = t ∩ Zᶜ := h
  change frontier s ∩ Zᶜ = frontier t ∩ Zᶜ
  rw [← frontier_inter_open_inter hZ.isOpen_compl, h', frontier_inter_open_inter hZ.isOpen_compl]

section SingleTrace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsHandleDecompositionOfTube.interior_pseudoCell_subset_interior
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) : Eint e ⊆ interior N' := by
  have hpc := hd.pseudoCell e he hcard
  obtain ⟨ψ⟩ := hpc.isOpenCell
  have hconn : IsPreconnected (Eint e) := by
    have : PreconnectedSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball 0 1).isPreconnected
    have hr := isPreconnected_range (continuous_subtype_val.comp ψ.symm.continuous)
    rwa [range_comp, ψ.symm.surjective.range_eq, image_univ, Subtype.range_coe] at hr
  have hPK : h (e.centroid ℝ id) ∈ interior N' := hd.tube.image_space_subset_interior
    ⟨_, K.convexHull_subset_space he (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he)),
      rfl⟩
  have hfr : Disjoint (Eint e) (frontier N') := by
    rw [Set.disjoint_left]
    intro y hyE hyfr
    have hyEc : y ∈ Ec e := by
      rw [hpc.carrierEq]
      exact Or.inl hyE
    have hyB : y ∈ Ebd e := by
      rw [← hd.rimFrontier e he hcard]
      exact ⟨hyEc, hyfr⟩
    exact Set.disjoint_left.mp hpc.disjointRim hyE hyB
  exact hconn.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure)
    (fun y hy => by
      by_cases hyi : y ∈ interior N'
      · exact Or.inl hyi
      · exact Or.inr fun hycl => Set.disjoint_left.mp hfr hy ⟨hycl, hyi⟩)
    ⟨_, hpc.centerMem, hPK⟩

theorem IsPolyhedralTubeNeighborhood.exists_singlePolygonTrace_edge
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) :
    ∃ XK' : Geometry.SimplicialComplex ℝ E3,
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
        (IsPLSphere 1 (Ec e ∩ frontier XK'.space) ∧ ∃ DJint : Set E3,
          IsTopologicalCellWithInterior 2 (Ec e ∩ XK'.space) DJint ∧
            (Ec e ∩ XK'.space) \ DJint = Ec e ∩ frontier XK'.space ∧
              h (e.centroid ℝ id) ∈ DJint) ∧
        ∀ f ∈ K.faces, f.card = 2 → f ≠ e →
          Ec f ∩ XK'.space = Ec f ∩ XK.space ∧
            Ec f ∩ frontier XK'.space = Ec f ∩ frontier XK.space := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hXcpt : IsCompact XK.space := (isPolyhedron_space XK).isCompact
  have ht := hd.tube
  have hpc := hd.pseudoCell e he hcard
  have hEcc : IsClosed (Ec e) := hpc.isClosed
  have hEEc : Eint e ⊆ Ec e := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hEN' := hd.interior_pseudoCell_subset_interior he hcard
  have hKint : h '' K.space ⊆ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
  have hPint : h (e.centroid ℝ id) ∈ interior XK.space := hKint
    ⟨_, K.convexHull_subset_space he (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he)),
      rfl⟩
  have hEcX : Ec e ∩ XK.space ⊆ Eint e := by
    rintro y ⟨hyEc, hyX⟩
    rw [hpc.carrierEq] at hyEc
    exact hyEc.resolve_right fun hyB =>
      Set.disjoint_left.mp (h2.rimDisjoint e he hcard) hyB hyX
  obtain ⟨J, Din, O, hJ, hJT, hDinE, hDJ, ⟨W, hW, hDinW⟩, hPD, hcell, hO, hJO, hOloc⟩ :=
    h2.exists_outerTrace hd he hcard
  have hJX : J ⊆ XK.space := fun y hy => hXc.frontier_subset (hJT hy).2
  have hJE : J ⊆ Eint e := fun y hy => hEcX ⟨(hJT hy).1, hJX hy⟩
  have hJc : IsCompact J := hJ.isPolyhedron.isCompact
  have hFc : IsCompact (Din ∪ J) := by
    obtain ⟨φ, -⟩ := hcell
    have : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
    have : CompactSpace (Din ∪ J : Set E3) := φ.compactSpace
    exact isCompact_iff_compactSpace.mpr this
  have hDinWsub : Din ⊆ W := fun y hy => by
    rw [hDinW] at hy
    exact hy.1
  set R := Din \ interior XK.space with hRdef
  set R' := (Eint e ∩ XK.space) \ (Din ∪ J) with hR'def
  have hRO : ∀ y ∈ R, y ∉ O := by
    rintro y ⟨hyD, hyi⟩ hyO
    have hyE := hDinE hyD
    have hyX : y ∈ XK.space := ((hOloc y ⟨hyO, hyE⟩).1).mpr (Or.inl hyD)
    have hyfr : y ∈ frontier XK.space := ⟨subset_closure hyX, hyi⟩
    exact Set.disjoint_left.mp hDJ hyD (((hOloc y ⟨hyO, hyE⟩).2).mp hyfr)
  have hR'O : ∀ y ∈ R', y ∉ O := by
    rintro y ⟨⟨hyE, hyX⟩, hyF⟩ hyO
    exact hyF (((hOloc y ⟨hyO, hyE⟩).1).mp hyX)
  have hRc : IsCompact R := by
    have heq : R = ((Din ∪ J) \ interior XK.space) \ O := by
      ext y
      constructor
      · intro hy
        exact ⟨⟨Or.inl hy.1, hy.2⟩, hRO y hy⟩
      · rintro ⟨⟨hyD | hyJ, hyi⟩, hyO⟩
        · exact ⟨hyD, hyi⟩
        · exact (hyO (hJO hyJ)).elim
    rw [heq]
    exact (hFc.diff isOpen_interior).diff hO
  have hR'c : IsCompact R' := by
    have heq : R' = ((Ec e ∩ XK.space) \ O) \ W := by
      ext y
      constructor
      · intro hy
        refine ⟨⟨⟨hEEc hy.1.1, hy.1.2⟩, hR'O y hy⟩, fun hyW => hy.2 (Or.inl ?_)⟩
        rw [hDinW]
        exact ⟨hyW, hy.1.1⟩
      · rintro ⟨⟨hyEX, hyO⟩, hyW⟩
        refine ⟨⟨hEcX hyEX, hyEX.2⟩, ?_⟩
        rintro (hyD | hyJ)
        · exact hyW (hDinWsub hyD)
        · exact hyO (hJO hyJ)
    rw [heq]
    exact ((hXcpt.inter_left hEcc).diff hO).diff hW
  have hRR'E : R ∪ R' ⊆ Eint e \ {h (e.centroid ℝ id)} := by
    rintro y (hy | hy)
    · refine ⟨hDinE hy.1, fun hyP => hy.2 ?_⟩
      rw [mem_singleton_iff.mp hyP]
      exact hPint
    · refine ⟨hy.1.1, fun hyP => hy.2 (Or.inl ?_)⟩
      rw [mem_singleton_iff.mp hyP]
      exact hPD
  obtain ⟨G, hG, hRR'G, hGE, hGnhds⟩ :=
    hpc.regular.exists_isPolyhedron_neighborhood_of_isCompact (hRc.union hR'c) hRR'E
  choose u hu using fun (x : E3) (hx : x ∈ R ∪ R') => mem_nhdsWithin.mp (hGnhds x hx)
  let V₀ : Set E3 := ⋃ x, ⋃ hx : x ∈ R ∪ R', u x hx
  have hV₀o : IsOpen V₀ := isOpen_iUnion fun x => isOpen_iUnion fun hx => (hu x hx).1
  have hV₀R : R ∪ R' ⊆ V₀ := fun x hx => mem_iUnion₂.mpr ⟨x, hx, (hu x hx).2.1⟩
  have hV₀G : V₀ ∩ (Eint e \ {h (e.centroid ℝ id)}) ⊆ G := by
    rintro y ⟨hyV, hyS⟩
    obtain ⟨x, hx, hyu⟩ := mem_iUnion₂.mp hyV
    exact (hu x hx).2.2 ⟨hyu, hyS⟩
  let oth : Finset (Finset E3) := (ht.facesFinite.toFinset.filter fun f => f.card = 2).erase e
  have hoth : ∀ f, f ∈ oth ↔ f ∈ K.faces ∧ f.card = 2 ∧ f ≠ e := by
    intro f
    simp only [oth, Finset.mem_erase, Finset.mem_filter, Set.Finite.mem_toFinset]
    tauto
  have hEbdc : IsClosed (Ebd e) := by
    rw [← hd.rimFrontier e he hcard]
    exact hEcc.inter isClosed_frontier
  let C₁ : Set E3 :=
    Ebd e ∪ {h (e.centroid ℝ id)} ∪ J ∪ (⋃ f ∈ oth, Ec f) ∪ h '' K.space
  have hC₁ : IsClosed C₁ :=
    (((hEbdc.union isClosed_singleton).union hJc.isClosed).union
      (isClosed_biUnion_finset fun f hf =>
        (hd.pseudoCell f ((hoth f).mp hf).1 ((hoth f).mp hf).2.1).isClosed)).union
      ht.isCompact_image_space.isClosed
  let U : Set E3 := V₀ ∩ interior N' ∩ C₁ᶜ
  have hUo : IsOpen U := (hV₀o.inter isOpen_interior).inter hC₁.isOpen_compl
  have hRR'Ec : R ∪ R' ⊆ Ec e := fun y hy => hEEc (hRR'E hy).1
  have hRR'U : R ∪ R' ⊆ U := by
    intro y hy
    refine ⟨⟨hV₀R hy, hEN' (hRR'E hy).1⟩, ?_⟩
    rintro ((((hyB | hyP) | hyJ) | hyf) | hyK)
    · exact Set.disjoint_left.mp hpc.disjointRim (hRR'E hy).1 hyB
    · exact (hRR'E hy).2 hyP
    · rcases hy with hy | hy
      · exact hRO y hy (hJO hyJ)
      · exact hR'O y hy (hJO hyJ)
    · obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp hyf
      obtain ⟨hfK, hfc, hfe⟩ := (hoth f).mp hf
      exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e he hcard f hfK hfc (Ne.symm hfe))
        (hRR'Ec hy) hyf
    · have hmeet : y ∈ Ec e ∩ h '' K.space := ⟨hRR'Ec hy, hyK⟩
      rw [hd.meetsGraph e he hcard] at hmeet
      exact (hRR'E hy).2 hmeet
  have hUEc : U ∩ Ec e ⊆ G := by
    rintro y ⟨⟨⟨hyV, -⟩, hyC⟩, hyEc⟩
    rw [hpc.carrierEq] at hyEc
    have hyE : y ∈ Eint e :=
      hyEc.resolve_right fun hyB => hyC (Or.inl (Or.inl (Or.inl (Or.inl hyB))))
    exact hV₀G ⟨hyV, hyE, fun hyP => hyC (Or.inl (Or.inl (Or.inl (Or.inr hyP))))⟩
  have hUJ : ∀ y ∈ U, y ∉ J := fun y hy hyJ => hy.2 (Or.inl (Or.inl (Or.inr hyJ)))
  have hUf : ∀ f ∈ K.faces, f.card = 2 → f ≠ e → ∀ y ∈ U, y ∉ Ec f :=
    fun f hf hc hfe y hy hyf =>
      hy.2 (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f, (hoth f).mpr ⟨hf, hc, hfe⟩, hyf⟩)))
  have hUK : ∀ y ∈ U, y ∉ h '' K.space := fun y hy hyK => hy.2 (Or.inr hyK)
  have hRW : R = W ∩ (G \ interior XK.space) := by
    ext y
    constructor
    · intro hy
      exact ⟨hDinWsub hy.1, hRR'G (Or.inl hy), hy.2⟩
    · rintro ⟨hyW, hyG, hyi⟩
      refine ⟨?_, hyi⟩
      rw [hDinW]
      exact ⟨hyW, (hGE hyG).1⟩
  have hR'W : R' = (Din ∪ J)ᶜ ∩ (G ∩ XK.space) := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.2, hRR'G (Or.inr hy), hy.1.2⟩
    · rintro ⟨hyF, hyG, hyX⟩
      exact ⟨⟨(hGE hyG).1, hyX⟩, hyF⟩
  have hRR' : Disjoint R R' := Set.disjoint_left.mpr fun y hy hy' => hy'.2 (Or.inl hy.1)
  obtain ⟨X₂, hX₂fin, hX₂m, ⟨Z, hZ, hZU, hZeq⟩, hGX₂, hint⟩ :=
    h2.isManifold.exists_add_remove_of_eq_inter finrank_euclideanSpace_fin hG hUo hW hRW hRc
      (fun y hy => hRR'U (Or.inl hy)) hFc.isClosed.isOpen_compl hR'W hR'c
      (fun y hy => hRR'U (Or.inr hy)) hRR'
  have : Finite X₂.faces := hX₂fin.to_subtype
  have hX₂c : IsClosed X₂.space := (isPolyhedron_space X₂).isClosed
  have hZX : ∀ y ∉ Z, y ∈ X₂.space ↔ y ∈ XK.space := by
    intro y hyZ
    constructor
    · intro hy
      have hy' : y ∈ X₂.space \ Z := ⟨hy, hyZ⟩
      rw [hZeq] at hy'
      exact hy'.1
    · intro hy
      have hy' : y ∈ XK.space \ Z := ⟨hy, hyZ⟩
      rw [← hZeq] at hy'
      exact hy'.1
  have hfrZ : ∀ y ∉ Z, y ∈ frontier X₂.space ↔ y ∈ frontier XK.space := by
    have hfr := frontier_sdiff_eq_of_sdiff_eq hZ hZeq
    intro y hyZ
    constructor
    · intro hy
      have hy' : y ∈ frontier X₂.space \ Z := ⟨hy, hyZ⟩
      rw [hfr] at hy'
      exact hy'.1
    · intro hy
      have hy' : y ∈ frontier XK.space \ Z := ⟨hy, hyZ⟩
      rw [← hfr] at hy'
      exact hy'.1
  have hintZ : ∀ y ∈ interior XK.space, y ∉ Z → y ∈ interior X₂.space := by
    intro y hyi hyZ
    refine mem_interior.mpr ⟨interior XK.space ∩ Zᶜ, fun z hz => ?_,
      isOpen_interior.inter hZ.isOpen_compl, ⟨hyi, hyZ⟩⟩
    exact (hZX z hz.2).mpr (interior_subset hz.1)
  have hX₂N' : X₂.space ⊆ interior N' := by
    intro y hy
    by_cases hyZ : y ∈ Z
    · exact (hZU hyZ).1.2
    · exact h2.subsetInterior ((hZX y hyZ).mp hy)
  have hR'Z : R' ⊆ Z := by
    intro y hy
    by_contra hyZ
    have hmem : y ∈ G ∩ X₂.space := ⟨hRR'G (Or.inr hy), (hZX y hyZ).mpr hy.1.2⟩
    rw [hGX₂] at hmem
    exact hmem.2 hy
  have hmemEc : ∀ y ∈ Ec e, y ∈ X₂.space ↔ y ∈ Din ∪ J := by
    intro y hyEc
    by_cases hyZ : y ∈ Z
    · have hyG : y ∈ G := hUEc ⟨hZU hyZ, hyEc⟩
      have hyE : y ∈ Eint e := (hGE hyG).1
      constructor
      · intro hy
        have hy' : y ∈ G ∩ X₂.space := ⟨hyG, hy⟩
        rw [hGX₂] at hy'
        rcases hy'.1 with ⟨-, hyX⟩ | hyR
        · by_contra hyF
          exact hy'.2 ⟨⟨hyE, hyX⟩, hyF⟩
        · exact Or.inl hyR.1
      · intro hyF
        have hmem : y ∈ (G ∩ XK.space ∪ R) \ R' := by
          refine ⟨?_, fun h => h.2 hyF⟩
          rcases hyF with hyD | hyJ
          · by_cases hyi : y ∈ interior XK.space
            · exact Or.inl ⟨hyG, interior_subset hyi⟩
            · exact Or.inr ⟨hyD, hyi⟩
          · exact Or.inl ⟨hyG, hJX hyJ⟩
        rw [← hGX₂] at hmem
        exact hmem.2
    · rw [hZX y hyZ]
      constructor
      · intro hyX
        by_contra hyF
        exact hyZ (hR'Z ⟨⟨hEcX ⟨hyEc, hyX⟩, hyX⟩, hyF⟩)
      · rintro (hyD | hyJ)
        · by_cases hyi : y ∈ interior XK.space
          · exact interior_subset hyi
          · have hmem : y ∈ (G ∩ XK.space ∪ R) \ R' :=
              ⟨Or.inr ⟨hyD, hyi⟩, fun h => h.2 (Or.inl hyD)⟩
            rw [← hGX₂] at hmem
            exact (hZX y hyZ).mp hmem.2
        · exact hJX hyJ
  have hDinint : ∀ y ∈ Din, y ∈ interior X₂.space := by
    intro y hyD
    have hyR' : y ∉ R' := fun h => h.2 (Or.inl hyD)
    by_cases hyi : y ∈ interior XK.space
    · by_cases hyZ : y ∈ Z
      · exact hint y (hUEc ⟨hZU hyZ, hEEc (hDinE hyD)⟩) (Or.inl hyi) hyR'
      · exact hintZ y hyi hyZ
    · exact hint y (hRR'G (Or.inl ⟨hyD, hyi⟩)) (Or.inr ⟨hyD, hyi⟩) hyR'
  have hEcfr : Ec e ∩ frontier X₂.space = J := by
    ext y
    constructor
    · rintro ⟨hyEc, hyfr⟩
      rcases (hmemEc y hyEc).mp (hX₂c.frontier_subset hyfr) with hyD | hyJ
      · exact (hyfr.2 (hDinint y hyD)).elim
      · exact hyJ
    · intro hyJ
      have hyZ : y ∉ Z := fun hyZ => hUJ y (hZU hyZ) hyJ
      exact ⟨(hJT hyJ).1, (hfrZ y hyZ).mpr (hJT hyJ).2⟩
  have hEcX₂ : Ec e ∩ X₂.space = Din ∪ J := by
    ext y
    constructor
    · rintro ⟨hyEc, hy⟩
      exact (hmemEc y hyEc).mp hy
    · intro hy
      have hyEc : y ∈ Ec e := hEEc (hy.elim (fun h => hDinE h) (fun h => hJE h))
      exact ⟨hyEc, (hmemEc y hyEc).mpr hy⟩
  refine ⟨X₂, ⟨hX₂fin, hX₂m, ?_, hX₂N', ?_, ?_⟩, ⟨?_, Din, ?_, ?_, hPD⟩, ?_⟩
  · exact subset_interior_iff_mem_nhdsSet.mp fun y hy =>
      hintZ y (hKint hy) fun hyZ => hUK y (hZU hyZ) hy
  · intro f hf hcardf
    refine Set.disjoint_left.mpr fun y hyB hyX => ?_
    rw [← hd.rimFrontier f hf hcardf] at hyB
    exact hyB.2.2 (hX₂N' hyX)
  · intro f hf hcardf y hy
    have hyZ : y ∉ Z := by
      intro hyZ
      by_cases hfe : f = e
      · rw [hfe, hEcfr] at hy
        exact hUJ y (hZU hyZ) hy
      · exact hUf f hf hcardf hfe y (hZU hyZ) hy.1
    have hyfrX : y ∈ frontier XK.space := (hfrZ y hyZ).mp hy.2
    refine (h2.crossing f hf hcardf y ⟨hy.1, hyfrX⟩).congr
      (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    filter_upwards [hZ.isOpen_compl.mem_nhds hyZ] with z hz
    exact (hfrZ z hz).symm
  · rw [hEcfr]
    exact hJ
  · rw [hEcX₂]
    exact hcell
  · rw [hEcX₂, hEcfr, Set.union_sdiff_left]
    exact hDJ.symm.sdiff_eq_left
  · intro f hf hcardf hfe
    have hfZ : ∀ y ∈ Ec f, y ∉ Z := fun y hy hyZ => hUf f hf hcardf hfe y (hZU hyZ) hy
    constructor
    · ext y
      constructor
      · rintro ⟨hy, hyX⟩
        exact ⟨hy, (hZX y (hfZ y hy)).mp hyX⟩
      · rintro ⟨hy, hyX⟩
        exact ⟨hy, (hZX y (hfZ y hy)).mpr hyX⟩
    · ext y
      constructor
      · rintro ⟨hy, hyfr⟩
        exact ⟨hy, (hfrZ y (hfZ y hy)).mp hyfr⟩
      · rintro ⟨hy, hyfr⟩
        exact ⟨hy, (hfrZ y (hfZ y hy)).mpr hyfr⟩

end SingleTrace

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_hasSinglePolygonTraces
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) :
    ∃ XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space := by
  classical
  let edges : Finset (Finset (EuclideanSpace ℝ (Fin 3))) :=
    hd.tube.facesFinite.toFinset.filter fun e => e.card = 2
  have hedges : ∀ e, e ∈ edges ↔ e ∈ K.faces ∧ e.card = 2 := fun e => by
    simp only [edges, Finset.mem_filter, Set.Finite.mem_toFinset]
  have key : ∀ S : Finset (Finset (EuclideanSpace ℝ (Fin 3))), S ⊆ edges →
      ∃ XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
        IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧ ∀ e ∈ S,
          IsPLSphere 1 (Ec e ∩ frontier XK'.space) ∧
            ∃ DJint : Set (EuclideanSpace ℝ (Fin 3)),
              IsTopologicalCellWithInterior 2 (Ec e ∩ XK'.space) DJint ∧
                (Ec e ∩ XK'.space) \ DJint = Ec e ∩ frontier XK'.space ∧
                  h (e.centroid ℝ id) ∈ DJint := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨XK, h2, fun e he => (Finset.notMem_empty e he).elim⟩
    | insert e S heS ih =>
      intro hsub
      obtain ⟨X₁, hX₁, hS⟩ := ih ((Finset.subset_insert e S).trans hsub)
      obtain ⟨heK, hcard⟩ := (hedges e).mp (hsub (Finset.mem_insert_self e S))
      obtain ⟨X₂, hX₂, hspt, hother⟩ := hX₁.exists_singlePolygonTrace_edge hd heK hcard
      refine ⟨X₂, hX₂, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hfS
      · exact hspt
      · have hfe : f ≠ e := fun hfe => heS (hfe ▸ hfS)
        obtain ⟨hfK, hfcard⟩ := (hedges f).mp (hsub (Finset.mem_insert_of_mem hfS))
        obtain ⟨hX, hfr⟩ := hother f hfK hfcard hfe
        rw [hX, hfr]
        exact hS f hfS
  obtain ⟨XK', hXK', hall⟩ := key edges subset_rfl
  exact ⟨XK', hXK', fun e he hcard => hall e ((hedges e).mpr ⟨he, hcard⟩)⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
