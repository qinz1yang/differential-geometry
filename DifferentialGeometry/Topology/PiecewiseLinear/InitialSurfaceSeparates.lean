/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars

open Set Topology

namespace DifferentialGeometry.Topology

theorem Separates.image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {C H K : Set X} (hs : Separates C H K) :
    Separates (e '' C) (e '' H) (e '' K) := by
  obtain ⟨U, V, hU, hV, hdis, hcov, hHU, hKV⟩ := hs
  refine ⟨e '' U, e '' V, e.isOpenMap U hU, e.isOpenMap V hV,
    (disjoint_image_iff e.injective).mpr hdis, ?_, image_mono hHU, image_mono hKV⟩
  rw [← image_union, hcov, e.image_compl]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem separates_image_interior_of_isEmbedding {N M M' Y : Set E} {f : E → E}
    (hf : IsEmbedding (N.domRestrict f)) (hMN : M ⊆ N) (hM : IsCompact M) (hM' : f '' M = M')
    (hYN : Y ⊆ N) {a b : E} (ha : a ∈ N) (hb : b ∈ N)
    (hsep : Separates (((↑) : interior M → E) ⁻¹' Y) (((↑) : interior M → E) ⁻¹' {a})
      (((↑) : interior M → E) ⁻¹' {b})) :
    Separates (((↑) : interior M' → E) ⁻¹' (f '' Y)) (((↑) : interior M' → E) ⁻¹' {f a})
      (((↑) : interior M' → E) ⁻¹' {f b}) := by
  have hcont : ContinuousOn f N := continuousOn_iff_continuous_domRestrict.mpr hf.continuous
  have hinj : InjOn f N := by
    intro x hx y hy hxy
    have hxy' : N.domRestrict f ⟨x, hx⟩ = N.domRestrict f ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hf.injective hxy')
  have hsub : interior M ⊆ N := interior_subset.trans hMN
  have hIeq : interior M' = f '' interior M := by
    rw [← hM']
    exact interior_image_eq_image_interior_of_isCompact hM (hcont.mono hMN) (hinj.mono hMN)
  have hg : IsEmbedding (fun x : interior M => f x) := hf.comp (IsEmbedding.inclusion hsub)
  have hrange : range (fun x : interior M => f x) = interior M' := by
    rw [hIeq, image_eq_range]
  let e : interior M ≃ₜ interior M' := hg.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have he : ∀ x, (e x : E) = f x := by
    intro x
    change ((hg.toHomeomorph x : range fun x : interior M => f x) : E) = f x
    exact hg.toHomeomorph_apply_coe x
  have hpre : ∀ Z ⊆ N, e '' (((↑) : interior M → E) ⁻¹' Z) =
      ((↑) : interior M' → E) ⁻¹' (f '' Z) := by
    intro Z hZN
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (he x).symm⟩
    · rintro ⟨w, hw, hwy⟩
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hfx : f (e.symm y : E) = f w := by rw [hwy, ← he, e.apply_symm_apply]
      have hxw : (e.symm y : E) = w := hinj (hsub (e.symm y).2) (hZN hw) hfx
      change ((e.symm y : interior M) : E) ∈ Z
      rw [hxw]
      exact hw
  have hsep' := hsep.image_homeomorph e
  rw [hpre Y hYN, hpre {a} (singleton_subset_iff.mpr ha), hpre {b} (singleton_subset_iff.mpr hb),
    image_singleton, image_singleton] at hsep'
  exact hsep'

end Transport

section Closedness

theorem isClosed_preimage_val_of_forall_mem_closure {X : Type*} [TopologicalSpace X]
    {I Z : Set X} (hZ : ∀ z ∈ I, z ∈ closure Z → z ∈ Z) :
    IsClosed (((↑) : I → X) ⁻¹' Z) :=
  isClosed_preimage_val.mpr fun z hz => hZ z hz.1 (closure_mono inter_subset_right hz.2)

theorem mem_of_mem_closure_of_inter_subset_isClosed {X : Type*} [TopologicalSpace X]
    {Z Y V : Set X} {z : X} (hV : IsOpen V) (hzV : z ∈ V) (hY : IsClosed Y) (hYZ : Y ⊆ Z)
    (hZV : Z ∩ V ⊆ Y) (hz : z ∈ closure Z) : z ∈ Z :=
  hYZ (closure_minimal (fun _ hx => hZV ⟨hx.2, hx.1⟩) hY (hV.inter_closure ⟨hzV, hz⟩))

end Closedness

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem separates_initialSurface (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3)) :
    IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' initialSurface S'' T'' P') ∧
    Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}) := by
  have hinner : ∀ i, S'' i ⊆ interior (φ '' S i) := fun i => by
    simpa using (htw.config i).innerSubset 0
  have hcompact : ∀ i, IsCompact (S'' i) := fun i => by
    have hi : IsCombinatorialSolidTorus (S'' i) := by
      simpa using (htw.config i).isPolyhedralSolidTorus 0
    let ψ := Classical.choice hi.1
    have _ : CompactSpace (S'' i) := ψ.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hbd : ∀ i, T'' i = frontier (S'' i) := fun i => by
    simpa using (htw.config i).boundaryEq 0
  have hann : ∀ i, φ '' A i ⊆ interior (S'' i) := fun i => by
    simpa using (htw.config i).annulusImageSubset 0
  have hSφ : ∀ i, S'' i ⊆ φ '' S i := fun i => (hinner i).trans interior_subset
  have hTS : ∀ i, T'' i ⊆ S'' i := fun i => by
    rw [hbd i]
    exact (hcompact i).isClosed.frontier_subset
  have hTc : ∀ i, IsClosed (T'' i) := fun i => by
    rw [hbd i]
    exact isClosed_frontier
  have hTφ : ∀ i, T'' i ⊆ φ '' S i := fun i => (hTS i).trans (hSφ i)
  have hfinite : ∀ z ∈ interior (h '' C u ∪ h '' C v), z ≠ P' →
      ∃ V : Set E3, IsOpen V ∧ z ∈ V ∧ {i | (φ '' S i ∩ V).Nonempty}.Finite := by
    intro z hz hzP
    obtain ⟨U, hU, hfin⟩ := htw.locallyFinite z hz hzP
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU,
      hfin.subset fun i ⟨x, hx⟩ => ⟨x, hx.1, interior_subset hx.2⟩⟩
  set X := initialSurface S'' T'' P' with hX
  set Ns : Set E3 := (⋃ i, S'' i) ∪ {P'}
  have hXmem : ∀ x, x ∈ X ↔ ((∃ i, x ∈ T'' (2 * i)) ∨
      ((∃ i, x ∈ T'' (2 * i + 1)) ∧ ∀ i, x ∉ interior (S'' (2 * i)))) ∨ x = P' := by
    intro x
    simp only [hX, initialSurface, mem_union, mem_sdiff, mem_iUnion, mem_singleton_iff, not_exists]
  have hPX : P' ∈ X := (hXmem P').mpr (Or.inr rfl)
  have hXNs : X ⊆ Ns := by
    intro x hx
    rcases (hXmem x).mp hx with (⟨i, hx⟩ | ⟨⟨i, hx⟩, -⟩) | hx
    · exact Or.inl (mem_iUnion.mpr ⟨2 * i, hTS _ hx⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨2 * i + 1, hTS _ hx⟩)
    · exact Or.inr hx
  have hXc : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' X) := by
    refine isClosed_preimage_val_of_forall_mem_closure fun z hz hzc => ?_
    by_cases hzP : z = P'
    · rw [hzP]
      exact hPX
    obtain ⟨V, hV, hzV, hfin⟩ := hfinite z hz hzP
    set F := {i | (φ '' S i ∩ V).Nonempty}
    have hF2 : ((fun i : ℤ => 2 * i) ⁻¹' F).Finite :=
      hfin.preimage fun a _ b _ hab => by
        have hab' : 2 * a = 2 * b := hab
        omega
    have hF21 : ((fun i : ℤ => 2 * i + 1) ⁻¹' F).Finite :=
      hfin.preimage fun a _ b _ hab => by
        have hab' : 2 * a + 1 = 2 * b + 1 := hab
        omega
    let Y : Set E3 := (⋃ i ∈ (fun i : ℤ => 2 * i) ⁻¹' F, T'' (2 * i)) ∪
      ((⋃ i ∈ (fun i : ℤ => 2 * i + 1) ⁻¹' F, T'' (2 * i + 1)) \
        ⋃ i, interior (S'' (2 * i))) ∪ {P'}
    have hYc : IsClosed Y :=
      ((hF2.isClosed_biUnion fun i _ => hTc _).union
        ((hF21.isClosed_biUnion fun i _ => hTc _).sdiff
          (isOpen_iUnion fun i => isOpen_interior))).union isClosed_singleton
    have hYX : Y ⊆ X := by
      intro x hx
      rw [hXmem]
      rcases hx with (hx | ⟨hx, hxn⟩) | hx
      · obtain ⟨i, -, hx⟩ := mem_iUnion₂.mp hx
        exact Or.inl (Or.inl ⟨i, hx⟩)
      · obtain ⟨i, -, hx⟩ := mem_iUnion₂.mp hx
        exact Or.inl (Or.inr ⟨⟨i, hx⟩, fun k hk => hxn (mem_iUnion.mpr ⟨k, hk⟩)⟩)
      · exact Or.inr hx
    have hXV : X ∩ V ⊆ Y := by
      rintro x ⟨hx, hxV⟩
      rcases (hXmem x).mp hx with (⟨i, hx⟩ | ⟨⟨i, hx⟩, hxn⟩) | hx
      · exact Or.inl (Or.inl (mem_biUnion (show i ∈ (fun i : ℤ => 2 * i) ⁻¹' F from
          ⟨x, hTφ _ hx, hxV⟩) hx))
      · refine Or.inl (Or.inr ⟨mem_biUnion (show i ∈ (fun i : ℤ => 2 * i + 1) ⁻¹' F from
          ⟨x, hTφ _ hx, hxV⟩) hx, fun hx' => ?_⟩)
        obtain ⟨k, hk⟩ := mem_iUnion.mp hx'
        exact hxn k hk
      · exact Or.inr hx
    exact mem_of_mem_closure_of_inter_subset_isClosed hV hzV hYc hYX hXV hzc
  have hNsc : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns) := by
    refine isClosed_preimage_val_of_forall_mem_closure fun z hz hzc => ?_
    by_cases hzP : z = P'
    · rw [hzP]
      exact Or.inr rfl
    obtain ⟨V, hV, hzV, hfin⟩ := hfinite z hz hzP
    let Y : Set E3 := (⋃ i ∈ {i | (φ '' S i ∩ V).Nonempty}, S'' i) ∪ {P'}
    have hYc : IsClosed Y :=
      (hfin.isClosed_biUnion fun i _ => (hcompact i).isClosed).union isClosed_singleton
    have hYNs : Y ⊆ Ns := union_subset_union (iUnion₂_subset_iUnion _ _) subset_rfl
    have hNsV : Ns ∩ V ⊆ Y := by
      rintro x ⟨hx | hx, hxV⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact Or.inl (mem_biUnion (show i ∈ {i | (φ '' S i ∩ V).Nonempty} from
          ⟨x, hSφ i hi, hxV⟩) hi)
      · exact Or.inr hx
    exact mem_of_mem_closure_of_inter_subset_isClosed hV hzV hYc hYNs hNsV hzc
  have hcard : ({u, v} : Finset E3).card = 2 := Finset.card_pair huv
  have hCu := ht.dualCell_subset hu
  have hCv := ht.dualCell_subset hv
  have hDC : D {u, v} = C u ∩ C v :=
    (ht.inter_eq_of_mem_faces hu hv huv he (Finset.mem_insert_self u {v})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))).symm
  have hDN : D {u, v} ⊆ N := by
    rw [hDC]
    exact inter_subset_left.trans hCu
  have hDbdD : Dbd {u, v} ⊆ D {u, v} := by
    rw [← ht.splitProper _ he hcard]
    exact inter_subset_left
  have hsep₀ := separates_image_interior_of_isEmbedding ht.isEmbedding (union_subset hCu hCv)
    ((ht.dualBall u hu).isPolyhedron.isCompact.union (ht.dualBall v hv).isPolyhedron.isCompact)
    (image_union h (C u) (C v)) (sdiff_subset.trans hDN) (hCu (ht.mem_dualCell hu))
    (hCv (ht.mem_dualCell hv)) (ht.splitSeparates u hu v hv huv he)
  have hspace : K.space ⊆ N := subset_of_mem_nhdsSet ht.isNeighborhood
  have hmid : ({u, v} : Finset E3).centroid ℝ id ∈ K.space :=
    K.convexHull_subset_space he
      (({u, v} : Finset E3).centroid_mem_convexHull (K.nonempty_of_mem_faces he))
  have hvertN : ∀ a ∈ K.vertices, a ∈ N :=
    fun a ha => hspace (Geometry.SimplicialComplex.vertices_subset_space ha)
  have hP'ne : ∀ a ∈ K.vertices, h a ≠ P' := by
    intro a ha hap
    rw [hP'] at hap
    exact vertex_ne_centroid_of_card_eq_two he hcard ha (ht.injOn (hvertN a ha) (hspace hmid) hap)
  have hnotNs : ∀ a ∈ K.vertices, a = u ∨ a = v → h a ∉ Ns := by
    rintro a ha hauv (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine disjoint_left.mp (havoid i) (hSφ i hi) ?_
      rcases hauv with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    · exact hP'ne a ha hx
  have hX₀Ns : h '' (D {u, v} \ Dbd {u, v}) ⊆ Ns := by
    rintro _ ⟨x, ⟨hxD, hxb⟩, rfl⟩
    by_cases hxP : h x = P'
    · exact Or.inr hxP
    · have hmem : h x ∈ h '' D {u, v} \ (h '' Dbd {u, v} ∪ {P'}) := by
        refine ⟨⟨x, hxD, rfl⟩, ?_⟩
        rintro (⟨w, hw, hwx⟩ | hx')
        · exact hxb (ht.injOn (hDN (hDbdD hw)) (hDN hxD) hwx ▸ hw)
        · exact hxP hx'
      rw [← htw.annuliEq] at hmem
      obtain ⟨y, hy, hyx⟩ := hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact Or.inl (mem_iUnion.mpr ⟨i, interior_subset (hann i ⟨y, hi, hyx⟩)⟩)
  have hout : ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' (h '' (D {u, v} \ Dbd {u, v})) \
      ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns =
      ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' X \
        ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns := by
    rw [sdiff_eq_empty.mpr (preimage_mono hX₀Ns), sdiff_eq_empty.mpr (preimage_mono hXNs)]
  have hfront : frontier (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns) ⊆
      ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' X := by
    intro z hz
    have hzNs : (z : E3) ∈ Ns := hNsc.frontier_subset hz
    have key : ∀ O : Set E3, IsOpen O → O ⊆ Ns → (z : E3) ∉ O := fun O hO hONs hzO =>
      hz.2 (interior_maximal (preimage_mono hONs) (hO.preimage continuous_subtype_val) hzO)
    have hint : ∀ i, (z : E3) ∉ interior (S'' i) := fun i =>
      key _ isOpen_interior (interior_subset.trans
        ((subset_iUnion S'' i).trans subset_union_left))
    rcases hzNs with hzS | hzP
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hzS
      have hzT : (z : E3) ∈ T'' j := by
        rw [hbd j]
        exact ⟨subset_closure hj, hint j⟩
      obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
      · exact (hXmem _).mpr (Or.inl (Or.inl ⟨k, hzT⟩))
      · exact (hXmem _).mpr (Or.inl (Or.inr ⟨⟨k, hzT⟩, fun i hi => hint _ hi⟩))
    · exact (hXmem _).mpr (Or.inr hzP)
  have hHNs : ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u} ⊆
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns)ᶜ := by
    intro z hz hzNs
    rw [mem_preimage, mem_singleton_iff] at hz
    rw [mem_preimage, hz] at hzNs
    exact hnotNs u hu (Or.inl rfl) hzNs
  have hKNs : ((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v} ⊆
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Ns)ᶜ := by
    intro z hz hzNs
    rw [mem_preimage, mem_singleton_iff] at hz
    rw [mem_preimage, hz] at hzNs
    exact hnotNs v hv (Or.inr rfl) hzNs
  exact ⟨hXc, hsep₀.of_frontier_subset_replacement hXc hNsc hout hfront hHNs hKNs⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
