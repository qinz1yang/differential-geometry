/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBalls

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Rim

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] {M₁ : Type u}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}
  {𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U}

open Classical in
theorem mem_biUnion_convexHull_erase_of_map_mem_graphSkeletonSpace
    (s : Section34SimplexIndex 𝒦 3) {x : Ea} (hx𝒦 : x ∈ 𝒦.complex.space)
    (hxs : x ∈ convexHull ℝ (s.1 : Set Ea)) (hxg : 𝒦.map x ∈ graphSkeletonSpace 𝒦) :
    x ∈ ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea) := by
  have hxg' : 𝒦.map x ∈ ⋃ t ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2},
      simplexBody 𝒦 t := hxg
  obtain ⟨t, ⟨ht, htc⟩, y, hy, hyx⟩ := mem_iUnion₂.mp hxg'
  have hyx' : y = x := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space ht hy) hx𝒦 hyx
  subst hyx'
  have hmem := 𝒦.complex.inter_subset_convexHull s.2.1 ht ⟨hxs, hy⟩
  obtain ⟨u, hus, hut⟩ : ∃ u ∈ s.1, u ∉ t := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.card_le_card (show s.1 ⊆ t from hcon)
    have h2 := s.2.2
    omega
  refine mem_iUnion₂.mpr ⟨u, hus, convexHull_mono ?_ hmem⟩
  rintro z ⟨hzs, hzt⟩
  rw [Finset.coe_erase]
  exact ⟨hzs, fun hzu => hut ((mem_singleton_iff.mp hzu) ▸ hzt)⟩

open Classical in
theorem map_mem_graphSkeletonSpace_of_mem_biUnion_convexHull_erase
    (s : Section34SimplexIndex 𝒦 3) {x : Ea}
    (hx : x ∈ ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)) :
    𝒦.map x ∈ graphSkeletonSpace 𝒦 := by
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
  have hcard : (s.1.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hu, s.2.2]
  change 𝒦.map x ∈ ⋃ t ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2}, simplexBody 𝒦 t
  refine mem_iUnion₂.mpr ⟨s.1.erase u, ⟨𝒦.complex.down_closed s.2.1 (Finset.erase_subset u s.1)
    (Finset.card_pos.mp (by omega)), hcard.le⟩, x, hxu, rfl⟩

end Rim

section FaceTorus

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {f₁ : M₁ → M₂}

theorem isCombinatorialSolidTorus_image_section34FaceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3)
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source) :
    IsCombinatorialSolidTorus (c '' section34FaceTorus (section34VertexBallImage src f₁) s) := by
  classical
  obtain ⟨-, hsubdiv, hmap, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvertexEdge,
    hends, -, -⟩ := id hcut
  set R : Set Ea := ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)
  have hRs : R ⊆ convexHull ℝ (s.1 : Set Ea) :=
    iUnion₂_subset fun u _ => convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u s.1))
  have hs𝒦 : convexHull ℝ (s.1 : Set Ea) ⊆ 𝒦.complex.space :=
    𝒦.complex.convexHull_subset_space s.2.1
  have hsp' : 𝒦'.complex.space = 𝒦.complex.space := hsubdiv.1
  have hRsph : IsPLSphere 1 R := isPLSphere_biUnion_erase s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hL₀ : (restrict 𝒦.complex R).space = R := by
    refine Subset.antisymm (restrict_space_subset _ _) fun x hx => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hcard : (s.1.erase u).card = 2 := by rw [Finset.card_erase_of_mem hu, s.2.2]
    exact (restrict 𝒦.complex R).convexHull_subset_space
      ⟨𝒦.complex.down_closed s.2.1 (Finset.erase_subset u s.1) (Finset.card_pos.mp (by omega)),
        subset_iUnion₂ (s := fun u (_ : u ∈ s.1) =>
          convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)) u hu⟩ hxu
  set L := restrict 𝒦'.complex R
  have hLsub : IsSubdivision L (restrict 𝒦.complex R) := by
    have := hsubdiv.restrict (restrict 𝒦.complex R) (restrict_faces_subset _ _)
    rwa [hL₀] at this
  have hLsp : L.space = R := hLsub.1.trans hL₀
  have hRc : IsCompact R := hRsph.isPolyhedron.isCompact
  have hLfin : L.faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hRc ((hRs.trans hs𝒦).trans hsp'.ge)).subset ?_
    rintro σ ⟨hσ, hσR⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces hσ
    exact ⟨hσ, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq),
      hσR (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq))⟩
  have : Finite L.faces := hLfin.to_subtype
  have hLman : IsCombinatorialManifold 1 L :=
    IsPLSphere.isCombinatorialManifold (n := 0) (by rw [hLsp]; exact hRsph)
  have hLconn : (SimplicialComplex.edgeGraph L).Connected :=
    edgeGraph_connected_of_isConnected_space L (by rw [hLsp]; exact hRsph.isConnected)
  let _ : Fintype L.vertices := (SimplicialComplex.finite_vertices L).fintype
  have hdeg : ∀ v, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 2 :=
    ncard_neighborSet_edgeGraph_eq_two hLman
  have hgraphR : ∀ x ∈ R, 𝒦'.map x ∈ graphSkeletonSpace 𝒦 := fun x hx => by
    rw [hmap]
    exact map_mem_graphSkeletonSpace_of_mem_biUnion_convexHull_erase s hx
  have hRof : ∀ σ : Finset Ea, σ ∈ 𝒦'.complex.faces →
      simplexBody 𝒦' σ ⊆ graphSkeletonSpace 𝒦 → (σ : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea) →
        convexHull ℝ (σ : Set Ea) ⊆ R := by
    intro σ hσ hσg hσs y hy
    have hy𝒦 : y ∈ 𝒦.complex.space := hsp'.le (𝒦'.complex.convexHull_subset_space hσ hy)
    have hys : y ∈ convexHull ℝ (s.1 : Set Ea) := convexHull_min hσs (convex_convexHull ℝ _) hy
    have hyg : 𝒦.map y ∈ graphSkeletonSpace 𝒦 := by
      rw [← hmap]
      exact hσg ⟨y, hy, rfl⟩
    exact mem_biUnion_convexHull_erase_of_map_mem_graphSkeletonSpace s hy𝒦 hys hyg
  have hvR : ∀ v : L.vertices, (v : Ea) ∈ R := fun v =>
    v.2.2 (subset_convexHull ℝ _ (by simp))
  let wv : L.vertices → Section34VertexIndex 𝒦 𝒦' := fun v =>
    ⟨{(v : Ea)}, v.2.1, Finset.card_singleton _, by
      rintro _ ⟨y, hy, rfl⟩
      exact hgraphR y (v.2.2 hy)⟩
  have hwv : ∀ v : L.vertices, (wv v).1 = {(v : Ea)} := fun _ => rfl
  have hwvinj : Function.Injective wv := by
    intro v v' hvv
    have h1 := congrArg Subtype.val hvv
    rw [hwv, hwv, Finset.singleton_inj] at h1
    exact Subtype.ext h1
  have hwvinc : ∀ v : L.vertices, Section34Incident (wv v).1 s.1 := by
    intro v
    change ((({(v : Ea)} : Finset Ea)) : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [Finset.coe_singleton, singleton_subset_iff]
    exact hRs (hvR v)
  have hwvsurj : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      ∃ v : L.vertices, wv v = w := by
    intro w hw
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.2.2.1
    have haR : convexHull ℝ (({a} : Finset Ea) : Set Ea) ⊆ R := by
      rw [← ha]
      exact hRof w.1 w.2.1 w.2.2.2 hw
    have haL : ({a} : Finset Ea) ∈ L.faces := ⟨ha ▸ w.2.1, haR⟩
    exact ⟨⟨a, haL⟩, Subtype.ext ha.symm⟩
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hadj : ∀ v v' : L.vertices, v ≠ v' →
      ((SimplicialComplex.edgeGraph L).Adj v v' ↔
        (src (.vertexBall (wv v)) ∩ src (.vertexBall (wv v'))).Nonempty) := by
    intro v v' hvv
    constructor
    · rintro ⟨-, hvL⟩
      have hcard : ({(v : Ea), (v' : Ea)} : Finset Ea).card = 2 :=
        Finset.card_pair fun h => hvv (Subtype.ext h)
      obtain ⟨e, he1⟩ : ∃ e : Section34EdgeIndex 𝒦 𝒦', e.1 = {(v : Ea), (v' : Ea)} :=
        ⟨⟨{(v : Ea), (v' : Ea)}, hvL.1, hcard, by
          rintro _ ⟨y, hy, rfl⟩
          exact hgraphR y (hvL.2 hy)⟩, rfl⟩
      obtain ⟨u, u', huu', heu, hDu⟩ := hends e
      have hsplit : ∀ z : Section34VertexIndex 𝒦 𝒦', ((z.1 : Finset Ea) : Set Ea) ⊆ e.1 →
          z = wv v ∨ z = wv v' := by
        intro z hz
        have hz' : ((z.1 : Finset Ea) : Set Ea) ⊆ ((wv v).1 : Set Ea) ∪ ((wv v').1 : Set Ea) := by
          intro y hy
          have hy' := hz hy
          rw [he1] at hy'
          rw [hwv, hwv, Finset.coe_singleton, Finset.coe_singleton]
          rcases (by simpa using hy' : y = (v : Ea) ∨ y = (v' : Ea)) with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases eq_or_eq_of_card_eq_one_of_subset_union z.2.2.1 (wv v).2.2.1 (wv v').2.2.1 hz'
          with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
      have hue : ((u.1 : Finset Ea) : Set Ea) ⊆ e.1 := by
        rw [heu]
        exact subset_union_left
      have hu'e : ((u'.1 : Finset Ea) : Set Ea) ⊆ e.1 := by
        rw [heu]
        exact subset_union_right
      obtain ⟨x, hx⟩ := (hcell (.splitDisk e)).nonempty
      rw [hDu] at hx
      rcases hsplit u hue with rfl | rfl <;> rcases hsplit u' hu'e with rfl | rfl
      · exact absurd rfl huu'
      · exact ⟨x, hx⟩
      · exact ⟨x, hx.2, hx.1⟩
      · exact absurd rfl huu'
    · intro hmeet
      obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut
        (fun h => hvv (hwvinj h)) hmeet
      obtain ⟨x, hx⟩ := hmeet
      have hxe : x ∈ src (.splitDisk e) := by rw [he]; exact hx
      have hve : (wv v).1 ⊆ e.1 := hvertexEdge (wv v) e ⟨x, hx.1, hxe⟩
      have hv'e : (wv v').1 ⊆ e.1 := hvertexEdge (wv v') e ⟨x, hx.2, hxe⟩
      rw [hwv, Finset.singleton_subset_iff] at hve hv'e
      have hsub : ({(v : Ea), (v' : Ea)} : Finset Ea) ⊆ e.1 := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hve
        · exact hv'e
      have heq : ({(v : Ea), (v' : Ea)} : Finset Ea) = e.1 :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [e.2.2.1, Finset.card_pair fun h => hvv (Subtype.ext h)])
      refine ⟨hvv, ?_⟩
      rw [heq]
      refine ⟨e.2.1, hRof e.1 e.2.1 e.2.2.2 ?_⟩
      rw [← heq, Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨hRs (hvR v), singleton_subset_iff.mpr (hRs (hvR v'))⟩
  have hTsin : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      section34VertexBallImage src f₁ w ⊆ section34FaceTorus (section34VertexBallImage src f₁) s :=
    fun w hw z hz => mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hz⟩
  have hVc : ∀ v : L.vertices, section34VertexBallImage src f₁ (wv v) ⊆ c.source :=
    fun v => (hTsin (wv v) (hwvinc v)).trans hTc
  have hVcell : ∀ w : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w) (f₁ '' srcBd (.vertexBall w)) := fun w =>
    (hcell (.vertexBall w)).image (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w)) (hNV w))
  have hDN : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w, _, -, -, he⟩ := hends e
    rw [he]
    exact inter_subset_left.trans (hNV w)
  have hDcell : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      IsPLCellOn 2 (f₁ '' src (.splitDisk e)) (f₁ '' srcBd (.splitDisk e)) := fun e =>
    (hcell (.splitDisk e)).image (hf₁.mono_of_isPLCellOn (hcell (.splitDisk e)) (hDN e))
  have hinter2 : ∀ v v' : L.vertices,
      c '' section34VertexBallImage src f₁ (wv v) ∩ c '' section34VertexBallImage src f₁ (wv v') =
        c '' (f₁ '' (src (.vertexBall (wv v)) ∩ src (.vertexBall (wv v')))) := by
    intro v v'
    have h2 := (c.injOn.mono (union_subset (hVc v) (hVc v'))).image_inter
      (subset_union_left (s := section34VertexBallImage src f₁ (wv v))) subset_union_right
    rw [hf₁.injOn.image_inter (hNV _) (hNV _)]
    exact h2.symm
  obtain ⟨g⟩ := (SimplicialComplex.edgeGraph L).exists_cycleGraphIsoOfConnectedDegreeTwo hLconn hdeg
  have h3 := (SimplicialComplex.edgeGraph L).three_le_card_of_connected_degree_two hLconn hdeg
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card L.vertices = m + 3 := ⟨Fintype.card L.vertices - 3, by omega⟩
  rw [hm] at g
  let B : Fin (m + 3) → Set (EuclideanSpace ℝ (Fin 3)) := fun i =>
    c '' section34VertexBallImage src f₁ (wv (g i))
  have hBb : ∀ i, IsPLBall 3 (B i) := fun i =>
    ((hVcell (wv (g i))).isPLBall_image_chart hc (hVc (g i))).1
  have hgne : ∀ i j, i ≠ j → g i ≠ g j := fun i j hij h => hij (g.injective h)
  have hnext : ∀ i j, (SimpleGraph.cycleGraph (m + 3)).Adj i j → IsPLBall 2 (B i ∩ B j) := by
    intro i j hij
    have hne := (hadj (g i) (g j) (hgne i j hij.ne)).mp (g.map_adj_iff.mpr hij)
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut
      (fun h => hgne i j hij.ne (hwvinj h)) hne
    change IsPLBall 2 (c '' section34VertexBallImage src f₁ (wv (g i)) ∩
      c '' section34VertexBallImage src f₁ (wv (g j)))
    rw [hinter2, ← he]
    have hDc : f₁ '' src (.splitDisk e) ⊆ c.source := by
      rw [he]
      exact (image_mono inter_subset_left).trans (hVc (g i))
    obtain ⟨q, hq, -⟩ := (hDcell e).exists_isPLHomeomorphOn_image_chart hc hDc
    exact ⟨q, hq⟩
  have hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (m + 3)).Adj i j → Disjoint (B i) (B j) := by
    intro i j hij hnadj
    have hempty : ¬ (src (.vertexBall (wv (g i))) ∩ src (.vertexBall (wv (g j)))).Nonempty :=
      fun hne => hnadj (g.map_adj_iff.mp ((hadj (g i) (g j) (hgne i j hij)).mpr hne))
    rw [Set.disjoint_iff_inter_eq_empty]
    change c '' _ ∩ c '' _ = ∅
    rw [hinter2, not_nonempty_iff_eq_empty.mp hempty, image_empty, image_empty]
  have htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → B i ∩ B j ∩ B k = ∅ := by
    intro i j k hij hik hjk
    refine Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_left.mpr ?_)
    change ∀ ⦃a⦄, a ∈ c '' _ ∩ c '' _ → a ∉ c '' _
    rw [hinter2]
    rintro _ ⟨_, ⟨x, ⟨hxi, hxj⟩, rfl⟩, rfl⟩ ⟨_, ⟨x', hx'k, rfl⟩, hceq⟩
    have hx' : x' = x := hf₁.injOn (hNV _ hx'k) (hNV _ hxi)
      (c.injOn (hVc (g k) (mem_image_of_mem f₁ hx'k)) (hVc (g i) (mem_image_of_mem f₁ hxi)) hceq)
    rw [hx'] at hx'k
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut
      (fun h => hgne i j hij (hwvinj h)) ⟨x, hxi, hxj⟩
    obtain ⟨w, w', -, hew, -⟩ := hends e
    have hxD : x ∈ src (.splitDisk e) := by
      rw [he]
      exact ⟨hxi, hxj⟩
    have hsub : ∀ z : Section34VertexIndex 𝒦 𝒦', x ∈ src (.vertexBall z) → z = w ∨ z = w' := by
      intro z hz
      have hze : ((z.1 : Finset Ea) : Set Ea) ⊆ (w.1 : Set Ea) ∪ (w'.1 : Set Ea) := by
        rw [← hew]
        exact Finset.coe_subset.mpr (hvertexEdge z e ⟨x, hz, hxD⟩)
      rcases eq_or_eq_of_card_eq_one_of_subset_union z.2.2.1 w.2.2.1 w'.2.2.1 hze with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hdi : ∀ a b : Fin (m + 3), a ≠ b → wv (g a) ≠ wv (g b) := fun a b hab h =>
      hgne a b hab (hwvinj h)
    rcases hsub _ hxi with hi' | hi' <;> rcases hsub _ hxj with hj' | hj' <;>
      rcases hsub _ hx'k with hk' | hk'
    all_goals first
      | exact hdi i j hij (hi'.trans hj'.symm)
      | exact hdi i k hik (hi'.trans hk'.symm)
      | exact hdi j k hjk (hj'.trans hk'.symm)
  have hunion : (⋃ i, B i) = c '' section34FaceTorus (section34VertexBallImage src f₁) s := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => image_mono (hTsin (wv (g i)) (hwvinc (g i)))
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      have hia : Section34Incident a.1.2.1 s.1 := by
        rw [← ha]
        exact a.2
      obtain ⟨v, hv⟩ := hwvsurj a.1.2 hia
      obtain ⟨i, rfl⟩ := g.surjective v
      exact mem_iUnion.mpr ⟨i, y, hv ▸ hya, rfl⟩
  rw [← hunion]
  exact isCombinatorialSolidTorus_iUnion_of_cycle B hBb hnext hdis htriple

theorem isPLTorus_image_frontier_section34FaceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3)
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source) :
    IsPLTorus (c '' frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) := by
  have hT := isCombinatorialSolidTorus_image_section34FaceTorus hcut hf₁ s hc hTc
  have hTcomp : IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s) := by
    have hK : IsCompact (c '' section34FaceTorus (section34VertexBallImage src f₁) s) :=
      hT.isPolyhedron.isCompact
    have ht : c '' section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact c.map_source (hTc hy)
    have hsymm := hK.image_of_continuousOn (c.continuousOn_symm.mono ht)
    convert hsymm using 1
    exact (c.symm_image_image_of_subset_source hTc).symm
  rw [c.image_frontier_of_isCompact hTcomp hTc]
  exact hT.isPLTorus_frontier

end FaceTorus

end DifferentialGeometry.Topology.PiecewiseLinear
