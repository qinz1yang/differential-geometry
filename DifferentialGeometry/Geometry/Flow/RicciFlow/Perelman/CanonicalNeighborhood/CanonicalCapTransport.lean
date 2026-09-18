import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapChainTransition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

variable {M : Type u} {N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]

theorem partialDiffeomorph_injOn_of_subset_source (F : PartialDiffeomorph I3 I3 M N ∞)
    {s : Set M} (hs : s ⊆ F.source) : InjOn (F : M → N) s := by
  intro x hx y hy hxy
  have h := congrArg F.invFun hxy
  rwa [F.left_inv' (hs hx), F.left_inv' (hs hy)] at h

theorem partialDiffeomorph_image_inter_of_subset_source (F : PartialDiffeomorph I3 I3 M N ∞)
    {s t : Set M} (hs : s ⊆ F.source) (ht : t ⊆ F.source) :
    F '' (s ∩ t) = F '' s ∩ F '' t :=
  Set.image_inter_on fun _x hx _y hy hxy =>
    partialDiffeomorph_injOn_of_subset_source F (Set.union_subset hs ht)
      (Or.inr hx) (Or.inl hy) hxy

theorem partialDiffeomorph_isImage_image_of_subset_source (F : PartialDiffeomorph I3 I3 M N ∞)
    {s : Set M} (hs : s ⊆ F.source) :
    F.toOpenPartialHomeomorph.IsImage s (F '' s) := by
  apply OpenPartialHomeomorph.IsImage.of_image_eq
  change ↑F.toPartialEquiv '' (F.source ∩ s) = F.target ∩ ↑F.toPartialEquiv '' s
  have ht : ↑F.toPartialEquiv '' s ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source' (hs hx)
  rw [inter_eq_right.mpr hs, inter_eq_right.mpr ht]

theorem partialDiffeomorph_image_interior_of_subset_source (F : PartialDiffeomorph I3 I3 M N ∞)
    {s : Set M} (hs : s ⊆ F.source) :
    F '' interior s = interior (F '' s) := by
  have h := (partialDiffeomorph_isImage_image_of_subset_source F hs).interior.image_eq
  change F '' (F.source ∩ interior s) = F.target ∩ interior (F '' s) at h
  have ht : F '' s ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source' (hs hx)
  rw [inter_eq_right.mpr (interior_subset.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h

theorem partialDiffeomorph_image_frontier_of_subset_source (F : PartialDiffeomorph I3 I3 M N ∞)
    {s : Set M} (hs : s ⊆ F.source) (hsc : IsClosed s) (htc : IsClosed (F '' s)) :
    F '' frontier s = frontier (F '' s) := by
  have h := (partialDiffeomorph_isImage_image_of_subset_source F hs).frontier.image_eq
  change F '' (F.source ∩ frontier s) = F.target ∩ frontier (F '' s) at h
  have ht : F '' s ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source' (hs hx)
  rw [inter_eq_right.mpr (hsc.frontier_subset.trans hs),
    inter_eq_right.mpr (htc.frontier_subset.trans ht)] at h
  exact h

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
variable {Mm : Type u} [TopologicalSpace Mm] [ChartedSpace ThreeSpace Mm] [IsManifold I3 ∞ Mm]
  [T2Space Mm] [SigmaCompactSpace Mm]

omit [T2Space P] [SigmaCompactSpace P] [T2Space Mm] [SigmaCompactSpace Mm] in
theorem StrongNeck.axial_fderiv_eq_of_right_trans
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {ym₀ ym₁ : P} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {x₀ x₁ : Mm}
    {nk₀ : StrongNeck Sm eps ym₀ 0} {nk₁ : StrongNeck Sm eps ym₁ 0}
    {nk₀' : StrongNeck S eps x₀ t} {nk₁' : StrongNeck S eps x₁ t}
    (e : PartialDiffeomorph I3 I3 P Mm ∞)
    (h₁ : nk₁'.map = nk₁.map.trans e) (h₀ : nk₀'.map = nk₀.map.trans e)
    {z : Cylinder} (hz : z ∈ nk₀'.map.source) (hzs : nk₀.map z ∈ e.source) :
    fderiv ℝ (fun a : ℝ => (nk₁'.map.symm (nk₀'.map (z.1, a))).2) z.2 1 =
      fderiv ℝ (fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2) z.2 1 := by
  have hz0 : z ∈ nk₀.map.source := by
    rw [h₀, partialDiffeomorph_trans_source] at hz
    exact hz.1
  have hev : (fun a : ℝ => (nk₁'.map.symm (nk₀'.map (z.1, a))).2) =ᶠ[𝓝 z.2]
      fun a : ℝ => (nk₁.map.symm (nk₀.map (z.1, a))).2 := by
    have hmem : {a : ℝ | (z.1, a) ∈ nk₀'.map.source ∧ nk₀.map (z.1, a) ∈ e.source} ∈
        𝓝 z.2 := by
      have h1 : {a : ℝ | (z.1, a) ∈ nk₀'.map.source} ∈ 𝓝 z.2 :=
        (nk₀'.map.open_source.preimage
          (continuous_const.prodMk continuous_id)).mem_nhds hz
      have h2 : {a : ℝ | nk₀.map (z.1, a) ∈ e.source} ∈ 𝓝 z.2 := by
        have hc : ContinuousAt (fun a : ℝ => nk₀.map (z.1, a)) z.2 :=
          (nk₀.map.contMDiffOn_toFun.continuousOn.continuousAt
            (nk₀.map.open_source.mem_nhds hz0)).comp
            (continuous_const.continuousAt.prodMk continuous_id.continuousAt)
        exact hc.preimage_mem_nhds (e.open_source.mem_nhds hzs)
      exact Filter.inter_mem h1 h2
    refine Filter.eventually_of_mem hmem ?_
    intro a ha
    rw [h₁, h₀]
    beta_reduce
    simp only [partialDiffeomorph_trans_apply, PartialDiffeomorph.trans_symm_apply, ha.2]
  rw [hev.fderiv_eq]

def orderedNeckChain_transport_of_map_eq_trans
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {V : Set P}
    (c : OrderedNeckChain Sm eps 0 V)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hV : V ⊆ e.source)
    (necks : ∀ i, StrongNeck S eps (e (c.centers i)) t)
    (hmap : ∀ i, (necks i).map = (c.necks i).map.trans e) :
    OrderedNeckChain S eps t (e '' V) where
  count := c.count
  count_pos := c.count_pos
  centers := fun i => e (c.centers i)
  necks := necks
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := by
    intro i z hz
    have hVmem : (c.necks i).map z ∈ V := by
      have hmem : (c.necks i).map z ∈ ⋃ i,
          (c.necks i).map '' (Set.univ ×ˢ Set.Icc (c.lo i) (c.hi i)) :=
        Set.mem_iUnion.mpr ⟨i, ⟨z, hz, rfl⟩⟩
      exact c.swept_eq.ge hmem
    rw [hmap i, partialDiffeomorph_trans_source]
    exact ⟨c.inside i hz, hV hVmem⟩
  swept_eq := by
    have h := congrArg (fun s => e '' s) c.swept_eq
    rw [Set.image_iUnion] at h
    rw [h]
    simp only [hmap, partialDiffeomorph_image_trans]
  transition_increasing := by
    intro i j hij z hz hmem
    have hz0 : z ∈ (c.necks i).map.source := by
      rw [hmap i, partialDiffeomorph_trans_source] at hz
      exact hz.1
    have hzs : (c.necks i).map z ∈ e.source := by
      rw [hmap i, partialDiffeomorph_trans_source] at hz
      exact hz.2
    have hkj : (c.necks i).map z ∈ (c.necks j).map.target := by
      rw [hmap j, partialDiffeomorph_trans_target] at hmem
      obtain ⟨w, ⟨hw1, hw2⟩, hwe⟩ := hmem
      have : w = (c.necks i).map z := by
        rw [hmap i, partialDiffeomorph_trans_apply] at hwe
        exact partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source) hw1 hzs hwe
      rwa [this] at hw2
    have hsrc := c.transition_increasing i j hij z hz0 hkj
    rw [StrongNeck.axial_fderiv_eq_of_right_trans e (hmap j) (hmap i) hz hzs]
    exact hsrc

def LocalCap.map
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {ym : P} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (chain : OrderedNeckChain S eps t (e '' L.tube)) :
    LocalCap (M := Mm) S eps (e ym) t (e '' Um) := by
  have hcoreU : L.core.carrier ⊆ Um := Set.subset_union_left.trans L.union_eq.ge
  have htubeU : L.tube ⊆ Um := Set.subset_union_right.trans L.union_eq.ge
  have hcore : L.core.carrier ⊆ e.source := hcoreU.trans hU
  have htube : L.tube ⊆ e.source := htubeU.trans hU
  have htube_cpt : IsCompact L.tube := L.isCompact_tube
  have hcore_cpt : IsCompact L.core.carrier := L.core.compact
  have hU_cpt : IsCompact Um := L.isCompact_carrier
  have hcore_closed : IsClosed L.core.carrier := hcore_cpt.isClosed
  have htube_closed : IsClosed L.tube := htube_cpt.isClosed
  have hU_closed : IsClosed Um := hU_cpt.isClosed
  have hecore_cpt : IsCompact (e '' L.core.carrier) :=
    hcore_cpt.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hcore)
  have hetube_cpt : IsCompact (e '' L.tube) :=
    htube_cpt.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono htube)
  have heU_cpt : IsCompact (e '' Um) :=
    hU_cpt.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hU)
  have hecore_closed : IsClosed (e '' L.core.carrier) := hecore_cpt.isClosed
  have hetube_closed : IsClosed (e '' L.tube) := hetube_cpt.isClosed
  have heU_closed : IsClosed (e '' Um) := heU_cpt.isClosed
  refine {
    core := L.core.map e hcore
    core_inside := ?_
    center_inside := ?_
    core_model := Classical.choice
      (capCore_transport_of_partialDiffeomorph L.core_model e hcore)
    tube := e '' L.tube
    tube_map := L.tube_map.trans e
    tube_domain := ?_
    tube_eq := ?_
    union_eq := ?_
    overlap_eq := ?_
    inner_boundary := ?_
    outer_boundary := ?_
    boundary_eq := ?_
    boundaries_disjoint := ?_
    chain := chain
    core_boundary_map := fun z => e (L.core_boundary_map z)
    core_boundary_eq := ?_ }
  · change e '' L.core.carrier ⊆ interior (e '' Um)
    exact (Set.image_mono L.core_inside).trans
      (le_of_eq (partialDiffeomorph_image_interior_of_subset_source e hU))
  · change e ym ∈ interior (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_interior_of_subset_source e hcore]
    exact ⟨ym, L.center_inside, rfl⟩
  · intro z hz
    rw [partialDiffeomorph_trans_source]
    exact ⟨L.tube_domain hz, htube (L.tube_eq ▸ ⟨z, hz, rfl⟩)⟩
  · rw [partialDiffeomorph_image_trans, L.tube_eq]
  · change e '' Um = e '' L.core.carrier ∪ e '' L.tube
    rw [← Set.image_union]
    exact congrArg _ L.union_eq
  · change e '' L.core.carrier ∩ e '' L.tube = frontier (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_inter_of_subset_source e hcore htube, L.overlap_eq,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcore_closed hecore_closed]
  · change (L.tube_map.trans e) '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      frontier (e '' L.core.carrier)
    rw [partialDiffeomorph_image_trans, L.inner_boundary,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcore_closed hecore_closed]
  · rw [partialDiffeomorph_image_trans, L.outer_boundary,
      partialDiffeomorph_image_frontier_of_subset_source e hU hU_closed heU_closed]
  · change frontier (e '' L.tube) = frontier (e '' L.core.carrier) ∪ frontier (e '' Um)
    rw [← partialDiffeomorph_image_frontier_of_subset_source e htube htube_closed hetube_closed,
      L.boundary_eq, Set.image_union,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcore_closed hecore_closed,
      partialDiffeomorph_image_frontier_of_subset_source e hU hU_closed heU_closed]
  · change Disjoint (frontier (e '' L.core.carrier)) (frontier (e '' Um))
    rw [← partialDiffeomorph_image_frontier_of_subset_source e hcore hcore_closed hecore_closed,
      ← partialDiffeomorph_image_frontier_of_subset_source e hU hU_closed heU_closed]
    exact L.boundaries_disjoint.image
      (partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source))
      (hcore_closed.frontier_subset.trans hcore) (hU_closed.frontier_subset.trans hU)
  · intro z
    rw [partialDiffeomorph_trans_apply, L.core_boundary_eq]

@[simp] theorem LocalCap.map_tube
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {ym : P} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (chain : OrderedNeckChain S eps t (e '' L.tube)) :
    (LocalCap.map L e hU chain).tube = e '' L.tube := rfl

@[simp] theorem LocalCap.map_core_carrier
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {ym : P} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (chain : OrderedNeckChain S eps t (e '' L.tube)) :
    (LocalCap.map L e hU chain).core.carrier =
      e '' L.core.carrier := rfl

omit [T2Space Mm] [SigmaCompactSpace Mm] in
theorem nonempty_orderedNeckChain_of_swept_eq {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := Mm) D} {eps t : ℝ} {x : Mm} {V : Set Mm}
    (nt : StrongNeck S eps x t) (hV : V = nt.map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) :
    Nonempty (OrderedNeckChain S eps t V) :=
  ⟨hV.symm ▸ OrderedNeckChain.single nt⟩

def LocalCap.mapOfNeckFamily
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps t : ℝ} {ym : P} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (necks : ∀ i, StrongNeck S eps (e (L.chain.centers i)) t)
    (hmap : ∀ i, (necks i).map = (L.chain.necks i).map.trans e) :
    LocalCap (M := Mm) S eps (e ym) t (e '' Um) :=
  LocalCap.map L e hU
    (orderedNeckChain_transport_of_map_eq_trans L.chain e
      (Set.subset_union_right.trans L.union_eq.ge |>.trans hU) necks hmap)

theorem canonicalAlternative_transport_cap {Dm : RealTimeInterval}
    {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps C t : ℝ} {ym : P} {x : Mm} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (chain : OrderedNeckChain S eps t (e '' L.tube)) (hbase : e ym = x)
    (deep : ∀ y ∈ e '' L.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) :
    Nonempty (CanonicalAlternative S eps C x t (e '' Um)) := by
  subst hbase
  exact ⟨CanonicalAlternative.cap
    (LocalCap.map L e hU chain) deep⟩

theorem canonicalAlternative_transport_cap_of_necks {Dm : RealTimeInterval}
    {Sm : SolutionOn (I := I3) (M := P) Dm}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := Mm) D}
    {eps C t : ℝ} {ym : P} {x : Mm} {Um : Set P}
    (L : LocalCap (M := P) Sm eps ym 0 Um)
    (e : PartialDiffeomorph I3 I3 P Mm ∞) (hU : Um ⊆ e.source)
    (necks : ∀ i, StrongNeck S eps (e (L.chain.centers i)) t)
    (hmap : ∀ i, (necks i).map = (L.chain.necks i).map.trans e) (hbase : e ym = x)
    (deep : ∀ y ∈ e '' L.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) :
    Nonempty (CanonicalAlternative S eps C x t (e '' Um)) :=
  canonicalAlternative_transport_cap L e hU
    (orderedNeckChain_transport_of_map_eq_trans L.chain e
      (Set.subset_union_right.trans L.union_eq.ge |>.trans hU) necks hmap) hbase deep

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
