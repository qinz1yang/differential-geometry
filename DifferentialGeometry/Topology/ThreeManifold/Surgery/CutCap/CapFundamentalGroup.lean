import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.ThreeManifold.CoreCapOppositeSides
import DifferentialGeometry.Topology.VanKampen.EmbeddedCell
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.Manifold.Components

/-!
# Capping a spherical cut preserves the fundamental group

For a spherical capping of the cut core of a tube system, the inclusion of the core into the
capped manifold induces a bijection on fundamental groups at every basepoint of the core. The
caps whose boundary sphere lies in the component of the basepoint are attached one at a time
as embedded closed three-cells; the resulting union is clopen in the capped manifold.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

private theorem map_comp_eq {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  ext a
  exact Path.Homotopic.Quotient.map_comp

private theorem bijective_map_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    Bijective (FundamentalGroup.map (e : C(X, Y)) x) :=
  bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv
    (e : C(X, Y)) (fun z => e.symm_apply_apply z) x

private theorem bijective_map_val_of_isClopen {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsClopen U) (x : U) :
    Bijective (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x) := by
  classical
  constructor
  · have hr (p : X) : U.piecewise id (fun _ => x.val) p ∈ U := by
      by_cases hp : p ∈ U
      · rw [Set.piecewise_eq_of_mem _ _ _ hp]
        exact hp
      · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
        exact x.2
    let r : C(X, U) :=
      ⟨Set.codRestrict (U.piecewise id (fun _ => x.val)) U hr,
        (Continuous.piecewise (fun p hp => by simp [hU.frontier_eq] at hp) continuous_id
          continuous_const).codRestrict _⟩
    refine injective_fundamentalGroup_map_of_leftInverse _ r ?_ x
    intro u
    apply Subtype.ext
    change U.piecewise id (fun _ => x.val) u.val = u.val
    exact Set.piecewise_eq_of_mem _ _ _ u.2
  · intro p
    induction p using Path.Homotopic.Quotient.ind with
    | mk γ =>
      have hγ (t) : γ t ∈ U :=
        (isConnected_range γ.continuous).isPreconnected.subset_isClopen hU
          ⟨x.val, ⟨0, γ.source⟩, x.2⟩ ⟨t, rfl⟩
      let δ : Path x x :=
        { toFun := fun t => ⟨γ t, hγ t⟩
          continuous_toFun := γ.continuous.subtype_mk hγ
          source' := Subtype.ext γ.source
          target' := Subtype.ext γ.target }
      refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
      change Path.Homotopic.Quotient.mk (δ.map continuous_subtype_val) =
        Path.Homotopic.Quotient.mk γ
      congr 1

private theorem bijective_map_inclusion_of_cell {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {Z Z' : Set Y} (hZ : Z ⊆ Z') (c : ClosedCell 3 → Y) (hc : Injective c)
    (hcont : Continuous c) (hrange : range c ⊆ Z')
    (hopen : IsOpen (c '' {z | ‖z.val‖ < 1}))
    (hcompl : ∀ y ∈ Z', y ∈ Z ↔ y ∉ c '' {z | ‖z.val‖ < 1}) (hpc : IsPathConnected Z)
    (x : Z) :
    Bijective
      (FundamentalGroup.map (⟨inclusion hZ, continuous_inclusion hZ⟩ : C(Z, Z')) x) := by
  let c' : ClosedCell 3 → Z' := fun z => ⟨c z, hrange ⟨z, rfl⟩⟩
  have hc' : Injective c' := fun a b h => hc (congrArg Subtype.val h)
  have hcont' : Continuous c' := hcont.subtype_mk _
  have hint : ThreeManifold.embeddedCellInteriorImage c' =
      Subtype.val ⁻¹' (c '' {z | ‖z.val‖ < 1}) := by
    ext y
    constructor
    · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
      exact ⟨cellInteriorInclusion 3 a, a.2, rfl⟩
    · rintro ⟨d, hd, hdy⟩
      exact ⟨d, ⟨⟨d.val, hd⟩, rfl⟩, Subtype.ext hdy⟩
  have hopen' : IsOpen (ThreeManifold.embeddedCellInteriorImage c') := by
    rw [hint]
    exact hopen.preimage continuous_subtype_val
  have hmem (y : Z') : y ∈ ThreeManifold.embeddedCellComplement c' ↔ y.val ∈ Z := by
    rw [hcompl y.val y.2]
    change y ∉ ThreeManifold.embeddedCellInteriorImage c' ↔ _
    rw [hint]
    rfl
  let φ : Z ≃ₜ ThreeManifold.embeddedCellComplement c' :=
    { toFun := fun z => ⟨⟨z.val, hZ z.2⟩, (hmem _).mpr z.2⟩
      invFun := fun y => ⟨y.val.val, (hmem y.val).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have : PathConnectedSpace Z := isPathConnected_iff_pathConnectedSpace.mp hpc
  have : PathConnectedSpace (ThreeManifold.embeddedCellComplement c') :=
    φ.surjective.pathConnectedSpace φ.continuous
  have hfac : (⟨inclusion hZ, continuous_inclusion hZ⟩ : C(Z, Z')) =
      (ThreeManifold.embeddedCellComplementInclusion c').comp (φ : C(Z, _)) := by
    ext z
    rfl
  rw [hfac, map_comp_eq]
  exact (ThreeManifold.fundamentalGroup_embeddedCellComplementInclusion_bijective c' hc' hcont'
    hopen' (φ x)).comp (bijective_map_homeomorph φ x)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

include C in
private theorem locallyPathConnectedSpace_core : LocallyPathConnectedSpace T.core := by
  let _ := C.coreCharts
  let _ : LocallyPathConnectedSpace (EuclideanHalfSpace 3) :=
    (EuclideanHalfSpace.convex (n := 3)).locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace (EuclideanHalfSpace 3) T.core

private theorem coreBoundarySphere_mem_connectedComponent {x : T.core} {b : T.Boundary}
    (hb : ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x) (z) :
    T.coreBoundarySphere b z ∈ connectedComponent x := by
  obtain ⟨z₀, hz₀⟩ := hb
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hdim _ zero_le_one)
  have hsub := (isConnected_range (T.coreBoundarySphere b).continuous).isPreconnected
    |>.subset_connectedComponent ⟨z₀, rfl⟩
  rw [← connectedComponent_eq hz₀] at hsub
  exact hsub ⟨z, rfl⟩

private theorem exists_eq_coreBoundarySphere_of_cap_eq (b : T.Boundary) {z : ClosedCell 3}
    {d : T.core} (h : C.cap b z = C.coreInclusion d) :
    ∃ w, d = T.coreBoundarySphere b w := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  obtain ⟨w, rfl⟩ := C.eq_sphereToClosedCell_of_cap_mem_coreImage b ⟨d, h.symm⟩
  exact ⟨C.attaching b w, C.core_embedding.isEmbedding.injective
    (h.symm.trans (C.boundary_eq b w))⟩

private theorem isPathConnected_range_cap (b : T.Boundary) :
    IsPathConnected (range (C.cap b)) := by
  have : PathConnectedSpace (ClosedCell 3) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    have hcell : ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) =
        Metric.closedBall 0 1 := by
      ext x
      simp
    change IsPathConnected {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1}
    rw [hcell]
    exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).isPathConnected ⟨0, by simp⟩
  exact isPathConnected_range (C.cap b).continuous

private def capPiece (x : T.core) (s : Finset T.Boundary) : Set N.Carrier :=
  C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b)

private theorem capPiece_insert [DecidableEq T.Boundary] (x : T.core) (s : Finset T.Boundary)
    (b : T.Boundary) : C.capPiece x (insert b s) = C.capPiece x s ∪ range (C.cap b) := by
  ext y
  simp only [capPiece, Finset.set_biUnion_insert, mem_union]
  tauto

private def coreToPiece (x : T.core) (s : Finset T.Boundary) :
    C(connectedComponent x, C.capPiece x s) :=
  ⟨fun y => ⟨C.coreInclusion y, Or.inl (mem_image_of_mem _ y.2)⟩,
    (C.coreInclusion.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem capPiece_attach (x : T.core) (s : Finset T.Boundary)
    (hs : ∀ b ∈ s, ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x) :
    IsPathConnected (C.capPiece x s) ∧
      Bijective (FundamentalGroup.map (C.coreToPiece x s) ⟨x, mem_connectedComponent⟩) := by
  classical
  let _ := C.locallyPathConnectedSpace_core
  let _ := C.coreCharts
  let _ := C.coreSmooth
  let _ : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
  let _ : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2
  induction s using Finset.induction_on with
  | empty =>
    have hset : C.capPiece x ∅ = C.coreInclusion '' connectedComponent x := by
      simp [capPiece]
    have hD : IsPathConnected (connectedComponent x) := by
      rw [← pathComponent_eq_connectedComponent]
      exact isPathConnected_pathComponent
    refine ⟨hset ▸ hD.image C.coreInclusion.continuous, ?_⟩
    have he : Topology.IsEmbedding (C.coreToPiece x ∅) :=
      (C.core_embedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
        (C.capPiece x ∅) (fun y => Or.inl (mem_image_of_mem _ y.2))
    have hsurj : Surjective (C.coreToPiece x ∅) := by
      rintro ⟨y, hy⟩
      rw [hset] at hy
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨⟨d, hd⟩, rfl⟩
    have heq : ((he.toHomeomorphOfSurjective hsurj : _ ≃ₜ _) : C(_, _)) =
        C.coreToPiece x ∅ := by
      ext
      rfl
    rw [← heq]
    exact bijective_map_homeomorph _ _
  | insert b s hb ih =>
    have hs' : ∀ b ∈ s, ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x :=
      fun b' hb' => hs b' (Finset.mem_insert_of_mem hb')
    obtain ⟨hpc, hbij⟩ := ih hs'
    have hbD := hs b (Finset.mem_insert_self b s)
    have hZ : C.capPiece x s ⊆ C.capPiece x (insert b s) := by
      rw [C.capPiece_insert]
      exact subset_union_left
    have hrange : range (C.cap b) ⊆ C.capPiece x (insert b s) := by
      rw [C.capPiece_insert]
      exact subset_union_right
    let w₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    have hmeet : (C.capPiece x s ∩ range (C.cap b)).Nonempty := by
      refine ⟨C.cap b (sphereToClosedCell w₀), ?_, ⟨_, rfl⟩⟩
      rw [C.boundary_eq b w₀]
      exact Or.inl ⟨_, coreBoundarySphere_mem_connectedComponent hbD _, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [C.capPiece_insert]
      exact hpc.union (C.isPathConnected_range_cap b) hmeet
    · have hopen : IsOpen (C.cap b '' {z | ‖z.val‖ < 1}) := by
        rw [← C.capBallChart_target]
        exact (C.capBallChart b).chart.open_target
      have hcompl : ∀ y ∈ C.capPiece x (insert b s),
          y ∈ C.capPiece x s ↔ y ∉ C.cap b '' {z | ‖z.val‖ < 1} := by
        intro y hy
        constructor
        · rintro (⟨d, hd, rfl⟩ | hy') hint
          · have hm : C.coreInclusion d ∈
                (C.cap b) '' {z : ClosedCell 3 | ‖z.1‖ < 1} ∩ range C.coreInclusion :=
              ⟨hint, d, rfl⟩
            rw [C.cap_interiorImage_disjoint_coreImage b] at hm
            exact hm
          · obtain ⟨b', hb', hyb'⟩ := mem_iUnion₂.mp hy'
            have hne : b' ≠ b := fun h => hb (h ▸ hb')
            obtain ⟨z, -, hz⟩ := hint
            exact Set.disjoint_left.mp (C.cap_disjoint hne) hyb' ⟨z, hz⟩
        · intro hnot
          rw [C.capPiece_insert] at hy
          rcases hy with hy | ⟨z, rfl⟩
          · exact hy
          · have hz : ‖z.val‖ = 1 := le_antisymm z.2 (not_lt.mp fun h => hnot ⟨z, h, rfl⟩)
            let w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
              ⟨z.val, by simpa using hz⟩
            have hw : sphereToClosedCell w = z := Subtype.ext rfl
            rw [← hw, C.boundary_eq b w]
            exact Or.inl ⟨_, coreBoundarySphere_mem_connectedComponent hbD _, rfl⟩
      have hfac : C.coreToPiece x (insert b s) =
          (⟨inclusion hZ, continuous_inclusion hZ⟩ : C(_, _)).comp (C.coreToPiece x s) := by
        ext
        rfl
      rw [hfac, map_comp_eq]
      exact (bijective_map_inclusion_of_cell hZ (C.cap b) (C.cap_embedding b).isEmbedding.injective
        (C.cap b).continuous hrange hopen hcompl hpc _).comp hbij

private theorem isClopen_capPiece (x : T.core) (s : Finset T.Boundary)
    (hs : ∀ b, b ∈ s ↔ ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x) :
    IsClopen (C.capPiece x s) := by
  let _ := C.locallyPathConnectedSpace_core
  let _ := C.coreCharts
  let _ := C.coreSmooth
  let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
  let W : Set N.Carrier :=
    C.coreInclusion '' (connectedComponent x)ᶜ ∪ ⋃ (b) (_ : b ∉ s), range (C.cap b)
  have hinj := C.core_embedding.isEmbedding.injective
  have hcover : ∀ y, y ∈ C.capPiece x s ∨ y ∈ W := by
    intro y
    have hy : y ∈ range C.coreInclusion ∪ ⋃ b, range (C.cap b) := by
      rw [C.exhaustive]
      trivial
    rcases hy with ⟨d, rfl⟩ | hy
    · by_cases hd : d ∈ connectedComponent x
      · exact Or.inl (Or.inl ⟨d, hd, rfl⟩)
      · exact Or.inr (Or.inl ⟨d, hd, rfl⟩)
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hy
      by_cases hbs : b ∈ s
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨b, hbs, hb⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨b, hbs, hb⟩))
  have hdisj : ∀ y, y ∈ C.capPiece x s → y ∉ W := by
    rintro y (⟨d, hd, rfl⟩ | hy) (⟨d', hd', hdd⟩ | hy')
    · exact hd' (by rw [hinj hdd]; exact hd)
    · obtain ⟨b, hbs, z, hz⟩ := mem_iUnion₂.mp hy'
      obtain ⟨w, rfl⟩ := C.exists_eq_coreBoundarySphere_of_cap_eq b hz
      exact hbs ((hs b).mpr ⟨w, hd⟩)
    · obtain ⟨b, hbs, z, hz⟩ := mem_iUnion₂.mp hy
      obtain ⟨w, rfl⟩ := C.exists_eq_coreBoundarySphere_of_cap_eq b (hz.trans hdd.symm)
      exact hd' (coreBoundarySphere_mem_connectedComponent ((hs b).mp hbs) w)
    · obtain ⟨b, hbs, hyb⟩ := mem_iUnion₂.mp hy
      obtain ⟨b', hbs', hyb'⟩ := mem_iUnion₂.mp hy'
      have hne : b ≠ b' := fun h => hbs' (h ▸ hbs)
      exact Set.disjoint_left.mp (C.cap_disjoint hne) hyb hyb'
  have hDopen : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have hcompactZ : IsCompact (C.capPiece x s) :=
    (isClosed_connectedComponent.isCompact.image C.coreInclusion.continuous).union
      (s.isCompact_biUnion fun b _ => isCompact_range (C.cap b).continuous)
  have hcompactW : IsCompact W :=
    (hDopen.isClosed_compl.isCompact.image C.coreInclusion.continuous).union
      (isCompact_iUnion fun b => isCompact_iUnion fun _ => isCompact_range (C.cap b).continuous)
  have hcompl : C.capPiece x s = Wᶜ := by
    ext y
    exact ⟨hdisj y, fun h => (hcover y).resolve_right h⟩
  exact ⟨hcompactZ.isClosed, hcompl ▸ hcompactW.isClosed.isOpen_compl⟩

theorem fundamentalGroup_map_coreInclusion_bijective (x : T.core) :
    Bijective (FundamentalGroup.map C.coreInclusion x) := by
  classical
  let _ := C.locallyPathConnectedSpace_core
  let s := Finset.univ.filter fun b => ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x
  have hs (b : T.Boundary) :
      b ∈ s ↔ ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x := by
    simp [s]
  have hbij := (C.capPiece_attach x s fun b hb => (hs b).mp hb).2
  let ιD : C(connectedComponent x, T.core) := ⟨Subtype.val, continuous_subtype_val⟩
  let ιZ : C(C.capPiece x s, N.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  have hsq : C.coreInclusion.comp ιD = ιZ.comp (C.coreToPiece x s) := by
    ext
    rfl
  have hcomp : Bijective
      (FundamentalGroup.map (C.coreInclusion.comp ιD) ⟨x, mem_connectedComponent⟩) := by
    rw [hsq, map_comp_eq]
    exact (bijective_map_val_of_isClopen (C.isClopen_capPiece x s hs) _).comp hbij
  rw [map_comp_eq] at hcomp
  exact (Bijective.of_comp_iff _
    (bijective_map_val_of_isClopen isClopen_connectedComponent _)).mp hcomp

def coreFundamentalGroupEquiv (x : T.core) :
    FundamentalGroup T.core x ≃* FundamentalGroup N.Carrier (C.coreInclusion x) :=
  MulEquiv.ofBijective _ (C.fundamentalGroup_map_coreInclusion_bijective x)

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem fundamentalGroup_map_coreInclusion_bijective (x : E.tubes.core) :
    Function.Bijective (FundamentalGroup.map E.capping.coreInclusion x) :=
  E.capping.fundamentalGroup_map_coreInclusion_bijective x

def capFundamentalGroupEquiv (x : E.tubes.core) :
    FundamentalGroup E.tubes.core x ≃*
      FundamentalGroup E.capped.Carrier (E.capping.coreInclusion x) :=
  E.capping.coreFundamentalGroupEquiv x

private theorem coreInclusion_mem_componentSet (K : ConnectedComponents E.capped.Carrier)
    (x : E.tubes.core) (hx : ConnectedComponents.mk (E.capping.coreInclusion x) = K)
    (y : connectedComponent x) : E.capping.coreInclusion y ∈ E.capped.componentSet K := by
  rw [ClosedOrientedManifold.mem_componentSet, ← hx]
  exact ConnectedComponents.coe_eq_coe'.mpr
    (E.capping.coreInclusion.continuous.image_connectedComponent_subset x ⟨y, y.2, rfl⟩)

def coreComponentCapMap (K : ConnectedComponents E.capped.Carrier) (x : E.tubes.core)
    (hx : ConnectedComponents.mk (E.capping.coreInclusion x) = K) :
    C(connectedComponent x, (E.capped.component K).Carrier) :=
  ⟨fun y => ⟨E.capping.coreInclusion y, E.coreInclusion_mem_componentSet K x hx y⟩,
    (E.capping.coreInclusion.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem fundamentalGroup_map_coreComponentCapMap_bijective
    (K : ConnectedComponents E.capped.Carrier) (x : E.tubes.core)
    (hx : ConnectedComponents.mk (E.capping.coreInclusion x) = K) (y : connectedComponent x) :
    Function.Bijective (FundamentalGroup.map (E.coreComponentCapMap K x hx) y) := by
  let _ := E.capping.locallyPathConnectedSpace_core
  let ιD : C(connectedComponent x, E.tubes.core) := ⟨Subtype.val, continuous_subtype_val⟩
  let ιK : C((E.capped.component K).Carrier, E.capped.Carrier) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hsq : ιK.comp (E.coreComponentCapMap K x hx) = E.capping.coreInclusion.comp ιD := by
    ext
    rfl
  have hK : IsClopen (E.capped.componentSet K) :=
    ⟨E.capped.isClosed_componentSet K, E.capped.isOpen_componentSet K⟩
  have hcomp : Function.Bijective
      (FundamentalGroup.map (ιK.comp (E.coreComponentCapMap K x hx)) y) := by
    rw [hsq, SphericalCapping.map_comp_eq]
    exact (E.fundamentalGroup_map_coreInclusion_bijective y.val).comp
      (SphericalCapping.bijective_map_val_of_isClopen isClopen_connectedComponent y)
  rw [SphericalCapping.map_comp_eq] at hcomp
  exact (Function.Bijective.of_comp_iff'
    (SphericalCapping.bijective_map_val_of_isClopen (U := E.capped.componentSet K) hK _)
      _).mp hcomp

end DifferentialGeometry.Topology.SphericalCutCapTransition
