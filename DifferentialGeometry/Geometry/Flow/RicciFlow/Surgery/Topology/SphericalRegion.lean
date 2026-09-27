import DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.SideClosureDisjoint
import DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData



noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure SmoothSphericalRegion (P : OrientedThreeStage.{u}) where
  region : Set P.Carrier
  compact : IsCompact region
  connected : IsConnected region
  [charts : ChartedSpace (EuclideanHalfSpace 3) region]
  [smooth : IsManifold (𝓡∂ 3) ∞ region]
  induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : region → P.Carrier)
  interior_connected : IsConnected ((Subtype.val : region → P.Carrier) '' (𝓡∂ 3).interior region)
  Boundary : Type
  [finiteBoundary : Fintype Boundary]
  sphere : Boundary → C(Sphere 2, region)
  sphere_smooth : ∀ b, IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => (sphere b y).1)
  sphere_disjoint : Pairwise fun b c => Disjoint (Set.range (sphere b)) (Set.range (sphere c))
  boundary_eq : (𝓡∂ 3).boundary region = ⋃ b, Set.range (sphere b)

structure ExteriorRegions {P : OrientedThreeStage.{u}} (C : SmoothSphericalRegion P) where
  exterior : C.Boundary → SmoothSphericalRegion P
  cover : C.region ∪ (⋃ b, (exterior b).region) = univ
  intersection : ∀ b, (exterior b).region ∩ C.region =
    (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b)
  boundary_eq : ∀ b,
    letI := (exterior b).charts
    letI := (exterior b).smooth
    (Subtype.val : (exterior b).region → P.Carrier) ''
      (𝓡∂ 3).boundary (exterior b).region =
        (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b)
  disjoint : Pairwise fun b c => Disjoint (exterior b).region (exterior c).region

theorem nonempty_exteriorRegions_of_region_eq_univ (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) [IsEmpty C.Boundary] (hregion : C.region = univ) :
    Nonempty (ExteriorRegions C) := by
  refine ⟨?_⟩
  refine ⟨fun b => isEmptyElim b, ?_, fun b => isEmptyElim b, fun b => isEmptyElim b,
    fun b => isEmptyElim b⟩
  rw [hregion]
  have hemp : (⋃ b : C.Boundary,
      (isEmptyElim b : SmoothSphericalRegion P).region) = (∅ : Set P.Carrier) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x hx
    obtain ⟨b, -⟩ := Set.mem_iUnion.mp hx
    exact isEmptyElim b
  rw [hemp, Set.union_empty]

theorem rfs_exterior_branches_of_side_data (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P)
    (side : C.Boundary → SmoothSphericalRegion P)
    (hinter : ∀ b, (side b).region ∩ C.region =
      (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b))
    (hbdry : ∀ b,
      letI := (side b).charts
      letI := (side b).smooth
      (Subtype.val : (side b).region → P.Carrier) ''
        (𝓡∂ 3).boundary (side b).region =
          (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b))
    (hdisj : Pairwise fun b c => Disjoint (side b).region (side c).region)
    (hcover : C.region ∪ (⋃ b, (side b).region) = univ) :
    Nonempty (ExteriorRegions C) :=
  ⟨⟨side, hcover, hinter, hbdry, hdisj⟩⟩

theorem rfs_exterior_branches_of_boundary_sides (P : OrientedThreeStage.{u})
    [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P)
    (side : C.Boundary → Set P.Carrier)
    (hopen : ∀ b, IsOpen (side b))
    (hconn : ∀ b, IsConnected (side b))
    (hregion : ∀ b, side b ∩ C.region = ∅)
    (hclosure : ∀ b, closure (side b) = side b ∪
      Set.range (fun y : Sphere 2 => (C.sphere b y).1))
    (hnormal : ∀ b (x : Sphere 2),
      Nonempty (DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereSideNormalChart
        (fun y : Sphere 2 => (C.sphere b y).1) (side b) x))
    (hcover : C.region ∪ (⋃ b, closure (side b)) = univ) :
    Nonempty (ExteriorRegions C) := by
  classical
  have hsphere_mem : ∀ (b : C.Boundary) (y : Sphere 2),
      (C.sphere b y).1 ∈ closure (side b) := fun b y => by
    rw [hclosure b]
    exact Or.inr (Set.mem_range_self y)
  let exteriorFun : C.Boundary → SmoothSphericalRegion P := fun b =>
    letI : ChartedSpace (EuclideanHalfSpace 3) ↥(closure (side b)) :=
      DifferentialGeometry.Topology.SphereSeparation.sideClosureChartedSpace
        (hopen b) (hclosure b) (hnormal b)
    letI : IsManifold (𝓡∂ 3) ∞ ↥(closure (side b)) :=
      DifferentialGeometry.Topology.SphereSeparation.sideClosureIsManifold
        (hopen b) (hclosure b) (hnormal b)
    let sphereMap : PUnit → C(Sphere 2, ↥(closure (side b))) := fun _ =>
      ⟨fun y => ⟨(C.sphere b y).1, hsphere_mem b y⟩,
        Continuous.subtype_mk (C.sphere_smooth b).contMDiff.continuous _⟩
    { region := closure (side b)
      compact := isClosed_closure.isCompact
      connected := (hconn b).closure
      charts := inferInstance
      smooth := inferInstance
      induced :=
        DifferentialGeometry.Topology.SphereSeparation.sideClosure_inclusion_isSmoothEmbedding
          (hopen b) (hclosure b) (hnormal b)
      interior_connected := by
        rw [DifferentialGeometry.Topology.SphereSeparation.sideClosure_interior_image
          (hopen b) (hclosure b) (hnormal b)]
        exact hconn b
      Boundary := PUnit
      finiteBoundary := inferInstance
      sphere := sphereMap
      sphere_smooth := fun _ => C.sphere_smooth b
      sphere_disjoint := fun b' d h => absurd (Subsingleton.elim b' d) h
      boundary_eq := by
        have himg := DifferentialGeometry.Topology.SphereSeparation.sideClosure_boundary_image
          (e := fun y : Sphere 2 => (C.sphere b y).1) (hopen b) (hclosure b) (hnormal b)
        have hiff : ∀ q : ↥(closure (side b)),
            q ∈ (𝓡∂ 3).boundary ↥(closure (side b)) ↔
              q.1 ∈ Set.range (fun y : Sphere 2 => (C.sphere b y).1) := by
          intro q
          constructor
          · intro hq
            rw [← himg]
            exact ⟨q, hq, rfl⟩
          · rintro ⟨y, hy⟩
            have hmem : (C.sphere b y).1 ∈
                (Subtype.val : ↥(closure (side b)) → P.Carrier) ''
                  (𝓡∂ 3).boundary ↥(closure (side b)) := by
              rw [himg]
              exact ⟨y, rfl⟩
            obtain ⟨q', hq', hq'val⟩ := hmem
            have hq'e : q' = q := Subtype.ext (hq'val.trans hy)
            rwa [hq'e] at hq'
        ext q
        rw [hiff q]
        simp only [Set.mem_iUnion, Set.mem_range]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨PUnit.unit, y, Subtype.ext hy⟩
        · rintro ⟨b', y, hy⟩
          exact ⟨y, congrArg Subtype.val hy⟩ }
  refine ⟨{ exterior := exteriorFun
            cover := ?_
            intersection := ?_
            boundary_eq := ?_
            disjoint := ?_ }⟩
  · simpa only [exteriorFun] using hcover
  · intro b
    change closure (side b) ∩ C.region =
      (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b)
    rw [hclosure b, Set.union_inter_distrib_right, hregion b, Set.empty_union]
    have hsub : Set.range (fun y : Sphere 2 => (C.sphere b y).1) ⊆ C.region := by
      rintro x ⟨y, rfl⟩
      exact (C.sphere b y).2
    rw [Set.inter_eq_left.mpr hsub]
    rw [← Set.range_comp]
    rfl
  · intro b
    dsimp only [exteriorFun]
    rw [DifferentialGeometry.Topology.SphereSeparation.sideClosure_boundary_image
      (e := fun y : Sphere 2 => (C.sphere b y).1) (hopen b) (hclosure b) (hnormal b)]
    rw [← Set.range_comp]
    rfl
  · exact DifferentialGeometry.Topology.SphereSeparation.pairwise_disjoint_closure_of_isOpen_side
      (C := C.region)
      (sphere := fun b => Set.range (fun y : Sphere 2 => (C.sphere b y).1))
      hopen hconn (fun b x hx => by
          obtain ⟨y, rfl⟩ := hx
          exact (C.sphere b y).2)
      (fun b => Set.disjoint_iff_inter_eq_empty.mpr (hregion b)) hclosure
      (fun b d hbd => Set.disjoint_left.mpr fun x hx hx' => by
        obtain ⟨y, hy⟩ := hx
        obtain ⟨z, hz⟩ := hx'
        exact Set.disjoint_left.mp (C.sphere_disjoint hbd) ⟨y, rfl⟩
          ⟨z, Subtype.ext (hz.trans hy.symm)⟩)
      (fun b => ⟨(C.sphere b DifferentialGeometry.Topology.sphereTwoNorth).1,
        DifferentialGeometry.Topology.sphereTwoNorth, rfl⟩)

theorem exterior_branch_eq_of_mem (P : OrientedThreeStage.{u}) (C : SmoothSphericalRegion P)
    (E : ExteriorRegions C)
    {b d : C.Boundary} {x : P.Carrier} (hb : x ∈ (E.exterior b).region)
    (hd : x ∈ (E.exterior d).region) : b = d := by
  by_contra hne
  exact Set.disjoint_left.mp (E.disjoint hne) hb hd

theorem exists_exterior_of_notMem_region (P : OrientedThreeStage.{u}) (C : SmoothSphericalRegion P)
    (E : ExteriorRegions C)
    {x : P.Carrier} (hx : x ∉ C.region) : ∃ b, x ∈ (E.exterior b).region := by
  have h : x ∈ C.region ∪ ⋃ b, (E.exterior b).region := by
    rw [E.cover]
    trivial
  rcases h with h' | h'
  · exact absurd h' hx
  · exact Set.mem_iUnion.mp h'

theorem exterior_inter_region_subset_sphere (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (E : ExteriorRegions C) (b : C.Boundary) :
    (E.exterior b).region ∩ C.region ⊆
      (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b) := by
  intro x hx
  rwa [E.intersection b] at hx

theorem region_eq_univ_of_isEmpty_boundary (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (E : ExteriorRegions C) [IsEmpty C.Boundary] :
    C.region = univ := by
  have h := E.cover
  rw [Set.iUnion_of_empty, Set.union_empty] at h
  exact h

theorem nonempty_boundary_of_region_ne_univ (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (E : ExteriorRegions C) (h : C.region ≠ univ) :
    Nonempty C.Boundary := by
  by_contra h'
  have : IsEmpty C.Boundary := not_nonempty_iff.mp h'
  exact h (region_eq_univ_of_isEmpty_boundary P C E)

theorem exists_exterior_not_subset_region (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (E : ExteriorRegions C) (h : C.region ≠ univ) :
    ∃ b, ¬ (E.exterior b).region ⊆ C.region := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem C.region).mp h
  obtain ⟨b, hb⟩ := exists_exterior_of_notMem_region P C E hx
  exact ⟨b, fun hsub => hx (hsub hb)⟩

theorem exists_unique_exterior_of_notMem_region (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (E : ExteriorRegions C) {x : P.Carrier} (hx : x ∉ C.region) :
    ∃! b, x ∈ (E.exterior b).region :=
  ⟨Classical.choose (exists_exterior_of_notMem_region P C E hx),
    Classical.choose_spec (exists_exterior_of_notMem_region P C E hx),
    fun _ hd => exterior_branch_eq_of_mem P C E hd
      (Classical.choose_spec (exists_exterior_of_notMem_region P C E hx))⟩


theorem sphereEmbedding_of_region (P : OrientedThreeStage.{u}) (C : SmoothSphericalRegion P)
    (b : C.Boundary) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => (C.sphere b y).1) :=
  C.sphere_smooth b

theorem nonempty_smoothTwoSidedCollar_of_region (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (b : C.Boundary) :
    Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
      (𝓡 2) ThreeModel (fun y : Sphere 2 => (C.sphere b y).1)) :=
  DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (fun y : Sphere 2 => (C.sphere b y).1) (sphereEmbedding_of_region P C b)

theorem interiorImage_subset_compl_sphere (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) (b : C.Boundary) :
    letI := C.charts
    letI := C.smooth
    (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ⊆
      (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ :=
  letI := C.charts
  letI := C.smooth
  fun _ hx =>
    let ⟨p, hp, hpx⟩ := hx
    hpx ▸ fun hrange =>
      let ⟨y, hy⟩ := hrange
      have hmem : C.sphere b y ∈ (𝓡∂ 3).boundary C.region :=
        C.boundary_eq ▸ Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩
      have hne : p = C.sphere b y := C.induced.isEmbedding.injective hy.symm
      (ModelWithCorners.disjoint_interior_boundary
        (I := (𝓡∂ 3)) (M := C.region)).le_bot ⟨hne ▸ hp, hmem⟩

theorem interiorImage_subset_side_of_union (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) [ConnectedSpace P.Carrier] (b : C.Boundary) {B D : Set P.Carrier}
    (hBopen : IsOpen B) (hDopen : IsOpen D) (hdisjoint : Disjoint B D)
    (hunion : (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ = B ∪ D) :
    letI := C.charts
    letI := C.smooth
    ((Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ⊆ B ∨
      (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ⊆ D) :=
  letI := C.charts
  letI := C.smooth
  C.interior_connected.isPreconnected.subset_or_subset hBopen hDopen hdisjoint
    (hunion ▸ interiorImage_subset_compl_sphere P C b)

theorem interiorImage_subset_collar_side (P : OrientedThreeStage.{u}) (C : SmoothSphericalRegion P)
    [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    [Nonempty (Sphere 2)] [CompactSpace (Sphere 2)] [ConnectedSpace (Sphere 2)]
    [LocallyPathConnectedSpace P.Carrier]
    (b : C.Boundary)
    (h : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun y : Sphere 2 => (C.sphere b y).1)) :
    letI := C.charts
    letI := C.smooth
    ((Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ⊆
        h.toTwoSidedCollar.negativeSide ∨
      (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ⊆
        h.toTwoSidedCollar.positiveSide) :=
  letI := C.charts
  letI := C.smooth
  interiorImage_subset_side_of_union P C b
    h.toTwoSidedCollar.isOpen_negativeSide
    h.toTwoSidedCollar.isOpen_positiveSide
    h.toTwoSidedCollar.disjoint_negativeSide_positiveSide
    h.toTwoSidedCollar.complement_eq_negativeSide_union_positiveSide

theorem exists_chartedSpace_closure_component_of_surgery_sphere
    (P : OrientedThreeStage.{0}) [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P)
    (b : C.Boundary)
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun y : Sphere 2 => (C.sphere b y).1))
    (p : ((Set.range fun y : Sphere 2 => (C.sphere b y).1)ᶜ : Set P.Carrier)) :
    ∃ c : ChartedSpace (EuclideanHalfSpace 3)
        (closure (Subtype.val '' connectedComponent p) : Set P.Carrier),
      letI := c
      IsManifold (𝓡∂ 3) ∞ (closure (Subtype.val '' connectedComponent p) : Set P.Carrier) ∧
      ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val :
        (closure (Subtype.val '' connectedComponent p) : Set P.Carrier) → P.Carrier) ∧
      ∀ q : (closure (Subtype.val '' connectedComponent p) : Set P.Carrier),
        (𝓡∂ 3).IsBoundaryPoint q ↔
          (q : P.Carrier) ∈ Set.range (fun y : Sphere 2 => (C.sphere b y).1) :=
  DifferentialGeometry.Topology.ThreeManifold.exists_chartedSpace_closure_component_of_smoothSphereEmbedding
    (M := P.Carrier) he p

theorem smoothSphericalRegion_of_collar_side (P : OrientedThreeStage.{u})
    {e : Sphere 2 → P.Carrier}
    (he : IsSmoothEmbedding (𝓡 2) ThreeModel ∞ e)
    {B : Set P.Carrier} (hBopen : IsOpen B) (hBconn : IsConnected B)
    (hBclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : Sphere 2,
      Nonempty (DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereSideNormalChart
        e B x)) :
    Nonempty (SmoothSphericalRegion P) := by
  classical
  let chartsInst : ChartedSpace (EuclideanHalfSpace 3) ↥(closure B) :=
    DifferentialGeometry.Topology.SphereSeparation.sideClosureChartedSpace
      hBopen hBclosure normalChart
  let smoothInst : IsManifold (𝓡∂ 3) ∞ ↥(closure B) :=
    DifferentialGeometry.Topology.SphereSeparation.sideClosureIsManifold
      hBopen hBclosure normalChart
  have hcompact : IsCompact (closure B) := isClosed_closure.isCompact
  have hconn : IsConnected (closure B) := hBconn.closure
  have hinduced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Subtype.val : ↥(closure B) → P.Carrier) :=
    DifferentialGeometry.Topology.SphereSeparation.sideClosure_inclusion_isSmoothEmbedding
      hBopen hBclosure normalChart
  have hinterior : IsConnected ((Subtype.val : ↥(closure B) → P.Carrier) ''
      (𝓡∂ 3).interior (closure B)) := by
    rw [DifferentialGeometry.Topology.SphereSeparation.sideClosure_interior_image
      hBopen hBclosure normalChart]
    exact hBconn
  have hsphere (y : Sphere 2) : e y ∈ closure B := hBclosure ▸ Or.inr ⟨y, rfl⟩
  let sphereMap : PUnit → C(Sphere 2, ↥(closure B)) := fun _ =>
    ⟨fun y => ⟨e y, hsphere y⟩, Continuous.subtype_mk he.contMDiff.continuous _⟩
  have hsphereMap_apply (b : PUnit) (y : Sphere 2) : (sphereMap b y).1 = e y := rfl
  have hsphere_smooth : ∀ b, IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (fun y : Sphere 2 => (sphereMap b y).1) := fun b => he
  have hbdy : (𝓡∂ 3).boundary (closure B) = ⋃ b, Set.range (sphereMap b) := by
    have himg := DifferentialGeometry.Topology.SphereSeparation.sideClosure_boundary_image
      hBopen hBclosure normalChart
    have hiff : ∀ q : ↥(closure B), q ∈ (𝓡∂ 3).boundary (closure B) ↔
        q.1 ∈ Set.range e := by
      intro q
      constructor
      · intro hq
        rw [← himg]
        exact ⟨q, hq, rfl⟩
      · rintro ⟨y, hy⟩
        have hmem : e y ∈ (Subtype.val : ↥(closure B) → P.Carrier) ''
            (𝓡∂ 3).boundary (closure B) := by
          rw [himg]
          exact ⟨y, rfl⟩
        obtain ⟨q', hq', hq'val⟩ := hmem
        have hq'e : q' = q := Subtype.ext (hq'val.trans hy)
        rwa [hq'e] at hq'
    ext q
    rw [hiff q]
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨PUnit.unit, y, Subtype.ext hy⟩
    · rintro ⟨b, y, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  exact ⟨{ region := closure B
           compact := hcompact
           connected := hconn
           charts := chartsInst
           smooth := smoothInst
           induced := hinduced
           interior_connected := hinterior
           Boundary := PUnit
           finiteBoundary := inferInstance
           sphere := sphereMap
           sphere_smooth := hsphere_smooth
           sphere_disjoint := fun b d h => absurd (Subsingleton.elim b d) h
           boundary_eq := hbdy }⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
