import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.SphereSeparation.SideClosureDisjoint
import DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure



noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem standardCapL_pos : 0 < standardCapL := by
  rw [standardCapL, standardCapA0]
  have h : 0 < Real.pi / Real.sqrt 2 :=
    div_pos Real.pi_pos (Real.sqrt_pos.2 (by norm_num))
  linarith

theorem sphereTwo_connectedSpace : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)

theorem riemannianCurveLength_eq_zero_of_apply_eq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} {q : M}
    (h : ∀ t ∈ Icc a b, γ t = q) : riemannianCurveLength g γ a b = 0 := by
  unfold riemannianCurveLength
  refine le_antisymm (iSup_le fun p => ?_) bot_le
  have hsum : (∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [h _ (p.2.2.2 (i + 1)), h _ (p.2.2.2 i)]
      exact riemannianEDistOf_self g q
  rw [hsum]

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

theorem rfs_exterior_branches (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P) :
    Nonempty (ExteriorRegions C) := by
  sorry

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

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

abbrev transition (_G : GeometricCutoffRecord H i parameters) := (H.event i).transition

abbrev Parent := (H.stage i.castSucc).component (G.transition.childParent c)
abbrev Child (_G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) := (H.stage i.succ).component c


abbrev ChildBoundary := {b : (H.event i).RetainedBoundaryIndex // ∀ y : Sphere 2,
  ConnectedComponents.mk (G.transition.trace.tubes.coreBoundarySphere b.1 y) =
    G.transition.childCoreComponent c}

structure ComparisonSupport where
  level : G.ChildBoundary c → ℝ
  level_lower : ∀ b, -(G.static b.1).delta⁻¹ < level b
  level_below_tip : ∀ b, level b < (G.static b.1).witness.tipCoordinate
  level_negative : ∀ b, level b < 0
  collarParameter : (b : G.ChildBoundary c) →
    Sphere 2 × Icc (level b) 0 → neckCentralDomain (G.static b.1).delta
  collarParameter_eq : ∀ b x, (collarParameter b x).1.1 = (x.1, x.2.1)
  collar : (b : G.ChildBoundary c) → C(Sphere 2 × Icc (level b) 0, (G.Parent c).Carrier)
  collar_eq : ∀ b x, (collar b x).1 =
    ((G.static b.1).neck.chart (collarParameter b x).1).1
  collar_core_intersection : ∀ b,
    Set.range (collar b) ∩ Set.range (G.transition.childCoreIntoParent c) =
      Set.range (fun y => collar b (y, ⟨0, (level_negative b).le, le_rfl⟩))
  collar_disjoint : Pairwise fun b d => Disjoint (Set.range (collar b)) (Set.range (collar d))
  support : SmoothSphericalRegion (G.Parent c)
  support_eq : support.region = Set.range (G.transition.childCoreIntoParent c) ∪
    (⋃ b, Set.range (collar b))
  support_terminal : ∀ x ∈ support.region, x.1 ∈ (H.event i).incoming.terminalRegularRegion
  boundaryLabel : G.ChildBoundary c ≃ support.Boundary
  boundary_eq : ∀ b,
    (Subtype.val : support.region → (G.Parent c).Carrier) '' Set.range (support.sphere (boundaryLabel b)) =
      Set.range (fun y => collar b (y, ⟨level b, le_rfl, (level_negative b).le⟩))
  exterior : ExteriorRegions support
  localCollapse : (b : G.ChildBoundary c) →
    C(neckCentralDomain (G.static b.1).delta, (G.Child c).Carrier)
  localCollapse_eq : ∀ b x, (localCollapse b x).1 =
    (G.static b.1).inclusion ((G.static b.1).witness.collapse x)
  tip : G.ChildBoundary c → (G.Child c).Carrier
  tip_eq : ∀ b, (tip b).1 = (G.static b.1).inclusion (G.static b.1).witness.tip

theorem rfs_comparison_support_of_inputs
    (I1_level : G.ChildBoundary c → ℝ)
    (I1_lower : ∀ b, -(G.static b.1).delta⁻¹ < I1_level b)
    (I1_below_tip : ∀ b, I1_level b < (G.static b.1).witness.tipCoordinate)
    (I1_negative : ∀ b, I1_level b < 0)
    (I2_parameter : (b : G.ChildBoundary c) →
      Sphere 2 × ↑(Icc (I1_level b) 0) → neckCentralDomain (G.static b.1).delta)
    (I2_eq : ∀ b x, (I2_parameter b x).1.1 = (x.1, x.2.1))
    (I3_collar : (b : G.ChildBoundary c) →
      C(Sphere 2 × ↑(Icc (I1_level b) 0), (G.Parent c).Carrier))
    (I3_eq : ∀ b x, (I3_collar b x).1 = ((G.static b.1).neck.chart (I2_parameter b x).1).1)
    (I4_inter : ∀ b, Set.range (I3_collar b) ∩
        Set.range (G.transition.childCoreIntoParent c) =
      Set.range (fun y : Sphere 2 =>
        I3_collar b (y, ⟨0, (I1_negative b).le, le_rfl⟩)))
    (I5_disjoint : Pairwise fun b d =>
      Disjoint (Set.range (I3_collar b)) (Set.range (I3_collar d)))
    (I6_support : SmoothSphericalRegion (G.Parent c))
    (I6_eq : I6_support.region = Set.range (G.transition.childCoreIntoParent c) ∪
      (⋃ b, Set.range (I3_collar b)))
    (I6_terminal : ∀ x ∈ I6_support.region,
      x.1 ∈ (H.event i).incoming.terminalRegularRegion)
    (I7_label : G.ChildBoundary c ≃ I6_support.Boundary)
    (I7_eq : ∀ b,
      (Subtype.val : I6_support.region → (G.Parent c).Carrier) ''
        Set.range (I6_support.sphere (I7_label b)) =
      Set.range (fun y : Sphere 2 =>
        I3_collar b (y, ⟨I1_level b, le_rfl, (I1_negative b).le⟩)))
    (I8_exterior : ExteriorRegions I6_support)
    (I8_localCollapse : (b : G.ChildBoundary c) →
      C(neckCentralDomain (G.static b.1).delta, (G.Child c).Carrier))
    (I8_localCollapse_eq : ∀ b x, (I8_localCollapse b x).1 =
      (G.static b.1).inclusion ((G.static b.1).witness.collapse x))
    (I8_tip : G.ChildBoundary c → (G.Child c).Carrier)
    (I8_tip_eq : ∀ b, (I8_tip b).1 = (G.static b.1).inclusion (G.static b.1).witness.tip) :
    Nonempty (G.ComparisonSupport c) :=
  ⟨{ level := I1_level
     level_lower := I1_lower
     level_below_tip := I1_below_tip
     level_negative := I1_negative
     collarParameter := I2_parameter
     collarParameter_eq := I2_eq
     collar := I3_collar
     collar_eq := I3_eq
     collar_core_intersection := I4_inter
     collar_disjoint := I5_disjoint
     support := I6_support
     support_eq := I6_eq
     support_terminal := I6_terminal
     boundaryLabel := I7_label
     boundary_eq := I7_eq
     exterior := I8_exterior
     localCollapse := I8_localCollapse
     localCollapse_eq := I8_localCollapse_eq
     tip := I8_tip
     tip_eq := I8_tip_eq }⟩

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

def comparisonLevel (b : G.ChildBoundary c) : ℝ :=
  (-(G.static b.1).delta⁻¹ + (G.static b.1).witness.tipCoordinate) / 2

theorem comparisonLevel_lower (b : G.ChildBoundary c) :
    -(G.static b.1).delta⁻¹ < G.comparisonLevel c b := by
  have h := (G.static b.1).witness.tipCoordinate_lower
  simp only [comparisonLevel]
  linarith

theorem comparisonLevel_below_tip (b : G.ChildBoundary c) :
    G.comparisonLevel c b < (G.static b.1).witness.tipCoordinate := by
  have h := (G.static b.1).witness.tipCoordinate_lower
  simp only [comparisonLevel]
  linarith

theorem comparisonLevel_negative (b : G.ChildBoundary c) : G.comparisonLevel c b < 0 := by
  have h2 := (G.static b.1).witness.tipCoordinate_upper
  have h3 := parameters.fixed.collar_pos
  have h4 : 0 < standardCapL := standardCapL_pos
  have h5 : 0 < (G.static b.1).delta⁻¹ := inv_pos.mpr (G.static b.1).neck.delta_pos
  simp only [comparisonLevel]
  linarith

theorem comparisonLevel_mem_Icc (b : G.ChildBoundary c) :
    G.comparisonLevel c b ∈ Icc (G.comparisonLevel c b) 0 :=
  ⟨le_rfl, (G.comparisonLevel_negative c b).le⟩

theorem collarParameter_mem (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    -(G.static b.1).delta⁻¹ < (x.2 : ℝ) ∧ (x.2 : ℝ) < (G.static b.1).delta⁻¹ := by
  have h1 : -(G.static b.1).delta⁻¹ < (x.2 : ℝ) :=
    lt_of_lt_of_le (G.comparisonLevel_lower c b) x.2.2.1
  have h2 : (x.2 : ℝ) < (G.static b.1).delta⁻¹ :=
    lt_of_le_of_lt x.2.2.2 (inv_pos.mpr (G.static b.1).neck.delta_pos)
  exact ⟨h1, h2⟩

def collarParameter (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    neckCentralDomain (G.static b.1).delta :=
  ⟨⟨(x.1, x.2.1), by
      obtain ⟨h1, h2⟩ := G.collarParameter_mem c b x
      exact ⟨by linarith, by linarith⟩⟩,
    G.collarParameter_mem c b x⟩

theorem collarParameter_apply (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    (G.collarParameter c b x).1.1 = (x.1, x.2.1) := rfl

theorem collarBuffer_continuous (b : G.ChildBoundary c) :
    Continuous (fun x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0) =>
      (⟨(x.1, x.2.1), by
        obtain ⟨h1, h2⟩ := G.collarParameter_mem c b x
        exact ⟨by linarith, by linarith⟩⟩ : neckBuffer (G.static b.1).delta)) := by
  apply Continuous.subtype_mk
  exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

theorem collarParameter_continuous (b : G.ChildBoundary c) :
    Continuous (G.collarParameter c b) :=
  Continuous.subtype_mk (G.collarBuffer_continuous c b) (fun x => G.collarParameter_mem c b x)

theorem collarSecond_preconnectedSpace (b : G.ChildBoundary c) :
    PreconnectedSpace ↑(Icc (G.comparisonLevel c b) 0) :=
  isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Icc (a := G.comparisonLevel c b) (b := 0))

def collarChartFun (b : G.ChildBoundary c) :
    Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0) → (H.stage i.castSucc).Carrier :=
  fun x => ((G.static b.1).neck.chart (G.collarParameter c b x)).1

theorem collarChartFun_continuous (b : G.ChildBoundary c) :
    Continuous (G.collarChartFun c b) :=
  (continuous_subtype_val.comp (G.static b.1).neck.chart.continuous).comp
    (continuous_subtype_val.comp (G.collarParameter_continuous c b))

theorem collarChartFun_zero_eq_boundarySphere (b : G.ChildBoundary c) (y : Sphere 2) :
    G.collarChartFun c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩) =
      G.transition.trace.tubes.boundarySphere b.1.1 y := by
  set z0 : ↑(Icc (G.comparisonLevel c b) 0) :=
    ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩ with hz0
  set Y : neckBuffer (G.static b.1).delta := (G.collarParameter c b (y, z0)).1 with hY
  have hY1 : Y.1.1 = y := rfl
  have hY2 : Y.1.2 = 0 := rfl
  set W : neckBuffer (G.delta b.1.1.1) :=
    ⟨(Y.1.1, (if b.1.1.2 then 1 else -1) * (1 + Y.1.2)), G.recenter_in_buffer b.1 Y⟩ with hW
  have hrc : (G.static b.1).neck.chart Y = (G.neck b.1.1.1).chart W :=
    G.recenter_chart b.1 Y (G.recenter_in_buffer b.1 Y)
  set Z : TubeDomain := (y, TubeSystem.boundaryLevel b.1.1.2) with hZ
  have htube : (G.transition.trace.tubes.tube b.1.1.1 Z) =
      ((G.neck b.1.1.1).chart ⟨(Z.1, Z.2.1), G.tube_in_buffer b.1.1.1 Z⟩).1 :=
    G.tube_eq b.1.1.1 Z (G.tube_in_buffer b.1.1.1 Z)
  have hpair : (Y.1.1, (if b.1.1.2 then 1 else -1) * (1 + Y.1.2)) = (Z.1, Z.2.1) := by
    rw [hY1, hY2, hZ]
    cases b.1.1.2 <;> simp [TubeSystem.boundaryLevel]
  have hWval : W = ⟨(Z.1, Z.2.1), G.tube_in_buffer b.1.1.1 Z⟩ := by
    rw [hW]
    exact Subtype.ext hpair
  calc G.collarChartFun c b (y, z0)
      = ((G.static b.1).neck.chart Y).1 := by rw [collarChartFun, ← hY]
    _ = ((G.neck b.1.1.1).chart W).1 := by rw [hrc]
    _ = ((G.neck b.1.1.1).chart ⟨(Z.1, Z.2.1), G.tube_in_buffer b.1.1.1 Z⟩).1 := by
          rw [hWval]
    _ = (G.transition.trace.tubes.tube b.1.1.1 Z) := htube.symm
    _ = G.transition.trace.tubes.boundarySphere b.1.1 y := rfl

theorem collarChartFun_mem_parent (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    ConnectedComponents.mk (G.collarChartFun c b x) = G.transition.childParent c := by
  let : PreconnectedSpace ↑(Icc (G.comparisonLevel c b) 0) := G.collarSecond_preconnectedSpace c b
  set z0 : ↑(Icc (G.comparisonLevel c b) 0) :=
    ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩ with hz0
  have hcont : Continuous (fun z : ↑(Icc (G.comparisonLevel c b) 0) =>
      G.collarChartFun c b (x.1, z)) :=
    (G.collarChartFun_continuous c b).comp (continuous_const.prodMk continuous_id)
  have hpre : IsPreconnected (Set.range fun z : ↑(Icc (G.comparisonLevel c b) 0) =>
      G.collarChartFun c b (x.1, z)) := isPreconnected_range hcont
  have hsub := hpre.subset_connectedComponent (Set.mem_range_self z0)
  have hmem : G.collarChartFun c b (x.1, x.2) ∈
      connectedComponent (G.collarChartFun c b (x.1, z0)) :=
    hsub (Set.mem_range_self x.2)
  have heq1 : ConnectedComponents.mk (G.collarChartFun c b (x.1, x.2)) =
      ConnectedComponents.mk (G.collarChartFun c b (x.1, z0)) :=
    ConnectedComponents.coe_eq_coe'.mpr hmem
  have heq2 : ConnectedComponents.mk (G.collarChartFun c b (x.1, z0)) =
      G.transition.childParent c := by
    have hz : z0 = ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩ := Subtype.ext rfl
    rw [hz, G.collarChartFun_zero_eq_boundarySphere c b x.1]
    exact G.transition.childCore_mem_parent c
      ⟨⟨G.transition.trace.tubes.boundarySphere b.1.1 x.1,
        G.transition.trace.tubes.boundarySphere_mem_core b.1.1 x.1⟩, b.2 x.1⟩
  exact heq1.trans heq2

def collarMap (b : G.ChildBoundary c) :
    C(Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0), (G.Parent c).Carrier) :=
  ⟨fun x => ⟨G.collarChartFun c b x, G.collarChartFun_mem_parent c b x⟩,
    Continuous.subtype_mk (G.collarChartFun_continuous c b)
      (fun x => G.collarChartFun_mem_parent c b x)⟩

theorem collarMap_apply (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    (G.collarMap c b x).1 = ((G.static b.1).neck.chart (G.collarParameter c b x)).1 := rfl

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem retainedBoundary_side_eq (G : GeometricCutoffRecord H i parameters)
    {α : (H.event i).transition.trace.tubes.Index} {s t : Bool}
    (hb : (H.event i).RetainedBoundary (α, s)) (hd : (H.event i).RetainedBoundary (α, t)) :
    s = t := by
  cases s <;> cases t
  · rfl
  · exact absurd hb ((G.one_retained_side α).mp hd)
  · exact absurd hd ((G.one_retained_side α).mp hb)
  · rfl

variable (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem collarChartFun_mem_neckChart_range (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    ∃ w : neckBuffer (G.delta b.1.1.1),
      G.collarChartFun c b x = ((G.neck b.1.1.1).chart w).1 :=
  ⟨⟨((G.collarParameter c b x).1.1.1,
      (if b.1.1.2 then 1 else -1) * (1 + (G.collarParameter c b x).1.1.2)),
      G.recenter_in_buffer b.1 (G.collarParameter c b x).1⟩,
    congrArg Subtype.val (G.recenter_chart b.1 (G.collarParameter c b x).1
      (G.recenter_in_buffer b.1 (G.collarParameter c b x).1))⟩

theorem collarMap_pairwise_disjoint :
    Pairwise fun b d => Disjoint (Set.range (G.collarMap c b)) (Set.range (G.collarMap c d)) := by
  intro b d hbd
  have hne : b.1.1.1 ≠ d.1.1.1 := by
    intro hidx
    refine hbd (Subtype.ext (Subtype.ext (Prod.ext hidx ?_)))
    exact retainedBoundary_side_eq G b.1.2 (hidx.symm ▸ d.1.2)
  refine Set.disjoint_left.mpr fun p hp hq => ?_
  obtain ⟨x, hx⟩ := hp
  obtain ⟨x', hx'⟩ := hq
  obtain ⟨w, hw⟩ := G.collarChartFun_mem_neckChart_range c b x
  obtain ⟨w', hw'⟩ := G.collarChartFun_mem_neckChart_range c d x'
  have hbp : ((G.neck b.1.1.1).chart w).1 = p.1 := hw.symm.trans (congrArg Subtype.val hx)
  have hdp : ((G.neck d.1.1.1).chart w').1 = p.1 := hw'.symm.trans (congrArg Subtype.val hx')
  have heq : (G.neck b.1.1.1).chart w = (G.neck d.1.1.1).chart w' := Subtype.ext (hbp.trans hdp.symm)
  have hmem : ((G.neck b.1.1.1).chart w) ∈ Set.range (G.neck d.1.1.1).chart := by
    rw [heq]
    exact Set.mem_range_self w'
  exact (Set.disjoint_left.mp (G.buffer_disjoint hne)) (Set.mem_range_self w) hmem

theorem collarMap_zero_mem_childCore_range (b : G.ChildBoundary c) (y : Sphere 2) :
    G.collarMap c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩) ∈
      Set.range (G.transition.childCoreIntoParent c) := by
  refine ⟨⟨⟨G.transition.trace.tubes.boundarySphere b.1.1 y,
      G.transition.trace.tubes.boundarySphere_mem_core b.1.1 y⟩, b.2 y⟩, ?_⟩
  apply Subtype.ext
  exact (G.collarChartFun_zero_eq_boundarySphere c b y).symm

theorem childCoreIntoParent_terminal (x : G.transition.ChildCore c) :
    (G.transition.childCoreIntoParent c x).1 ∈ (H.event i).incoming.terminalRegularRegion := by
  have hret : x.1 ∈ G.transition.trace.retainedCore := by
    obtain ⟨q, hq, _⟩ := G.transition.childCore_mapsTo_child c x
    exact ⟨q.1, hq⟩
  exact G.retained_terminal x.1 hret

theorem collarMap_terminal (b : G.ChildBoundary c)
    (x : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    (G.collarMap c b x).1 ∈ (H.event i).incoming.terminalRegularRegion := by
  obtain ⟨w, hw⟩ := G.collarChartFun_mem_neckChart_range c b x
  have h1 : (G.collarMap c b x).1 = ((G.neck b.1.1.1).chart w).1 := hw
  rw [h1]
  exact ((G.neck b.1.1.1).chart w).2

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem capPoint_mem_child (b : G.ChildBoundary c) (t : ThreeBall) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.cap t) :
      (H.stage i.succ).Carrier) = c := by
  obtain ⟨q, hq, -⟩ := G.transition.childCap_mapsTo_child c ⟨b.1.1, b.2⟩ t
  have hcap := (G.static b.1).cap_eq t
  rw [hcap] at hq
  have hinj : (G.static b.1).inclusion ((G.static b.1).witness.cap t) = q.1 := Sum.inl.inj hq
  rw [hinj]
  exact q.2

theorem tipPoint_mem_child (b : G.ChildBoundary c) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.tip) :
      (H.stage i.succ).Carrier) = c := by
  obtain ⟨t, -, ht⟩ := (G.static b.1).witness.tip_interior
  rw [← ht]
  exact G.capPoint_mem_child c b t

abbrev spherePoint : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth

theorem spherePoint_norm (y : Sphere 2) : ‖(y : ThreeSpace)‖ = 1 := by
  have h : dist (y : ThreeSpace) 0 = 1 := Metric.mem_sphere.mp y.2
  rwa [dist_eq_norm, sub_zero] at h

theorem capCentralDomain_preconnectedSpace (b : G.ChildBoundary c) :
    PreconnectedSpace ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo

def capCentralElement (b : G.ChildBoundary c) :
    Sphere 2 × ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) →
      neckCentralDomain (G.static b.1).delta :=
  fun p => ⟨⟨(p.1, p.2.1), by
      obtain ⟨h1, h2⟩ := p.2.2
      exact ⟨by linarith, by linarith⟩⟩, p.2.2⟩

theorem capCentralElement_continuous (b : G.ChildBoundary c) :
    Continuous (G.capCentralElement c b) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

theorem tipCoordinate_negative (b : G.ChildBoundary c) :
    (G.static b.1).witness.tipCoordinate < 0 := by
  have h2 := (G.static b.1).witness.tipCoordinate_upper
  have h3 := parameters.fixed.collar_pos
  have h4 : 0 < standardCapL := standardCapL_pos
  linarith

theorem radialZero_mem_closedCore (b : G.ChildBoundary c) (y : Sphere 2) :
    (G.static b.1).witness.radial 0 • (y : ThreeSpace) ∈ standardCapClosedCore := by
  have htip := G.tipCoordinate_negative c b
  have h0mem : (0 : ℝ) ∈ Icc (G.static b.1).witness.tipCoordinate 0 := ⟨htip.le, le_rfl⟩
  obtain ⟨hnn, hle⟩ := (G.static b.1).witness.radial_range h0mem
  rw [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right, norm_smul, spherePoint_norm y,
    mul_one, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

def capCentralZero (b : G.ChildBoundary c) :
    ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  ⟨0, ⟨neg_lt_zero.mpr (inv_pos.mpr (G.static b.1).neck.delta_pos),
    inv_pos.mpr (G.static b.1).neck.delta_pos⟩⟩

def capCentralBase (b : G.ChildBoundary c) (y : Sphere 2) :
    Sphere 2 × ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  (y, G.capCentralZero c b)

def capCollapseMap (b : G.ChildBoundary c) :
    Sphere 2 × ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) →
      (H.stage i.succ).Carrier :=
  fun p => (G.static b.1).inclusion ((G.static b.1).witness.collapse (G.capCentralElement c b p))

theorem capCollapseMap_continuous (b : G.ChildBoundary c) :
    Continuous (G.capCollapseMap c b) :=
  (G.static b.1).inclusion.continuous.comp
    ((G.static b.1).witness.collapse.continuous.comp (G.capCentralElement_continuous c b))

theorem capCollapse_zero_eq (b : G.ChildBoundary c) (y : Sphere 2) :
    (G.static b.1).witness.collapse (G.capCentralElement c b (G.capCentralBase c b y)) =
      (G.static b.1).witness.capChart
        ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
          G.radialZero_mem_closedCore c b y⟩ :=
  (G.static b.1).witness.collapse_radial _ (G.tipCoordinate_negative c b) le_rfl _

theorem capCollapseMap_base_eq_capChart (b : G.ChildBoundary c) (y : Sphere 2) :
    G.capCollapseMap c b (G.capCentralBase c b y) =
      (G.static b.1).inclusion ((G.static b.1).witness.capChart
        ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
          G.radialZero_mem_closedCore c b y⟩) :=
  congrArg (G.static b.1).inclusion (G.capCollapse_zero_eq c b y)

theorem capCollapseMap_base_mem_child (b : G.ChildBoundary c) (y : Sphere 2) :
    ConnectedComponents.mk (G.capCollapseMap c b (G.capCentralBase c b y)) = c := by
  rw [G.capCollapseMap_base_eq_capChart c b y]
  have hmem : (G.static b.1).witness.capChart
      ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
        G.radialZero_mem_closedCore c b y⟩ ∈ Set.range (G.static b.1).witness.cap := by
    rw [← (G.static b.1).witness.capChart_range]
    exact Set.mem_range_self _
  obtain ⟨t, ht⟩ := hmem
  rw [← ht]
  exact G.capPoint_mem_child c b t

theorem connectedComponents_mk_eq_of_mem_preconnected {α : Type*} [TopologicalSpace α] {s : Set α}
    (h : IsPreconnected s) {p q : α} (hp : p ∈ s) (hq : q ∈ s) :
    ConnectedComponents.mk p = ConnectedComponents.mk q :=
  ConnectedComponents.coe_eq_coe'.mpr ((h.subset_connectedComponent hq) hp)

theorem capCollapseMap_preconnected (b : G.ChildBoundary c) :
    IsPreconnected (Set.range (G.capCollapseMap c b)) := by
  have : PreconnectedSpace (Sphere 2) := sphereTwo_connectedSpace.toPreconnectedSpace
  have : PreconnectedSpace ↑(Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
    G.capCentralDomain_preconnectedSpace c b
  exact isPreconnected_range (G.capCollapseMap_continuous c b)

theorem collapsePoint_mem_child (b : G.ChildBoundary c)
    (x : neckCentralDomain (G.static b.1).delta) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.collapse x) :
      (H.stage i.succ).Carrier) = c := by
  have hxmem : (G.static b.1).inclusion ((G.static b.1).witness.collapse x) ∈
      Set.range (G.capCollapseMap c b) := by
    refine ⟨(x.1.1.1, ⟨x.1.1.2, x.2.1, x.2.2⟩), ?_⟩
    have hxeq : G.capCentralElement c b (x.1.1.1, ⟨x.1.1.2, x.2.1, x.2.2⟩) = x :=
      Subtype.ext (Subtype.ext rfl)
    rw [capCollapseMap, hxeq]
  exact (connectedComponents_mk_eq_of_mem_preconnected (G.capCollapseMap_preconnected c b)
    hxmem (Set.mem_range_self (spherePoint, G.capCentralZero c b))).trans
    (G.capCollapseMap_base_mem_child c b spherePoint)

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

def localCollapseMap (b : G.ChildBoundary c) :
    C(neckCentralDomain (G.static b.1).delta, (G.Child c).Carrier) :=
  ⟨fun x => ⟨(G.static b.1).inclusion ((G.static b.1).witness.collapse x),
      G.collapsePoint_mem_child c b x⟩,
    Continuous.subtype_mk
      ((G.static b.1).inclusion.continuous.comp (G.static b.1).witness.collapse.continuous)
      (fun x => G.collapsePoint_mem_child c b x)⟩

theorem localCollapseMap_apply (b : G.ChildBoundary c) (x : neckCentralDomain (G.static b.1).delta) :
    (G.localCollapseMap c b x).1 =
      (G.static b.1).inclusion ((G.static b.1).witness.collapse x) := rfl

def tipPoint (b : G.ChildBoundary c) : (G.Child c).Carrier :=
  ⟨(G.static b.1).inclusion ((G.static b.1).witness.tip), G.tipPoint_mem_child c b⟩

theorem tipPoint_apply (b : G.ChildBoundary c) :
    (G.tipPoint c b).1 = (G.static b.1).inclusion ((G.static b.1).witness.tip) := rfl

theorem collarMap_inter_childCore_range_of_subset_ne_zero
    (hsubset : ∀ (b : G.ChildBoundary c) (y : Sphere 2)
      (t : ↑(Icc (G.comparisonLevel c b) 0)),
      G.collarMap c b (y, t) ∈ Set.range (G.transition.childCoreIntoParent c) → (t : ℝ) = 0)
    (b : G.ChildBoundary c) :
    Set.range (G.collarMap c b) ∩ Set.range (G.transition.childCoreIntoParent c) =
      Set.range (fun y : Sphere 2 =>
        G.collarMap c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩)) := by
  ext p
  constructor
  · rintro ⟨hp, hcore⟩
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, t⟩ := x
    have ht : (t : ℝ) = 0 := hsubset b y t hcore
    have ht' : t = ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩ := Subtype.ext ht
    refine ⟨y, ?_⟩
    rw [ht']
  · rintro ⟨y, rfl⟩
    exact ⟨Set.mem_range_self _, G.collarMap_zero_mem_childCore_range c b y⟩

theorem support_terminal_of_region (S : SmoothSphericalRegion (G.Parent c))
    (hregion : S.region = Set.range (G.transition.childCoreIntoParent c) ∪
      ⋃ b, Set.range (G.collarMap c b)) :
    ∀ x ∈ S.region, x.1 ∈ (H.event i).incoming.terminalRegularRegion := by
  intro x hx
  rw [hregion] at hx
  rcases hx with hx | hx
  · obtain ⟨y, rfl⟩ := hx
    exact G.childCoreIntoParent_terminal c y
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    obtain ⟨w, rfl⟩ := hb
    exact G.collarMap_terminal c b w

theorem rfs_comparison_support_of_region_data
    [SimplyConnectedSpace (G.Parent c).Carrier]
    (S : SmoothSphericalRegion (G.Parent c))
    (hregion : S.region = Set.range (G.transition.childCoreIntoParent c) ∪
      ⋃ b, Set.range (G.collarMap c b))
    (hlabel : G.ChildBoundary c ≃ S.Boundary)
    (hboundary : ∀ b : G.ChildBoundary c,
      (Subtype.val : S.region → (G.Parent c).Carrier) '' Set.range (S.sphere (hlabel b)) =
        Set.range (fun y : Sphere 2 => G.collarMap c b
          (y, ⟨G.comparisonLevel c b, le_rfl, (G.comparisonLevel_negative c b).le⟩))) :
    Nonempty (G.ComparisonSupport c) :=
  ⟨{ level := G.comparisonLevel c
     level_lower := G.comparisonLevel_lower c
     level_below_tip := G.comparisonLevel_below_tip c
     level_negative := G.comparisonLevel_negative c
     collarParameter := G.collarParameter c
     collarParameter_eq := G.collarParameter_apply c
     collar := G.collarMap c
     collar_eq := G.collarMap_apply c
     collar_core_intersection := G.collarMap_inter_childCore_range_of_subset_ne_zero c (by
       intro b y t ht
       by_contra hne
       obtain ⟨z, hz⟩ := ht
       have hzval : (z.1.1 : (H.stage i.castSucc).Carrier) =
           ((G.static b.1).neck.chart (G.collarParameter c b (y, t)).1).1 := by
         have h1 : (G.transition.childCoreIntoParent c z).1 = (G.collarMap c b (y, t)).1 :=
           congrArg Subtype.val hz
         exact h1.trans (G.collarMap_apply c b (y, t))
       have hneg : (G.collarParameter c b (y, t)).1.1.2 < 0 := by
         rw [G.collarParameter_apply c b (y, t)]
         exact lt_of_le_of_ne t.2.2 hne
       exact G.staticNeckChart_ne_childCore_of_coordinate_negative b.1 c b.2
         (G.collarParameter c b (y, t)).1 hneg z hzval.symm)
     collar_disjoint := G.collarMap_pairwise_disjoint c
     support := S
     support_eq := hregion
     support_terminal := G.support_terminal_of_region c S hregion
     boundaryLabel := hlabel
     boundary_eq := hboundary
     exterior := Classical.choice (rfs_exterior_branches (G.Parent c) S)
     localCollapse := G.localCollapseMap c
     localCollapse_eq := fun _ _ => rfl
     tip := G.tipPoint c
     tip_eq := fun _ => rfl }⟩

theorem rfs_comparison_support
    [SimplyConnectedSpace (G.Parent c).Carrier] : Nonempty (G.ComparisonSupport c) := by
  sorry

namespace ComparisonSupport

variable {G c} (K : G.ComparisonSupport c)


def IsWholeParentMap (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  (∀ x : G.transition.ChildCore c,
    f (G.transition.childCoreIntoParent c x) = G.transition.childCoreInclusion c x) ∧
  (∀ b x, f (K.collar b x) = K.localCollapse b (K.collarParameter b x)) ∧
  (∀ b x, x ∈ (K.exterior.exterior (K.boundaryLabel b)).region → f x = K.tip b)

def childCoreIntoParentFun : G.transition.ChildCore c → (G.Parent c).Carrier :=
  ⇑(G.transition.childCoreIntoParent c)

noncomputable def childCoreInclusionCoe : G.transition.ChildCore c → (G.Child c).Carrier :=
  ⇑(G.transition.childCoreInclusion c)

theorem childCoreIntoParent_isEmbedding :
    Topology.IsEmbedding (G.transition.childCoreIntoParent c) := by
  have hcomp : Topology.IsEmbedding (fun x : G.transition.ChildCore c =>
      (x.1.1 : (H.stage i.castSucc).Carrier)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hcomp' : Topology.IsEmbedding (Subtype.val ∘ ⇑(G.transition.childCoreIntoParent c)) :=
    hcomp
  exact (Topology.IsEmbedding.of_comp_iff
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (Subtype.val : (G.Parent c).Carrier → (H.stage i.castSucc).Carrier))).mp hcomp'

theorem collar_injective (b : G.ChildBoundary c) : Function.Injective (K.collar b) := by
  intro x y hxy
  have h1 : ((G.static b.1).neck.chart (K.collarParameter b x).1).1 =
      ((G.static b.1).neck.chart (K.collarParameter b y).1).1 := by
    rw [← K.collar_eq b x, ← K.collar_eq b y]
    exact congrArg (fun z : (G.Parent c).Carrier => (z.1 : (H.stage i.castSucc).Carrier)) hxy
  have h2 : (G.static b.1).neck.chart (K.collarParameter b x).1 =
      (G.static b.1).neck.chart (K.collarParameter b y).1 := Subtype.ext h1
  have h3 : (K.collarParameter b x).1 = (K.collarParameter b y).1 :=
    ((G.static b.1).neck.chart_smooth).isEmbedding.injective h2
  have h4 : K.collarParameter b x = K.collarParameter b y := Subtype.ext h3
  have h7 : (K.collarParameter b x).1.1 = (K.collarParameter b y).1.1 :=
    congrArg (fun z : ↑(neckCentralDomain (G.static b.1).delta) => z.1.1) h4
  rw [K.collarParameter_eq b x, K.collarParameter_eq b y] at h7
  obtain ⟨hx1, hx2⟩ := Prod.ext_iff.mp h7
  exact Prod.ext hx1 (Subtype.ext hx2)

theorem collar_isClosedEmbedding (b : G.ChildBoundary c) :
    Topology.IsClosedEmbedding (K.collar b) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (K.collar b).continuous (K.collar_injective b)
    (fun _s hs => (hs.isCompact.image (K.collar b).continuous).isClosed)

theorem collarParameter_continuous (b : G.ChildBoundary c) :
    Continuous (K.collarParameter b) := by
  have h2 : Continuous (fun x : Sphere 2 × ↑(Icc (K.level b) 0) =>
      (K.collarParameter b x).1.1) := by
    have heq : (fun x : Sphere 2 × ↑(Icc (K.level b) 0) =>
        (K.collarParameter b x).1.1) =
        fun x => (x.1, ((x.2 : ↑(Icc (K.level b) 0)) : ℝ)) := by
      funext x
      exact K.collarParameter_eq b x
    rw [heq]
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact Continuous.subtype_mk (Continuous.subtype_mk h2 (fun x => (K.collarParameter b x).1.2))
    (fun x => (K.collarParameter b x).2)

theorem exterior_exists (x : (G.Parent c).Carrier) (hx : x ∉ K.support.region) :
    ∃ b : G.ChildBoundary c, x ∈ (K.exterior.exterior (K.boundaryLabel b)).region := by
  have hx' : x ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
    rw [K.exterior.cover]
    trivial
  rcases hx' with hR | hU
  · exact absurd hR hx
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
    refine ⟨K.boundaryLabel.symm e, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact he

theorem localCollapse_level_zero_eq_childCoreInclusion
    (b : G.ChildBoundary c) (y : Sphere 2) (y' : G.transition.ChildCore c)
    (hy' : G.transition.childCoreIntoParent c y' =
      K.collar b (y, ⟨0, (K.level_negative b).le, le_rfl⟩)) :
    K.localCollapse b (K.collarParameter b (y, ⟨0, (K.level_negative b).le, le_rfl⟩)) =
      G.transition.childCoreInclusion c y' := by
  set x0 : Sphere 2 × ↑(Icc (K.level b) 0) := (y, ⟨0, (K.level_negative b).le, le_rfl⟩) with hx0
  set p : ↑(neckCentralDomain (G.static b.1).delta) := K.collarParameter b x0 with hp
  have hp1 : p.1.1 = (y, (0 : ℝ)) := by
    rw [hp, K.collarParameter_eq b x0]
  have hp2 : p.1.1.2 = (0 : ℝ) := congrArg Prod.snd hp1
  have hz0 : 0 ≤ p.1.1.2 := by rw [hp2]
  set zz : neckRetainedCollar (G.static b.1).delta := ⟨p.1.1, hz0, p.2.2⟩ with hzz
  have hcollapse : (G.static b.1).witness.collapse p =
      (G.static b.1).witness.retained zz := by
    rw [hzz]
    exact (G.static b.1).witness.collapse_retained p hz0
  have hlc : (K.localCollapse b p).1 =
      (G.static b.1).inclusion ((G.static b.1).witness.retained zz) := by
    rw [K.localCollapse_eq b p, hcollapse]
  have hpres : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion ((G.static b.1).retained_point zz).1)
      = Sum.inl ((K.localCollapse b p).1) := by
    rw [hlc]
    exact (G.static b.1).retained_eq zz
  have hpt : ((G.static b.1).retained_point zz).1.1 = (K.collar b x0).1 := by
    rw [(G.static b.1).retained_point_eq zz p.1.2, K.collar_eq b x0]
  have hy1 : y'.1.1 = (K.collar b x0).1 :=
    congrArg (fun z : (G.Parent c).Carrier => (z.1 : (H.stage i.castSucc).Carrier)) hy'
  have hcore : ((G.static b.1).retained_point zz).1 = y'.1 :=
    Subtype.ext (hpt.trans hy1.symm)
  have hpres' : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion y'.1)
      = Sum.inl ((K.localCollapse b p).1) := by
    rw [← hcore]
    exact hpres
  have hcc := G.transition.childCoreInclusionFun_eq c y'
  have hinl : Sum.inl ((K.localCollapse b p).1) =
      Sum.inl ((G.transition.childCoreInclusionFun c y').1) := hpres'.symm.trans hcc
  exact Subtype.ext (Sum.inl.inj hinl)

theorem localCollapse_level_eq_tip (b : G.ChildBoundary c) (y : Sphere 2) :
    K.localCollapse b (K.collarParameter b
      (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)) = K.tip b := by
  have hlt : (K.collarParameter b
      (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)).1.1.2 = K.level b := by
    rw [K.collarParameter_eq b _]
  have hc : (G.static b.1).witness.collapse
      (K.collarParameter b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩))
      = (G.static b.1).witness.tip :=
    (G.static b.1).witness.collapse_tip _
      (by
        rw [hlt]
        exact (K.level_below_tip b).le)
  apply Subtype.ext
  rw [K.localCollapse_eq b _, K.tip_eq b, hc]

theorem childCoreIntoParentFun_injective :
    Function.Injective (childCoreIntoParentFun (G := G) (c := c)) :=
  fun _ _ h => (childCoreIntoParent_isEmbedding (G := G) (c := c)).injective h

theorem exists_collarValue (x : (G.Parent c).Carrier)
    (h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(Icc (K.level b) 0)),
      K.collar b w = x) :
    ∃ v : (G.Child c).Carrier, ∀ (b : G.ChildBoundary c)
      (w : Sphere 2 × ↑(Icc (K.level b) 0)),
      K.collar b w = x → v = K.localCollapse b (K.collarParameter b w) := by
  obtain ⟨b₀, w₀, hw₀⟩ := h
  refine ⟨K.localCollapse b₀ (K.collarParameter b₀ w₀), fun b w hw => ?_⟩
  have hb : b₀ = b := by
    by_contra hne
    exact (Set.disjoint_left.mp (K.collar_disjoint hne)) ⟨_, hw₀⟩ ⟨_, hw⟩
  subst hb
  have hw' : w₀ = w := K.collar_injective _ (hw₀.trans hw.symm)
  subst hw'
  rfl

noncomputable def collarChoiceValue (x : (G.Parent c).Carrier)
    (h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(Icc (K.level b) 0)),
      K.collar b w = x) : (G.Child c).Carrier :=
  Classical.choose (K.exists_collarValue x h)

theorem collarChoiceValue_eq {x : (G.Parent c).Carrier}
    {h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(Icc (K.level b) 0)),
      K.collar b w = x} {b : G.ChildBoundary c}
    {w : Sphere 2 × ↑(Icc (K.level b) 0)} (hw : K.collar b w = x) :
    K.collarChoiceValue x h = K.localCollapse b (K.collarParameter b w) :=
  Classical.choose_spec (K.exists_collarValue x h) b w hw

noncomputable def supportFun (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    (G.Child c).Carrier := by
  classical
  exact if h : ∃ y : G.transition.ChildCore c, childCoreIntoParentFun y = x then
    childCoreInclusionCoe (Classical.choose h)
  else if h' : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(Icc (K.level b) 0)),
      K.collar b w = x then
    K.collarChoiceValue x h'
  else d

theorem supportFun_core (d : (G.Child c).Carrier) (y : G.transition.ChildCore c) :
    K.supportFun d (childCoreIntoParentFun y) = childCoreInclusionCoe y := by
  have h : ∃ y' : G.transition.ChildCore c,
      childCoreIntoParentFun y' = childCoreIntoParentFun y := ⟨y, rfl⟩
  rw [supportFun, dif_pos h]
  exact congrArg childCoreInclusionCoe
    (childCoreIntoParentFun_injective (G := G) (c := c) (Classical.choose_spec h))

theorem supportFun_collar (d : (G.Child c).Carrier) (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (K.level b) 0)) :
    K.supportFun d (K.collar b w) = K.localCollapse b (K.collarParameter b w) := by
  by_cases h : ∃ y : G.transition.ChildCore c, childCoreIntoParentFun y = K.collar b w
  · rw [supportFun, dif_pos h]
    have hmem : K.collar b w ∈ Set.range (K.collar b) ∩
        Set.range (G.transition.childCoreIntoParent c) :=
      ⟨Set.mem_range_self w, ⟨Classical.choose h, Classical.choose_spec h⟩⟩
    rw [K.collar_core_intersection b] at hmem
    obtain ⟨y', hy'⟩ := Set.mem_range.mp hmem
    have hw : w = (y', ⟨0, (K.level_negative b).le, le_rfl⟩) :=
      (K.collar_injective b hy').symm
    have hpp : K.collarParameter b w =
        K.collarParameter b (y', ⟨0, (K.level_negative b).le, le_rfl⟩) := by
      apply Subtype.ext
      apply Subtype.ext
      rw [K.collarParameter_eq b w,
        K.collarParameter_eq b (y', ⟨0, (K.level_negative b).le, le_rfl⟩), hw]
    rw [hpp]
    refine (K.localCollapse_level_zero_eq_childCoreInclusion b y' (Classical.choose h) ?_).symm
    exact (Classical.choose_spec h).trans (congrArg (K.collar b) hw)
  · have h' : ∃ (b' : G.ChildBoundary c) (w' : Sphere 2 × ↑(Icc (K.level b') 0)),
        K.collar b' w' = K.collar b w := ⟨b, w, rfl⟩
    rw [supportFun, dif_neg h, dif_pos h']
    exact K.collarChoiceValue_eq rfl

theorem childCoreIntoParentFun_continuous :
    Continuous (childCoreIntoParentFun (G := G) (c := c)) :=
  (G.transition.childCoreIntoParent c).continuous

theorem isClosed_range_childCoreIntoParentFun :
    IsClosed (Set.range (childCoreIntoParentFun (G := G) (c := c))) := by
  have hcl : IsClosed {z : (H.event i).transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} := by
    obtain ⟨z₀, hz₀⟩ := ConnectedComponents.surjective_coe (G.transition.childCoreComponent c)
    have hset : {z : (H.event i).transition.trace.tubes.core |
        ConnectedComponents.mk z = G.transition.childCoreComponent c} = connectedComponent z₀ := by
      ext z
      rw [← ConnectedComponents.coe_eq_coe', hz₀]
      exact Iff.rfl
    rw [hset]
    exact isClosed_connectedComponent
  have hcompact : IsCompact {z : (H.event i).transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} :=
    @IsClosed.isCompact _ _ _ G.transition.core_compact hcl
  have hsub : CompactSpace (G.transition.ChildCore c) := isCompact_iff_compactSpace.mp hcompact
  exact (@isCompact_range _ _ _ _ hsub _
    (childCoreIntoParentFun_continuous (G := G) (c := c))).isClosed

theorem continuousOn_supportFun_range_core (d : (G.Child c).Carrier) :
    ContinuousOn (K.supportFun d) (Set.range (childCoreIntoParentFun (G := G) (c := c))) := by
  have hind : Topology.IsInducing (childCoreIntoParentFun (G := G) (c := c)) :=
    (childCoreIntoParent_isEmbedding (G := G) (c := c)).isInducing
  rw [← Set.image_univ, hind.continuousOn_image_iff, continuousOn_univ]
  exact (G.transition.childCoreInclusion c).continuous.congr
    fun y => (K.supportFun_core d y).symm

theorem continuousOn_supportFun_range_collar (d : (G.Child c).Carrier) (b : G.ChildBoundary c) :
    ContinuousOn (K.supportFun d) (Set.range (K.collar b)) := by
  have hind : Topology.IsInducing (K.collar b) :=
    (K.collar_isClosedEmbedding b).isEmbedding.isInducing
  rw [← Set.image_univ, hind.continuousOn_image_iff, continuousOn_univ]
  exact ((K.localCollapse b).continuous.comp (K.collarParameter_continuous b)).congr
    fun w => (K.supportFun_collar d b w).symm

theorem continuousOn_supportFun_region (d : (G.Child c).Carrier) :
    ContinuousOn (K.supportFun d) K.support.region := by
  classical
  let piece : Option (G.ChildBoundary c) → Set (G.Parent c).Carrier := fun o =>
    match o with
    | none => Set.range (childCoreIntoParentFun (G := G) (c := c))
    | some b => Set.range (K.collar b)
  have hcover : ⋃ o, piece o = K.support.region := by
    rw [Set.iUnion_option piece]
    simp only [piece, K.support_eq]
    rfl
  rw [← hcover]
  refine (locallyFinite_of_finite piece).continuousOn_iUnion ?_ ?_
  · intro o
    cases o with
    | none => exact isClosed_range_childCoreIntoParentFun (G := G) (c := c)
    | some b => exact (K.collar_isClosedEmbedding b).isClosed_range
  · intro o
    cases o with
    | none => exact K.continuousOn_supportFun_range_core d
    | some b => exact K.continuousOn_supportFun_range_collar d b

noncomputable def wholeParentMapFun (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    (G.Child c).Carrier := by
  classical
  exact if hx : x ∈ K.support.region then K.supportFun d x
    else K.tip (Classical.choose (K.exterior_exists x hx))

theorem wholeParentMapFun_of_mem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∈ K.support.region) :
    K.wholeParentMapFun d x = K.supportFun d x := by
  rw [wholeParentMapFun, dif_pos hx]

theorem wholeParentMapFun_of_notMem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∉ K.support.region) :
    K.wholeParentMapFun d x = K.tip (Classical.choose (K.exterior_exists x hx)) := by
  rw [wholeParentMapFun, dif_neg hx]

theorem wholeParentMapFun_continuousOn_region (d : (G.Child c).Carrier) :
    ContinuousOn (K.wholeParentMapFun d) K.support.region :=
  (K.continuousOn_supportFun_region d).congr fun _ hx => K.wholeParentMapFun_of_mem d hx

theorem wholeParentMapFun_eq_tip_of_mem_exterior (d : (G.Child c).Carrier)
    {e : K.support.Boundary} {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior e).region) :
    K.wholeParentMapFun d x = K.tip (K.boundaryLabel.symm e) := by
  by_cases hR : x ∈ K.support.region
  · have hxint : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        Set.range (K.support.sphere e) := by
      rw [← K.exterior.intersection e]
      exact ⟨hx, hR⟩
    have hx' : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        Set.range (K.support.sphere (K.boundaryLabel (K.boundaryLabel.symm e))) := by
      rw [Equiv.apply_symm_apply]
      exact hxint
    rw [K.boundary_eq (K.boundaryLabel.symm e)] at hx'
    obtain ⟨y', hy'⟩ := hx'
    rw [K.wholeParentMapFun_of_mem d hR, ← hy',
      K.supportFun_collar d (K.boundaryLabel.symm e)]
    exact K.localCollapse_level_eq_tip (K.boundaryLabel.symm e) y'
  · have heq : K.boundaryLabel (Classical.choose (K.exterior_exists x hR)) = e := by
      by_contra hne
      exact (Set.disjoint_left.mp (K.exterior.disjoint hne))
        (Classical.choose_spec (K.exterior_exists x hR)) hx
    have hb : Classical.choose (K.exterior_exists x hR) = K.boundaryLabel.symm e :=
      K.boundaryLabel.injective (heq.trans (Equiv.apply_symm_apply K.boundaryLabel e).symm)
    rw [K.wholeParentMapFun_of_notMem d hR, hb]

theorem wholeParentMapFun_continuousOn_exterior (d : (G.Child c).Carrier)
    (e : K.support.Boundary) :
    ContinuousOn (K.wholeParentMapFun d) (K.exterior.exterior e).region :=
  continuousOn_const.congr fun _ hx => K.wholeParentMapFun_eq_tip_of_mem_exterior d hx

theorem wholeParentMapFun_continuous (d : (G.Child c).Carrier) :
    Continuous (K.wholeParentMapFun d) := by
  classical
  let finBoundary : Fintype K.support.Boundary := K.support.finiteBoundary
  let piece : Option K.support.Boundary → Set (G.Parent c).Carrier := fun o =>
    match o with
    | none => K.support.region
    | some e => (K.exterior.exterior e).region
  refine (locallyFinite_of_finite piece).continuous ?_ ?_ ?_
  · rw [Set.iUnion_option piece]
    simp only [piece]
    exact K.exterior.cover
  · intro o
    cases o with
    | none => exact K.support.compact.isClosed
    | some e => exact (K.exterior.exterior e).compact.isClosed
  · intro o
    cases o with
    | none => exact K.wholeParentMapFun_continuousOn_region d
    | some e => exact K.wholeParentMapFun_continuousOn_exterior d e

noncomputable def wholeParentMap (d : (G.Child c).Carrier) :
    C((G.Parent c).Carrier, (G.Child c).Carrier) :=
  ⟨K.wholeParentMapFun d, K.wholeParentMapFun_continuous d⟩

@[simp] theorem wholeParentMap_apply (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    K.wholeParentMap d x = K.wholeParentMapFun d x := rfl

theorem wholeParentMap_of_mem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∈ K.support.region) :
    K.wholeParentMap d x = K.supportFun d x := by
  rw [wholeParentMap_apply, K.wholeParentMapFun_of_mem d hx]

theorem wholeParentMap_isWholeParentMap (d : (G.Child c).Carrier) :
    K.IsWholeParentMap (K.wholeParentMap d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine (K.wholeParentMap_of_mem d ?_).trans (K.supportFun_core d y)
    rw [K.support_eq]
    exact Or.inl ⟨y, rfl⟩
  · intro b w
    refine (K.wholeParentMap_of_mem d ?_).trans (K.supportFun_collar d b w)
    rw [K.support_eq]
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self w⟩)
  · intro b x hx
    rw [K.wholeParentMap_apply, K.wholeParentMapFun_eq_tip_of_mem_exterior d hx,
      Equiv.symm_apply_apply]

theorem exists_unique_wholeParentMap :
    ∃! f : C((G.Parent c).Carrier, (G.Child c).Carrier), K.IsWholeParentMap f := by
  classical
  obtain ⟨q₀, hq₀⟩ := ConnectedComponents.surjective_coe c
  let d : (G.Child c).Carrier := ⟨q₀, hq₀⟩
  refine ⟨K.wholeParentMap d, K.wholeParentMap_isWholeParentMap d, ?_⟩
  · intro g hg
    apply ContinuousMap.ext
    intro x
    rw [K.wholeParentMap_apply]
    have hx' : x ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
      rw [K.exterior.cover]
      trivial
    rcases hx' with hR | hU
    · have hmem : x ∈ Set.range (G.transition.childCoreIntoParent c) ∪
          ⋃ b, Set.range (K.collar b) := by
        rw [← K.support_eq]
        exact hR
      rcases hmem with hc | hcoll
      · obtain ⟨y, hy⟩ := Set.mem_range.mp hc
        have hxR : G.transition.childCoreIntoParent c y ∈ K.support.region := by
          rw [K.support_eq]
          exact Or.inl ⟨y, rfl⟩
        have hwv : K.wholeParentMapFun d (G.transition.childCoreIntoParent c y) =
            childCoreInclusionCoe y :=
          (K.wholeParentMapFun_of_mem d hxR).trans (K.supportFun_core d y)
        rw [← hy]
        exact (hg.1 y).trans hwv.symm
      · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcoll
        obtain ⟨w, hw⟩ := Set.mem_range.mp hb
        have hxR : K.collar b w ∈ K.support.region := by
          rw [K.support_eq]
          exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self w⟩)
        have hwv : K.wholeParentMapFun d (K.collar b w) =
            K.localCollapse b (K.collarParameter b w) :=
          (K.wholeParentMapFun_of_mem d hxR).trans (K.supportFun_collar d b w)
        rw [← hw]
        exact (hg.2.1 b w).trans hwv.symm
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      have hge : g x = K.tip (K.boundaryLabel.symm e) := by
        refine hg.2.2 (K.boundaryLabel.symm e) x ?_
        rwa [Equiv.apply_symm_apply]
      rw [hge, K.wholeParentMapFun_eq_tip_of_mem_exterior d he]

def rfs_whole_parent_map : C((G.Parent c).Carrier, (G.Child c).Carrier) :=
  Classical.choose K.exists_unique_wholeParentMap

theorem wholeParentMap_spec : K.IsWholeParentMap K.rfs_whole_parent_map :=
  (Classical.choose_spec K.exists_unique_wholeParentMap).1

theorem rfs_whole_parent_map_eq_wholeParentMap (d : (G.Child c).Carrier) :
    K.rfs_whole_parent_map = K.wholeParentMap d :=
  ((Classical.choose_spec K.exists_unique_wholeParentMap).2 _
    (K.wholeParentMap_isWholeParentMap d)).symm

theorem rfs_whole_parent_map_childCore (x : G.transition.ChildCore c) :
    K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
      G.transition.childCoreInclusion c x :=
  K.wholeParentMap_spec.1 x

theorem rfs_whole_parent_map_collar (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (K.level b) 0)) :
    K.rfs_whole_parent_map (K.collar b w) =
      K.localCollapse b (K.collarParameter b w) :=
  K.wholeParentMap_spec.2.1 b w

theorem rfs_whole_parent_map_eq_tip_of_mem_exterior (b : G.ChildBoundary c)
    {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior (K.boundaryLabel b)).region) :
    K.rfs_whole_parent_map x = K.tip b :=
  K.wholeParentMap_spec.2.2 b x hx

theorem rfs_whole_parent_map_locallyConstant_of_notMem {x : (G.Parent c).Carrier}
    (hx : x ∉ K.support.region) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, K.rfs_whole_parent_map y = K.rfs_whole_parent_map x := by
  classical
  let : Fintype K.support.Boundary := K.support.finiteBoundary
  obtain ⟨b₀, hb₀⟩ := K.exterior_exists x hx
  have hxS : x ∈ (K.exterior.exterior (K.boundaryLabel b₀)).region := hb₀
  have hclosed : IsClosed (K.support.region ∪
      ⋃ e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀},
        (K.exterior.exterior e.1).region) :=
    K.support.compact.isClosed.union
      (isClosed_iUnion_of_finite fun e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀} =>
        (K.exterior.exterior e.1).compact.isClosed)
  have hxU : x ∈ (K.support.region ∪
      ⋃ e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀},
        (K.exterior.exterior e.1).region)ᶜ := by
    intro hmem
    rcases hmem with hR | hU
    · exact hx hR
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      exact (Set.disjoint_left.mp (K.exterior.disjoint (Ne.symm e.2))) hxS he
  refine ⟨_, hclosed.isOpen_compl.mem_nhds hxU, ?_⟩
  intro y hy
  have hyS : y ∈ (K.exterior.exterior (K.boundaryLabel b₀)).region := by
    have hcover : y ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
      rw [K.exterior.cover]
      trivial
    rcases hcover with hR | hU
    · exact absurd hR (fun h => hy (Or.inl h))
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      by_cases hee : e = K.boundaryLabel b₀
      · rwa [hee] at he
      · exact absurd (Set.mem_iUnion.mpr ⟨⟨e, hee⟩, he⟩) (fun h => hy (Or.inr h))
  rw [K.rfs_whole_parent_map_eq_tip_of_mem_exterior b₀ hxS,
    K.rfs_whole_parent_map_eq_tip_of_mem_exterior b₀ hyS]

theorem rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl
    {γ : ℝ → (G.Parent c).Carrier} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    (hmap : ∀ t ∈ Icc a b, γ t ∉ K.support.region) :
    riemannianCurveLength (H.event i).outputMetric
      (fun t => (K.rfs_whole_parent_map (γ t)).1) a b = 0 := by
  by_cases hab : a ≤ b
  · refine riemannianCurveLength_eq_zero_of_apply_eq_const _ _
      (q := (K.rfs_whole_parent_map (γ a)).1) ?_
    let γ' : Icc a b → (G.Parent c).Carrier := fun t => γ t
    have hcont : Continuous γ' := hγ.domRestrict
    have hlc : IsLocallyConstant (fun t : Icc a b => K.rfs_whole_parent_map (γ' t)) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro t
      have ht : γ t ∉ K.support.region := hmap t t.2
      obtain ⟨U, hU, hfU⟩ := K.rfs_whole_parent_map_locallyConstant_of_notMem ht
      obtain ⟨V, hVU, hVo, htV⟩ := mem_nhds_iff.mp hU
      exact ⟨γ' ⁻¹' V, hcont.isOpen_preimage V hVo, htV,
        fun s hs => hfU (γ' s) (hVU hs)⟩
    have hpre : PreconnectedSpace (Icc a b) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hconst := congrFun (@IsLocallyConstant.eq_const (Icc a b)
      ((G.Child c).Carrier) inferInstance hpre
      (fun t : Icc a b => K.rfs_whole_parent_map (γ' t)) hlc ⟨a, left_mem_Icc.mpr hab⟩)
    intro t ht
    exact congrArg Subtype.val (hconst ⟨t, ht⟩)
  · exact riemannianCurveLength_eq_zero_of_apply_eq_const _ _
      (q := (K.rfs_whole_parent_map (γ a)).1)
      (fun t ht => absurd (ht.1.trans ht.2) hab)

theorem rfs_whole_parent_map_surjective_of_cover
    (hcov : Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = univ) :
    Function.Surjective K.rfs_whole_parent_map := by
  intro v
  have hv : v ∈ Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) := by
    rw [hcov]
    trivial
  rcases hv with hcore | hcollar
  · obtain ⟨y, rfl⟩ := hcore
    exact ⟨G.transition.childCoreIntoParent c y, K.rfs_whole_parent_map_childCore y⟩
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcollar
    obtain ⟨w, rfl⟩ := hb
    exact ⟨K.collar b w, K.rfs_whole_parent_map_collar b w⟩

def LocalTerminalLengthControl (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  ∀ x ∈ K.support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    (∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf (H.event i).outputMetric (f y).1 (f z).1 ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩) ∧
    (∀ (γ : ℝ → (H.event i).incoming.terminalRegularOpen)
      (hparent : ∀ t, ConnectedComponents.mk (γ t).1 = G.transition.childParent c)
      (a b : ℝ), a ≤ b → ContinuousOn γ (Icc a b) →
      (∀ t ∈ Icc a b, (⟨(γ t).1, hparent t⟩ : (G.Parent c).Carrier) ∈ U) →
      riemannianCurveLength (H.event i).terminal.metric γ a b ≠ ⊤ →
      riemannianCurveLength (H.event i).outputMetric
        (fun t => (f ⟨(γ t).1, hparent t⟩).1) a b ≤
          riemannianCurveLength (H.event i).terminal.metric γ a b)

theorem rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz
    (hf : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map := by
  intro x hx
  refine ⟨{y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      (K.support_terminal x hx),
    fun _ hy => hy, fun y _ z _ hy hz => hf y z hy hz, ?_⟩
  intro γ hparent a b hab hγ hU hlen
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_iSup (fun q : ℕ ×
    {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ Icc a b} =>
      ∑ j ∈ Finset.range q.1, riemannianEDistOf (H.event i).terminal.metric
        (γ (q.2.1 (j + 1))) (γ (q.2.1 j))) p)
  exact hf ⟨(γ (p.2.1 (k + 1))).1, hparent (p.2.1 (k + 1))⟩
    ⟨(γ (p.2.1 k)).1, hparent (p.2.1 k)⟩ (γ (p.2.1 (k + 1))).2 (γ (p.2.1 k)).2

theorem rfs_collapse_degree_of_local_inputs
    (hlip : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)
    (hcov : Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = univ) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    Function.Surjective K.rfs_whole_parent_map :=
  ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz hlip,
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    fun x => K.rfs_whole_parent_map_childCore x,
    K.rfs_whole_parent_map_surjective_of_cover hcov⟩

theorem collarParameter_fst (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (K.level b) 0)) :
    (K.collarParameter b w).1.1.1 = w.1 :=
  congrArg Prod.fst (K.collarParameter_eq b w)

theorem collarParameter_snd (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (K.level b) 0)) :
    (K.collarParameter b w).1.1.2 = (w.2 : ℝ) :=
  congrArg (fun p : Sphere 2 × ℝ => p.2) (K.collarParameter_eq b w)

private theorem standardCapL_pos : (0 : ℝ) < standardCapL := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h : 0 < Real.pi / Real.sqrt 2 := div_pos hpi hsqrt
  simp only [standardCapL, standardCapA0]
  linarith

theorem exists_collarParameter_collapse_eq_cap (b : G.ChildBoundary c) (x : ThreeBall) :
    ∃ w : Sphere 2 × ↑(Icc (K.level b) 0),
      (K.localCollapse b (K.collarParameter b w)).1 =
        (G.static b.1).inclusion ((G.static b.1).witness.cap x) := by
  classical
  have hmem : (G.static b.1).witness.cap x ∈
      Set.range (G.static b.1).witness.capChart := by
    rw [(G.static b.1).witness.capChart_range]
    exact Set.mem_range_self x
  obtain ⟨x₀, hx₀⟩ := hmem
  have hnorm_le : ‖x₀.1‖ ≤ standardCapL := by
    simpa [standardCapClosedCore, Metric.mem_closedBall, dist_eq_norm] using x₀.2
  by_cases hzero : x₀.1 = 0
  · refine ⟨((G.static b.1).neck.sphereMark,
      ⟨K.level b, le_rfl, (K.level_negative b).le⟩), ?_⟩
    have hx0eq : x₀ = (⟨0, by simpa [standardCapClosedCore, hzero] using x₀.2⟩ :
        standardCapClosedCore) := Subtype.ext hzero
    have hcap : (G.static b.1).witness.cap x = (G.static b.1).witness.tip := by
      rw [← hx₀, hx0eq]
      exact (G.static b.1).witness.capChart_tip _
    have hcoll : (G.static b.1).witness.collapse
        (K.collarParameter b ((G.static b.1).neck.sphereMark,
          ⟨K.level b, le_rfl, (K.level_negative b).le⟩)) =
        (G.static b.1).witness.tip := by
      refine (G.static b.1).witness.collapse_tip _ ?_
      rw [K.collarParameter_snd b _]
      exact (K.level_below_tip b).le
    rw [K.localCollapse_eq b _, hcoll, hcap]
  · have hpos : 0 < ‖x₀.1‖ := norm_pos_iff.mpr hzero
    let y : Sphere 2 :=
      ⟨(‖x₀.1‖⁻¹ : ℝ) • x₀.1, by
        rw [Metric.mem_sphere, dist_zero_right]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x₀.1))]
        exact inv_mul_cancel₀ (ne_of_gt hpos)⟩
    have htip_le : (G.static b.1).witness.tipCoordinate ≤ 0 := by
      have h1 := (G.static b.1).witness.tipCoordinate_upper
      have h2 := parameters.fixed.collar_pos
      have h3 := standardCapL_pos
      linarith
    obtain ⟨zz, hzz, hzzr⟩ : ∃ zz ∈ Set.Icc (G.static b.1).witness.tipCoordinate 0,
        (G.static b.1).witness.radial zz = ‖x₀.1‖ := by
      have hsub := intermediate_value_Icc htip_le (G.static b.1).witness.radial_continuous
      have hmem' : ‖x₀.1‖ ∈ Set.Icc
          ((G.static b.1).witness.radial (G.static b.1).witness.tipCoordinate)
          ((G.static b.1).witness.radial 0) := by
        rw [(G.static b.1).witness.radial_tip, (G.static b.1).witness.radial_boundary]
        exact ⟨norm_nonneg _, hnorm_le⟩
      exact hsub hmem'
    have hzz_gt : (G.static b.1).witness.tipCoordinate < zz := by
      rcases lt_trichotomy zz (G.static b.1).witness.tipCoordinate with h | h | h
      · exact absurd h (not_lt.mpr hzz.1)
      · rw [h, (G.static b.1).witness.radial_tip] at hzzr
        exact absurd hzzr.symm (ne_of_gt hpos)
      · exact h
    have hsmul : (G.static b.1).witness.radial zz • y.1 = x₀.1 := by
      rw [hzzr]
      exact smul_inv_smul₀ (ne_of_gt hpos) x₀.1
    have hlevel : K.level b ≤ (⟨zz, (lt_trans (K.level_below_tip b) hzz_gt).le, hzz.2⟩ :
        ↑(Icc (K.level b) 0)) := (lt_trans (K.level_below_tip b) hzz_gt).le
    refine ⟨(y, ⟨zz, hlevel, hzz.2⟩), ?_⟩
    have hball : (G.static b.1).witness.radial
        ((K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2) •
        ((K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.1.1) ∈ standardCapClosedCore := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩),
        K.collarParameter_fst b (y, ⟨zz, hlevel, hzz.2⟩), hsmul]
      exact x₀.2
    have hgt : (G.static b.1).witness.tipCoordinate <
        (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2 := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hzz_gt
    have hle : (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2 ≤ 0 := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hzz.2
    have hcollapse : (G.static b.1).witness.collapse
        (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)) =
        (G.static b.1).witness.capChart x₀ := by
      rw [(G.static b.1).witness.collapse_radial (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩))
        hgt hle hball]
      refine congrArg (G.static b.1).witness.capChart (Subtype.ext ?_)
      simp only [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩),
        K.collarParameter_fst b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hsmul
    rw [K.localCollapse_eq b (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)), hcollapse, hx₀]

theorem rfs_collapse_cover :
    Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = univ := by
  have hcov := G.transition.range_childCoreInclusion_union_range_childCap c
  refine Set.eq_univ_of_forall fun v => ?_
  have hv : v ∈ Set.range (G.transition.childCoreInclusion c) ∪
      ⋃ b : G.transition.ChildCapBoundary c, Set.range (G.transition.childCap c b) := by
    rw [hcov]
    trivial
  rcases hv with h | h
  · exact Or.inl h
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
    obtain ⟨z, hz⟩ := hb
    have hbRet : (H.event i).RetainedBoundary b.1 :=
      G.transition.retainedBoundary_of_mem_childCapBoundary c b
    obtain ⟨w, hw⟩ := K.exists_collarParameter_collapse_eq_cap
      (⟨⟨b.1, hbRet⟩, b.2⟩ : G.ChildBoundary c) z
    refine Or.inr (Set.mem_iUnion.mpr ⟨(⟨⟨b.1, hbRet⟩, b.2⟩ : G.ChildBoundary c), ?_⟩)
    refine ⟨w, Subtype.ext ?_⟩
    have hz1 : (G.transition.childCap c b z).1 =
        (G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).inclusion
          ((G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).witness.cap z) :=
      Sum.inl.inj ((G.transition.childCapFun_eq c b z).symm.trans
        ((G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).cap_eq z))
    exact hw.trans (hz1.symm.trans (congrArg Subtype.val hz))


theorem childCore_subset_old (x : G.transition.ChildCore c) : x.1 ∈ (H.event i).old := by
  have hcoreCompact : CompactSpace G.transition.trace.tubes.core := G.transition.core_compact
  have hcoreConnected : LocallyConnectedSpace G.transition.trace.tubes.core :=
    G.transition.core_locallyConnected
  have h := CutCapTopology.childCore_subset_retainedCore (E := G.transition.trace) c x.2
  rw [G.old_eq_retained]
  exact h

theorem oldOutput_eq_childCoreInclusion (x : G.transition.ChildCore c) :
    (H.event i).oldOutput ⟨x.1, childCore_subset_old x⟩ =
      (G.transition.childCoreInclusion c x).1 :=
  Sum.inl.inj (((H.event i).oldOutput_eq
    ⟨x.1, childCore_subset_old x⟩).symm.trans (G.transition.childCoreInclusionFun_eq c x))

theorem rfs_collapse_degree_of_lipschitz_and_degree
    (hlip : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)
    (hclass : integralHomologyMap 3 K.rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.rfs_whole_parent_map := by
  obtain ⟨h1, h2, h3, h4⟩ := K.rfs_collapse_degree_of_local_inputs hlip K.rfs_collapse_cover
  exact ⟨h1, h2, h3, hclass, h4⟩
theorem rfs_collapse_degree [SimplyConnectedSpace (G.Parent c).Carrier] :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.rfs_whole_parent_map := by
  sorry

end ComparisonSupport

theorem rfs_child_comparison_of_local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hdegree : ∀ c, integralHomologyMap 3 (Kc c).rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation)
    (hlocal : ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region,
        ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
          riemannianCurveLength ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s)
            (G.transition.childParent c)) γ a b ≠ ⊤ →
          riemannianCurveLength
            ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength
            ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₀, hs₀, ell, hell, htend, hloc⟩ := hlocal
  refine ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => ⟨Kc c, rfl⟩,
    fun c => hdegree c, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x y
  let gs : SmoothRiemannianMetric ThreeModel (G.Parent c).Carrier :=
    (H.stage i.castSucc).componentMetric ((H.event i).incoming.flow.base.metric s)
      (G.transition.childParent c)
  let hc : SmoothRiemannianMetric ThreeModel (G.Child c).Carrier :=
    (H.stage i.succ).componentMetric (H.event i).outputMetric c
  have hL : (0 : ℝ) ≤ ell s := le_trans zero_le_one (hell s hs)
  have hlocFull : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
      ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
        riemannianCurveLength gs γ a b ≠ ⊤ →
        riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength gs γ a b := by
    intro x
    by_cases hx : x ∈ (Kc c).support.region
    · obtain ⟨U, hU, hU'⟩ := hloc c s hs x hx
      exact ⟨U, hU, hU'⟩
    · obtain ⟨U, hU, hconst⟩ := (Kc c).rfs_whole_parent_map_locallyConstant_of_notMem hx
      refine ⟨U, hU, fun a b γ hab hγ hmap hfin => ?_⟩
      have hone : ∀ t ∈ Icc a b, (fun t => (Kc c).rfs_whole_parent_map (γ t)) t =
          (Kc c).rfs_whole_parent_map x :=
        fun t ht => hconst (γ t) (hmap ht)
      have hzero := riemannianCurveLength_eq_zero_of_apply_eq_const (g := hc)
        (γ := fun t => (Kc c).rfs_whole_parent_map (γ t))
        (a := a) (b := b) (q := (Kc c).rfs_whole_parent_map x) hone
      rw [hzero]
      exact bot_le
  let : SecondCountableTopology (G.Parent c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Parent c).Carrier
  let : SecondCountableTopology (G.Child c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Child c).Carrier
  by_cases hfin : riemannianEDistOf gs x y = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (hell s hs))))]
    exact le_top
  · have hlocCoe : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
        ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
          riemannianCurveLength gs γ a b ≠ ⊤ →
          riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
            ↑(NNReal.mk (ell s) hL) * riemannianCurveLength gs γ a b :=
      fun x => by
        obtain ⟨U, hU, hU'⟩ := hlocFull x
        exact ⟨U, hU, fun a b γ hab hγ hmap hfin => by
          simpa only [ENNReal.ofReal_eq_coe_nnreal hL] using hU' a b γ hab hγ hmap hfin⟩
    have h := rfs_local_to_global_length_of_ne_top gs hc
      ((Kc c).rfs_whole_parent_map) (NNReal.mk (ell s) hL) hlocCoe hfin
    rwa [ENNReal.ofReal_eq_coe_nnreal hL]

theorem rfs_child_comparison
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
    (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  sorry

theorem rfs_child_comparison_maps_of_inputs
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
      ∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map :=
  ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => ⟨Kc c, rfl⟩⟩

theorem rfs_child_comparison_length_of_inputs
    (f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier))
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hf : ∀ c, f c = (Kc c).rfs_whole_parent_map)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) (ell : ℝ → ℝ)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlen : ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
      riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        ((Kc c).rfs_whole_parent_map x) ((Kc c).rfs_whole_parent_map y) ≤
      ENNReal.ofReal (ell s) * riemannianEDistOf
        ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y) :
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤
        ENNReal.ofReal (ell s) * riemannianEDistOf
          ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  ⟨s₀, hs₀, ell, hell, htend, fun c s hs x y => by
    rw [hf c]
    exact hlen c s hs x y⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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
