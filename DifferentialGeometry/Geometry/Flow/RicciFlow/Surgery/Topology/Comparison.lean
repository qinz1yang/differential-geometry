import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation



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
  sphere_smooth : ∀ b, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (sphere b)
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
