import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff



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

theorem exists_unique_wholeParentMap :
    ∃! f : C((G.Parent c).Carrier, (G.Child c).Carrier), K.IsWholeParentMap f := by
  sorry

def rfs_whole_parent_map : C((G.Parent c).Carrier, (G.Child c).Carrier) :=
  Classical.choose K.exists_unique_wholeParentMap

theorem wholeParentMap_spec : K.IsWholeParentMap K.rfs_whole_parent_map :=
  (Classical.choose_spec K.exists_unique_wholeParentMap).1

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

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
