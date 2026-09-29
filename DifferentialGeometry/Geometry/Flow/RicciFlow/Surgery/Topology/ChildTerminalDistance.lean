import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreSurvivorLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegionConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs
import DifferentialGeometry.Geometry.Metric.DistancePullback

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem rfs_whole_parent_map_staticNeckPoint_of_nonneg (b : G.ChildBoundary c)
    (z : neckCentralDomain (G.static b.1).delta) (hz : 0 ≤ z.1.1.2) :
    K.canonicalWholeParentMap (G.staticNeckPoint c b z.1) = K.localCollapse b z := by
  obtain ⟨x, hx⟩ := G.staticNeckPoint_mem_childCore_range c b z.1 hz
  rw [← hx, K.rfs_whole_parent_map_childCore]
  apply Subtype.ext
  rw [K.localCollapse_eq b z, (G.static b.1).witness.collapse_retained z hz]
  let w : neckRetainedCollar (G.static b.1).delta := ⟨z.1.1, hz, z.2.2⟩
  have hpoint : ((G.static b.1).retainedPoint w).1 = x.1 := by
    apply Subtype.ext
    rw [(G.static b.1).retained_point_eq w z.1.2]
    exact congrArg Subtype.val hx.symm
  have hpres := (G.static b.1).retained_eq w
  rw [hpoint] at hpres
  exact (Sum.inl.inj ((G.transition.childCoreInclusionFun_eq c x).symm.trans hpres))

private theorem rfs_whole_parent_map_staticNeckPoint_of_level_le (b : G.ChildBoundary c)
    (z : neckCentralDomain (G.static b.1).delta) (hz : K.level b ≤ z.1.1.2) :
    K.canonicalWholeParentMap (G.staticNeckPoint c b z.1) = K.localCollapse b z := by
  by_cases h0 : 0 ≤ z.1.1.2
  · exact K.rfs_whole_parent_map_staticNeckPoint_of_nonneg b z h0
  · let w : Sphere 2 × ↑(Icc (K.level b) 0) := ⟨z.1.1.1, z.1.1.2, hz, (not_le.mp h0).le⟩
    have harg : K.collarParameter b w = z := by
      apply Subtype.ext
      apply Subtype.ext
      rw [K.collarParameter_eq]
    have hpoint : K.collar b w = G.staticNeckPoint c b z.1 := by
      apply Subtype.ext
      rw [K.collar_eq, harg]
      rfl
    rw [← hpoint, K.rfs_whole_parent_map_collar, harg]

private theorem exists_nhds_staticNeckPoint_eq_localCollapse (b : G.ChildBoundary c)
    (z : neckCentralDomain (G.static b.1).delta) (hz : K.level b < z.1.1.2)
    {U : Set (neckCentralDomain (G.static b.1).delta)} (hU : U ∈ 𝓝 z) :
    ∃ V ∈ 𝓝 (G.staticNeckPoint c b z.1), ∀ y ∈ V,
      ∃ w ∈ U, G.staticNeckPoint c b w.1 = y ∧
        K.canonicalWholeParentMap y = K.localCollapse b w := by
  obtain ⟨O, Φ, hO, -, -⟩ := G.exists_diffeomorph_range_staticNeck c b
  have hopen : _root_.Topology.IsOpenEmbedding (G.staticNeckPoint c b) :=
    ⟨(G.staticNeckPoint_isSmoothEmbedding c b).isEmbedding, hO ▸ O.isOpen⟩
  have hcentral : IsOpen (neckCentralDomain (G.static b.1).delta) :=
    (isOpen_lt continuous_const continuous_subtype_val.snd).inter
      (isOpen_lt continuous_subtype_val.snd continuous_const)
  have hopen' : _root_.Topology.IsOpenEmbedding
      (fun w : neckCentralDomain (G.static b.1).delta => G.staticNeckPoint c b w.1) :=
    hopen.comp hcentral.isOpenEmbedding_subtypeVal
  let S : Set (neckCentralDomain (G.static b.1).delta) := {w | K.level b < w.1.1.2}
  have hS : IsOpen S :=
    isOpen_lt continuous_const (continuous_subtype_val.comp continuous_subtype_val).snd
  refine ⟨(fun w : neckCentralDomain (G.static b.1).delta => G.staticNeckPoint c b w.1) ''
      (U ∩ S), hopen'.isOpenMap.image_mem_nhds (Filter.inter_mem hU (hS.mem_nhds hz)), ?_⟩
  rintro y ⟨w, hw, rfl⟩
  exact ⟨w, hw.1, rfl, K.rfs_whole_parent_map_staticNeckPoint_of_level_le b w hw.2.le⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem localCollapse_eq_tip_of_le (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (K.level b) 0))
    (hw : (w.2 : ℝ) ≤ (G.static b.1).witness.tipCoordinate) :
    K.localCollapse b (K.collarParameter b w) = K.tip b := by
  apply Subtype.ext
  rw [K.localCollapse_eq, K.tip_eq]
  congr 1
  apply (G.static b.1).witness.collapse_tip
  have heq := congrArg Prod.snd (K.collarParameter_eq b w)
  exact heq ▸ hw

private theorem collar_level_mem_exterior (b : G.ChildBoundary c) (y : Sphere 2) :
    K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) ∈
      (K.exterior.exterior (K.boundaryLabel b)).region := by
  have hb : K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) ∈
      (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        range (K.support.sphere (K.boundaryLabel b)) := by
    rw [K.boundary_eq b]
    exact mem_range_self y
  rw [← K.exterior.intersection] at hb
  exact hb.1

private theorem collar_level_notMem_core (b : G.ChildBoundary c) (y : Sphere 2) :
    K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) ∉
      range (G.transition.childCoreIntoParent c) := by
  intro hx
  have hi : K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) ∈
      range (K.collar b) ∩ range (G.transition.childCoreIntoParent c) :=
    ⟨mem_range_self _, hx⟩
  rw [K.collar_core_intersection] at hi
  obtain ⟨y', hy'⟩ := hi
  have hcoord := congrArg (fun w : Sphere 2 × ↑(Icc (K.level b) 0) => (w.2 : ℝ))
    (K.collar_injective b hy')
  exact (ne_of_lt (K.level_negative b)) hcoord.symm

private theorem rfs_whole_parent_map_eventually_eq_tip_at_collar_level
    (b : G.ChildBoundary c) (y : Sphere 2) :
    ∀ᶠ x in 𝓝 (K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)),
      K.canonicalWholeParentMap x = K.tip b := by
  classical
  let : Fintype K.support.Boundary := K.support.finiteBoundary
  let upper : Set (Sphere 2 × ↑(Icc (K.level b) 0)) :=
    {w | (G.static b.1).witness.tipCoordinate ≤ (w.2 : ℝ)}
  have hupper : IsClosed (K.collar b '' upper) := by
    apply (K.collar_isClosedEmbedding b).isClosedMap
    exact isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  let bad : Set (G.Parent c).Carrier :=
    range (G.transition.childCoreIntoParent c) ∪
      ((⋃ d : {d : G.ChildBoundary c // d ≠ b}, range (K.collar d.1)) ∪
        ((⋃ e : {e : K.support.Boundary // e ≠ K.boundaryLabel b},
          (K.exterior.exterior e.1).region) ∪ K.collar b '' upper))
  have hbad : IsClosed bad :=
    (isClosed_range_childCoreIntoParentFun (G := G) (c := c)).union
      ((isClosed_iUnion_of_finite fun d : {d : G.ChildBoundary c // d ≠ b} =>
        (K.collar_isClosedEmbedding d.1).isClosed_range).union
        ((isClosed_iUnion_of_finite fun e : {e : K.support.Boundary // e ≠ K.boundaryLabel b} =>
          (K.exterior.exterior e.1).compact.isClosed).union
          hupper))
  have hnot : K.collar b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) ∉ bad := by
    rintro (hcore | hcollar | hext | hu)
    · exact K.collar_level_notMem_core b y hcore
    · obtain ⟨d, hd⟩ := mem_iUnion.mp hcollar
      exact disjoint_left.mp (K.collar_disjoint (Ne.symm d.2)) (mem_range_self _) hd
    · obtain ⟨e, he⟩ := mem_iUnion.mp hext
      exact disjoint_left.mp (K.exterior.disjoint (Ne.symm e.2))
        (K.collar_level_mem_exterior b y) he
    · obtain ⟨w, hw, heq⟩ := hu
      have hw' := K.collar_injective b heq
      have hcoord := congrArg (fun w : Sphere 2 × ↑(Icc (K.level b) 0) => (w.2 : ℝ)) hw'
      have hle : (G.static b.1).witness.tipCoordinate ≤ K.level b := by
        change (G.static b.1).witness.tipCoordinate ≤ (w.2 : ℝ) at hw
        change (w.2 : ℝ) = K.level b at hcoord
        exact hcoord ▸ hw
      exact (not_le.mpr (K.level_below_tip b)) hle
  filter_upwards [hbad.isOpen_compl.mem_nhds hnot] with x hx
  have hxcore : x ∉ range (G.transition.childCoreIntoParent c) :=
    fun h => hx (Or.inl h)
  have hxc : ∀ d : {d : G.ChildBoundary c // d ≠ b}, x ∉ range (K.collar d.1) :=
    fun d h => hx (Or.inr (Or.inl (mem_iUnion.mpr ⟨d, h⟩)))
  have hxe : ∀ e : {e : K.support.Boundary // e ≠ K.boundaryLabel b},
      x ∉ (K.exterior.exterior e.1).region :=
    fun e h => hx (Or.inr (Or.inr (Or.inl (mem_iUnion.mpr ⟨e, h⟩))))
  have hxu : x ∉ K.collar b '' upper :=
    fun h => hx (Or.inr (Or.inr (Or.inr h)))
  have hcover : x ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
    rw [K.exterior.cover]
    trivial
  rcases hcover with hsupport | hext
  · rw [K.support_eq] at hsupport
    rcases hsupport with hcore | hcollar
    · exact (hxcore hcore).elim
    · obtain ⟨d, w, hw⟩ := mem_iUnion.mp hcollar
      have hdb : d = b := by
        by_contra hne
        exact hxc ⟨d, hne⟩ ⟨w, hw⟩
      subst d
      rw [← hw, K.rfs_whole_parent_map_collar]
      apply K.localCollapse_eq_tip_of_le
      exact (not_le.mp (fun hu => hxu ⟨w, hu, hw⟩)).le
  · obtain ⟨e, he⟩ := mem_iUnion.mp hext
    have heb : e = K.boundaryLabel b := by
      by_contra hne
      exact hxe ⟨e, hne⟩ he
    apply K.rfs_whole_parent_map_eq_tip_of_mem_exterior b
    rwa [heb] at he

private theorem rfs_whole_parent_map_eventually_eq_tip_of_mem_exterior
    (b : G.ChildBoundary c) {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior (K.boundaryLabel b)).region) :
    ∀ᶠ y in 𝓝 x, K.canonicalWholeParentMap y = K.tip b := by
  by_cases hxR : x ∈ K.support.region
  · have hboundary : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        range (K.support.sphere (K.boundaryLabel b)) := by
      rw [← K.exterior.intersection]
      exact ⟨hx, hxR⟩
    rw [K.boundary_eq b] at hboundary
    obtain ⟨y, rfl⟩ := hboundary
    exact K.rfs_whole_parent_map_eventually_eq_tip_at_collar_level b y
  · obtain ⟨U, hU, heq⟩ := K.rfs_whole_parent_map_locallyConstant_of_notMem hxR
    filter_upwards [hU] with y hy
    exact (heq y hy).trans (K.rfs_whole_parent_map_eq_tip_of_mem_exterior b hx)

private theorem rfs_whole_parent_map_locallyConstant_of_mem_exterior
    (b : G.ChildBoundary c) {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior (K.boundaryLabel b)).region) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, K.canonicalWholeParentMap y = K.canonicalWholeParentMap x := by
  refine ⟨{y | K.canonicalWholeParentMap y = K.tip b},
    K.rfs_whole_parent_map_eventually_eq_tip_of_mem_exterior b hx, ?_⟩
  intro y hy
  exact hy.trans (K.rfs_whole_parent_map_eq_tip_of_mem_exterior b hx).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace ComparisonSupport

variable (K : G.ComparisonSupport c)

private theorem localCollapse_edist_le (b : G.ChildBoundary c)
    (y z : neckCentralDomain (G.static b.1).delta) :
    riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        (K.localCollapse b y) (K.localCollapse b z) ≤
      riemannianEDistOf (G.static b.1).witness.metric
        ((G.static b.1).witness.collapse y) ((G.static b.1).witness.collapse z) := by
  rw [(H.stage i.succ).edistOf_componentMetric]
  rw [K.localCollapse_eq b y, K.localCollapse_eq b z]
  exact G.inclusion_edist_le c b _ _

end ComparisonSupport

theorem local_terminal_edist_comparison_iff_local_terminal_distance_control
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    G.LocalTerminalEDistComparison Kc ↔
      ∀ c, (Kc c).LocalTerminalDistanceControl (Kc c).canonicalWholeParentMap := by
  constructor
  · intro h c
    exact ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison Kc h
  · intro h c x hx
    obtain ⟨U, hU, hterm, hdist⟩ := h c x hx
    refine ⟨U, hU, hterm, fun y hy z hz hy' hz' => ?_⟩
    rw [(H.stage i.succ).edistOf_componentMetric]
    exact hdist y hy z hz hy' hz'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem mem_interior_childCore_range_or_collar (x : (G.Parent c).Carrier)
    (hx : x ∈ K.support.region) :
    (∃ y : G.transition.ChildCore c, (𝓡∂ 3).IsInteriorPoint y.1 ∧
      G.transition.childCoreIntoParent c y = x) ∨
    ∃ b : G.ChildBoundary c, ∃ w : Sphere 2 × Icc (K.level b) 0, K.collar b w = x := by
  rw [K.support_eq] at hx
  rcases hx with ⟨y, rfl⟩ | hx
  · by_cases hy : (𝓡∂ 3).IsInteriorPoint y.1
    · exact Or.inl ⟨y, hy, rfl⟩
    · obtain ⟨b, v, hv⟩ := G.exists_childCore_boundary_sphere_of_not_interior c y hy
      refine Or.inr ⟨b, (v, ⟨0, (K.level_negative b).le, le_rfl⟩), ?_⟩
      apply Subtype.ext
      rw [K.collar_eq]
      have harg : K.collarParameter b (v, ⟨0, (K.level_negative b).le, le_rfl⟩) =
          G.collarParameter c b (v, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩) := by
        apply Subtype.ext
        apply Subtype.ext
        rw [K.collarParameter_eq, G.collarParameter_apply]
      rw [harg]
      have hzero := G.collarChartFun_zero_eq_boundarySphere c b v
      exact hzero.trans (congrArg (fun z : G.transition.trace.tubes.core => z.1) hv)
  · obtain ⟨b, w, hw⟩ := Set.mem_iUnion.mp hx
    exact Or.inr ⟨b, w, hw⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport
universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem exists_terminal_smooth_survivor_lift (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
    ∃ U : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen,
      (H.event i).oldTerminal ⟨x.1, childCore_subset_old x⟩ ∈ U ∧
      ∃ σ : U → (H.event i).old,
        ContMDiff ThreeModel (𝓡∂ 3) ∞ σ ∧
        (∀ y, (H.event i).oldTerminal (σ y) = y.1) ∧
        ∀ y, ∃ z : (G.Parent c).Carrier, z.1 = y.1.1 ∧
          (H.event i).oldOutput (σ y) = (K.canonicalWholeParentMap z).1 := by
  classical
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let : IsManifold (𝓡∂ 3) ∞ (H.event i).old := (H.event i).oldSmooth
  obtain ⟨V, hxV, σ, hσ, hσval, hσout⟩ := K.exists_smooth_survivor_lift x hx
  let W : Set (H.stage i.castSucc).Carrier := Subtype.val '' (V : Set (G.Parent c).Carrier)
  have hWopen : IsOpen W := ((H.stage i.castSucc).componentOpen
    (G.transition.childParent c)).isOpen.isOpenMap_subtype_val _ V.isOpen
  let U : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
  have hxU : (H.event i).oldTerminal ⟨x.1, childCore_subset_old x⟩ ∈ U := by
    change ((H.event i).oldTerminal ⟨x.1, childCore_subset_old x⟩).1 ∈ W
    rw [(H.event i).oldTerminal_eq]
    exact ⟨G.transition.childCoreIntoParent c x, hxV, rfl⟩
  have hρ : ∀ y : U, ∃ z : V, z.1.1 = y.1.1 := by
    intro y
    obtain ⟨z, hz, hzy⟩ := y.2
    exact ⟨⟨z, hz⟩, hzy⟩
  choose ρ hρval using hρ
  have hρcomp : ((fun z : V => z.1.1) ∘ ρ) = (fun y : U => y.1.1) := funext hρval
  have hρsmooth : ContMDiff ThreeModel ThreeModel ∞ ρ := by
    intro y
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp ThreeModel ThreeModel ∞) ρ univ y).mp
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp ThreeModel ThreeModel ∞)
      (Subtype.val ∘ ρ) univ y).mp
    have hbase : ContMDiff ThreeModel ThreeModel ∞ (fun y : U => y.1.1) :=
      (contMDiff_subtype_val (U := (H.event i).incoming.terminalRegularOpen)).comp
        (contMDiff_subtype_val (U := U))
    have hbase' : ContMDiff ThreeModel ThreeModel ∞ ((fun z : V => z.1.1) ∘ ρ) :=
      hρcomp ▸ hbase
    exact hbase' y
  refine ⟨U, hxU, σ ∘ ρ, hσ.comp hρsmooth, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    exact ((H.event i).oldTerminal_eq (σ (ρ y))).trans ((hσval (ρ y)).trans (hρval y))
  · intro y
    exact ⟨(ρ y).1, hρval y, hσout (ρ y)⟩

private theorem terminal_lift_inner_eq
    (U : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (σ : U → (H.event i).old)
    (hσ : letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      ContMDiff ThreeModel (𝓡∂ 3) ∞ σ)
    (hterm : ∀ y, (H.event i).oldTerminal (σ y) = y.1)
    (y : U) (v w : TangentSpace ThreeModel y) :
    (H.event i).outputMetric.inner ((H.event i).oldOutput (σ y))
        (mfderiv ThreeModel ThreeModel ((H.event i).oldOutput ∘ σ) y v)
        (mfderiv ThreeModel ThreeModel ((H.event i).oldOutput ∘ σ) y w) =
      ((H.event i).terminal.metric.restrictOpen U).inner y v w := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  change (H.event i).outputMetric.inner ((H.event i).oldOutput (σ y))
    (mfderiv ThreeModel ThreeModel ((H.event i).oldOutput ∘ σ) y v)
    (mfderiv ThreeModel ThreeModel ((H.event i).oldOutput ∘ σ) y w) = _
  have hO := mfderiv_comp y ((H.event i).contMDiff_oldOutput.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp))
  have hT := mfderiv_comp y
    ((H.event i).oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp))
  have hfT : ((H.event i).oldTerminal ∘ σ) = Subtype.val := funext hterm
  rw [hfT, DifferentialGeometry.mfderiv_subtype_val] at hT
  have hv : mfderiv (𝓡∂ 3) ThreeModel (H.event i).oldTerminal (σ y)
      (mfderiv ThreeModel (𝓡∂ 3) σ y v) = v := by
    exact (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A v) hT).symm
  have hw : mfderiv (𝓡∂ 3) ThreeModel (H.event i).oldTerminal (σ y)
      (mfderiv ThreeModel (𝓡∂ 3) σ y w) = w := by
    exact (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A w) hT).symm
  rw [hO]
  change (H.event i).outputMetric.inner ((H.event i).oldOutput (σ y))
      (mfderiv (𝓡∂ 3) ThreeModel (H.event i).oldOutput (σ y)
        (mfderiv ThreeModel (𝓡∂ 3) σ y v))
      (mfderiv (𝓡∂ 3) ThreeModel (H.event i).oldOutput (σ y)
        (mfderiv ThreeModel (𝓡∂ 3) σ y w)) = _
  rw [← (H.event i).old_metric_eq, hv, hw, hterm]
  rfl

private theorem terminal_lift_edist_le
    (U : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (σ : U → (H.event i).old)
    (hσ : letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      ContMDiff ThreeModel (𝓡∂ 3) ∞ σ)
    (hterm : ∀ y, (H.event i).oldTerminal (σ y) = y.1)
    (y z : U) :
    riemannianEDistOf (H.event i).outputMetric ((H.event i).oldOutput (σ y))
        ((H.event i).oldOutput (σ z)) ≤
      riemannianEDistOf ((H.event i).terminal.metric.restrictOpen U) y z := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let f : U → (H.stage i.succ).Carrier := (H.event i).oldOutput ∘ σ
  have hf : ContMDiff ThreeModel ThreeModel ∞ f := (H.event i).contMDiff_oldOutput.comp hσ
  have hpres := terminal_lift_inner_eq (H := H) (i := i) U σ hσ hterm
  have hinj : ∀ y, Function.Injective (mfderiv ThreeModel ThreeModel f y) := by
    intro y v w hvw
    have hzero : mfderiv ThreeModel ThreeModel f y (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have heq := hpres y (v - w) (v - w)
    change (H.event i).outputMetric.inner (f y)
      (mfderiv ThreeModel ThreeModel f y (v - w))
      (mfderiv ThreeModel ThreeModel f y (v - w)) = _ at heq
    rw [hzero, map_zero] at heq
    by_contra hne
    exact (ne_of_gt (((H.event i).terminal.metric.restrictOpen U).pos y (v - w)
      (sub_ne_zero.mpr hne))) heq.symm
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv f hf hinj rfl
  have hdist := DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    ((H.event i).terminal.metric.restrictOpen U) (H.event i).outputMetric f hlocal
    (c := 1) (by norm_num) (fun y v => (hpres y v v).le.trans_eq (one_mul _).symm) y z
  change riemannianEDistOf (H.event i).outputMetric (f y) (f z) ≤ _
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using hdist

private theorem exists_nhds_terminal_edist_le_of_core_interior (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ W ∈ 𝓝 (G.transition.childCoreIntoParent c x),
      (∀ y ∈ W, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
      ∀ y ∈ W, ∀ z ∈ W,
        ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
        ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf (H.event i).outputMetric
            (K.canonicalWholeParentMap y).1 (K.canonicalWholeParentMap z).1 ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
  classical
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let : IsManifold (𝓡∂ 3) ∞ (H.event i).old := (H.event i).oldSmooth
  obtain ⟨U, hxU, σ, hσ, hterm, hout⟩ := K.exists_terminal_smooth_survivor_lift x hx
  let p := (H.event i).oldTerminal ⟨x.1, childCore_subset_old x⟩
  obtain ⟨V, hV, hdist⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_mem_nhds_riemannianEDistOf_restrictOpen_eq
      (H.event i).terminal.metric U ⟨p, hxU⟩
  obtain ⟨O, hOV, hOopen, hpO⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hV (U.isOpen.mem_nhds hxU))
  let A : Set (H.stage i.castSucc).Carrier := Subtype.val '' O
  have hAopen : IsOpen A :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _ hOopen
  let W : Set (G.Parent c).Carrier := Subtype.val ⁻¹' A
  have hWopen : IsOpen W := hAopen.preimage continuous_subtype_val
  have hpval : p.1 = (G.transition.childCoreIntoParent c x).1 := (H.event i).oldTerminal_eq _
  have hxW : G.transition.childCoreIntoParent c x ∈ W := ⟨p, hpO, hpval⟩
  refine ⟨W, hWopen.mem_nhds hxW, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, _, hqy⟩ := hy
    exact hqy ▸ q.2
  · intro y hy z hz hy' hz'
    obtain ⟨q, hqO, hqy⟩ := hy
    obtain ⟨r, hrO, hrz⟩ := hz
    have hqU := (hOV hqO).2
    have hrU := (hOV hrO).2
    obtain ⟨y', hy'val, hy'out⟩ := hout ⟨q, hqU⟩
    obtain ⟨z', hz'val, hz'out⟩ := hout ⟨r, hrU⟩
    have hyy : y' = y := Subtype.ext (hy'val.trans hqy)
    have hzz : z' = z := Subtype.ext (hz'val.trans hrz)
    rw [hyy] at hy'out
    rw [hzz] at hz'out
    have hb := terminal_lift_edist_le U σ hσ hterm ⟨q, hqU⟩ ⟨r, hrU⟩
    rw [hy'out, hz'out, hdist ⟨q, hqU⟩ ⟨r, hrU⟩ (hOV hqO).1 (hOV hrO).1] at hb
    have hqq : q = ⟨y.1, hy'⟩ := Subtype.ext hqy
    have hrr : r = ⟨z.1, hz'⟩ := Subtype.ext hrz
    simpa only [hqq, hrr] using hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem exists_nhds_terminal_edist_le_of_level_lt (b : G.ChildBoundary c)
    (p : neckCentralDomain (G.static b.1).delta) (hp : K.level b < p.1.1.2) :
    ∃ U ∈ 𝓝 (G.staticNeckPoint c b p.1),
      (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
      ∀ y ∈ U, ∀ z ∈ U,
        ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
        ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (K.canonicalWholeParentMap y) (K.canonicalWholeParentMap z) ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
  obtain ⟨V, hV, hdist⟩ :=
    (G.static b.1).witness.exists_mem_nhds_collapse_riemannianEDistOf_le p
  obtain ⟨U, hU, hmap⟩ := K.exists_nhds_staticNeckPoint_eq_localCollapse b p hp hV
  refine ⟨U, hU, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, _, hq, _⟩ := hmap y hy
    rw [← hq]
    exact ((G.static b.1).neck.chart q.1).2
  · intro y hy z hz hy' hz'
    obtain ⟨q, hqV, hqy, hqmap⟩ := hmap y hy
    obtain ⟨r, hrV, hrz, hrmap⟩ := hmap z hz
    rw [hqmap, hrmap]
    have hq : (G.static b.1).neck.chart q.1 = ⟨y.1, hy'⟩ :=
      Subtype.ext (congrArg (fun a : (G.Parent c).Carrier => a.1) hqy)
    have hr : (G.static b.1).neck.chart r.1 = ⟨z.1, hz'⟩ :=
      Subtype.ext (congrArg (fun a : (G.Parent c).Carrier => a.1) hrz)
    exact (K.localCollapse_edist_le b q r).trans (by simpa only [hq, hr] using hdist q hqV r hrV)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem exists_nhds_terminal_edist_le_at_collar_level (b : G.ChildBoundary c) (p : Sphere 2) :
    ∃ U ∈ 𝓝 (K.collar b (p, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)),
      (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
      ∀ y ∈ U, ∀ z ∈ U,
        ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
        ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (K.canonicalWholeParentMap y) (K.canonicalWholeParentMap z) ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
  let x := K.collar b (p, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)
  have hboundary : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
      Set.range (K.support.sphere (K.boundaryLabel b)) := by
    rw [K.boundary_eq]
    exact Set.mem_range_self p
  have hboth : x ∈ (K.exterior.exterior (K.boundaryLabel b)).region ∩ K.support.region := by
    rwa [K.exterior.intersection]
  have hterminal := K.support_terminal x hboth.2
  obtain ⟨V, hV, hconst⟩ := K.rfs_whole_parent_map_locallyConstant_of_mem_exterior b hboth.1
  let W := {y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion}
  have hW : W ∈ 𝓝 x :=
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      hterminal
  refine ⟨V ∩ W, Filter.inter_mem hV hW, fun _ hy => hy.2, ?_⟩
  intro y hy z hz hy' hz'
  rw [hconst y hy.1, hconst z hz.1, riemannianEDistOf_self]
  exact bot_le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem exists_nhds_terminal_edist_le_on_collar (b : G.ChildBoundary c)
    (p : Sphere 2 × Icc (K.level b) 0) :
    ∃ U ∈ 𝓝 (K.collar b p),
      (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
      ∀ y ∈ U, ∀ z ∈ U,
        ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
        ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (K.canonicalWholeParentMap y) (K.canonicalWholeParentMap z) ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
  rcases lt_or_eq_of_le p.2.2.1 with hp | hp
  · have hpoint : G.staticNeckPoint c b (K.collarParameter b p).1 = K.collar b p := by
      apply Subtype.ext
      exact (K.collar_eq b p).symm
    have hcoord : K.level b < (K.collarParameter b p).1.1.2 := by
      rw [K.collarParameter_eq]
      exact hp
    exact hpoint ▸ K.exists_nhds_terminal_edist_le_of_level_lt b (K.collarParameter b p) hcoord
  · have hp' : p = (p.1, ⟨K.level b, le_rfl, (K.level_negative b).le⟩) :=
      Prod.ext rfl (Subtype.ext hp.symm)
    rw [hp']
    exact K.exists_nhds_terminal_edist_le_at_collar_level b p.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem ComparisonSupport.rfs_whole_parent_map_localTerminalDistanceControl
    {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c) :
    K.LocalTerminalDistanceControl K.canonicalWholeParentMap := by
  intro x hx
  obtain (⟨y, hy, rfl⟩ | ⟨b, p, rfl⟩) := K.mem_interior_childCore_range_or_collar x hx
  · exact K.exists_nhds_terminal_edist_le_of_core_interior y hy
  · obtain ⟨U, hU, hterm, hdist⟩ := K.exists_nhds_terminal_edist_le_on_collar b p
    refine ⟨U, hU, hterm, fun z hz w hw hz' hw' => ?_⟩
    have h := hdist z hz w hw hz' hw'
    rwa [(H.stage i.succ).edistOf_componentMetric] at h

theorem local_terminal_edist_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    G.LocalTerminalEDistComparison Kc :=
  (local_terminal_edist_comparison_iff_local_terminal_distance_control (G := G) Kc).mpr
    fun c => ComparisonSupport.rfs_whole_parent_map_localTerminalDistanceControl G (Kc c)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
