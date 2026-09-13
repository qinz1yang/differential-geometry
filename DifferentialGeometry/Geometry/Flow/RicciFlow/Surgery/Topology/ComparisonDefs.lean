import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore



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

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
