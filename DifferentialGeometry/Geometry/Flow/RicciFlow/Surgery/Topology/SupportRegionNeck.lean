import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SupportRegion
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem neckBuffer_preconnectedSpace (b : G.ChildBoundary c) :
    PreconnectedSpace (neckBuffer (G.static b.1).delta) := by
  have hsphere : PreconnectedSpace (Sphere 2) :=
    isPreconnected_iff_preconnectedSpace.mp
      ((isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
        (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one).isPreconnected)
  have hInt : PreconnectedSpace (Ioo (-((G.static b.1).delta)⁻¹ - 1)
      (((G.static b.1).delta)⁻¹ + 1)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hset : (neckBuffer (G.static b.1).delta : Set (NeckCylinder)) =
      Set.univ ×ˢ Ioo (-((G.static b.1).delta)⁻¹ - 1) (((G.static b.1).delta)⁻¹ + 1) := by
    ext x
    exact ⟨fun h => ⟨trivial, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  have hpre : IsPreconnected (neckBuffer (G.static b.1).delta : Set (NeckCylinder)) := by
    rw [hset]
    exact hsphere.isPreconnected_univ.prod isPreconnected_Ioo
  exact isPreconnected_iff_preconnectedSpace.mp hpre

theorem staticNeckChart_mem_parent (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) :
    ConnectedComponents.mk (((G.static b.1).neck.chart z).1 :
      (H.stage i.castSucc).Carrier) = G.transition.childParent c := by
  let : PreconnectedSpace (neckBuffer (G.static b.1).delta) :=
    G.neckBuffer_preconnectedSpace c b
  have hpre : IsPreconnected (Set.range fun w : neckBuffer (G.static b.1).delta =>
      (((G.static b.1).neck.chart w).1 : (H.stage i.castSucc).Carrier)) :=
    isPreconnected_range (continuous_subtype_val.comp (G.static b.1).neck.chart.continuous)
  let y : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth
  set z0 : neckBuffer (G.static b.1).delta :=
    (G.collarParameter c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩)).1 with hz0
  have hpar : ConnectedComponents.mk (((G.static b.1).neck.chart z0).1 :
      (H.stage i.castSucc).Carrier) = G.transition.childParent c := by
    have hchart0 : (((G.static b.1).neck.chart z0).1 : (H.stage i.castSucc).Carrier) =
        G.collarChartFun c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩) := by
      rw [hz0]
      rfl
    rw [hchart0]
    exact G.collarChartFun_mem_parent c b _
  have hmem := hpre.subset_connectedComponent (Set.mem_range_self z0) (Set.mem_range_self z)
  exact (ConnectedComponents.coe_eq_coe'.mpr hmem).trans hpar

noncomputable def staticNeckPoint (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) : (G.Parent c).Carrier :=
  ⟨((G.static b.1).neck.chart z).1, G.staticNeckChart_mem_parent c b z⟩

@[simp]
theorem staticNeckPoint_apply (b : G.ChildBoundary c) (z : neckBuffer (G.static b.1).delta) :
    (G.staticNeckPoint c b z).1 = ((G.static b.1).neck.chart z).1 := rfl

theorem staticNeckPoint_mem_core (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) (hz : 0 ≤ z.1.2) :
    ((G.static b.1).neck.chart z).1 ∈ G.transition.trace.tubes.core := by
  rw [G.staticNeckChart_eq_neckChart b.1 z]
  refine G.mem_core_of_neckChart_one_le_abs b.1.1.1 _ ?_
  have hsign : |(if b.1.1.2 then (1 : ℝ) else -1)| = 1 := by cases b.1.1.2 <;> norm_num
  rw [abs_mul, hsign, one_mul, abs_of_nonneg (by linarith)]
  linarith

theorem staticNeckPoint_mem_childCore_range (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) (hz : 0 ≤ z.1.2) :
    G.staticNeckPoint c b z ∈ Set.range (G.transition.childCoreIntoParent c) := by
  have hδpos : 0 < ((G.static b.1).delta)⁻¹ := inv_pos.mpr (G.static b.1).neck.delta_pos
  have hbuf : ∀ τ ∈ Icc (0 : ℝ) z.1.2, (z.1.1, τ) ∈ neckBuffer (G.static b.1).delta := by
    intro τ hτ
    exact ⟨by linarith [z.2.1, hτ.1, hδpos], by linarith [hτ.2, z.2.2]⟩
  let : PreconnectedSpace ↑(Icc (0 : ℝ) z.1.2) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ray : ↑(Icc (0 : ℝ) z.1.2) → G.transition.trace.tubes.core := fun τ =>
    ⟨((G.static b.1).neck.chart ⟨(z.1.1, τ.1), hbuf τ.1 τ.2⟩).1,
      G.staticNeckPoint_mem_core c b ⟨(z.1.1, τ.1), hbuf τ.1 τ.2⟩ τ.2.1⟩
  have hdom : Continuous (fun τ : ↑(Icc (0 : ℝ) z.1.2) =>
      (⟨(z.1.1, τ.1), hbuf τ.1 τ.2⟩ : neckBuffer (G.static b.1).delta)) := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_subtype_val
  have hchartcont : Continuous (fun τ : ↑(Icc (0 : ℝ) z.1.2) =>
      ((G.static b.1).neck.chart ⟨(z.1.1, τ.1), hbuf τ.1 τ.2⟩).1) :=
    continuous_subtype_val.comp ((G.static b.1).neck.chart.continuous.comp hdom)
  have hcont : Continuous ray := by
    apply Continuous.subtype_mk
    exact hchartcont
  have hrange : IsPreconnected (Set.range ray) := isPreconnected_range hcont
  have h0mem : ray ⟨0, ⟨le_rfl, hz⟩⟩ =
      G.transition.trace.tubes.coreBoundarySphere b.1.1 z.1.1 := by
    apply Subtype.ext
    change ((G.static b.1).neck.chart ⟨(z.1.1, (0 : ℝ)), hbuf 0 ⟨le_rfl, hz⟩⟩).1 =
      G.transition.trace.tubes.boundarySphere b.1.1 z.1.1
    have harg : (G.collarParameter c b
          (z.1.1, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩)).1 =
        (⟨(z.1.1, (0 : ℝ)), hbuf 0 ⟨le_rfl, hz⟩⟩ :
          neckBuffer (G.static b.1).delta) := by
      apply Subtype.ext
      rw [G.collarParameter_apply c b]
    rw [show ((G.static b.1).neck.chart
          ⟨(z.1.1, (0 : ℝ)), hbuf 0 ⟨le_rfl, hz⟩⟩).1 =
        G.collarChartFun c b
          (z.1.1, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩) from
      congrArg (fun w : neckBuffer (G.static b.1).delta =>
        ((G.static b.1).neck.chart w).1) harg.symm]
    exact G.collarChartFun_zero_eq_boundarySphere c b z.1.1
  have hpoint : ray ⟨z.1.2, ⟨hz, le_rfl⟩⟩ = ⟨((G.static b.1).neck.chart z).1,
      G.staticNeckPoint_mem_core c b z hz⟩ := by
    apply Subtype.ext
    change ((G.static b.1).neck.chart ⟨(z.1.1, z.1.2), _⟩).1 =
      ((G.static b.1).neck.chart z).1
    congr 2
  have hsame : ConnectedComponents.mk ⟨((G.static b.1).neck.chart z).1,
      G.staticNeckPoint_mem_core c b z hz⟩ = G.transition.childCoreComponent c := by
    have h1 : ConnectedComponents.mk (ray ⟨z.1.2, ⟨hz, le_rfl⟩⟩) =
        ConnectedComponents.mk ⟨((G.static b.1).neck.chart z).1,
          G.staticNeckPoint_mem_core c b z hz⟩ := congrArg ConnectedComponents.mk hpoint
    have h2 : ConnectedComponents.mk (ray ⟨z.1.2, ⟨hz, le_rfl⟩⟩) =
        ConnectedComponents.mk (ray ⟨0, ⟨le_rfl, hz⟩⟩) :=
      ConnectedComponents.coe_eq_coe'.mpr
        ((hrange.subset_connectedComponent (Set.mem_range_self _)) (Set.mem_range_self _))
    rw [← h1, h2, h0mem]
    exact b.2 z.1.1
  exact ⟨⟨_, hsame⟩, rfl⟩

theorem staticNeckPoint_mem_collarMap_range (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) (hlev : G.comparisonLevel c b ≤ z.1.2)
    (h0 : z.1.2 ≤ 0) :
    G.staticNeckPoint c b z ∈ Set.range (G.collarMap c b) := by
  let τ : ↑(Icc (G.comparisonLevel c b) 0) := ⟨z.1.2, hlev, h0⟩
  have harg : (G.collarParameter c b (z.1.1, τ)).1 = z := by
    apply Subtype.ext
    rw [G.collarParameter_apply c b]
  refine ⟨(z.1.1, τ), ?_⟩
  apply Subtype.ext
  rw [G.collarMap_apply]
  exact congrArg (fun w : neckBuffer (G.static b.1).delta =>
    ((G.static b.1).neck.chart w).1) harg

theorem staticNeckPoint_notMem_supportRegion (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) (hlt : z.1.2 < G.comparisonLevel c b) :
    G.staticNeckPoint c b z ∉ supportRegion G c := by
  intro hmem
  rw [supportRegion, mem_union, mem_iUnion] at hmem
  have hbret : (H.event i).RetainedBoundary b.1.1 :=
    G.transition.retainedBoundary_of_mem_childCapBoundary c ⟨b.1.1, b.2⟩
  rcases hmem with hcore | ⟨d, hd⟩
  · obtain ⟨x, hx⟩ := hcore
    have hxval : ((G.static b.1).neck.chart z).1 =
        (x.1.1 : (H.stage i.castSucc).Carrier) := congrArg Subtype.val hx.symm
    exact (G.staticNeckChart_ne_childCore_of_coordinate_negative b.1 c b.2 z
      (lt_of_lt_of_le hlt (G.comparisonLevel_negative c b).le) x) hxval
  · obtain ⟨w, hw⟩ := hd
    have hdret : (H.event i).RetainedBoundary d.1.1 :=
      G.transition.retainedBoundary_of_mem_childCapBoundary c ⟨d.1.1, d.2⟩
    have harg_eq : ((G.static b.1).neck.chart z).1 =
        ((G.static d.1).neck.chart (G.collarParameter c d w).1).1 := by
      calc ((G.static b.1).neck.chart z).1 = (G.staticNeckPoint c b z).1 := rfl
        _ = (G.collarMap c d w).1 := congrArg Subtype.val hw.symm
        _ = ((G.static d.1).neck.chart (G.collarParameter c d w).1).1 :=
            G.collarMap_apply c d w
    by_cases hidx : b.1.1.1 = d.1.1.1
    · have hside : b.1.1.2 = d.1.1.2 :=
        G.retainedBoundary_side_eq (α := d.1.1.1) (hidx ▸ hbret) hdret
      have hbd : b = d := Subtype.ext (Subtype.ext (Prod.ext hidx hside))
      subst hbd
      have h2 : (G.collarParameter c b w).1 = z :=
        (G.static b.1).neck.chart_smooth.isEmbedding.injective (Subtype.ext harg_eq.symm)
      have hw2 : (w.2 : ℝ) = z.1.2 := by
        have hval := congrArg (fun u : neckBuffer (G.static b.1).delta => u.1.2) h2
        rw [G.collarParameter_apply c b w] at hval
        exact hval
      exact absurd (hw2 ▸ w.2.2.1) (not_le.mpr hlt)
    · have htube : ((G.neck b.1.1.1).chart
          ⟨(z.1.1, (if b.1.1.2 then (1 : ℝ) else -1) * (1 + z.1.2)),
            G.recenter_in_buffer b.1 z⟩).1 =
          ((G.neck d.1.1.1).chart
          ⟨((G.collarParameter c d w).1.1.1,
            (if d.1.1.2 then (1 : ℝ) else -1) * (1 + (G.collarParameter c d w).1.1.2)),
            G.recenter_in_buffer d.1 (G.collarParameter c d w).1⟩).1 := by
        calc ((G.neck b.1.1.1).chart
              ⟨(z.1.1, (if b.1.1.2 then (1 : ℝ) else -1) * (1 + z.1.2)),
                G.recenter_in_buffer b.1 z⟩).1
            = ((G.static b.1).neck.chart z).1 :=
              (G.staticNeckChart_eq_neckChart b.1 z).symm
          _ = ((G.static d.1).neck.chart (G.collarParameter c d w).1).1 := harg_eq
          _ = ((G.neck d.1.1.1).chart
              ⟨((G.collarParameter c d w).1.1.1,
                (if d.1.1.2 then (1 : ℝ) else -1) *
                  (1 + (G.collarParameter c d w).1.1.2)),
                G.recenter_in_buffer d.1 (G.collarParameter c d w).1⟩).1 :=
              G.staticNeckChart_eq_neckChart d.1 (G.collarParameter c d w).1
      exact Set.disjoint_left.mp (G.buffer_disjoint hidx)
        (Set.mem_range_self _) ⟨_, Subtype.ext htube.symm⟩

theorem staticNeckPoint_mem_supportRegion_iff (b : G.ChildBoundary c)
    (z : neckBuffer (G.static b.1).delta) :
    G.staticNeckPoint c b z ∈ supportRegion G c ↔ G.comparisonLevel c b ≤ z.1.2 := by
  constructor
  · intro hmem
    by_contra hlt
    exact G.staticNeckPoint_notMem_supportRegion c b z (not_le.mp hlt) hmem
  · intro hlev
    rcases le_or_gt z.1.2 (0 : ℝ) with h0 | h0
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨b, G.staticNeckPoint_mem_collarMap_range c b z hlev h0⟩)
    · exact Or.inl (G.staticNeckPoint_mem_childCore_range c b z h0.le)

theorem staticNeckPoint_isSmoothEmbedding (b : G.ChildBoundary c) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (G.staticNeckPoint c b) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hF : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (fun z : ↥(neckBuffer (G.static b.1).delta) =>
        ((G.static b.1).neck.chart z).1) :=
    IsSmoothEmbedding.comp
      (g := (Subtype.val : ↥((H.event i).incoming.terminalRegularOpen) →
        (H.stage i.castSucc).Carrier))
      (f := (G.static b.1).neck.chart)
      (IsSmoothEmbedding.of_opens ((H.event i).incoming.terminalRegularOpen))
      (G.static b.1).neck.chart_smooth hn
  have hg : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      ((Subtype.val : (G.Parent c).Carrier → (H.stage i.castSucc).Carrier) ∘
        G.staticNeckPoint c b) := by
    have hEq : ((Subtype.val : (G.Parent c).Carrier → (H.stage i.castSucc).Carrier) ∘
        G.staticNeckPoint c b) =
        (fun z : ↥(neckBuffer (G.static b.1).delta) =>
          ((G.static b.1).neck.chart z).1) := rfl
    rw [hEq]
    exact hF
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    (I := NeckCylinderModel) (J := ThreeModel)
    (M := ↥(neckBuffer (G.static b.1).delta))
    (N := (H.stage i.castSucc).Carrier)
    ((H.stage i.castSucc).componentOpen (G.transition.childParent c))
    (G.staticNeckPoint c b) hg

theorem exists_diffeomorph_range_staticNeck (b : G.ChildBoundary c) :
    ∃ (V : TopologicalSpace.Opens (G.Parent c).Carrier)
      (Φ : ↥(neckBuffer (G.static b.1).delta) ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V),
      (V : Set (G.Parent c).Carrier) = Set.range (G.staticNeckPoint c b) ∧
      (∀ z, (Φ z : (G.Parent c).Carrier) = G.staticNeckPoint c b z) ∧
      ∀ y : V, G.staticNeckPoint c b (Φ.symm y) = (y : (G.Parent c).Carrier) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [Module.finrank_prod, ThreeSpace]
  obtain ⟨V, Φ, hV, hval, hsymm⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      (G.staticNeckPoint c b) (G.staticNeckPoint_isSmoothEmbedding c b).contMDiff
      (G.staticNeckPoint_isSmoothEmbedding c b).isEmbedding.injective
      (fun z => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
        NeckCylinderModel ThreeModel (G.staticNeckPoint c b) z
        ((G.staticNeckPoint_isSmoothEmbedding c b).isImmersion.isImmersionAt z))
      hdim
  exact ⟨V, Φ, hV, hval, hsymm⟩

theorem extChartAt_neckBuffer_snd_apply
    (b : G.ChildBoundary c) (z₀ z : neckBuffer (G.static b.1).delta) :
    (extChartAt NeckCylinderModel z₀ z).2 = z.1.2 := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe]
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe]
  simp only [Set.domRestrict_apply, Function.comp_apply]
  rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply, chartAt_self_eq]
  rfl

theorem exists_staticNeck_inverse (b : G.ChildBoundary c) :
    ∃ σ : PartialDiffeomorph ThreeModel NeckCylinderModel (G.Parent c).Carrier
        ↥(neckBuffer (G.static b.1).delta) ∞,
      σ.source = Set.range (G.staticNeckPoint c b) ∧
      (∀ y, y ∈ Set.range (G.staticNeckPoint c b) → G.staticNeckPoint c b (σ y) = y) ∧
      (∀ z, σ (G.staticNeckPoint c b z) = z) := by
  obtain ⟨V, Φ, hV, hval, hsymm⟩ := G.exists_diffeomorph_range_staticNeck c b
  let y₀ : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth
  have hδpos : 0 < ((G.static b.1).delta)⁻¹ := inv_pos.mpr (G.static b.1).neck.delta_pos
  have hz₀ : (y₀, (0 : ℝ)) ∈ neckBuffer (G.static b.1).delta := ⟨by linarith, by linarith⟩
  have hVne : Nonempty V :=
    ⟨⟨G.staticNeckPoint c b ⟨(y₀, 0), hz₀⟩, by
      change G.staticNeckPoint c b ⟨(y₀, 0), hz₀⟩ ∈ (V : Set (G.Parent c).Carrier)
      rw [hV]
      exact Set.mem_range_self _⟩⟩
  let σ : PartialDiffeomorph ThreeModel NeckCylinderModel (G.Parent c).Carrier
      ↥(neckBuffer (G.static b.1).delta) ∞ :=
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V hVne).symm.trans
      Φ.symm.toPartialDiffeomorph
  have hσapply : ∀ (y : (G.Parent c).Carrier) (hy : y ∈ V),
      σ y = Φ.symm (⟨y, hy⟩ : V) := by
    intro y hy
    rw [show σ y = (Φ.symm.toPartialEquiv)
        ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V
          hVne).symm.toPartialEquiv y) from rfl]
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply ThreeModel V hVne hy]
    rfl
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [show σ.source = ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V
        hVne).symm.toPartialEquiv.trans Φ.symm.toPartialEquiv).source from rfl]
    rw [PartialEquiv.trans_source]
    rw [PartialDiffeomorph.symm_toPartialEquiv_source]
    rw [show (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V
        hVne).target = (V : Set (G.Parent c).Carrier) from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target ThreeModel V hVne]
    rw [show Φ.symm.toPartialEquiv.source = Set.univ from rfl]
    simp only [Set.preimage_univ, Set.inter_univ]
    exact hV
  · intro y hy
    have hyV : y ∈ V := by
      change y ∈ (V : Set (G.Parent c).Carrier)
      rw [hV]
      exact hy
    rw [hσapply y hyV]
    exact hsymm ⟨y, hyV⟩
  · intro z
    have hzV : G.staticNeckPoint c b z ∈ V := by
      change G.staticNeckPoint c b z ∈ (V : Set (G.Parent c).Carrier)
      rw [hV]
      exact Set.mem_range_self z
    rw [hσapply _ hzV]
    have hz : (⟨G.staticNeckPoint c b z, hzV⟩ : V) = Φ z := Subtype.ext (hval z).symm
    rw [hz, Diffeomorph.symm_apply_apply]

theorem exists_ambientChart_staticNeckImage (b : G.ChildBoundary c)
    (z₀ : neckBuffer (G.static b.1).delta) :
    ∃ φ : PartialDiffeomorph ThreeModel ThreeModel (G.Parent c).Carrier
        (EuclideanSpace ℝ (Fin 3)) ∞,
      G.staticNeckPoint c b z₀ ∈ φ.source ∧
      φ (G.staticNeckPoint c b z₀) 0 = z₀.1.2 - G.comparisonLevel c b ∧
      ∀ y ∈ φ.source, (y ∈ supportRegion G c ↔ 0 ≤ φ y 0) := by
  obtain ⟨σ, hσsource, hσinv, hσleft⟩ := G.exists_staticNeck_inverse c b
  let χ := extChartAtPartialDiffeomorph (I := NeckCylinderModel) ∞ z₀
  let ψ : PartialDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (EuclideanSpace ℝ (Fin 2) × ℝ) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    ((DifferentialGeometry.Topology.translateDiffeomorph
        ((0 : EuclideanSpace ℝ (Fin 2)), -(G.comparisonLevel c b))).trans
      (DifferentialGeometry.Topology.normalFirstEquiv 2).toDiffeomorph).toPartialDiffeomorph
  let φ := (σ.trans χ).trans ψ
  have hφsource : φ.source = σ.source ∩ σ ⁻¹' (extChartAt NeckCylinderModel z₀).source := by
    rw [show φ.source = (σ.trans χ).source ∩ (σ.trans χ) ⁻¹' ψ.source from
      PartialDiffeomorph.trans_source _ _]
    rw [show (σ.trans χ).source = σ.source ∩ σ ⁻¹' χ.source from
      PartialDiffeomorph.trans_source _ _]
    rw [show ψ.source = Set.univ from rfl, Set.preimage_univ, Set.inter_univ]
    rfl
  have hbase : G.staticNeckPoint c b z₀ ∈ φ.source := by
    rw [hφsource]
    exact ⟨by rw [hσsource]; exact Set.mem_range_self z₀,
      by rw [Set.mem_preimage, hσleft z₀]; exact mem_extChartAt_source z₀⟩
  have hcoord : ∀ y ∈ φ.source, φ y 0 = (σ y).1.2 - G.comparisonLevel c b := by
    intro y hy
    rw [hφsource] at hy
    rw [PartialDiffeomorph.trans_apply, PartialDiffeomorph.trans_apply]
    change (DifferentialGeometry.Topology.normalFirstEquiv 2
      ((extChartAt NeckCylinderModel z₀) (σ y) +
        ((0 : EuclideanSpace ℝ (Fin 2)), -(G.comparisonLevel c b)))) 0 =
      (σ y).1.2 - G.comparisonLevel c b
    rw [DifferentialGeometry.Topology.normalFirstEquiv_zero, Prod.snd_add,
      extChartAt_neckBuffer_snd_apply]
    simp [sub_eq_add_neg]
  refine ⟨φ, hbase, ?_, ?_⟩
  · rw [hcoord (G.staticNeckPoint c b z₀) hbase, hσleft z₀]
  · intro y hy
    have hyφ := hy
    rw [hφsource] at hy
    have hyσ := hy.1
    have hyrange : y ∈ Set.range (G.staticNeckPoint c b) := by
      rw [← hσsource]; exact hyσ
    have hσy : G.staticNeckPoint c b (σ y) = y := hσinv y hyrange
    rw [hcoord y hyφ]
    constructor
    · intro hyK
      have hlev : G.comparisonLevel c b ≤ (σ y).1.2 :=
        (G.staticNeckPoint_mem_supportRegion_iff c b (σ y)).mp (by rwa [hσy])
      linarith
    · intro h0
      rw [← hσy]
      exact (G.staticNeckPoint_mem_supportRegion_iff c b (σ y)).mpr (by linarith)

theorem collarMap_mem_range_staticNeckPoint (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(Icc (G.comparisonLevel c b) 0)) :
    G.collarMap c b w ∈ Set.range (G.staticNeckPoint c b) := by
  refine ⟨(G.collarParameter c b w).1, ?_⟩
  apply Subtype.ext
  rw [G.staticNeckPoint_apply, G.collarMap_apply]

theorem mem_childCore_range_of_notMem_staticNeckImage (y : (G.Parent c).Carrier)
    (hy : y ∈ supportRegion G c)
    (hnot : ∀ b : G.ChildBoundary c, y ∉ Set.range (G.staticNeckPoint c b)) :
    y ∈ Set.range (G.transition.childCoreIntoParent c) := by
  rw [supportRegion, mem_union, mem_iUnion] at hy
  rcases hy with h | ⟨b, hb⟩
  · exact h
  · obtain ⟨w, hw⟩ := hb
    exact absurd (hw ▸ G.collarMap_mem_range_staticNeckPoint c b w) (hnot b)

theorem exists_childCore_boundary_sphere_of_not_interior (x : G.transition.ChildCore c)
    (hx : ¬ (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ b : G.ChildBoundary c, ∃ y : Sphere 2,
      G.transition.trace.tubes.coreBoundarySphere b.1.1 y = x.1 := by
  let : CompactSpace G.transition.trace.tubes.core := G.transition.core_compact
  let : LocallyConnectedSpace G.transition.trace.tubes.core := G.transition.core_locallyConnected
  have hbd : x.1 ∈ (𝓡∂ 3).boundary G.transition.trace.tubes.core := by
    by_contra h
    exact hx ((ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := 𝓡∂ 3) x.1).mpr h)
  rw [G.transition.core_boundary] at hbd
  obtain ⟨b', hb'⟩ := Set.mem_iUnion.mp hbd
  obtain ⟨y, hy⟩ := hb'
  have hcomp : ConnectedComponents.mk (G.transition.trace.tubes.coreBoundarySphere b' y) =
      G.transition.childCoreComponent c := hy ▸ x.2
  have hall : ∀ y' : Sphere 2,
      ConnectedComponents.mk (G.transition.trace.tubes.coreBoundarySphere b' y') =
        G.transition.childCoreComponent c := by
    intro y'
    let : ConnectedSpace (Sphere 2) := sphere_connectedSpace
    have hpre : IsPreconnected
        (Set.range (G.transition.trace.tubes.coreBoundarySphere b')) :=
      isPreconnected_range (G.transition.trace.tubes.coreBoundarySphere b').continuous
    exact (ConnectedComponents.coe_eq_coe'.mpr
      ((hpre.subset_connectedComponent (Set.mem_range_self y))
        (Set.mem_range_self y'))).trans hcomp
  exact ⟨⟨⟨b', fun y' => CutCapTopology.childCore_subset_retainedCore _ c (hall y')⟩, hall⟩,
    y, hy⟩

theorem childCore_boundary_mem_range_staticNeckPoint (x : G.transition.ChildCore c)
    (hx : ¬ (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ b : G.ChildBoundary c,
      G.transition.childCoreIntoParent c x ∈ Set.range (G.staticNeckPoint c b) := by
  obtain ⟨b, y, hy⟩ := G.exists_childCore_boundary_sphere_of_not_interior c x hx
  have hδpos : 0 < ((G.static b.1).delta)⁻¹ := inv_pos.mpr (G.static b.1).neck.delta_pos
  have hz : (y, (0 : ℝ)) ∈ neckBuffer (G.static b.1).delta := ⟨by linarith, by linarith⟩
  refine ⟨b, ⟨⟨(y, 0), hz⟩, ?_⟩⟩
  have hxval : (x.1.1 : (H.stage i.castSucc).Carrier) =
      (G.transition.trace.tubes.boundarySphere b.1.1 y : (H.stage i.castSucc).Carrier) :=
    (congrArg (fun z : G.transition.trace.tubes.core =>
      (z.1 : (H.stage i.castSucc).Carrier)) hy).symm
  apply Subtype.ext
  change ((G.static b.1).neck.chart ⟨(y, (0 : ℝ)), hz⟩).1 =
    (x.1.1 : (H.stage i.castSucc).Carrier)
  rw [hxval]
  change ((G.static b.1).neck.chart ⟨(y, (0 : ℝ)), hz⟩).1 =
    (G.transition.trace.tubes.tube b.1.1.1
      (y, TubeSystem.boundaryLevel b.1.1.2) : (H.stage i.castSucc).Carrier)
  rw [G.tube_eq b.1.1.1 (y, TubeSystem.boundaryLevel b.1.1.2)
    (G.tube_in_buffer b.1.1.1 _)]
  rw [G.staticNeckChart_eq_neckChart b.1 ⟨(y, (0 : ℝ)), hz⟩]
  have hbl : (if b.1.1.2 then (1 : ℝ) else -1) * (1 + (0 : ℝ)) =
      (TubeSystem.boundaryLevel b.1.1.2 : ℝ) := by
    cases hb : b.1.1.2 <;> simp [TubeSystem.boundaryLevel]
  exact congrArg
    (fun w : neckBuffer (G.delta b.1.1.1) => ((G.neck b.1.1.1).chart w).1)
    (Subtype.ext (Prod.ext rfl hbl))

theorem exists_isOpen_subset_supportRegion_of_childCore_notMem_staticNeckImage
    (x : G.transition.ChildCore c)
    (hnot : ∀ b : G.ChildBoundary c,
      G.transition.childCoreIntoParent c x ∉ Set.range (G.staticNeckPoint c b)) :
    ∃ V : Set (G.Parent c).Carrier, IsOpen V ∧
      G.transition.childCoreIntoParent c x ∈ V ∧ V ⊆ supportRegion G c := by
  have hint : (𝓡∂ 3).IsInteriorPoint x.1 := by
    by_contra hx
    obtain ⟨b, hb⟩ := G.childCore_boundary_mem_range_staticNeckPoint c x hx
    exact hnot b hb
  let : CompactSpace G.transition.trace.tubes.core := G.transition.core_compact
  let : LocallyConnectedSpace G.transition.trace.tubes.core :=
    G.transition.core_locallyConnected
  obtain ⟨z₀, hz₀⟩ := ConnectedComponents.surjective_coe (G.transition.childCoreComponent c)
  have hUeq : ({z : G.transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) =
      connectedComponent z₀ := by
    ext z
    rw [← hz₀]
    exact ConnectedComponents.coe_eq_coe'
  have hUopen : IsOpen ({z : G.transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) := by
    rw [hUeq]
    exact isOpen_connectedComponent
  have hxU : x.1 ∈ ({z : G.transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) := x.2
  have hnhds : ({z : G.transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) ∈ 𝓝 x.1 :=
    hUopen.mem_nhds hxU
  have hW : Subtype.val ''
      ({z : G.transition.trace.tubes.core |
        ConnectedComponents.mk z = G.transition.childCoreComponent c} : Set _) ∈
      𝓝 (x.1.1 : (H.stage i.castSucc).Carrier) :=
    DifferentialGeometry.Topology.immersion_image_mem_nhds
      (G.transition.core_induced.isImmersion.isImmersionAt x.1)
      (by simp [ThreeSpace]) hint hnhds
  obtain ⟨O, hOW, hOopen, hxO⟩ := mem_nhds_iff.mp hW
  refine ⟨Subtype.val ⁻¹' O, hOopen.preimage continuous_subtype_val, hxO, ?_⟩
  rintro y hy
  obtain ⟨w, hwU, hweq⟩ := hOW hy
  exact Or.inl ⟨⟨w, hwU⟩, Subtype.ext hweq⟩
theorem exists_smoothBoundaryAtlas :
    Nonempty (DifferentialGeometry.Topology.SmoothBoundaryAtlas ThreeModel 3
      (supportRegion G c)) := by
  classical
  have hchart : ∀ x : (supportRegion G c),
      ∃ φ : PartialDiffeomorph ThreeModel ThreeModel (G.Parent c).Carrier
          (EuclideanSpace ℝ (Fin 3)) ∞,
        x.val ∈ φ.source ∧ ∀ y ∈ φ.source, (y ∈ supportRegion G c ↔ 0 ≤ φ y 0) := by
    intro x
    by_cases hx : ∃ b : G.ChildBoundary c, x.val ∈ Set.range (G.staticNeckPoint c b)
    · obtain ⟨b, z₀, hz₀⟩ := hx
      obtain ⟨φ, hφ, -, hmem⟩ := G.exists_ambientChart_staticNeckImage c b z₀
      exact ⟨φ, hz₀ ▸ hφ, hmem⟩
    · have hcore : x.val ∈ Set.range (G.transition.childCoreIntoParent c) :=
        G.mem_childCore_range_of_notMem_staticNeckImage c x.val x.2 (by
          intro b hb
          exact hx ⟨b, hb⟩)
      obtain ⟨x', hx'⟩ := hcore
      obtain ⟨V, hVopen, hx'V, hVsub⟩ :=
        G.exists_isOpen_subset_supportRegion_of_childCore_notMem_staticNeckImage c x' (by
          intro b hb
          exact hx ⟨b, hx' ▸ hb⟩)
      obtain ⟨φ, hxin, hsub, hpos⟩ :=
        DifferentialGeometry.Topology.exists_positiveChart_of_mem_open (n := 3) hVopen (hx' ▸ hx'V)
      refine ⟨φ, hxin, ?_⟩
      intro y hy
      exact iff_of_true (hVsub (hsub hy)) (hpos y hy).le
  choose φ hφ hmem using hchart
  exact ⟨{ ambientChart := φ, mem_source := hφ, mem_iff := hmem }⟩

theorem isBoundaryPoint_iff_exists_levelSphere
    (C : DifferentialGeometry.Topology.SmoothBoundaryAtlas ThreeModel 3 (supportRegion G c))
    (hbdry : ∀ x : (supportRegion G c),
      C.ambientChart x x.val 0 = 0 ↔
        ∃ b : G.ChildBoundary c, x.val ∈ Set.range (levelSphere G c b))
    (x : (supportRegion G c)) :
    letI := C.toChartedSpace
    (𝓡∂ 3).IsBoundaryPoint x ↔
      ∃ b : G.ChildBoundary c, x.val ∈ Set.range (levelSphere G c b) := by
  letI := C.toChartedSpace
  rw [C.isBoundaryPoint_iff x]
  exact hbdry x

theorem isConnected_interiorImage_supportRegion
    (C : DifferentialGeometry.Topology.SmoothBoundaryAtlas ThreeModel 3 (supportRegion G c)) :
    letI := C.toChartedSpace
    letI := C.isManifold
    IsConnected ((Subtype.val : (supportRegion G c) → (G.Parent c).Carrier) ''
      (𝓡∂ 3).interior (supportRegion G c)) := by
  letI := C.toChartedSpace
  letI := C.isManifold
  have hconn : IsConnected (supportRegion G c) := G.isConnected_supportRegion c
  let : ConnectedSpace (supportRegion G c) := isConnected_iff_connectedSpace.mp hconn
  have hpre : IsPreconnected ((𝓡∂ 3).interior (supportRegion G c)) :=
    DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior
  have hne : ((𝓡∂ 3).interior (supportRegion G c)).Nonempty :=
    DifferentialGeometry.Topology.Manifold.dense_manifold_interior.nonempty hconn.nonempty
  exact ⟨hne.image _, hpre.image _ continuous_subtype_val.continuousOn⟩

noncomputable def sphereFun (b : G.ChildBoundary c) : C(Sphere 2, (supportRegion G c)) :=
  ⟨fun y => ⟨levelSphere G c b y, levelSphere_mem_supportRegion G c b y⟩,
    Continuous.subtype_mk (levelSphere G c b).continuous _⟩

theorem sphereFun_apply (b : G.ChildBoundary c) (y : Sphere 2) :
    (sphereFun G c b y).1 = levelSphere G c b y := rfl

theorem sphereFun_pairwise_disjoint :
    Pairwise fun b d : G.ChildBoundary c =>
      Disjoint (Set.range (sphereFun G c b)) (Set.range (sphereFun G c d)) := by
  intro b d hbd
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨y', hy'⟩ := hz'
  exact Set.disjoint_left.mp (pairwise_disjoint_levelSphere G c hbd)
    (Set.mem_range_self y) ⟨y', congrArg Subtype.val hy'⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
