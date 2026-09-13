import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SupportRegion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

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

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
