import DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource

noncomputable section

open Bundle Manifold Set Topology TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

section ChartedSpace

variable {ι : Type u} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable (M : ι → Type u) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]

private def sigmaAtlas : Set (OpenPartialHomeomorph (Σ i, M i) H) :=
  ⋃ i, (fun e : OpenPartialHomeomorph (M i) H =>
    e.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i))) '' atlas H (M i)

private theorem mem_sigmaAtlas_iff {e : OpenPartialHomeomorph (Σ i, M i) H} :
    e ∈ sigmaAtlas M ↔ ∃ (i : ι) (f : OpenPartialHomeomorph (M i) H),
      f ∈ atlas H (M i) ∧ f.lift_openEmbedding (IsOpenEmbedding.sigmaMk (i := i)) = e := by
  simp only [sigmaAtlas, Set.mem_iUnion, Set.mem_image]

@[instance_reducible]
instance sigmaChartedSpace : ChartedSpace H (Σ i, M i) where
  atlas := sigmaAtlas M
  chartAt := fun x => (chartAt H x.2).lift_openEmbedding
    (IsOpenEmbedding.sigmaMk (i := x.1))
  mem_chart_source := by
    rintro ⟨i, x⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact mem_image_of_mem _ (mem_chart_source H x)
  chart_mem_atlas := by
    rintro ⟨i, x⟩
    exact (mem_sigmaAtlas_iff M).mpr ⟨i, chartAt H x, chart_mem_atlas H x, rfl⟩

theorem sigmaChartedSpace_chartAt (x : Σ i, M i) :
    chartAt H x = (chartAt H x.2).lift_openEmbedding
      (IsOpenEmbedding.sigmaMk (i := x.1)) := rfl

private theorem sigmaChartedSpace_atlas : atlas H (Σ i, M i) = sigmaAtlas M := rfl

end ChartedSpace

section Manifold

variable {ι : Type u} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
variable [∀ i, IsManifold I n (M i)]

instance sigmaIsManifold : IsManifold I n (Σ i, M i) where
  compatible := by
    intro e e' he he'
    rw [sigmaChartedSpace_atlas] at he he'
    obtain ⟨i, f, hf, rfl⟩ := (mem_sigmaAtlas_iff M).mp he
    obtain ⟨i', f', hf', rfl⟩ := (mem_sigmaAtlas_iff M).mp he'
    by_cases hii : i = i'
    · subst hii
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact StructureGroupoid.compatible (contDiffGroupoid n I) hf hf'
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext z
      simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
        OpenPartialHomeomorph.lift_openEmbedding_symm_source,
        OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
        OpenPartialHomeomorph.lift_openEmbedding_source, Set.mem_image, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro - ⟨y, -, hy⟩
      exact hii (Sigma.mk.inj_iff.mp hy).1.symm

end Manifold

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

section Orientation

variable {ι : Type u} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H} [∀ i, IsManifold I ∞ (M i)]
variable {k : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem mem_sigmaTrivializationAt_baseSet_self {i : ι} (p y : M i) :
    (⟨i, y⟩ : Σ j, M j) ∈
        (trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet ↔
      y ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
    sigmaChartedSpace_chartAt, OpenPartialHomeomorph.lift_openEmbedding_source]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact sigma_mk_injective hzy ▸ hz
  · exact fun hy => ⟨y, hy, rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem not_mem_sigmaTrivializationAt_baseSet_of_ne {i i' : ι} (h : i ≠ i')
    (p : M i) (y : M i') :
    (⟨i', y⟩ : Σ j, M j) ∉
      (trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, sigmaChartedSpace_chartAt,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hzy⟩
  exact h (congrArg Sigma.fst hzy)

omit [FiniteDimensional ℝ E] [∀ i, IsManifold I ∞ (M i)] in
private theorem extend_sigma_aux {i : ι} (p x : M i) :
    ((chartAt H (⟨i, p⟩ : Σ j, M j)).extend I) ∘
        ((chartAt H (⟨i, x⟩ : Σ j, M j)).extend I).symm =
      ((chartAt H p).extend I) ∘ ((chartAt H x).extend I).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, sigmaChartedSpace_chartAt,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [FiniteDimensional ℝ E] [∀ i, IsManifold I ∞ (M i)] in
private theorem extend_sigma_aux_apply {i : ι} (x : M i) :
    ((chartAt H (⟨i, x⟩ : Σ j, M j)).extend I) (⟨i, x⟩ : Σ j, M j) =
      ((chartAt H x).extend I) x := by
  simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    sigmaChartedSpace_chartAt, OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [FiniteDimensional ℝ E] in
private theorem tangentChartEquiv_sigma_apply {i : ι} (p x : M i)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hx' : (⟨i, x⟩ : Σ j, M j) ∈
      (trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet)
    (v : TangentSpace I x) :
    tangentChartEquiv I (Σ j, M j) (⟨i, p⟩ : Σ j, M j) ⟨i, x⟩ hx'
        (show TangentSpace I (⟨i, x⟩ : Σ j, M j) from v) =
      tangentChartEquiv I (M i) p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sigma_aux, extend_sigma_aux_apply]

omit [FiniteDimensional ℝ E] in
private theorem tangentChartEquiv_sigma {i : ι} (p x : M i)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hx' : (⟨i, x⟩ : Σ j, M j) ∈
      (trivializationAt E (TangentSpace I) (⟨i, p⟩ : Σ j, M j)).baseSet) :
    tangentChartEquiv I (Σ j, M j) (⟨i, p⟩ : Σ j, M j) ⟨i, x⟩ hx' =
      tangentChartEquiv I (M i) p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sigma_apply p x hx hx' v

def manifoldOrientationUnion (hdim : Module.finrank ℝ E = k)
    (o : ∀ i, ManifoldOrientation I (M i) k) : ManifoldOrientation I (Σ i, M i) k where
  dimension_eq := hdim
  orientation x := (o x.1).orientation x.2
  locally_constant := by
    intro p x hx
    obtain ⟨i, p₀⟩ := p
    obtain ⟨i', x₀⟩ := x
    by_cases hii : i' = i
    · subst i'
      have hx₀ := (mem_sigmaTrivializationAt_baseSet_self p₀ x₀).mp hx
      obtain ⟨U, hUopen, hxU, hUsub, hconst⟩ := (o i).locally_constant p₀ x₀ hx₀
      have hU'sub : Sigma.mk i '' U ⊆
          (trivializationAt E (TangentSpace I) (⟨i, p₀⟩ : Σ j, M j)).baseSet := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_sigmaTrivializationAt_baseSet_self p₀ y).mpr (hUsub hy)
      refine ⟨Sigma.mk i '' U, (IsOpenEmbedding.sigmaMk (i := i)).isOpenMap U hUopen,
        ⟨x₀, hxU, rfl⟩, hU'sub, ?_⟩
      intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      rw [tangentChartEquiv_sigma p₀ y₀ (hUsub hy₀) (hU'sub ⟨y₀, hy₀, rfl⟩),
        tangentChartEquiv_sigma p₀ x₀ hx₀ hx]
      exact hconst y₀ hy₀
    · exact absurd hx (not_mem_sigmaTrivializationAt_baseSet_of_ne (Ne.symm hii) p₀ x₀)

theorem manifoldOrientationUnion_orientation (hdim : Module.finrank ℝ E = k)
    (o : ∀ i, ManifoldOrientation I (M i) k) (i : ι) (y : M i) :
    (manifoldOrientationUnion hdim o).orientation (⟨i, y⟩ : Σ j, M j) = (o i).orientation y :=
  rfl

end Orientation

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

universe u

section SigmaEmbedding

variable {ι : Type u} {H : Type*} [TopologicalSpace H] [Nonempty H]
variable {M : ι → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
variable [∀ i, IsManifold I n (M i)]

private theorem lift_openEmbedding_extend_apply {X X' Z : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Z] [Nonempty Z] {f : X → X'}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
    (J : ModelWithCorners 𝕜 E' Z) (x : X) :
    (e.lift_openEmbedding hf).extend J (f x) = e.extend J x := by
  rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
    Function.comp_apply, Function.comp_apply]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]

theorem sigmaMk_isImmersionOfComplement (i : ι) :
    IsImmersionOfComplement Unit I I n (Sigma.mk i : M i → Σ j, M j) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sigma.mk i x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sigma.mk i x))
  intro y hy
  simp only [Function.comp_apply]
  rw [sigmaChartedSpace_chartAt, lift_openEmbedding_extend_apply,
    PartialEquiv.right_inv _ hy]
  simp

theorem isSmoothEmbedding_sigmaMk (i : ι) :
    IsSmoothEmbedding I I n (Sigma.mk i : M i → Σ j, M j) :=
  ⟨(sigmaMk_isImmersionOfComplement (I := I) (n := n) i).isImmersion,
    (IsOpenEmbedding.sigmaMk (i := i)).toIsEmbedding⟩

end SigmaEmbedding

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

section Union

variable {ι : Type u} [Fintype ι]

def closedOrientedUnion (M : ι → ClosedOrientedManifold.{u} 3) : ClosedOrientedManifold.{u} 3 where
  Carrier := Σ i, (M i).Carrier
  orientation := manifoldOrientationUnion (M := fun i => (M i).Carrier) (I := 𝓡 3)
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by norm_num)
    (fun i => (M i).orientation)

theorem closedOrientedUnion_carrier (M : ι → ClosedOrientedManifold.{u} 3) :
    (closedOrientedUnion M).Carrier = (Σ i, (M i).Carrier) := rfl

theorem closedOrientedUnion_orientation (M : ι → ClosedOrientedManifold.{u} 3) (i : ι)
    (y : (M i).Carrier) :
    (closedOrientedUnion M).orientation.orientation (⟨i, y⟩ : Σ j, (M j).Carrier) =
      (M i).orientation.orientation y := rfl


end Union

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

private theorem disjoint_sigmaMk_image_of_ne {ι : Type u} {M : ι → Type u} {i i' : ι}
    (h : i ≠ i') (A : Set (M i)) (B : Set (M i')) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i' '' B) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
  exact h (congrArg Sigma.fst hb).symm

private theorem disjoint_sigmaMk_image {ι : Type u} {M : ι → Type u} {i : ι}
    {A B : Set (M i)} (h : Disjoint A B) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i '' B) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  exact Set.disjoint_left.mp h ha ((sigma_mk_injective hba).symm ▸ hb)

private theorem disjoint_sigmaMk_image_of_eq {ι : Type u} {M : ι → Type u} {i i' : ι}
    (h : i = i') {A : Set (M i)} {B : Set (M i')} (hd : Disjoint A (h ▸ B)) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i' '' B) := by
  cases h
  exact disjoint_sigmaMk_image hd

private theorem connectedComponents_mk_sigmaMk_eq_iff {ι : Type u} {M : ι → Type u}
    [∀ i, TopologicalSpace (M i)] [∀ i, PreconnectedSpace (M i)]
    {i i' : ι} (y : M i) (y' : M i') :
    ConnectedComponents.mk (⟨i, y⟩ : Σ j, M j) = ConnectedComponents.mk (⟨i', y'⟩ : Σ j, M j) ↔
      i = i' := by
  constructor
  · intro h
    have hmem : (⟨i', y'⟩ : Σ j, M j) ∈ connectedComponent (⟨i, y⟩ : Σ j, M j) :=
      (ConnectedComponents.coe_eq_coe').mp h.symm
    have hsub := isPreconnected_connectedComponent.subset_isClopen isClopen_range_sigmaMk
      ⟨⟨i, y⟩, mem_connectedComponent, ⟨y, rfl⟩⟩
    obtain ⟨z, hz⟩ := hsub hmem
    exact (Sigma.mk.inj_iff.mp hz).1
  · rintro rfl
    rw [ConnectedComponents.coe_eq_coe']
    exact (isPreconnected_univ.image _
        continuous_sigmaMk.continuousOn).subset_connectedComponent ⟨y', trivial, rfl⟩
      ⟨y, trivial, rfl⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

local instance localClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance localClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

abbrev vertexSum : ClosedOrientedManifold.{u} 3 :=
  closedOrientedUnion fun v => (G.vertexManifold v).toClosedOrientedManifold

theorem vertexSum_carrier :
    (vertexSum G).Carrier = (Σ v, (G.vertexManifold v).Carrier) := rfl

theorem vertexSum_orientation (v : G.Vertex) (y : (G.vertexManifold v).Carrier) :
    (vertexSum G).orientation.orientation (⟨v, y⟩ : Σ w, (G.vertexManifold w).Carrier) =
      (G.vertexManifold v).orientation.orientation y := rfl

def flagMarkedBall (e : G.Edge) : MarkedBall (vertexSum G) where
  ball x := (⟨G.endpoint e false, (G.flag e false).ball x⟩ : (vertexSum G).Carrier)
  ball_embedding :=
    IsSmoothEmbedding.comp_of_smoothBoundary
      (isSmoothEmbedding_sigmaMk
        (M := fun v => (G.vertexManifold v).Carrier)
        (I := 𝓡 3) (n := ∞) (G.endpoint e false))
      (G.flag e false).ball_embedding
  collar := Sigma.mk (G.endpoint e false) '' (G.flag e false).collar
  collar_isOpen :=
    (IsOpenEmbedding.sigmaMk (i := G.endpoint e false)).isOpenMap _ (G.flag e false).collar_isOpen
  ball_subset_collar := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(G.flag e false).ball x,
      (G.flag e false).ball_subset_collar (mem_range_self x), rfl⟩
  collarBudget := (G.flag e false).collarBudget
  collarBudget_pos := (G.flag e false).collarBudget_pos

theorem flagMarkedBall_ball (e : G.Edge) (x : ClosedCell 3) :
    (flagMarkedBall G e).ball x =
      (⟨G.endpoint e false, (G.flag e false).ball x⟩ : (vertexSum G).Carrier) := rfl

theorem flagMarkedBall_collar (e : G.Edge) :
    (flagMarkedBall G e).collar =
      Sigma.mk (G.endpoint e false) '' (G.flag e false).collar := rfl

theorem flagMarkedBall_collar_disjoint (e e' : G.Edge) (h : e ≠ e') :
    Disjoint (flagMarkedBall G e).collar (flagMarkedBall G e').collar := by
  rw [flagMarkedBall_collar, flagMarkedBall_collar]
  by_cases hv : G.endpoint e false = G.endpoint e' false
  · refine disjoint_sigmaMk_image_of_eq hv ?_
    refine G.flag_collar_disjoint (G.endpoint e false) ⟨(e, false), rfl⟩ ⟨(e', false), hv.symm⟩ ?_
    intro heq
    exact h (Prod.mk.inj (Subtype.ext_iff.mp heq)).1
  · exact disjoint_sigmaMk_image_of_ne hv _ _

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

open ClosedOrientedManifold

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

def initialPartialRealization : PartialRealization G ∅ where
  realization := vertexSum G
  vertexPiece v :=
    ⟨fun y => (⟨v, y.1⟩ : (vertexSum G).Carrier),
      continuous_sigmaMk.comp continuous_subtype_val⟩
  cylinderPiece e he := (Finset.notMem_empty e he).elim
  survivingFlag e _ := flagMarkedBall G e
  covers x := Or.inl ⟨x.1,
    ⟨x.2, by rw [removedBallSet_empty]; exact Set.notMem_empty x.2⟩, Sigma.eta x⟩
  survivingFlag_collar_disjoint e e' _ _ hne := flagMarkedBall_collar_disjoint G e e' hne

theorem componentCorrespondence_initialPartialRealization :
    (initialPartialRealization G).componentCorrespondence := by
  intro v v' y y'
  rw [show G.processedGraph ∅ = (⊥ : SimpleGraph G.Vertex) from Finset.sup_empty,
    SimpleGraph.reachable_bot]
  exact connectedComponents_mk_sigmaMk_eq_iff
    (M := fun w => (G.vertexManifold w).Carrier) y.1 y'.1

theorem cylinderComponentCovering_initialPartialRealization :
    (initialPartialRealization G).CylinderComponentCovering := by
  intro x
  exact ⟨x.1, ⟨x.2, by rw [removedBallSet_empty]; exact Set.notMem_empty x.2⟩,
    (congrArg ConnectedComponents.mk (Sigma.eta x)).symm⟩

end MarkedManifoldGraph

def HasSummandComponentDiffeomorph : Prop :=
  ∀ (ι : Type u) [Fintype ι] (M : ι → ClosedOrientedManifold.{u} 3) (i : ι)
    (y : (M i).Carrier),
    Nonempty (OrientedDiffeomorph
      ((closedOrientedUnion M).component
        (ConnectedComponents.mk (⟨i, y⟩ : (closedOrientedUnion M).Carrier))).toClosedOrientedManifold
      ((M i).component (ConnectedComponents.mk y)).toClosedOrientedManifold)

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem hasBlockPresentation_initialPartialRealization (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    (initialPartialRealization G).HasBlockPresentation Z := by
  refine ⟨fun _ => 0, fun _ _ _ => rfl, fun v y => ?_⟩
  have hb : (finiteConnectedSum
      (G.vertexBlockList ∅ v ++ List.replicate 0 Z)).toClosedOrientedManifold =
      (G.vertexManifold v).toClosedOrientedManifold := by
    rw [vertexBlockList_empty, List.replicate_zero, List.append_nil, finiteConnectedSum_singleton]
  rw [hb]
  obtain ⟨e⟩ := h (G.Vertex) (fun w => (G.vertexManifold w).toClosedOrientedManifold) v y.1
  exact ⟨e.trans (ClosedOrientedManifold.componentOrientedDiffeomorph
    (G.vertexManifold v).toClosedOrientedManifold (ConnectedComponents.mk y.1))⟩

theorem isBlockInvariant_initialPartialRealization (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    (initialPartialRealization G).IsBlockInvariant Z :=
  ⟨componentCorrespondence_initialPartialRealization G,
    hasBlockPresentation_initialPartialRealization G h Z,
    cylinderComponentCovering_initialPartialRealization G⟩

theorem exists_initial_of_hasSummandComponentDiffeomorph (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z := by
  exact ⟨initialPartialRealization G, isBlockInvariant_initialPartialRealization G h Z⟩

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem hasBlockPresentation_of_blockStepLaw {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h : BlockStepLaw G Z) :
    ∃ P : PartialRealization G ∅, P.HasBlockPresentation Z :=
  h.initial.imp fun _ hP => hP.2.1

theorem isBlockInvariant_iff_hasBlockPresentation {Z : ConnectedClosedOrientedManifold.{u} 3} :
    (initialPartialRealization G).IsBlockInvariant Z ↔
      (initialPartialRealization G).HasBlockPresentation Z :=
  ⟨fun h => h.2.1, fun h => ⟨componentCorrespondence_initialPartialRealization G, h,
    cylinderComponentCovering_initialPartialRealization G⟩⟩

theorem blockStepLaw_of_hasSummandComponentDiffeomorph (h : HasSummandComponentDiffeomorph.{u})
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (hstep : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
      P.IsBlockInvariant Z → ∃ P' : PartialRealization G (insert e S), P'.IsBlockInvariant Z) :
    BlockStepLaw G Z :=
  ⟨exists_initial_of_hasSummandComponentDiffeomorph G h Z, hstep⟩

end MarkedManifoldGraph

namespace MarkedManifoldGraph

theorem exists_initial_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization (oneVertex N) ∅, P.IsBlockInvariant Z :=
  (oneVertexBlockStepLaw N Z).initial

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

namespace MarkedManifoldGraph

theorem exists_initial_of_hasSummandComponentDiffeomorph_twoVertex
    (h : HasSummandComponentDiffeomorph.{0}) (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold)
    (Z : ConnectedClosedOrientedManifold.{0} 3) :
    ∃ P : PartialRealization (twoVertex N B B') ∅, P.IsBlockInvariant Z :=
  exists_initial_of_hasSummandComponentDiffeomorph (twoVertex N B B') h Z

theorem initialPartialRealization_twoVertex_componentCorrespondence
    (N : ConnectedClosedOrientedManifold.{0} 3) (B B' : MarkedBall N.toClosedOrientedManifold) :
    (initialPartialRealization (twoVertex N B B')).componentCorrespondence :=
  componentCorrespondence_initialPartialRealization (twoVertex N B B')

theorem initialPartialRealization_twoVertex_cylinderComponentCovering
    (N : ConnectedClosedOrientedManifold.{0} 3) (B B' : MarkedBall N.toClosedOrientedManifold) :
    (initialPartialRealization (twoVertex N B B')).CylinderComponentCovering :=
  cylinderComponentCovering_initialPartialRealization (twoVertex N B B')

end MarkedManifoldGraph

end DifferentialGeometry.Topology
