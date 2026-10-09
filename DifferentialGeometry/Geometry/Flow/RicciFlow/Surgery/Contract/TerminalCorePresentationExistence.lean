import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Topology.Manifold.OpenSubsetImage
import DifferentialGeometry.Topology.ProperMap.HalfCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalComponentEnds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutoffScale
import DifferentialGeometry.Geometry.Neck.NormalizedOpen
import DifferentialGeometry.Geometry.Neck.SpatialRestriction
import DifferentialGeometry.Geometry.Neck.SpatialTolerance
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarAmbient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmoothCutCapTransitionInstance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private structure ComponentEndPresentation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (C : Set M) (A B ε : ℝ) where
  core : Set M
  compact : IsCompact core
  connected : C.Nonempty → IsConnected core
  charts : ChartedSpace (EuclideanHalfSpace 3) core
  smooth : letI := charts; IsManifold (𝓡∂ 3) ∞ core
  induced : letI := charts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : core → M)
  interior_eq : letI := charts
    (Subtype.val : core → M) '' (𝓡∂ 3).interior core = interior core
  boundary_eq : letI := charts
    (Subtype.val : core → M) '' (𝓡∂ 3).boundary core = frontier core
  low : {x | x ∈ C ∧ metricScalarAt g x ≤ A} ⊆ interior core
  Index : Type u
  finite : Finite Index
  horn : Index → NeckCylinder → M
  base_neck : ∀ i, ∃ (p : M) (N : SpatialNeck g (1 / 156000) p) (level : ℝ),
    |level| ≤ 3 ∧ ∀ y, horn i (y, 0) = N.map (y, level)
  horn_smooth : ∀ i, ContMDiffOn NeckCylinderModel ThreeModel ∞ (horn i) (univ ×ˢ Ici (0 : ℝ))
  horn_embedding : ∀ i,
    let U : TopologicalSpace.Opens NeckCylinder :=
      ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (fun p : U => horn i p)
  horn_injOn : ∀ i, InjOn (horn i) (univ ×ˢ Ici (0 : ℝ))
  horn_proper : ∀ i, IsProperMap (fun p : HalfNeckCylinder => horn i p.val)
  horn_disjoint : Pairwise (fun i j => Disjoint
    (range (fun p : HalfNeckCylinder => horn i p.val))
    (range (fun p : HalfNeckCylinder => horn j p.val)))
  horn_meets : ∀ i, (range (fun p : HalfNeckCylinder => horn i p.val)) ∩ core =
    range (fun y : Sphere 2 => horn i (y, 0))
  frontier_eq : frontier core = ⋃ i, range (fun y : Sphere 2 => horn i (y, 0))
  collar : ∀ i, SmoothTwoSidedCollar (𝓡 2) ThreeModel (fun y : Sphere 2 => horn i (y, 0))
  collar_side : ∀ i (p : Sphere 2 × symmetricOpenInterval (collar i).radius),
    (collar i).toFun p ∈ core ↔ (p.2 : ℝ) ≤ 0
  collar_eq : ∀ i (p : Sphere 2 × symmetricOpenInterval (collar i).radius),
    0 ≤ (p.2 : ℝ) → (collar i).toFun p = horn i (p.1, p.2)
  cover : C = core ∪ ⋃ i, range (fun p : HalfNeckCylinder => horn i p.val)
  scalar_large : ∀ i y t, 0 ≤ t → A < metricScalarAt g (horn i (y, t))
  scalar_base : ∀ i y, metricScalarAt g (horn i (y, 0)) ≤ B
  scalar_diverges : ∀ i L, ∃ T : ℝ, ∀ y t, T ≤ t → L < metricScalarAt g (horn i (y, t))
  spatial_neck : ∀ i x, x ∈ interior (range (fun p : HalfNeckCylinder => horn i p.val)) →
    ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck g δ k),
      N.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k

private def compactComponentPresentation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (C : Set M) (A B ε : ℝ)
    (hopen : IsOpen C) (hclosed : IsClosed C) (hcpt : IsCompact C)
    (hconn : C.Nonempty → IsConnected C) : ComponentEndPresentation g C A B ε := by
  have hboundary : let _ := subsetChartedSpace C hopen; (𝓡∂ 3).boundary C = ∅ :=
    subset_boundary_eq_empty C hopen
  have hinterior : let _ := subsetChartedSpace C hopen;
      (Subtype.val : C → M) '' (𝓡∂ 3).interior C = interior C := by
    let _ := subsetChartedSpace C hopen
    have hb := hboundary
    have hi : (𝓡∂ 3).interior C = (univ : Set C) := by
      simpa only [hb, union_empty] using
        (ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 3) (M := C))
    change (Subtype.val : C → M) '' (𝓡∂ 3).interior C = interior C
    rw [hi, image_univ, Subtype.range_coe, hopen.interior_eq]
  have hfront : frontier C = ∅ := (show IsClopen C from ⟨hclosed, hopen⟩).frontier_eq
  exact {
    core := C
    compact := hcpt
    connected := hconn
    charts := subsetChartedSpace C hopen
    smooth := subsetIsManifold C hopen
    induced := subset_inclusion_isSmoothEmbedding C hopen
    interior_eq := hinterior
    boundary_eq := by rw [hboundary, image_empty, hfront]
    low := fun _ hx => hopen.interior_eq.symm ▸ hx.1
    Index := PEmpty
    finite := inferInstance
    horn := fun i => isEmptyElim i
    base_neck := fun i => isEmptyElim i
    horn_smooth := fun i => isEmptyElim i
    horn_embedding := fun i => isEmptyElim i
    horn_injOn := fun i => isEmptyElim i
    horn_proper := fun i => isEmptyElim i
    horn_disjoint := fun i => isEmptyElim i
    horn_meets := fun i => isEmptyElim i
    frontier_eq := by rw [hfront, iUnion_of_empty]
    collar := fun i => isEmptyElim i
    collar_side := fun i => isEmptyElim i
    collar_eq := fun i => isEmptyElim i
    cover := by rw [iUnion_of_empty, union_empty]
    scalar_large := fun i => isEmptyElim i
    scalar_base := fun i => isEmptyElim i
    scalar_diverges := fun i => isEmptyElim i
    spatial_neck := fun i => isEmptyElim i }

private def ComponentEndPresentation.toAmbient
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric ThreeModel M} {U : TopologicalSpace.Opens M}
    (hUclosed : IsClosed (U : Set M)) {A B ε : ℝ}
    (P : ComponentEndPresentation (g.restrictOpen U) (univ : Set U) A B ε) :
    ComponentEndPresentation g (U : Set M) A B ε := by
  let _ := P.charts
  let _ := P.smooth
  let hex := DifferentialGeometry.Topology.Manifold.exists_manifold_image_open_subtype
    (𝓡∂ 3) ThreeModel U P.core (P.compact.image continuous_subtype_val).isClosed
    P.induced P.interior_eq
  let charts := hex.choose
  obtain ⟨hmanifold, hinduced, hinterior, hboundary⟩ := hex.choose_spec
  let core : Set M := Subtype.val '' P.core
  let horn (i : P.Index) (p : NeckCylinder) : M := (P.horn i p).val
  let collar (i : P.Index) : SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun z : Sphere 2 => horn i (z, 0)) :=
    (P.collar i).mapAmbient Subtype.val (DifferentialGeometry.isLocalDiffeomorph_subtype_val U)
      Subtype.val_injective
  have hrange (i : P.Index) : range (fun p : HalfNeckCylinder => horn i p.val) =
      Subtype.val '' range (fun p : HalfNeckCylinder => P.horn i p.val) := by
    exact Set.range_comp _ _
  have hbase (i : P.Index) : range (fun z : Sphere 2 => horn i (z, 0)) =
      Subtype.val '' range (fun z : Sphere 2 => P.horn i (z, 0)) := by
    exact Set.range_comp _ _
  have hcoremem (x : U) : x.val ∈ core ↔ x ∈ P.core := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact (Subtype.ext hzx : z = x) ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfront : frontier core = Subtype.val '' frontier P.core :=
    (Embedding.image_frontier_of_isOpenEmbedding_of_isCompact U.isOpenEmbedding' P.compact).symm
  have hint : interior core = Subtype.val '' interior P.core :=
    (Embedding.image_interior_of_isOpenEmbedding U.isOpenEmbedding' P.core).symm
  refine {
    core := core
    compact := P.compact.image continuous_subtype_val
    connected := ?_
    charts := charts
    smooth := hmanifold
    induced := hinduced
    interior_eq := hinterior
    boundary_eq := hboundary
    low := ?_
    Index := P.Index
    finite := P.finite
    horn := horn
    base_neck := by
      intro i
      obtain ⟨p, N, level, hlevel, hmap⟩ := P.base_neck i
      obtain ⟨Nout, _, hNout, _, _, _⟩ := N.exists_of_restrictOpen
      exact ⟨p.val, Nout, level, hlevel, fun y =>
        (congrArg Subtype.val (hmap y)).trans (hNout (y, level)).symm⟩
    horn_smooth := ?_
    horn_embedding := ?_
    horn_injOn := ?_
    horn_proper := ?_
    horn_disjoint := ?_
    horn_meets := ?_
    frontier_eq := ?_
    collar := collar
    collar_side := ?_
    collar_eq := ?_
    cover := ?_
    scalar_large := ?_
    scalar_base := ?_
    scalar_diverges := ?_
    spatial_neck := ?_ }
  · intro hUne
    have hU : (univ : Set U).Nonempty := by
      obtain ⟨x, hx⟩ := hUne
      exact ⟨⟨x, hx⟩, mem_univ _⟩
    exact (P.connected hU).image Subtype.val continuous_subtype_val.continuousOn
  · intro x hx
    rw [hint]
    let z : U := ⟨x, hx.1⟩
    refine ⟨z, P.low ⟨mem_univ z, ?_⟩, rfl⟩
    simpa only [CheegerGromovCompactness.metricScalarAt_restrictOpen] using hx.2
  · intro i
    exact (contMDiff_subtype_val (I := ThreeModel) (U := U)).comp_contMDiffOn (P.horn_smooth i)
  · intro i
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel U _ (P.horn_embedding i)
  · intro i x hx y hy hxy
    exact P.horn_injOn i hx hy (Subtype.ext hxy)
  · intro i
    exact hUclosed.isProperMap_subtypeVal.comp (P.horn_proper i)
  · intro i j hij
    rw [hrange, hrange]
    exact (P.horn_disjoint hij).image Subtype.val_injective.injOn (subset_univ _) (subset_univ _)
  · intro i
    rw [hrange, hbase]
    change (Subtype.val '' range (fun p : HalfNeckCylinder => P.horn i p.val)) ∩
      (Subtype.val '' P.core) = _
    rw [← image_inter Subtype.val_injective, P.horn_meets i]
  · rw [hfront, P.frontier_eq, image_iUnion]
    exact iUnion_congr (fun i => (hbase i).symm)
  · intro i p
    change ((P.collar i).toFun p).val ∈ core ↔ _
    rw [hcoremem]
    exact P.collar_side i p
  · intro i p hp
    exact congrArg Subtype.val (P.collar_eq i p hp)
  · have hc := congrArg (Set.image (Subtype.val : U → M)) P.cover
    rw [image_univ, Subtype.range_coe, image_union, image_iUnion] at hc
    exact hc.trans (congrArg (fun E => core ∪ E) (iUnion_congr (fun i => (hrange i).symm)))
  · intro i y t ht
    simpa only [horn, CheegerGromovCompactness.metricScalarAt_restrictOpen] using P.scalar_large i y t ht
  · intro i y
    simpa only [horn, CheegerGromovCompactness.metricScalarAt_restrictOpen] using P.scalar_base i y
  · intro i L
    obtain ⟨T, hT⟩ := P.scalar_diverges i L
    refine ⟨T, fun y t ht => ?_⟩
    simpa only [horn, CheegerGromovCompactness.metricScalarAt_restrictOpen] using hT y t ht
  · intro i x hx
    have hxrange := interior_subset hx
    rw [hrange] at hxrange
    obtain ⟨z, hz, rfl⟩ := hxrange
    have hzint : z ∈ interior (range (fun p : HalfNeckCylinder => P.horn i p.val)) := by
      have heq := U.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
        continuous_subtype_val (range (fun p : HalfNeckCylinder => horn i p.val))
      have hp : z ∈ interior ((Subtype.val : U → M) ⁻¹'
          range (fun p : HalfNeckCylinder => horn i p.val)) := heq ▸ hx
      simpa only [hrange, preimage_image_eq _ Subtype.val_injective] using hp
    obtain ⟨δ, k, N, hcenter, hδ, hk⟩ := P.spatial_neck i z hzint
    exact ⟨δ, k, N.toAmbient, congrArg Subtype.val hcenter, hδ, hk⟩

private def componentPresentationOfHalfCylinders
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {g : SmoothRiemannianMetric ThreeModel M} {A B ε : ℝ}
    (K : Set M) (m : ℕ) (Θ : Fin m → NeckCylinder → M)
    (charts : ChartedSpace (EuclideanHalfSpace 3) K)
    (collar : ∀ i, SmoothTwoSidedCollar (𝓡 2) ThreeModel (fun y : Sphere 2 => Θ i (y, 0)))
    (hcompact : IsCompact K) (hconnected : IsConnected K)
    (hlow : {x | metricScalarAt g x ≤ A} ⊆ interior K)
    (hends : ∀ i, ContMDiffOn NeckCylinderModel ThreeModel ∞ (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
      InjOn (Θ i) (univ ×ˢ Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ i (z.1, z.2.val)) ∧
      (let V : TopologicalSpace.Opens NeckCylinder :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (fun z : V => Θ i z)) ∧
      Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun z => Θ i (z, 0)) ∧
      (∀ L : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → L < metricScalarAt g (Θ i (z, t.val))) ∧
      (∀ z t, 0 ≤ t → A < metricScalarAt g (Θ i (z, t))) ∧
      (∀ z, metricScalarAt g (Θ i (z, 0)) ≤ B) ∧
      ∀ x, x ∈ Θ i '' (univ ×ˢ Ici (0 : ℝ)) →
        ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck g δ k),
          N.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k)
    (hbase : ∀ i, ∃ (p : M) (N : SpatialNeck g (1 / 156000) p) (level : ℝ),
      |level| ≤ 3 ∧ ∀ y, Θ i (y, 0) = N.map (y, level))
    (hdisjoint : Pairwise fun i j => Disjoint (Θ i '' (univ ×ˢ Ici (0 : ℝ)))
      (Θ j '' (univ ×ˢ Ici (0 : ℝ))))
    (hfrontier : frontier K = ⋃ i, range (fun z => Θ i (z, 0)))
    (hcover : K ∪ (⋃ i, Θ i '' (univ ×ˢ Ici (0 : ℝ))) = univ)
    (hcharts : let _ := charts
      IsManifold (𝓡∂ 3) ∞ K ∧ IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : K → M) ∧
      (∀ x : K, (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
      (∀ x : K, (𝓡∂ 3).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
      Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
      Subtype.val '' ((𝓡∂ 3).interior K) = interior K)
    (hcollar : ∀ i, (collar i).radius < 1 ∧
      (∀ p : Sphere 2 × symmetricOpenInterval (collar i).radius,
        (collar i).toFun p ∈ K ↔ p.2.val ≤ 0) ∧
      (∀ p : Sphere 2 × symmetricOpenInterval (collar i).radius,
        p.2.val < 0 → (collar i).toFun p ∈ interior K) ∧
      ∀ p : Sphere 2 × symmetricOpenInterval (collar i).radius,
        0 ≤ p.2.val → (collar i).toFun p = Θ i (p.1, p.2.val)) :
    ComponentEndPresentation g (univ : Set M) A B ε := by
  let Ind := ULift.{u} (Fin m)
  have hiUnion : (⋃ i : Ind, range (fun p : HalfNeckCylinder => Θ i.down p.val)) =
      ⋃ i : Fin m, Θ i '' (univ ×ˢ Ici (0 : ℝ)) := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      exact ⟨i.down, (range_half_cylinder_eq_image _).subset hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨ULift.up i, (range_half_cylinder_eq_image _).superset hx⟩
  refine {
    core := K
    compact := hcompact
    connected := fun _ => hconnected
    charts := charts
    smooth := hcharts.1
    induced := hcharts.2.1
    interior_eq := hcharts.2.2.2.2.2
    boundary_eq := hcharts.2.2.2.2.1
    low := fun _ hx => hlow hx.2
    Index := Ind
    finite := inferInstance
    horn := fun i => Θ i.down
    base_neck := fun i => hbase i.down
    horn_smooth := fun i => (hends i.down).1
    horn_embedding := fun i => (hends i.down).2.2.2.1
    horn_injOn := fun i => (hends i.down).2.1
    horn_proper := fun i => (isProperMap_half_cylinder_iff _).mpr (hends i.down).2.2.1
    horn_disjoint := ?_
    horn_meets := fun i => by rw [range_half_cylinder_eq_image]; exact (hends i.down).2.2.2.2.1
    frontier_eq := ?_
    collar := fun i => collar i.down
    collar_side := fun i => (hcollar i.down).2.1
    collar_eq := fun i => (hcollar i.down).2.2.2
    cover := ?_
    scalar_large := fun i => (hends i.down).2.2.2.2.2.2.1
    scalar_base := fun i => (hends i.down).2.2.2.2.2.2.2.1
    scalar_diverges := fun i L => (uniform_scalar_divergence_nnreal_iff _ _ _).mp
      ((hends i.down).2.2.2.2.2.1 L)
    spatial_neck := ?_ }
  · intro i j hij
    rw [range_half_cylinder_eq_image, range_half_cylinder_eq_image]
    exact hdisjoint (fun h => hij (ULift.ext h))
  · rw [hfrontier]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩, fun ⟨i, hi⟩ => ⟨i.down, hi⟩⟩
  · rw [hiUnion]
    exact hcover.symm
  · intro i x hx
    exact (hends i.down).2.2.2.2.2.2.2.2 x
      ((range_half_cylinder_eq_image _).subset (interior_subset hx))

private def assembleTerminalCorePresentation
    (D : OneStepIncoming.{u}) {ε Λ r : ℝ}
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hr : 0 < r)
    (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (produce : ∀ c : ConnectedComponents D.slab.terminalRegularOpen,
      (∃ y : D.slab.terminalRegularOpen, ConnectedComponents.mk y = c ∧
        metricScalarAt D.terminal.metric y ≤ (r ^ 2)⁻¹) →
      Nonempty (ComponentEndPresentation D.terminal.metric
        {x | ConnectedComponents.mk x = c} (r ^ 2)⁻¹ (Λ * (r ^ 2)⁻¹) ε)) :
    {P : TerminalCorePresentation D ε Λ //
      ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
        (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
        |level| ≤ 3 ∧ ∀ y, P.horn c e (y, 0) = N.map (y, level)} := by
  classical
  let component : Set (ConnectedComponents D.slab.terminalRegularOpen) :=
    {c | ∃ y : D.slab.terminalRegularOpen, ConnectedComponents.mk y = c ∧
      metricScalarAt D.terminal.metric y ≤ (r ^ 2)⁻¹}
  let data (c : ConnectedComponents D.slab.terminalRegularOpen) :
      ComponentEndPresentation D.terminal.metric
        (if c ∈ component then {x | ConnectedComponents.mk x = c} else ∅)
        (r ^ 2)⁻¹ (Λ * (r ^ 2)⁻¹) ε := by
    by_cases hc : c ∈ component
    · rw [ite_eq_left hc]
      exact (produce c hc).some
    · rw [ite_eq_right hc]
      exact compactComponentPresentation D.terminal.metric ∅ _ _ _
        isOpen_empty isClosed_empty isCompact_empty (fun h => h.ne_empty rfl |>.elim)
  refine ⟨{
    epsilon_pos := hε
    Lambda_ge_one := hΛ
    coreRadius := r
    coreRadius_pos := hr
    coreRadius_eq := hradius
    component := component
    component_finite := D.terminal.finite_components_meeting_scalar_sublevel ((r ^ 2)⁻¹)
    core := fun c => (data c).core
    core_isCompact := fun c _ => (data c).compact
    core_isConnected := ?_
    core_empty := ?_
    coreCharts := fun c _ => (data c).charts
    core_smooth := fun c _ => (data c).smooth
    core_induced := fun c _ => (data c).induced
    core_interior_eq := fun c _ => (data c).interior_eq
    core_boundary_eq := fun c _ => (data c).boundary_eq
    component_iff_meets_low := fun _ => Iff.rfl
    low_mem_interior_core := ?_
    hornIndex := fun c => (data c).Index
    hornIndex_finite := fun c => (data c).finite
    hornIndex_empty := ?_
    horn := fun c => (data c).horn
    horn_smooth := fun c => (data c).horn_smooth
    horn_interior_embedding := fun c => (data c).horn_embedding
    horn_injOn := fun c => (data c).horn_injOn
    horn_proper := fun c => (data c).horn_proper
    horn_range_disjoint := fun c _ _ hij => (data c).horn_disjoint hij
    horn_meets_core := fun c => (data c).horn_meets
    horn_base_covers_boundary := fun c _ => (data c).frontier_eq
    hornCollar := fun c => (data c).collar
    horn_collar_core_side := fun c => (data c).collar_side
    horn_collar_eq := fun c => (data c).collar_eq
    horn_covers_component := ?_
    horn_scalar_large := fun c => (data c).scalar_large
    horn_base_scalar := fun c => (data c).scalar_base
    horn_scalar_diverges := fun c => (data c).scalar_diverges
    horn_spatial_neck := fun c => (data c).spatial_neck }, ?_⟩
  · intro c hc
    apply (data c).connected
    obtain ⟨y, hy, _⟩ := (show c ∈ component from hc)
    exact ⟨y, by simp only [ite_eq_left hc]; exact hy⟩
  · intro c hc
    have h := (data c).cover.symm.trans (ite_eq_right hc)
    exact (union_empty_iff.mp h).1
  · intro c hc x hx hscalar
    apply (data c).low
    exact ⟨by simp only [ite_eq_left hc]; exact hx, hscalar⟩
  · intro c hc
    have h := (data c).cover.symm.trans (ite_eq_right hc)
    have he := (union_empty_iff.mp h).2
    refine ⟨fun i => ?_⟩
    let q : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
    have hm : (data c).horn i (q, 0) ∈ ⋃ j, range (fun p : HalfNeckCylinder => (data c).horn j p.val) :=
      mem_iUnion.mpr ⟨i, ⟨(q, 0), le_rfl⟩, rfl⟩
    exact Set.notMem_empty _ (he.subset hm)
  · intro c hc
    exact (ite_eq_left hc).symm.trans (data c).cover
  · intro c e
    exact (data c).base_neck e

namespace OneStepIncoming

theorem exists_neckRadius_terminalCorePresentation_with_base_necks_of_canonical_neighborhoods
    {ε : ℝ} (hε : 0 < ε) :
    ∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧
      ∀ C1 C2 : ℝ, 1 ≤ C2 →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ q : ℝ, 0 < q →
      ∀ D : OneStepIncoming.{u},
        (∀ x t, t ∈ Ioo D.startTime D.endTime → q < D.slab.flow.scalar t x →
          ∃ W : CanonicalWitness D.slab.flow εcan C1 C2 x t,
            W.capTubeHasNeckChart εcan) →
        ∀ q' : ℝ, q ≤ q' →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          q' < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / C) ∧
          (∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
          ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
            (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
            |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
            ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
  classical
  obtain ⟨η₁, hη₁, hcutoff⟩ :=
    exists_neckRadius_spherical_region_with_exterior_alternatives_of_canonical_neighborhoods.{u}
  obtain ⟨η₂, hη₂, hends⟩ := exists_smooth_saved_end_decomposition_on_noncompact_component.{u,u}
  let δ := min η₁ (min η₂ (min (ε / 26000) (1 / 156000)))
  have hδ : 0 < δ := lt_min hη₁ (lt_min hη₂ (lt_min (by positivity) (by norm_num)))
  have hδ₁ : δ ≤ η₁ := min_le_left _ _
  have hδ₂ : δ ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : 26000 * δ ≤ ε := by
    have hh : δ ≤ ε / 26000 := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hδsmall : δ ≤ 1 / 156000 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ / 4, by positivity, by linarith, ?_⟩
  intro C1 C2 hC2
  let C := 2 * C2
  let Λ := 8 * C2 ^ 2 * C
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hΛ : 1 ≤ Λ := by
    dsimp [Λ]
    have hsq : 1 ≤ C2 ^ 2 := by nlinarith
    have hp := mul_le_mul hsq hC (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg C2)
    nlinarith
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro q hq D hcanonical q' hqq'
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, hscale, hscaleBound, hregions⟩ :=
    hcutoff δ hδ hδ₁ C1 C2 q hC2 hq D hcanonical q' hqq'
  let D' := D.withNeckRadius ρ hρ
  let r := D.parameters.delta D.endTime * ρ D.endTime
  let A := (r ^ 2)⁻¹
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hr : 0 < r := mul_pos (D.parameters.delta_pos _ hs) (hρ _ hs)
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hr)
  have hproducer (c : ConnectedComponents D'.slab.terminalRegularOpen)
      (hc : ∃ y : D'.slab.terminalRegularOpen, ConnectedComponents.mk y = c ∧
        metricScalarAt D'.terminal.metric y ≤ A) :
      Nonempty (ComponentEndPresentation D'.terminal.metric
        {x | ConnectedComponents.mk x = c} A (Λ * A) ε) := by
    obtain ⟨y, hyc, hyA⟩ := hc
    let U := connectedComponentOpen (I := ThreeModel) y
    have hUeq : (U : Set D'.slab.terminalRegularOpen) = {x | ConnectedComponents.mk x = c} := by
      ext x
      exact ⟨fun hx => (ConnectedComponents.coe_eq_coe'.mpr hx).trans hyc,
        fun hx => ConnectedComponents.coe_eq_coe'.mp (hx.trans hyc.symm)⟩
    have hUclosed : IsClosed (U : Set D'.slab.terminalRegularOpen) := isClosed_connectedComponent
    by_cases hcompact : IsCompact (connectedComponent y)
    · have hcompact' : IsCompact {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ hcompact
      have hopen : IsOpen {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ U.isOpen
      have hclosed : IsClosed {x : D'.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
        hUeq ▸ hUclosed
      exact ⟨compactComponentPresentation D'.terminal.metric _ A (Λ * A) ε
        hopen hclosed hcompact' (fun _ => hUeq ▸ isConnected_connectedComponent)⟩
    · obtain ⟨ι, hi, hne, v, neck, level, W, hW, hreg, hlow, hprotected,
        hupper, hpair, hfront, hlevel, _, _, hexterior⟩ := hregions y hyA hcompact
      let _ := hi
      let _ := hne
      obtain ⟨K, m, origin, Θ, charts, collar, _, hK, hconn, _, _, _, _, hzero,
        hlowK, _, hendsK, hdisjoint, hfrontK, hcover, hcharts, hcollar⟩ :=
        hends D' δ ε A C Λ hδ₂ hδε hA.le hC y hyA hcompact ι v neck level W hW hreg
          hlow hprotected hupper (fun i => (hlevel i).trans (by norm_num)) hpair hfront hexterior
      have hbase : ∀ i, ∃ (p : U) (N : SpatialNeck (D'.terminal.metric.restrictOpen U)
          (1 / 156000) p) (level : ℝ), |level| ≤ 3 ∧ ∀ z, Θ i (z, 0) = N.map (z, level) := by
        intro i
        exact ⟨v (origin i), (neck (origin i)).mono hδsmall (by norm_num),
          level (origin i), hlevel (origin i), hzero i⟩
      let Q := componentPresentationOfHalfCylinders K m Θ charts collar hK hconn
        hlowK hendsK hbase hdisjoint hfrontK hcover hcharts hcollar
      exact ⟨hUeq ▸ Q.toAmbient hUclosed⟩
  let assembled := assembleTerminalCorePresentation D' hε hΛ hr rfl hproducer
  let P := assembled.val
  have hbase : ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
      (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
      |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
      ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
    intro c e
    obtain ⟨p, N, level, hlevel, hmap⟩ := assembled.property c e
    refine ⟨p, N, level, hlevel, ?_, hmap⟩
    have hwindow : (N.center, level) ∈ univ ×ˢ Ioo (-((1 / 156000 : ℝ)⁻¹)) ((1 / 156000 : ℝ)⁻¹) := by
      refine ⟨mem_univ _, abs_lt.mp ?_⟩
      exact hlevel.trans_lt (by norm_num)
    have hlo := (N.scalar_bounds_on_image_window ⟨(N.center, level), hwindow, rfl⟩).1
    have hupper := P.horn_base_scalar c e N.center
    rw [hmap] at hupper
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 4323 * (1 / 156000) := by norm_num
    have hscale := mul_le_mul_of_nonneg_right hhalf N.Q_pos.le
    change metricScalarAt D'.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹
    nlinarith
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, P.coreRadius_eq, ?_, ?_, ?_, hbase⟩
  · rw [P.coreRadius_eq]
    exact hscale
  · rw [P.coreRadius_eq]
    exact hscaleBound
  · intro x hx
    have hprotectA : ((D.parameters.protectedRadius D.endTime)^2)⁻¹ ≤ A := by
      apply inv_anti₀ (sq_pos_of_pos hr)
      have hp := D.parameters.protectedRadius_pos D.endTime hs
      change r ≤ D.parameters.protectedRadius D.endTime at hprotect
      nlinarith
    have hxA : metricScalarAt D'.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹ := by
      rw [P.coreRadius_eq]
      exact hx.trans hprotectA
    have hc := (P.component_iff_meets_low (ConnectedComponents.mk x)).mpr ⟨x, rfl, hxA⟩
    exact ⟨ConnectedComponents.mk x, hc,
      P.low_mem_interior_core _ hc x rfl hxA⟩

theorem exists_neckRadius_terminalCorePresentation_with_scale_bound_and_base_necks {ε : ℝ} (hε : 0 < ε) :
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ D : OneStepIncoming.{u},
      ∃ q : ℝ, 0 < q ∧ ∀ q' : ℝ, q ≤ q' →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          q' < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / C) ∧
          (∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
          ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
            (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
            |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
            ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
  obtain ⟨εcan, hεcan, hsmall, hproduce⟩ :=
    exists_neckRadius_terminalCorePresentation_with_base_necks_of_canonical_neighborhoods.{u} hε
  obtain ⟨C2, hC2, hcanonical⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_constants_with_cap_neck_charts.{u} hεcan hsmall
  obtain ⟨C, Λ, hC, hΛ, hproduce⟩ := hproduce C2 C2 hC2
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro D
  obtain ⟨q, hq, hcanonical⟩ := hcanonical D.stage D.startTime D.endTime D.slab
  refine ⟨q, hq, ?_⟩
  exact hproduce q hq D (fun x t ht hx => hcanonical x t ⟨ht.1.le, ht.2⟩ hx.le)

theorem exists_neckRadius_terminalCorePresentation_with_scale_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ ∀ D : OneStepIncoming.{u},
      ∃ q : ℝ, 0 < q ∧ ∀ q' : ℝ, q ≤ q' →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          q' < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q' 0 + 1) / C) ∧
          ∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c) := by
  obtain ⟨C, Λ, hC, hΛ, hproduce⟩ :=
    exists_neckRadius_terminalCorePresentation_with_scale_bound_and_base_necks hε
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro D
  obtain ⟨q, hq, hproduce⟩ := hproduce D
  refine ⟨q, hq, ?_⟩
  intro q' hqq'
  obtain ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hscale, hupper, hlow, _⟩ := hproduce q' hqq'
  exact ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, P, hradius, hscale, hupper, hlow⟩

theorem exists_neckRadius_terminalCorePresentation {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ D : OneStepIncoming.{u},
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          ∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c) := by
  obtain ⟨C, Λ, _, hΛ, hproduce⟩ := exists_neckRadius_terminalCorePresentation_with_scale_bound hε
  refine ⟨Λ, hΛ, ?_⟩
  intro D
  obtain ⟨q, _, hproduce⟩ := hproduce D
  obtain ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, P, hradius, _, _, hlow⟩ :=
    hproduce q le_rfl
  exact ⟨ρ, hρ, hle, hmono, hmonoOn, hrecenter, hprotect, P, hradius, hlow⟩

theorem exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_canonical_neighborhoods
    {ε : ℝ} (hε : 0 < ε) :
    ∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧
      ∀ C1 C2 : ℝ, 1 ≤ C2 →
      ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
      ∀ q originalCoreFloor protectedFloor : ℝ,
        0 < q → 0 < originalCoreFloor → 0 < protectedFloor →
      ∃ radiusFloor : ℝ, 0 < radiusFloor ∧
      ∀ D : OneStepIncoming.{u},
        originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
        protectedFloor ≤ D.parameters.protectedRadius D.endTime →
        (∀ x t, t ∈ Ioo D.startTime D.endTime → q < D.slab.flow.scalar t x →
          ∃ W : CanonicalWitness D.slab.flow εcan C1 C2 x t,
            W.capTubeHasNeckChart εcan) →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
        ∃ P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε Λ,
          P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
          radiusFloor ≤ P.coreRadius ∧ radiusFloor ≤ ρ D.endTime ∧
          q < C * (P.coreRadius ^ 2)⁻¹ ∧
          (P.coreRadius ^ 2)⁻¹ ≤
            max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
              ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max q 0 + 1) / C) ∧
          (∀ x : D.slab.terminalRegularOpen,
            metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
              ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
          ∀ c e, ∃ (p : D.slab.terminalRegularOpen)
            (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
            |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
            ∀ y, P.horn c e (y, 0) = N.map (y, level) := by
  obtain ⟨εcan, hεcan, hεsmall, hproduce⟩ :=
    exists_neckRadius_terminalCorePresentation_with_base_necks_of_canonical_neighborhoods.{u} hε
  refine ⟨εcan, hεcan, hεsmall, ?_⟩
  intro C1 C2 hC2
  obtain ⟨C, Λ, hC, hΛ, hproduce⟩ := hproduce C1 C2 hC2
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro q originalCoreFloor protectedFloor hq hcoreFloor hprotectedFloor
  let M := max (max (originalCoreFloor ^ 2)⁻¹ (protectedFloor ^ 2)⁻¹)
    (4 * (max q 0 + 1) / C)
  have hM : 0 < M :=
    (inv_pos.mpr (sq_pos_of_pos hcoreFloor)).trans_le
      ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨Real.sqrt M⁻¹, Real.sqrt_pos.mpr (inv_pos.mpr hM), ?_⟩
  intro D hcore hprotected hcanonical
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hscale, hupper, hlow, hbase⟩ := hproduce q hq D hcanonical q le_rfl
  have hs : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hcoreInv : ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ ≤
      (originalCoreFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hcoreFloor) (by nlinarith)
  have hprotectedInv : (D.parameters.protectedRadius D.endTime ^ 2)⁻¹ ≤
      (protectedFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hprotectedFloor) (by nlinarith)
  have hupperM : (P.coreRadius ^ 2)⁻¹ ≤ M :=
    hupper.trans (max_le_max (max_le_max hcoreInv hprotectedInv) le_rfl)
  have hroot : Real.sqrt M⁻¹ ≤ P.coreRadius := by
    have hinv : M⁻¹ ≤ P.coreRadius ^ 2 := by
      simpa only [inv_inv] using
        inv_anti₀ (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos)) hupperM
    calc
      Real.sqrt M⁻¹ ≤ Real.sqrt (P.coreRadius ^ 2) := Real.sqrt_le_sqrt hinv
      _ = P.coreRadius := Real.sqrt_sq P.coreRadius_pos.le
  have hneck : P.coreRadius ≤ ρ D.endTime := by
    have hd := D.parameters.delta_lt_one D.endTime hs
    have hn := hρ D.endTime hs
    nlinarith [hradius]
  exact ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hroot, hroot.trans hneck, hscale, hupper, hlow, hbase⟩

end OneStepIncoming

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
