import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCutRegions
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusDecompositionPresentation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

def slicePhi_CPG (s : RegularSlice F.observation) :
    (postStage F.observation s.time).Carrier ≃ₜ s.stage.Carrier :=
  (exists_slicePhi_CPG s).choose

theorem slicePhi_spec_CPG (s : RegularSlice F.observation)
    (S : Set (postStage F.observation s.time).Carrier) (T : Set s.stage.Carrier) (h : HEq S T) :
    slicePhi_CPG s '' S = T :=
  (exists_slicePhi_CPG s).choose_spec S T h

theorem continuous_val_CPG (s : RegularSlice F.observation) (C : ConnectedComponents s.stage.Carrier) :
    Continuous (Subtype.val : (s.stage.toClosedOrientedManifold.component C).Carrier → s.stage.Carrier) :=
  continuous_subtype_val

/-- The cut carrier of the decomposition of component `C` mapped into the stage at the slice time. -/
def psi_CPG (L : LateCutFamily F K slices) (j : ℕ) (C : ConnectedComponents (slices j).stage.Carrier) :
    C((L.decomposition j C).carrier.Carrier, (postStage F.observation (slices j).time).Carrier) :=
  ⟨fun x => (slicePhi_CPG (slices j)).symm
      (((L.decomposition j C).reconstructionHomeomorph ((L.decomposition j C).boundary.quotientMap x)).val),
    (slicePhi_CPG (slices j)).symm.continuous.comp ((continuous_val_CPG (slices j) C).comp
      ((L.decomposition j C).reconstructionHomeomorph.continuous.comp
        (L.decomposition j C).boundary.quotientMap.continuous))⟩

theorem psi_not_port_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    {x : (L.decomposition j C).carrier.Carrier}
    (hx : (L.decomposition j C).carrier.model.IsInteriorPoint x)
    (p : Σ i : Fin L.cores.count, Fin (L.truncation j i).count) (y : Torus) :
    psi_CPG L j C x ≠ portPoint_CPE L j hj p.1 p.2 y := by
  obtain ⟨⟨C', s'⟩, rfl⟩ := (L.port j hj).surjective p
  intro heq
  obtain ⟨e, he⟩ := exists_seam_reparam_CPG L j hj C' s' (slicePhi_CPG (slices j))
    (slicePhi_spec_CPG (slices j))
  have h1 : (((L.decomposition j C).reconstructionHomeomorph
      ((L.decomposition j C).boundary.quotientMap x)).val) =
      ((L.decomposition j C').reconstructionAtlas.torusInPrime
        (L.decomposition j C').reconstruction s' (e.symm y)).val := by
    have := congrArg (slicePhi_CPG (slices j)) heq
    rw [he (e.symm y)] at *
    simpa [psi_CPG] using this
  have hCC : C = C' := by
    have p1 : ConnectedComponents.mk (((L.decomposition j C).reconstructionHomeomorph
      ((L.decomposition j C).boundary.quotientMap x)).val) = C :=
      ((L.decomposition j C).reconstructionHomeomorph
        ((L.decomposition j C).boundary.quotientMap x)).property
    have p2 : ConnectedComponents.mk (((L.decomposition j C').reconstructionAtlas.torusInPrime
        (L.decomposition j C').reconstruction s' (e.symm y)).val) = C' :=
      ((L.decomposition j C').reconstructionAtlas.torusInPrime
        (L.decomposition j C').reconstruction s' (e.symm y)).property
    rw [← p1, ← p2, h1]
  subst hCC
  have h2 : (L.decomposition j C).reconstructionHomeomorph
      ((L.decomposition j C).boundary.quotientMap x) =
      (L.decomposition j C).reconstructionHomeomorph
        ((L.decomposition j C).boundary.quotientMap
          ((L.decomposition j C).boundary.leftParam s' (e.symm y)).val) :=
    Subtype.ext h1
  have h3 := (L.decomposition j C).reconstructionHomeomorph.injective h2
  have h4 := (L.decomposition j C).boundary.interior_fiber_singleton hx h3
  have hb : x ∈ (L.decomposition j C).carrier.model.boundary (L.decomposition j C).carrier.Carrier := by
    rw [h4, (L.decomposition j C).boundary.boundary_exhausted]
    exact Set.mem_iUnion.mpr ⟨s', Or.inl ((L.decomposition j C).boundary.leftParam s' (e.symm y)).property⟩
  exact ((L.decomposition j C).carrier.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb

theorem piece_subset_closure_interior_CPG {C0 : CompactCarrier.{u}} (D : C0.Components)
    (p : Fin D.count) :
    (D.piece p : Set C0.Carrier) ⊆ closure (C0.pieceInterior (D.piece p) : Set C0.Carrier) := by
  intro x hx
  rw [mem_closure_iff]
  intro o ho hxo
  have hd : Dense (C0.model.interior C0.Carrier) := ModelWithCorners.dense_interior C0.model
  obtain ⟨z, ⟨hzo, hzp⟩, hzi⟩ := hd.inter_open_nonempty (o ∩ (D.piece p : Set C0.Carrier))
    (ho.inter (D.piece p).isOpen) ⟨x, hxo, hx⟩
  exact ⟨z, hzo, hzp, hzi⟩

theorem piece_dichotomy_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (p : Fin (L.decomposition j C).components.count) :
    (∃ i0, ∀ x ∈ ((L.decomposition j C).components.piece p : Set (L.decomposition j C).carrier.Carrier),
        psi_CPG L j C x ∈ Set.range (coreMap_CPG L j hj i0)) ∨
    (∀ x ∈ ((L.decomposition j C).components.piece p : Set (L.decomposition j C).carrier.Carrier),
        psi_CPG L j C x ∈ exteriorRegion_CPE L j hj) := by
  let D := L.decomposition j C
  let Sint : Set D.carrier.Carrier := (D.carrier.pieceInterior (D.components.piece p) : Set _)
  have hconn : IsConnected Sint := isConnected_iff_connectedSpace.mpr (D.components.interior_connected p)
  have hXc : IsConnected (psi_CPG L j C '' Sint) := hconn.image _ (psi_CPG L j C).continuous.continuousOn
  have hcl : ∀ x ∈ (D.components.piece p : Set D.carrier.Carrier),
      psi_CPG L j C x ∈ closure (psi_CPG L j C '' Sint) := fun x hx =>
    image_closure_subset_closure_image (psi_CPG L j C).continuous
      ⟨x, piece_subset_closure_interior_CPG D.components p hx, rfl⟩
  have hB : ∀ i, Disjoint (psi_CPG L j C '' Sint)
      (Set.range (coreMap_CPG L j hj i) \ coreInteriorImage_CPE L j hj i) := by
    intro i
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hy
    obtain ⟨q, z, hz⟩ := Set.mem_iUnion.mp (range_diff_subset_ports_CPG L j hj i hy)
    exact psi_not_port_CPG L j hj C hx.2 ⟨i, q⟩ z hz.symm
  rcases classify_CPG (fun i => coreInteriorImage_CPE L j hj i)
    (fun i => Set.range (coreMap_CPG L j hj i)) (isOpen_coreInteriorImage_CPG L j hj)
    (coreInteriorImage_disjoint_CPG L j hj) (isClosed_range_coreMap_CPG L j hj)
    (coreInteriorImage_subset_range_CPG L j hj) _ hXc.isPreconnected hXc.nonempty hB with
    ⟨i0, hi0⟩ | hV
  · left
    refine ⟨i0, fun x hx => ?_⟩
    exact (isClosed_range_coreMap_CPG L j hj i0).closure_subset_iff.mpr
      (fun y hy => coreInteriorImage_subset_range_CPG L j hj i0 (hi0 hy)) (hcl x hx)
  · right
    intro x hx
    have hEc : IsClosed (exteriorRegion_CPE L j hj) :=
      (isOpen_iUnion (isOpen_coreInteriorImage_CPG L j hj)).isClosed_compl
    refine hEc.closure_subset_iff.mpr (fun y hy => ?_) (hcl x hx)
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact (hV hy) (Set.mem_iUnion.mpr ⟨i, coreInteriorImage_subset_range_CPG L j hj i hi⟩)

end GC.LongTime.CuspP1
