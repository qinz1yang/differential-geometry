import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedBaseBundle

/-!
# Consumers of FC42 packets T1a–T1b: the rounded base surfaces and the total space over them

* `CircleRegion.exists_roundedBase_surfaces` (consumer of T1a): the rounded base of a circle region
  is a finite disjoint union of compact connected surfaces with boundary, smoothly and injectively
  included in the base, with boundary the level `{rounding = 0}`;
* `CircleRegion.isCompact_proj_preimage_range_roundedBaseIncl`,
  `CircleRegion.isConnected_proj_preimage_range_roundedBaseIncl` (consumers of the compact and the
  connected preimage lemmas): the part of the circle region over one rounded base component is
  compact and connected — the topological input of the rounded pieces of packet T2;
* `CircleRegion.isOpen_iff_isOpen_proj_preimage` (consumer of the open surjection): the base carries
  the quotient topology of the domain;
* `CircleRegion.metrizableSpace_base` (consumer of the second countability): the base is metrizable.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- **The rounded base as finitely many compact surfaces.** -/
theorem exists_roundedBase_surfaces :
    ∃ (m : ℕ) (B : Fin m → CompactSurface.{u}) (ι : ∀ j, (B j).Carrier → R.Base),
      (∀ j, (B j).kind = .withBoundary) ∧
      (∀ j, ContMDiff (SurfaceModel.model (B j).kind) (𝓡 2) ∞ (ι j)) ∧
      (∀ j, Injective (ι j)) ∧ (⋃ j, range (ι j)) = R.roundedBase ∧
      Pairwise (fun j j' => Disjoint (range (ι j)) (range (ι j'))) ∧
      ∀ j b, (SurfaceModel.model (B j).kind).IsBoundaryPoint b ↔ R.rounding (ι j b) = 0 := by
  let e := Finite.equivFin (ConnectedComponents R.roundedBase)
  refine ⟨Nat.card (ConnectedComponents R.roundedBase), fun k => R.roundedBaseSurface (e.symm k),
    fun k => R.roundedBaseIncl (e.symm k), fun k => R.roundedBaseSurface_kind _,
    fun k => R.contMDiff_roundedBaseIncl _, fun k => R.roundedBaseIncl_injective _, ?_, ?_,
    fun k b => roundedBaseSurface_isBoundaryPoint_iff⟩
  · exact (e.symm.surjective.iUnion_comp fun j => range (R.roundedBaseIncl j)).trans
      R.iUnion_range_roundedBaseIncl
  · intro k k' hkk'
    exact R.pairwise_disjoint_range_roundedBaseIncl (e.symm.injective.ne hkk')

theorem isCompact_range_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    IsCompact (range (R.roundedBaseIncl j)) := by
  rw [R.range_roundedBaseIncl]
  exact (R.isClosed_roundedBaseComponent j).isCompact.image continuous_subtype_val

theorem isConnected_range_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    IsConnected (range (R.roundedBaseIncl j)) := by
  rw [R.range_roundedBaseIncl]
  exact (R.isConnected_roundedBaseComponent j).image _ continuous_subtype_val.continuousOn

/-- The circle region over one rounded base component is compact. -/
theorem isCompact_proj_preimage_range_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    IsCompact (R.proj ⁻¹' range (R.roundedBaseIncl j)) :=
  R.isCompact_proj_preimage (R.isCompact_range_roundedBaseIncl j)

/-- The circle region over one rounded base component is connected. -/
theorem isConnected_proj_preimage_range_roundedBaseIncl (j : ConnectedComponents R.roundedBase) :
    IsConnected (R.proj ⁻¹' range (R.roundedBaseIncl j)) :=
  R.isConnected_proj_preimage (R.isCompact_range_roundedBaseIncl j).isClosed
    (R.isConnected_range_roundedBaseIncl j)

variable {R} in
/-- The base carries the quotient topology of the projection. -/
theorem isOpen_iff_isOpen_proj_preimage {U : Set R.Base} :
    IsOpen U ↔ IsOpen (R.proj ⁻¹' U) :=
  (R.isOpenQuotientMap_proj.isQuotientMap.isOpen_preimage).symm

/-- The base of a circle region is metrizable. -/
theorem metrizableSpace_base : TopologicalSpace.MetrizableSpace R.Base := by
  have := R.secondCountableTopology_base
  have : LocallyCompactSpace R.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) R.Base
  exact Manifold.metrizableSpace (𝓡 2) R.Base

end CircleRegion

end GC.GraphManifold.Assembly
