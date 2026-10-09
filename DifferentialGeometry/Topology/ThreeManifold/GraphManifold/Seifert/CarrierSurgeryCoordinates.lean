import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryPatches
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceInteriorSmooth
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProd

/-!
Actual local coordinates for quotient-surgery patch sources. Interior and signed patches have
Euclidean coordinates, and retained half collars have coordinates in the three-dimensional half
space.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.Seifert

private abbrev SurgeryE1 := EuclideanSpace ℝ (Fin 1)
private abbrev SurgeryE2 := EuclideanSpace ℝ (Fin 2)
private abbrev SurgeryE3 := EuclideanSpace ℝ (Fin 3)

private def surgeryTorusLinear : (SurgeryE1 × SurgeryE1) ≃L[ℝ] SurgeryE2 :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofFinrankEq _ _ (by simp))

private def surgerySignedLinear : ((SurgeryE1 × SurgeryE1) × ℝ) ≃L[ℝ] SurgeryE3 :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofFinrankEq _ _ (by simp))

theorem exists_surgerySignedCoordinates (p : Torus × ℝ) :
    ∃ d : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) SurgeryE3 ∞,
      p ∈ d.source := by
  let a := PartialDiffeomorph.extendedChart (I := signedCollarModel) p
  let d := a.trans surgerySignedLinear.toDiffeomorph.toPartialDiffeomorph
  exact ⟨d, mem_extChartAt_source p, mem_univ _⟩

theorem exists_surgeryTorusCoordinates (t : Torus) :
    ∃ d : PartialDiffeomorph torusModel (𝓡 2) Torus SurgeryE2 ∞, t ∈ d.source := by
  let a := PartialDiffeomorph.extendedChart (I := torusModel) t
  let d := a.trans surgeryTorusLinear.toDiffeomorph.toPartialDiffeomorph
  exact ⟨d, mem_extChartAt_source t, mem_univ _⟩

theorem exists_surgeryInteriorCoordinates (C : CompactCarrier.{u}) {x : C.Carrier}
    (hx : x ∈ C.interior) :
    ∃ d : PartialDiffeomorph C.model (𝓡 3) C.Carrier SurgeryE3 ∞, x ∈ d.source := by
  obtain ⟨d, hd, hsource, hforward, hbackward⟩ := exists_interior_coordinates hx
  exact ⟨d, hd⟩

private def surgeryHalfProductDiffeomorph :
    (SurgeryE2 × EuclideanHalfSpace 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯
      EuclideanHalfSpace 3 := by
  let e := DifferentialGeometry.Manifold.modelLinearHomeomorphDiffeomorph
    ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
  refine { e.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [chartedSpaceSelf_prod]
    exact e.contMDiff
  · rw [chartedSpaceSelf_prod]
    exact e.symm.contMDiff

theorem exists_surgeryHalfCollarCoordinates (p : Torus × EuclideanHalfSpace 1) :
    ∃ d : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (EuclideanHalfSpace 3) ∞, p ∈ d.source := by
  obtain ⟨a, ha⟩ := exists_surgeryTorusCoordinates p.1
  let d := (DifferentialGeometry.Topology.PartialDiffeomorph.prod a
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞).toPartialDiffeomorph).trans
      surgeryHalfProductDiffeomorph.toPartialDiffeomorph
  exact ⟨d, ⟨ha, mem_univ _⟩, mem_univ _⟩

section HalfCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_surgeryHalfCoordinates_of_euclidean
    (d : PartialDiffeomorph I (𝓡 3) M SurgeryE3 ∞) {x : M} (hx : x ∈ d.source) :
    ∃ e : PartialDiffeomorph I (𝓡∂ 3) M (EuclideanHalfSpace 3) ∞, x ∈ e.source := by
  let a := (halfSpaceThreeSplit (d x)).1 - 1
  let e := d.trans (halfSpaceThreeInteriorPartialDiffeomorph a)
  refine ⟨e, hx, ?_⟩
  change d x ∈ (halfSpaceThreeInteriorChart a).source
  rw [halfSpaceThreeInteriorChart_mem_source]
  dsimp [a]
  linarith

end HalfCoordinates

end GC.Seifert
