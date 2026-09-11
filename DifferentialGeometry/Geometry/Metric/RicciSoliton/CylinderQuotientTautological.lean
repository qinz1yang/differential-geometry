import DifferentialGeometry.Bundle.ProjectiveSpace.Tautological
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Topology.ProjectiveSpace.Manifold

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open Filter Topology

namespace DifferentialGeometry.Geometry

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

private def cylinderDiagonalToTautological :
    CylinderDiagonalQuotient → RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) :=
  Quotient.lift realProjectiveTautologicalQuotientMap (by
    intro x y hxy
    have hq : cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y := Quotient.sound hxy
    apply realProjectiveTautologicalQuotientMap_eq_iff.mpr
    exact cylinderDiagonalQuotientMap_eq_iff.mp hq)

private theorem cylinderDiagonalToTautological_bijective :
    Function.Bijective cylinderDiagonalToTautological := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        intro h
        apply cylinderDiagonalQuotientMap_eq_iff.mpr
        exact realProjectiveTautologicalQuotientMap_eq_iff.mp h
  · intro z
    obtain ⟨x, hx⟩ := realProjectiveTautologicalQuotientMap_surjective z
    exact ⟨cylinderDiagonalQuotientMap x, hx⟩

private def cylinderDiagonalTautologicalEquiv :
    CylinderDiagonalQuotient ≃ RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) :=
  Equiv.ofBijective cylinderDiagonalToTautological cylinderDiagonalToTautological_bijective

private theorem cylinderDiagonalToTautological_continuous : Continuous cylinderDiagonalToTautological := by
  exact continuous_quot_lift _ realProjectiveTautologicalQuotientMap_continuous

private theorem cylinderDiagonalTautologicalEquiv_symm_continuous :
    Continuous cylinderDiagonalTautologicalEquiv.symm := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨y, hy⟩ := realProjectiveSpaceQuotientMap_surjective z.1.1
  change realProjectivePlaneQuotientMap y = z.1.1 at hy
  let hlocal := realProjectiveSpaceQuotientMap_isLocalDiffeomorph
    (E := EuclideanSpace Real (Fin 3)) (n := 2) y
  let s (p : RealProjectivePlane) := hlocal.localInverse p
  have hs : ContinuousAt s z.1.1 := by
    have h := hlocal.localInverse_contMDiffAt.continuousAt
    change ContinuousAt s (realProjectivePlaneQuotientMap y) at h
    rw [hy] at h
    exact h
  have hbase : ContinuousAt (fun z : RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) => z.1.1) z :=
    continuous_fst.continuousAt.comp continuous_subtype_val.continuousAt
  have hsection : ContinuousAt (fun z : RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) =>
      s z.1.1) z := hs.comp (f := fun z : RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) => z.1.1) hbase
  have hvec : ContinuousAt (fun z : RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) => z.1.2) z :=
    continuous_snd.continuousAt.comp continuous_subtype_val.continuousAt
  have hinner : ContinuousAt (fun w : RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) =>
      inner Real (s w.1.1 : EuclideanSpace Real (Fin 3)) w.1.2) z :=
    (continuous_subtype_val.continuousAt.comp hsection).inner hvec
  have hcoords := hsection.prodMk hinner
  have hc := cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous.continuousAt.comp hcoords
  apply hc.congr_of_eventuallyEq
  have hright := hlocal.localInverse_eventuallyEq_right
  change (fun p => realProjectivePlaneQuotientMap (s p)) =ᶠ[𝓝 (realProjectivePlaneQuotientMap y)] id at hright
  rw [hy] at hright
  have hevent := hright.comp_tendsto hbase
  filter_upwards [hevent] with w hw
  change realProjectivePlaneQuotientMap (s w.1.1) = w.1.1 at hw
  apply cylinderDiagonalTautologicalEquiv.injective
  rw [Equiv.apply_symm_apply]
  change w = realProjectiveTautologicalQuotientMap
    (s w.1.1, inner Real (s w.1.1 : EuclideanSpace Real (Fin 3)) w.1.2)
  apply Subtype.ext
  apply Prod.ext hw.symm
  exact (realProjectiveTautologicalLine_inner_smul (s w.1.1) w.1.2 (by
    change w.1.2 ∈ realProjectiveTautologicalLine (realProjectivePlaneQuotientMap (s w.1.1))
    rw [hw]
    exact w.2)).symm

noncomputable def cylinderDiagonalQuotientTautologicalHomeomorph :
    CylinderDiagonalQuotient ≃ₜ RealProjectiveTautologicalSpace (EuclideanSpace Real (Fin 3)) where
  toEquiv := cylinderDiagonalTautologicalEquiv
  continuous_toFun := cylinderDiagonalToTautological_continuous
  continuous_invFun := cylinderDiagonalTautologicalEquiv_symm_continuous

@[simp] theorem cylinderDiagonalQuotientTautologicalHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientTautologicalHomeomorph (cylinderDiagonalQuotientMap x) =
      realProjectiveTautologicalQuotientMap x := rfl

noncomputable def cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph :
    CylinderDiagonalQuotient ≃ₜ
      Bundle.TotalSpace Real (RealProjectiveTautologicalFiber (A := EuclideanSpace Real (Fin 3))) :=
  cylinderDiagonalQuotientTautologicalHomeomorph.trans realProjectiveTautologicalTotalSpaceHomeomorph.symm

@[simp] theorem cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph (cylinderDiagonalQuotientMap x) =
      ⟨realProjectivePlaneQuotientMap x.1,
        ⟨x.2 • (x.1 : EuclideanSpace Real (Fin 3)), Submodule.mem_span_singleton.mpr ⟨x.2, rfl⟩⟩⟩ := rfl

end DifferentialGeometry.Geometry
