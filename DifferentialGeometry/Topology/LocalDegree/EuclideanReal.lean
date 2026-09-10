import DifferentialGeometry.Topology.LocalDegree.Euclidean
import DifferentialGeometry.Topology.LocalDegree.Real
import DifferentialGeometry.Topology.LocalDegree.IsometricCoordinate

set_option autoImplicit false
open CategoryTheory Metric Set
noncomputable section
namespace Poincare.LocalDegree
open Poincare.Homology

theorem realIsolatingRadius_iff {f : ℝ → ℝ} {x R : ℝ} :
    RealIsolatingRadius f x R ↔ IsolatingRadius f x R :=
  ⟨fun h => ⟨h.pos, h.continuousOn, h.zero_iff⟩,
    fun h => ⟨h.pos, h.continuousOn, h.zero_iff⟩⟩


theorem realIsolatedZero_iff {f : ℝ → ℝ} {x : ℝ} :
    realIsolatedZero f x ↔ isolatedZero f x :=
  exists_congr fun _ => realIsolatingRadius_iff


def realEuclideanIsometry : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr


theorem linearSphereMap_realEuclideanIsometry_symm :
    linearSphereMap realEuclideanIsometry.symm.toContinuousLinearEquiv =
      euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [linearSphereMap_apply]
  change ‖realEuclideanIsometry.symm v‖⁻¹ • realEuclideanIsometry.symm v =
    realEuclideanIsometry.symm v
  rw [realEuclideanIsometry.symm.norm_map, norm_eq_of_mem_sphere v]
  simp

theorem euclideanSphereDegree_zero_eq {f : C(EuclideanSphere 0, EuclideanSphere 0)}
    {g : C(ZeroSphere, ZeroSphere)}
    (he : TopCat.ofHom f ≫ TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun =
      TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun ≫ TopCat.ofHom g) :
    euclideanSphereDegree f = zeroSphereDegree g := by
  have h := congrArg (fun m => reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) m 0) he
  simp only [reducedSingularHomologyMap_comp] at h
  change euclideanZeroSphereReducedHomologyEquiv _ = _
  rw [euclideanZeroSphereReducedHomologyEquiv_apply]
  change zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
    ((reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) 0 ≫
     reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0)
        (euclideanSphereTopGenerator 0))) = _
  rw [h]
  change zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom g) 0 _)) = _
  rw [realZeroSphereReducedHomologyEquiv_map]
  exact congrArg (fun c => zeroSphereReducedEquiv (zeroSphereReducedMap g c))
    euclideanSphereTopGenerator_zero_comparison

theorem RealIsolatingRadius.euclidean {f : ℝ → ℝ} {x R : ℝ}
    (h : RealIsolatingRadius f x R) :
    IsolatingRadius (fun v => realEuclideanIsometry (f (realEuclideanIsometry.symm v)))
      (realEuclideanIsometry x) R := by
  have h' : IsolatingRadius f
      (realEuclideanIsometry.symm (realEuclideanIsometry x)) R := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using realIsolatingRadius_iff.mp h
  exact h'.isometry_conjugate realEuclideanIsometry.symm

theorem euclideanLocalDegree_eq_realLocalDegree {f : ℝ → ℝ} {x R : ℝ}
    (hR : RealIsolatingRadius f x R) :
    euclideanLocalDegree (fun v => realEuclideanIsometry (f (realEuclideanIsometry.symm v)))
      (realEuclideanIsometry x) ⟨R, hR.euclidean⟩ = realLocalDegree f x ⟨R, hR⟩ := by
  let r : Ioc (0 : ℝ) R := ⟨R, hR.pos, le_rfl⟩
  erw [euclideanLocalDegree_eq_sphereDegree _ hR.euclidean r,
    realLocalDegree_eq_sphereDegree _ hR r]
  apply euclideanSphereDegree_zero_eq
  have h' : IsolatingRadius f
      (realEuclideanIsometry.symm (realEuclideanIsometry x)) R := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using realIsolatingRadius_iff.mp hR
  have hh := sphereMap_isometry_conjugate realEuclideanIsometry.symm h' r
  rw [linearSphereMap_realEuclideanIsometry_symm] at hh
  apply ConcreteCategory.hom_ext
  intro v
  simpa only [LinearIsometryEquiv.symm_apply_apply] using! ContinuousMap.congr_fun hh v

theorem euclideanLocalDegree_real_eq_endpoints {f : ℝ → ℝ} {x R : ℝ}
    (hR : RealIsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    euclideanLocalDegree (fun v => realEuclideanIsometry (f (realEuclideanIsometry.symm v)))
      (realEuclideanIsometry x) ⟨R, hR.euclidean⟩ =
        (if 0 < f (x + (r : ℝ)) then 1 else 0) -
        (if 0 < f (x - (r : ℝ)) then 1 else 0) := by
  rw [euclideanLocalDegree_eq_realLocalDegree hR]
  exact realLocalDegree_eq_endpoints ⟨R, hR⟩ hR r

end Poincare.LocalDegree
