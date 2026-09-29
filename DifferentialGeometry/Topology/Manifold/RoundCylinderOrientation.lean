import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def positiveCylinderReparametrization : S2 × ℝ → S2 × ℝ := Prod.map id Real.exp

theorem positiveCylinderReparametrization_contMDiff :
    ContMDiff IC IC ∞ positiveCylinderReparametrization :=
  contMDiff_id.prodMap Real.contDiff_exp.contMDiff

private theorem exp_mfderiv_bijective (t : ℝ) :
    Bijective (mfderiv 𝓘(ℝ) 𝓘(ℝ) Real.exp t) := by
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.exp t) (Real.exp_ne_zero t))
  have h : mfderiv 𝓘(ℝ) 𝓘(ℝ) Real.exp t = (A : ℝ →L[ℝ] ℝ) := by
    rw [mfderiv_eq_fderiv, (Real.hasDerivAt_exp t).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change ℝ at v
    change v * Real.exp t = Real.exp t * v
    exact mul_comm _ _
  rw [h]
  exact A.bijective

theorem positiveCylinderReparametrization_mfderiv_bijective (q : S2 × ℝ) :
    Bijective (mfderiv IC IC positiveCylinderReparametrization q) := by
  have hexp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.exp := Real.contDiff_exp.contMDiff
  change Bijective (mfderiv IC IC (Prod.map (id : S2 → S2) Real.exp) q)
  rw [mfderiv_prodMap mdifferentiableAt_id (hexp.mdifferentiableAt (by simp)), mfderiv_id]
  exact Function.bijective_id.prodMap (exp_mfderiv_bijective q.2)

def exponentialPolarMap (q : S2 × ℝ) : E3 := euclideanPolarMap (positiveCylinderReparametrization q)

theorem exponentialPolarMap_contMDiff : ContMDiff IC (𝓡 3) ∞ exponentialPolarMap :=
  (euclideanPolarMap_smooth (n := 2)).comp positiveCylinderReparametrization_contMDiff

theorem exponentialPolarMap_mfderiv_bijective (q : S2 × ℝ) :
    Bijective (mfderiv IC (𝓡 3) exponentialPolarMap q) := by
  have hP : IsLocalDiffeomorphAt IC (𝓡 3) ∞ euclideanPolarMap
      (positiveCylinderReparametrization q) :=
    PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
      (euclideanPolarDiffeomorph (E := E3) (n := 2)) (Real.exp_pos q.2)
  have h := mfderiv_comp q (hP.contMDiffAt.mdifferentiableAt (by simp))
    (positiveCylinderReparametrization_contMDiff.mdifferentiableAt (by simp))
  change Bijective (mfderiv IC (𝓡 3) (euclideanPolarMap ∘ positiveCylinderReparametrization) q)
  rw [h]
  exact (hP.mfderivToContinuousLinearEquiv (by simp)).bijective.comp (positiveCylinderReparametrization_mfderiv_bijective q)

def roundCylinderSmoothOrientation (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    SmoothOrientation IC (S2 × ℝ) :=
  pullbackSmoothOrientation IC (𝓡 3) exponentialPolarMap exponentialPolarMap_contMDiff
    exponentialPolarMap_mfderiv_bijective (euclideanSmoothOrientation E3 o)

theorem roundCylinderSmoothOrientation_pushforward
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (q : S2 × ℝ) :
    tangentOrientationEquiv (differentialEquivOfBijective IC (𝓡 3) exponentialPolarMap
      exponentialPolarMap_mfderiv_bijective q).toLinearEquiv ((roundCylinderSmoothOrientation o).val q) = o :=
  tangentOrientationEquiv_symm
    (differentialEquivOfBijective IC (𝓡 3) exponentialPolarMap
      exponentialPolarMap_mfderiv_bijective q).symm.toLinearEquiv o
end DifferentialGeometry.Topology.Manifold
