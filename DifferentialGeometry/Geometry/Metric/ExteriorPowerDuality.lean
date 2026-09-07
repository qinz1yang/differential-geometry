import DifferentialGeometry.Geometry.Metric.ExteriorPowerBundle
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Bundle.Hom.Regularity

noncomputable section

open scoped Bundle Manifold ContDiff RealInnerProductSpace Topology

namespace exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ E)).finiteDimensional_of_finite

private def evaluationLinearMap (k : ℕ) :
    (⋀[ℝ]^k E) →ₗ[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  (alternatingMapLinearEquiv.toLinearMap.comp
    (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))).flip

private theorem evaluationLinearMap_injective (k : ℕ) :
    Function.Injective (evaluationLinearMap (E := E) k) := by
  intro u v h
  have heq (w : ⋀[ℝ]^k E) : ⟪w, u⟫ = ⟪w, v⟫ := by
    have ht := LinearMap.congr_fun h (musicalEquiv k w)
    change alternatingMapLinearEquiv (musicalEquiv k w).toAlternatingMap u =
      alternatingMapLinearEquiv (musicalEquiv k w).toAlternatingMap v at ht
    simpa only [alternatingMapLinearEquiv_musicalEquiv] using ht
  exact ext_inner_left ℝ heq

def alternatingDualEquiv (k : ℕ) :
    (⋀[ℝ]^k E) ≃L[ℝ] ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  let L := (LinearEquiv.ofInjectiveOfFinrankEq (evaluationLinearMap (E := E) k)
    (evaluationLinearMap_injective (E := E) k) (by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one,
        ContinuousAlternatingMap.finrank_continuousAlternatingMap, exteriorPower.finrank_eq])).trans
      LinearMap.toContinuousLinearMap
  exact L.toContinuousLinearEquiv

theorem alternatingDualEquiv_apply (k : ℕ) (u : ⋀[ℝ]^k E) (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingDualEquiv k u a = alternatingMapLinearEquiv a.toAlternatingMap u := rfl

theorem alternatingDualEquiv_ιMulti_apply (k : ℕ) (u : Fin k → E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) : alternatingDualEquiv k (ιMulti ℝ k u) a = a u :=
  alternatingMapLinearEquiv_apply_ιMulti _ u

theorem alternatingDualEquiv_map_apply
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) (f : E →L[ℝ] F) (u : ⋀[ℝ]^k E) (a : F [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingDualEquiv k (map k f.toLinearMap u) a =
      alternatingDualEquiv k u (a.compContinuousLinearMap f) := by
  have h : (alternatingMapLinearEquiv a.toAlternatingMap).comp (map k f.toLinearMap) =
      alternatingMapLinearEquiv (a.compContinuousLinearMap f).toAlternatingMap := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      map_apply_ιMulti, alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun h u

end exteriorPower
