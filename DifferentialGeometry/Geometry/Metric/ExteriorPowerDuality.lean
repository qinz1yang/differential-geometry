import DifferentialGeometry.Geometry.Metric.ExteriorPowerBundle
import DifferentialGeometry.Geometry.Metric.BundleAlternating
import DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import DifferentialGeometry.Tensor.Alternating.Bundle.Defs
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

namespace Bundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem alternatingRiemannianMetric_musicalEquiv_left (k : ℕ) (x : B)
    (u : ⋀[ℝ]^k (V x)) (a : V x [⋀^Fin k]→L[ℝ] ℝ) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    (alternatingRiemannianMetric (F := F) V k).inner x (exteriorPower.musicalEquiv k u) a =
      (k.factorial : ℝ) * exteriorPower.alternatingDualEquiv k u a := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
    ContinuousLinearEquiv.symm_apply_apply]
  congr 1
  rw [real_inner_comm, exteriorPower.alternatingDualEquiv_apply]
  have h := exteriorPower.alternatingMapLinearEquiv_musicalEquiv k
    ((exteriorPower.musicalEquiv k).symm a) u
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm


theorem hilbertSchmidtInner_musicalEquiv_conjugate (k : ℕ) (x : B) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI : RiemannianBundle
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) :=
      ⟨alternatingRiemannianMetric (F := F) V k⟩
    letI alternatingNorm : ∀ y, NormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
    letI : ∀ y, SeminormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => (alternatingNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y [⋀^Fin k]→L[ℝ] ℝ) :=
      fun y => Bundle.instInnerProductSpaceReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
    let e := exteriorPower.musicalEquiv (E := V x) k
    ∀ A C : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x),
      @ContinuousLinearMap.hilbertSchmidtInner _ _ (alternatingNorm x) _ _ (alternatingNorm x) _
          (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap))
          (e.toContinuousLinearMap.comp (C.comp e.symm.toContinuousLinearMap)) =
        ContinuousLinearMap.hilbertSchmidtInner A C := by
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let : RiemannianBundle
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) :=
    ⟨alternatingRiemannianMetric (F := F) V k⟩
  let alternatingNorm : ∀ y, NormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
  let : ∀ y, SeminormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => (alternatingNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instInnerProductSpaceReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) y
  let : FiniteDimensional ℝ (V x [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ (V x))).finiteDimensional_of_finite
  dsimp only
  intro A C
  have hinner (u v : ⋀[ℝ]^k (V x)) :
      @inner ℝ _ (by infer_instance : Inner ℝ (V x [⋀^Fin k]→L[ℝ] ℝ))
        (exteriorPower.musicalEquiv k u) (exteriorPower.musicalEquiv k v) =
        (k.factorial : ℝ) * inner ℝ u v := by
    change (alternatingRiemannianMetric (F := F) V k).inner x
      (exteriorPower.musicalEquiv k u) (exteriorPower.musicalEquiv k v) = _
    rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact @ContinuousLinearMap.hilbertSchmidtInner_conjugate_of_inner_eq_mul
    (⋀[ℝ]^k (V x)) (V x [⋀^Fin k]→L[ℝ] ℝ) _ _ _ (alternatingNorm x) _ _
    (exteriorPower.musicalEquiv k) (k.factorial : ℝ) (Nat.cast_pos.mpr k.factorial_pos)
    hinner A C

end Bundle
