import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace OrthonormalBasis

variable {𝕜 U V : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {ι : Type*} [Fintype ι]

def continuousLinearMapEquiv (b : OrthonormalBasis ι 𝕜 U) :
    (U →L[𝕜] V) ≃L[𝕜] PiLp 2 (fun _ : ι => V) := by
  classical
  exact ((b.toBasis.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 V)).trans
    (ContinuousLinearEquiv.piRing ι)).trans
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => V)).symm

@[simp] theorem continuousLinearMapEquiv_apply (b : OrthonormalBasis ι 𝕜 U)
    (A : U →L[𝕜] V) (i : ι) : b.continuousLinearMapEquiv A i = A (b i) := by
  classical
  change A (b.toBasis.equivFunL.symm (Pi.single i 1)) = A (b i)
  congr 1

end OrthonormalBasis

namespace ContinuousLinearMap

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def hilbertSchmidtInner (A C : U →L[ℝ] V) : ℝ :=
  ∑ i, inner ℝ (A (stdOrthonormalBasis ℝ U i)) (C (stdOrthonormalBasis ℝ U i))

theorem hilbertSchmidtInner_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ U) (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C = ∑ i, inner ℝ (A (b i)) (C (b i)) := by
  let L : U →ₗ[ℝ] U →ₗ[ℝ] ℝ :=
    LinearMap.compl₂ ((innerₗ V).comp A.toLinearMap) C.toLinearMap
  have h := congrArg (TensorProduct.lift L)
    (InnerProductSpace.canonicalCovariantTensor_eq_sum U b)
  simpa [InnerProductSpace.canonicalCovariantTensor, hilbertSchmidtInner, L] using h

theorem hilbertSchmidtInner_eq_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ U)
    (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C =
      inner ℝ (b.continuousLinearMapEquiv A) (b.continuousLinearMapEquiv C) := by
  rw [hilbertSchmidtInner_eq_sum b, PiLp.inner_apply]
  simp only [OrthonormalBasis.continuousLinearMapEquiv_apply]

theorem hilbertSchmidtInner_comm (A C : U →L[ℝ] V) :
    hilbertSchmidtInner A C = hilbertSchmidtInner C A := by
  simp only [hilbertSchmidtInner, real_inner_comm]

theorem hilbertSchmidtInner_self_pos {A : U →L[ℝ] V} (hA : A ≠ 0) :
    0 < hilbertSchmidtInner A A := by
  rw [hilbertSchmidtInner_eq_inner (stdOrthonormalBasis ℝ U)]
  apply real_inner_self_pos.mpr
  exact (stdOrthonormalBasis ℝ U).continuousLinearMapEquiv.injective.ne
    (by simpa using hA)

def hilbertSchmidtInnerSL : (U →L[ℝ] V) →L[ℝ] (U →L[ℝ] V) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (E := V)).bilinearComp
    (apply ℝ V (stdOrthonormalBasis ℝ U i))
    (apply ℝ V (stdOrthonormalBasis ℝ U i))

@[simp] theorem hilbertSchmidtInnerSL_apply (A C : U →L[ℝ] V) :
    hilbertSchmidtInnerSL A C = hilbertSchmidtInner A C := by
  simp [hilbertSchmidtInnerSL, hilbertSchmidtInner]

theorem continuous_hilbertSchmidtInner :
    Continuous (fun p : (U →L[ℝ] V) × (U →L[ℝ] V) => hilbertSchmidtInner p.1 p.2) := by
  exact (hilbertSchmidtInnerSL (U := U) (V := V)).continuous₂.congr
    (fun p => hilbertSchmidtInnerSL_apply p.1 p.2)

variable {U' V' : Type*} [NormedAddCommGroup U'] [InnerProductSpace ℝ U']
  [FiniteDimensional ℝ U'] [NormedAddCommGroup V'] [InnerProductSpace ℝ V']

theorem hilbertSchmidtInner_congr (eU : U ≃ₗᵢ[ℝ] U') (eV : V →ₗᵢ[ℝ] V')
    (A C : U →L[ℝ] V) :
    hilbertSchmidtInner
        (eV.toContinuousLinearMap.comp (A.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap))
        (eV.toContinuousLinearMap.comp (C.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      hilbertSchmidtInner A C := by
  rw [hilbertSchmidtInner_eq_sum ((stdOrthonormalBasis ℝ U).map eU)]
  simp only [OrthonormalBasis.map_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometry.inner_map_map, hilbertSchmidtInner]

end ContinuousLinearMap


namespace ContinuousLinearMap

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hilbertSchmidtInner_comp_right (A C : U →L[ℝ] V) (K : U →L[ℝ] U) :
    hilbertSchmidtInner (A.comp K) C = hilbertSchmidtInner A (C.comp K.adjoint) := by
  classical
  let b := stdOrthonormalBasis ℝ U
  rw [hilbertSchmidtInner_eq_sum b, hilbertSchmidtInner_eq_sum b]
  simp only [comp_apply]
  have hleft (i) : inner ℝ (A (K (b i))) (C (b i)) =
      ∑ j, inner ℝ (b j) (K (b i)) * inner ℝ (A (b j)) (C (b i)) := by
    nth_rw 1 [← b.sum_repr' (K (b i))]
    rw [map_sum, sum_inner]
    simp only [map_smul, inner_smul_left, conj_trivial]
  have hright (i) : inner ℝ (A (b i)) (C (K.adjoint (b i))) =
      ∑ j, inner ℝ (b j) (K.adjoint (b i)) * inner ℝ (A (b i)) (C (b j)) := by
    nth_rw 1 [← b.sum_repr' (K.adjoint (b i))]
    rw [map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [K.adjoint_inner_right]
  rw [real_inner_comm (K (b j)) (b i)]


theorem hilbertSchmidtInner_comp_add_eq_zero (A C : U →L[ℝ] V) (K : U →L[ℝ] U)
    (hK : K.adjoint = -K) :
    hilbertSchmidtInner (A.comp K) C + hilbertSchmidtInner A (C.comp K) = 0 := by
  rw [hilbertSchmidtInner_comp_right, hK, comp_neg]
  rw [← hilbertSchmidtInnerSL_apply, ← hilbertSchmidtInnerSL_apply, map_neg]
  exact neg_add_cancel _

end ContinuousLinearMap
