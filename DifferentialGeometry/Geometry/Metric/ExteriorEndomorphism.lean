import DifferentialGeometry.Geometry.Metric.ExteriorPowerSmooth
import DifferentialGeometry.Tensor.Alternating.Block

set_option autoImplicit false

noncomputable section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def ιMultiContinuous (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (⋀[ℝ]^k E) :=
  { (ιMulti ℝ k).toMultilinearMap with cont := (contDiff_ιMulti k 0).continuous }

@[simp] theorem ιMultiContinuous_apply (k : ℕ) (v : Fin k → E) :
    ιMultiContinuous k v = ιMulti ℝ k v := rfl

def endomorphismTensor (k : ℕ) (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ :=
  (((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).comp
      ((musicalEquiv k).toContinuousLinearMap.comp R)).compContinuousMultilinearMap
        (ιMultiContinuous k)).uncurrySum.domDomCongr finSumFinEquiv

theorem endomorphismTensor_apply (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) (v : Fin (k + k) → E) :
    endomorphismTensor k R v =
      ⟪R (ιMulti ℝ k (v ∘ Fin.castAdd k)), ιMulti ℝ k (v ∘ Fin.natAdd k)⟫ := by
  simp only [endomorphismTensor, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply]
  exact musicalEquiv_apply k _ _

theorem endomorphismTensor_apply_append (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) (v w : Fin k → E) :
    endomorphismTensor k R (Fin.append v w) = ⟪R (ιMulti ℝ k v), ιMulti ℝ k w⟫ := by
  rw [endomorphismTensor_apply]
  simp only [Function.comp_def, Fin.append_left, Fin.append_right]

def endomorphismTensorLinear (k : ℕ) :
    ((⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ where
  toFun := endomorphismTensor k
  map_add' R S := by
    ext v
    simp only [endomorphismTensor_apply, add_apply, inner_add_left]
  map_smul' c R := by
    ext v
    simp only [endomorphismTensor_apply, smul_apply,
      real_inner_smul_left, smul_eq_mul,
      RingHom.id_apply]

theorem endomorphismTensor_injective (k : ℕ) :
    Function.Injective (endomorphismTensor (E := E) k) := by
  intro R S h
  apply ContinuousLinearMap.coe_injective
  apply linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  have hPair : innerₗ (⋀[ℝ]^k E) (R (ιMulti ℝ k v)) =
      innerₗ (⋀[ℝ]^k E) (S (ιMulti ℝ k v)) := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro z
    have hh := congrArg (fun T => T (Fin.append v z)) h
    simpa only [endomorphismTensor_apply_append, LinearMap.compAlternatingMap_apply,
      innerₗ_apply_apply] using hh
  exact LinearMap.congr_fun hPair w

theorem isSymmetric_iff_endomorphismTensor (k : ℕ)
    (R : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E) :
    R.toLinearMap.IsSymmetric ↔ ∀ (v w : Fin k → E),
      endomorphismTensor k R (Fin.append v w) =
        endomorphismTensor k R (Fin.append w v) := by
  constructor
  · intro h v w
    simpa only [endomorphismTensor_apply_append, ContinuousLinearMap.coe_coe,
      real_inner_comm] using h (ιMulti ℝ k v) (ιMulti ℝ k w)
  · intro h u z
    have heq : (innerₗ (⋀[ℝ]^k E)).comp R.toLinearMap =
        (innerₗ (⋀[ℝ]^k E)).flip.compl₂ R.toLinearMap := by
      apply linearMap_ext
      apply AlternatingMap.ext
      intro v
      apply linearMap_ext
      apply AlternatingMap.ext
      intro w
      simpa only [endomorphismTensor_apply_append, LinearMap.compAlternatingMap_apply,
        LinearMap.coe_comp, Function.comp_apply, innerₗ_apply_apply,
        LinearMap.flip_apply, LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe,
        real_inner_comm] using h v w
    simpa only [LinearMap.coe_comp, Function.comp_apply, innerₗ_apply_apply,
      LinearMap.flip_apply, LinearMap.compl₂_apply, real_inner_comm] using
      LinearMap.congr_fun (LinearMap.congr_fun heq u) z

end exteriorPower

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def alternatingEndomorphism (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) :
    (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E :=
  (alternatingMapLinearEquiv
    (((musicalEquiv k).symm.toContinuousLinearMap).compContinuousAlternatingMap A).toAlternatingMap
    ).toContinuousLinearMap

theorem alternatingEndomorphism_apply_ιMulti (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    alternatingEndomorphism k A (ιMulti ℝ k v) = (musicalEquiv k).symm (A v) :=
  alternatingMapLinearEquiv_apply_ιMulti _ _

theorem endomorphismTensor_alternatingEndomorphism_apply_append (k : ℕ)
    (A : E [⋀^Fin k]→L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) (v w : Fin k → E) :
    endomorphismTensor k (alternatingEndomorphism k A) (Fin.append v w) = A v w := by
  rw [endomorphismTensor_apply_append, alternatingEndomorphism_apply_ιMulti,
    inner_musicalEquiv_symm_ιMulti]

def multilinearEndomorphism (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0) : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k E :=
  alternatingEndomorphism k (ContinuousMultilinearMap.toBlockAlternating k k T hleft)

theorem endomorphismTensor_multilinearEndomorphism (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0)
    (hright : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → w i = w j →
      T (Fin.append v w) = 0) :
    endomorphismTensor k (multilinearEndomorphism k T hleft) = T := by
  ext z
  have hz : Fin.append (z ∘ Fin.castAdd k) (z ∘ Fin.natAdd k) = z := by
    funext i
    exact Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) i
  rw [← hz]
  exact (endomorphismTensor_alternatingEndomorphism_apply_append k
    (ContinuousMultilinearMap.toBlockAlternating k k T hleft) _ _).trans
      (ContinuousMultilinearMap.toBlockAlternating_apply k k T hleft hright _ _)

theorem multilinearEndomorphism_isSymmetric (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => E) ℝ)
    (hleft : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → v i = v j →
      T (Fin.append v w) = 0)
    (hright : ∀ (v w : Fin k → E) (i j : Fin k), i ≠ j → w i = w j →
      T (Fin.append v w) = 0)
    (hpair : ∀ v w : Fin k → E, T (Fin.append v w) = T (Fin.append w v)) :
    (multilinearEndomorphism k T hleft).toLinearMap.IsSymmetric := by
  rw [isSymmetric_iff_endomorphismTensor,
    endomorphismTensor_multilinearEndomorphism k T hleft hright]
  exact hpair

end exteriorPower
