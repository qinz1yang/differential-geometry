import DifferentialGeometry.Tensor.Alternating.Composition
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ContinuousMultilinearMap

noncomputable section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem currySum_domDomCongr_finSumFinEquiv_apply (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (v : Fin p → E) (w : Fin q → E) :
    (T.domDomCongr finSumFinEquiv.symm).currySum v w = T (Fin.append v w) := by
  simp only [currySum_apply, domDomCongr_apply]
  apply congrArg T
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
  · rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]

variable [CharZero 𝕜]

def toBlockAlternating (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (hleft : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin p),
      i ≠ j → v i = v j → T (Fin.append v w) = 0) :
    E [⋀^Fin p]→L[𝕜] E [⋀^Fin q]→L[𝕜] F := by
  let C := (T.domDomCongr finSumFinEquiv.symm).currySum
  let B := alternatizationCLM.compContinuousMultilinearMap C
  exact
    { B with
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        change alternatizationCLM (C v) = 0
        have hz : C v = 0 := by
          ext w
          rw [show C v w = T (Fin.append v w) from
            currySum_domDomCongr_finSumFinEquiv_apply p q T v w]
          change T (Fin.append v w) = 0
          exact hleft v w i j hij hv
        rw [hz, _root_.map_zero] }

theorem toBlockAlternating_apply (p q : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (p + q) => E) F)
    (hleft : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin p),
      i ≠ j → v i = v j → T (Fin.append v w) = 0)
    (hright : ∀ (v : Fin p → E) (w : Fin q → E) (i j : Fin q),
      i ≠ j → w i = w j → T (Fin.append v w) = 0)
    (v : Fin p → E) (w : Fin q → E) :
    toBlockAlternating p q T hleft v w = T (Fin.append v w) := by
  let C := (T.domDomCongr finSumFinEquiv.symm).currySum
  let A : E [⋀^Fin q]→L[𝕜] F :=
    { C v with
      map_eq_zero_of_eq' := by
        intro u i j hu hij
        change C v u = 0
        rw [currySum_domDomCongr_finSumFinEquiv_apply]
        exact hright v u i j hij hu }
  change alternatizationCLM A.toContinuousMultilinearMap w = _
  rw [alternatizationCLM_apply_toContinuousMultilinearMap]
  exact currySum_domDomCongr_finSumFinEquiv_apply p q T v w

end

end ContinuousMultilinearMap
