import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

def evalCurriedFourLastTwo
    (F : E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (u w : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] E →L[𝕜] 𝕜) 𝕜
    ((ContinuousLinearMap.apply 𝕜 𝕜 w).comp
      (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] 𝕜) u))).comp F

def curriedBilinearMul (A B : E →L[𝕜] E →L[𝕜] 𝕜) :
    E →L[𝕜] E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜 :=
  precompL E
    (precompR E
      (precompL E (precompR E (mul 𝕜 𝕜)))) A B

@[simp]
theorem curriedBilinearMul_apply
    (A B : E →L[𝕜] E →L[𝕜] 𝕜) (c v c' v' : E) :
    curriedBilinearMul A B c v c' v' = A c c' * B v v' := by
  rfl

def evalCurriedThreeLast
    (f : E →L[𝕜] E →L[𝕜] E →L[𝕜] 𝕜) (e : E) :
    E →L[𝕜] E →L[𝕜] 𝕜 :=
  (compL 𝕜 E (E →L[𝕜] 𝕜) 𝕜 (apply 𝕜 𝕜 e)).comp f

end ContinuousLinearMap

end
