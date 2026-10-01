import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem surjective_of_norm_comp_sub_id_lt_one (A : E →L[𝕜] F) (R : F →L[𝕜] E)
    (h : ‖A.comp R - ContinuousLinearMap.id 𝕜 F‖ < 1) : Function.Surjective A := by
  have hu : IsUnit (A.comp R) := by
    have hn : ‖(1 : F →L[𝕜] F) - A.comp R‖ < 1 := by
      rwa [norm_sub_rev]
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  exact Function.Surjective.of_comp (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2

theorem surjective_of_norm_sub_mul_lt_one (A B : E →L[𝕜] F) (R : F →L[𝕜] E)
    (hR : B.comp R = ContinuousLinearMap.id 𝕜 F)
    (h : ‖A - B‖ * ‖R‖ < 1) : Function.Surjective A := by
  apply A.surjective_of_norm_comp_sub_id_lt_one R
  rw [← hR, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt h

end ContinuousLinearMap
