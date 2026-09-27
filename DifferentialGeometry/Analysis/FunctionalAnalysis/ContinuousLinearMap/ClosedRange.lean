import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Prod

namespace ContinuousLinearMap

variable {𝕜 X Y Z W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

private theorem isClosed_range_prod_of_lifting
    (J : X →L[𝕜] Y) (QH : X →L[𝕜] Z)
    (QL : Y →L[𝕜] W) (K : Z →L[𝕜] W)
    (hcomm : QL.comp J = K.comp QH)
    (hlift : ∀ y z, QL y = K z → ∃ x, J x = y ∧ QH x = z) :
    IsClosed (Set.range (J.prod QH)) := by
  have hrange : Set.range (J.prod QH) = {p : Y × Z | QL p.1 = K p.2} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact DFunLike.congr_fun hcomm x
    · intro hp
      obtain ⟨x, hJx, hQx⟩ := hlift p.1 p.2 hp
      exact ⟨x, Prod.ext hJx hQx⟩
  rw [hrange]
  exact isClosed_eq (QL.continuous.comp continuous_fst) (K.continuous.comp continuous_snd)

theorem exists_norm_le_max_of_lifting
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (J : X →L[𝕜] Y) (QH : X →L[𝕜] Z)
    (QL : Y →L[𝕜] W) (K : Z →L[𝕜] W)
    (hJ : Function.Injective J)
    (hcomm : QL.comp J = K.comp QH)
    (hlift : ∀ y z, QL y = K z → ∃ x, J x = y ∧ QH x = z) :
    ∃ C ≥ (0 : ℝ), ∀ x, ‖x‖ ≤ C * max ‖J x‖ ‖QH x‖ := by
  have hprod : Function.Injective (J.prod QH) := by
    intro x y hxy
    exact hJ (congrArg Prod.fst hxy)
  obtain ⟨C, hC⟩ := (J.prod QH).antilipschitz_of_injective_of_isClosed_range
    hprod (isClosed_range_prod_of_lifting J QH QL K hcomm hlift)
  refine ⟨C, C.coe_nonneg, fun x => ?_⟩
  simpa only [map_zero, dist_zero_right, prod_apply, Prod.norm_def] using hC.le_mul_dist x 0

end ContinuousLinearMap
