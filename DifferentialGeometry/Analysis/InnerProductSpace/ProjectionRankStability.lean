import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem injective_orthogonalProjectionOnto_restrict_of_norm_sub_lt_one
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hclose : ‖P.starProjection - Q.starProjection‖ < 1) :
    Function.Injective (fun v : P => Q.orthogonalProjectionOnto v) := by
  let T := Q.orthogonalProjectionOnto.toLinearMap.comp P.subtype
  change Function.Injective T
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : Q.starProjection v = 0 := by
    have h := congrArg (fun w : Q => (w : H)) (LinearMap.mem_ker.mp hv)
    exact h
  have hp : P.starProjection v = v := starProjection_eq_self_iff.mpr v.property
  have hn := (P.starProjection - Q.starProjection).le_opNorm (v : H)
  simp only [sub_apply, hp, hz, sub_zero] at hn
  have hnorm : ‖(v : H)‖ = 0 := by nlinarith [norm_nonneg (v : H)]
  exact Subtype.ext (norm_eq_zero.mp hnorm)

theorem finrank_eq_of_norm_starProjection_sub_lt_one
    (P Q : Submodule 𝕜 H) [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 Q]
    (hclose : ‖P.starProjection - Q.starProjection‖ < 1) :
    Module.finrank 𝕜 P = Module.finrank 𝕜 Q := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := Q.orthogonalProjectionOnto.toLinearMap.comp P.subtype)
      (injective_orthogonalProjectionOnto_restrict_of_norm_sub_lt_one P Q hclose)
  · have hrev : ‖Q.starProjection - P.starProjection‖ < 1 := by rwa [norm_sub_rev]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := P.orthogonalProjectionOnto.toLinearMap.comp Q.subtype)
      (injective_orthogonalProjectionOnto_restrict_of_norm_sub_lt_one Q P hrev)

end Submodule
