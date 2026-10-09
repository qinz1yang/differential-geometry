import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem surjective_codRestrict_of_rank_margin (T D : E →L[ℝ] H)
    (W : Submodule ℝ H) [FiniteDimensional ℝ W] (hDW : ∀ v, D v ∈ W)
    {μ δ : ℝ} (hδ : δ < μ) (herror : ‖D - T‖ ≤ δ)
    (hlower : ∀ v ∈ T.kerᗮ, μ * ‖v‖ ≤ ‖T v‖)
    (hdim : Module.finrank ℝ W ≤ Module.finrank ℝ T.range) :
    Function.Surjective (D.codRestrict W hDW) := by
  let V := T.kerᗮ
  let A : V →ₗ[ℝ] W := (D.codRestrict W hDW).toLinearMap.comp V.subtype
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    change A v = 0 at hv
    have hDv : D v = 0 := congrArg (fun w : W => (w : H)) hv
    have he := ((D - T).le_opNorm (v : E)).trans
      (mul_le_mul_of_nonneg_right herror (norm_nonneg _))
    simp only [sub_apply, hDv, zero_sub, norm_neg] at he
    have hl := hlower v v.property
    have hn : ‖(v : E)‖ = 0 := by nlinarith [norm_nonneg (v : E)]
    have hz : (v : E) = 0 := norm_eq_zero.mp hn
    exact Subtype.ext hz
  have hdimV : Module.finrank ℝ V = Module.finrank ℝ T.range := by
    have h1 := T.ker.finrank_add_finrank_orthogonal
    have h2 := T.toLinearMap.finrank_range_add_finrank_ker
    dsimp [V]
    omega
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdimA : Module.finrank ℝ V = Module.finrank ℝ W := by omega
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimA).mp hinj
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  exact ⟨v, hv⟩

end ContinuousLinearMap
