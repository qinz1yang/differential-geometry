import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology
open scoped NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def smallPerturbationHomeomorph (u : E → E) {c : ℝ≥0} (hu : LipschitzWith c u)
    (hc : c < 1) : E ≃ₜ E := by
  have happrox : ApproximatesLinearOn (fun x => x + u x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ c := by
    apply LipschitzOnWith.approximatesLinearOn
    rw [lipschitzOnWith_univ]
    convert hu using 1
    funext x
    simp only [Pi.sub_apply, ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.coe_coe,
      add_sub_cancel_left]
  apply happrox.toHomeomorph (fun x => x + u x)
  rcases subsingleton_or_nontrivial E with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using hc)

@[simp]
theorem smallPerturbationHomeomorph_apply (u : E → E) {c : ℝ≥0} (hu : LipschitzWith c u)
    (hc : c < 1) (x : E) : smallPerturbationHomeomorph u hu hc x = x + u x := rfl

theorem smallPerturbationHomeomorph_fixed (u : E → E) {c : ℝ≥0} (hu : LipschitzWith c u)
    (hc : c < 1) {x : E} (hx : u x = 0) : smallPerturbationHomeomorph u hu hc x = x := by
  simp only [smallPerturbationHomeomorph_apply, hx, add_zero]

theorem smallPerturbationHomeomorph_norm_sub (u : E → E) {c : ℝ≥0}
    (hu : LipschitzWith c u) (hc : c < 1) (x : E) :
    ‖smallPerturbationHomeomorph u hu hc x - x‖ = ‖u x‖ := by
  simp only [smallPerturbationHomeomorph_apply, add_sub_cancel_left]

theorem smallPerturbationHomeomorph_symm_norm_sub_lt (u : E → E) {c : ℝ≥0}
    (hu : LipschitzWith c u) (hc : c < 1) {ε : ℝ} (hε : ∀ x, ‖u x‖ < ε) (y : E) :
    ‖(smallPerturbationHomeomorph u hu hc).symm y - y‖ < ε := by
  let H := smallPerturbationHomeomorph u hu hc
  have he : H.symm y + u (H.symm y) = y := H.apply_symm_apply y
  have hdiff : H.symm y - y = -u (H.symm y) := by
    calc
      H.symm y - y = H.symm y - (H.symm y + u (H.symm y)) :=
        congrArg (fun z => H.symm y - z) he.symm
      _ = -u (H.symm y) := by abel
  change ‖H.symm y - y‖ < ε
  rw [hdiff, norm_neg]
  exact hε _

theorem homeomorph_image_eq_of_fixed_compl {X : Type*} [TopologicalSpace X]
    (H : X ≃ₜ X) {S : Set X} (hfix : ∀ x ∉ S, H x = x) : H '' S = S := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_contra hn
    have he := H.injective (hfix (H x) hn)
    exact hn (he.symm ▸ hx)
  · intro y hy
    refine ⟨H.symm y, ?_, H.apply_symm_apply y⟩
    by_contra hn
    have he : y = H.symm y := (H.apply_symm_apply y).symm.trans (hfix _ hn)
    exact hn (he ▸ hy)

end

end DifferentialGeometry.Topology.Engulfing
