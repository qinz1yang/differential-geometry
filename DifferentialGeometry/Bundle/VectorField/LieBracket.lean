import DifferentialGeometry.Bundle.VectorField.Pushforward
import Mathlib.Geometry.Manifold.VectorField.LieBracket


namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pushforward_mlieBracket
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (X Y : ∀ x : M, TangentSpace I x)
    (x : M)
    (hX : MDifferentiableAt I I.tangent
      (fun y => (TotalSpace.mk' E y (X y) : TangentBundle I M)) (Φ.symm x))
    (hY : MDifferentiableAt I I.tangent
      (fun y => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) (Φ.symm x)) :
    mlieBracket I (Diffeomorph.pushforward Φ X) (Diffeomorph.pushforward Φ Y) x
      = Diffeomorph.pushforward Φ (mlieBracket I X Y) x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [Diffeomorph.pushforward_eq_mpullback_symm (I := I) Φ X,
    Diffeomorph.pushforward_eq_mpullback_symm (I := I) Φ Y,
    Diffeomorph.pushforward_eq_mpullback_symm (I := I) Φ (mlieBracket I X Y)]
  have hΦsymm_smooth : ContMDiffAt I I ∞ (⇑Φ.symm) x := Φ.symm.contMDiffAt
  have : IsManifold I (minSmoothness ℝ (2 : WithTop ℕ∞)) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hn : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  exact (VectorField.mpullback_mlieBracket hX hY hΦsymm_smooth hn).symm

end DifferentialGeometry
