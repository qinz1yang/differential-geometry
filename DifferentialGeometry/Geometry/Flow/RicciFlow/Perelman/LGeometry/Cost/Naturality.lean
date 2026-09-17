import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]
  {D : RealTimeInterval}

theorem lCost_pullback_cross
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (x y : M) (tau : ℝ) :
    lCost (S.pullback Φ) T x y tau = lCost S T (Φ x) (Φ y) tau := by
  unfold lCost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨alpha, halpha, hzero, hend, hlength⟩
    refine ⟨fun s => Φ (alpha s),
      (Φ.contMDiff.of_le (by norm_num)).comp halpha,
      congrArg Φ hzero, congrArg Φ hend, ?_⟩
    rw [lLength_pullback_cross] at hlength
    exact hlength
  · rintro ⟨alpha, halpha, hzero, hend, hlength⟩
    refine ⟨fun s => Φ.symm (alpha s),
      (Φ.symm.contMDiff.of_le (by norm_num)).comp halpha, ?_, ?_, ?_⟩
    · change Φ.symm (alpha 0) = x
      rw [hzero, Φ.symm_apply_apply]
    · change Φ.symm (alpha (Real.sqrt tau)) = y
      rw [hend, Φ.symm_apply_apply]
    · rw [lLength_pullback_cross]
      change lLength S T (fun r => Φ (Φ.symm (alpha (Real.sqrt r)))) 0 tau = r
      have hfun : (fun r => Φ (Φ.symm (alpha (Real.sqrt r)))) =
          squareRootReparametrization alpha := by
        funext r
        simp only [Φ.apply_symm_apply, squareRootReparametrization]
      rw [hfun]
      exact hlength

end DifferentialGeometry.PDE.RicciFlow.Perelman
