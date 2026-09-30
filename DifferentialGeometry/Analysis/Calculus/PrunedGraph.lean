import DifferentialGeometry.Analysis.InnerProductSpace.PrunedGraphRank
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter
open scoped Topology

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem pruned_graph_derivative_surjective_of_approximation
    (K : H →L[ℝ] H) (Q : H →L[ℝ] F)
    {f : E → H} {η : E → F} {Φ : F → H} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hΦ : DifferentiableAt ℝ Φ (η x))
    (hfix : (K ∘ f) =ᶠ[𝓝 x] f)
    (hgraph : (Q ∘ K ∘ Φ) =ᶠ[𝓝 (η x)] id)
    (hK : ‖K‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) {a e b l : ℝ}
    (ha : 0 < a) (he : e < a)
    (hl : ∀ z, a * ‖z‖ ≤ ‖(fderiv ℝ η x).adjoint z‖)
    (hT : ‖fderiv ℝ Φ (η x)‖ ≤ b) (hL : ‖fderiv ℝ η x‖ ≤ l)
    (herror : ‖fderiv ℝ f x - (fderiv ℝ Φ (η x)).comp (fderiv ℝ η x)‖ ≤ e) :
    let T := fderiv ℝ (K ∘ Φ) (η x)
    let D := fderiv ℝ f x
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  have hKD : K.comp (fderiv ℝ f x) = fderiv ℝ f x := by
    rw [← (K.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
    exact hfix.fderiv_eq
  have hQT : Q.comp (K.comp (fderiv ℝ Φ (η x))) = ContinuousLinearMap.id ℝ F := by
    have hd := Q.hasFDerivAt.comp (η x) (K.hasFDerivAt.comp (η x) hΦ.hasFDerivAt)
    exact (hd.congr_of_eventuallyEq hgraph.symm).unique (hasFDerivAt_id (η x))
  have hder : fderiv ℝ (K ∘ Φ) (η x) = K.comp (fderiv ℝ Φ (η x)) :=
    (K.hasFDerivAt.comp (η x) hΦ.hasFDerivAt).fderiv
  dsimp only
  rw [hder]
  exact ContinuousLinearMap.pruned_graph_range_surjective_of_approximation
    K Q (fderiv ℝ Φ (η x)) (fderiv ℝ η x) (fderiv ℝ f x)
    hK hQ hQT hKD ha he hl hT hL herror

end DifferentialGeometry.Analysis
