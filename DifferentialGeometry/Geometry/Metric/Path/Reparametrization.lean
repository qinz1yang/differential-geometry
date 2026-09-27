import DifferentialGeometry.Geometry.Metric.Path.Length
import DifferentialGeometry.Topology.Manifold.Path.Reparametrization

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x y : M}

variable [(x : M) → ENorm (TangentSpace I x)]
  [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]

theorem riemannianELength_withSittingInstants (p : Path x y)
    (hp : MDifferentiableOn 𝓘(ℝ, ℝ) I p.extend (Icc 0 1)) :
    p.withSittingInstants.riemannianELength (I := I) = p.riemannianELength (I := I) := by
  rw [riemannianELength, extend_withSittingInstants]
  have h0 : Real.smoothTransition (3 * (0 : ℝ) - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : Real.smoothTransition (3 * (1 : ℝ) - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  have hmono : Monotone (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.monotone.comp (by
      intro t s hts
      dsimp
      linarith)
  have hcd : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  rw [Manifold.pathELength_comp_of_monotoneOn zero_le_one
    (hmono.monotoneOn _)
    (hcd.differentiable (by norm_num)).differentiableOn
    (by simpa only [h0, h1] using hp), h0, h1]
  rfl

end Path
