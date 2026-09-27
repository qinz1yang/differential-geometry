import DifferentialGeometry.Geometry.Boundary.SmoothParametrization
import DifferentialGeometry.Topology.Manifold.NestedBallShell

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_diffeomorph_sphere_prod_interval_of_nested_balls
    {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)]
    (ι : W → F) (hι : ContMDiff I 𝓘(ℝ, F) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I 𝓘(ℝ, F) ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (outer inner : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : closedBall (0 : F) R ⊆ outer.source)
    (hinner : closedBall (0 : F) r ⊆ inner.source)
    (hnested : inner '' closedBall 0 r ⊆ outer '' ball 0 R)
    (hrange : range ι = outer '' closedBall 0 R \ inner '' ball 0 r)
    (v : sphere (0 : F) 1) :
    Nonempty (Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) I (sphere (0 : F) 1 × unitInterval) W ∞) := by
  obtain ⟨e, hes, het, he, hei⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_nestedBallShell_parametrization (n := n)
      outer inner hr houter hinner hnested v
  obtain ⟨D, _⟩ := exists_diffeomorph_of_smooth_partial_equiv_to_range ι hι hemb hinj hdim
    e hes (het.trans hrange.symm) he hei
  exact ⟨D⟩

end DifferentialGeometry.Geometry.Boundary
