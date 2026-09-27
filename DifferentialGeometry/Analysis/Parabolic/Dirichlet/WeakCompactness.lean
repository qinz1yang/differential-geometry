import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section

open Bundle Filter Manifold MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

theorem exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet
    (q : SmoothRiemannianMetric (I_half n) M) {T C : ℝ}
    (U : ℕ → timeL2 (H1ComplDirichlet q) T)
    (hU : ∀ m, ‖U m‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ u : timeL2 (H1ComplDirichlet q) T,
      StrictMono φ ∧
        ∀ z, Tendsto (fun m => inner ℝ (U (φ m)) z) atTop
          (𝓝 (inner ℝ u z)) := by
  let _ : SecondCountableTopology (H1ComplDirichlet q) :=
    UniformSpace.secondCountable_of_separable _
  let _ : IsSeparable (timeMeasure T) := inferInstance
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : SecondCountableTopology (timeL2 (H1ComplDirichlet q) T) :=
    Lp.SecondCountableTopology
  let _ : TopologicalSpace.SeparableSpace
      (timeL2 (H1ComplDirichlet q) T) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact DifferentialGeometry.Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded
    U hU

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
