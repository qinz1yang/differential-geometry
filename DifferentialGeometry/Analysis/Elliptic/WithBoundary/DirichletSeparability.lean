import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothBasis

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

noncomputable instance instSeparableSpaceH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    TopologicalSpace.SeparableSpace (H1ComplDirichlet g) := by
  let b := smoothDirichletHilbertBasis g
  have hrange : TopologicalSpace.IsSeparable (Set.range b) :=
    Set.countable_range b |>.isSeparable
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range b) : Set
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) :=
    hrange.span
  have hclosure : closure (Submodule.span ℝ (Set.range b) : Set
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) = Set.univ := by
    change closure (Submodule.span ℝ (Set.range b) : Set
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) =
        (↑(⊤ : Submodule ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) : Set _)
    simpa only [Submodule.topologicalClosure_coe] using
      congrArg SetLike.coe b.dense_span
  let _ : TopologicalSpace.SeparableSpace
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      rw [← hclosure]
      exact hspan.closure)
  have hres : DenseRange (resolventDirichlet g) := by
    apply Dense.mono _ (denseRange_smoothToH1ComplDirichlet g)
    rintro _ ⟨u, rfl⟩
    exact ⟨u.oneSubLapClassicalLp,
      smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u |>.symm⟩
  exact hres.separableSpace (resolventDirichlet g).continuous

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end
