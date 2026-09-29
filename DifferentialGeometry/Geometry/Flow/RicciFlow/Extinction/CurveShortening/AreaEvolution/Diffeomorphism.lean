import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BackgroundBounds

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]

omit [T2Space M] in
theorem loopFamilyLeastArea_postcomposeDiffeomorph
    (g : ℝ → SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop M) (t : ℝ) :
    loopFamilyLeastArea (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm)
      (fun s => (⟨Φ, Φ.continuous⟩ : C(M, A)).comp (γ s)) t =
      loopFamilyLeastArea g γ t := by
  unfold loopFamilyLeastArea
  rw [Width.competitorAreas_pullbackDiffeo]
  congr 2
  ext theta
  exact Φ.symm_apply_apply (γ t theta)

theorem scalarMinimum_pullback [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (t : ℝ) :
    scalarMinimum (S.pullback Φ.symm).base t = scalarMinimum S.base t := by
  unfold scalarMinimum
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨Φ.symm x, (S.pullback_scalar Φ.symm t x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨Φ x, ?_⟩
    change (S.pullback Φ.symm).scalar t (Φ x) = S.scalar t x
    rw [S.pullback_scalar, Φ.symm_apply_apply]

theorem exists_ricciBackground_pullback [I.Boundaryless] [CompactSpace A]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (Φ : M ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) :
    ∃ B' : RicciBackground (I := 𝓘(ℝ, E)) (M := A) D a b,
      B'.family = (SolutionOn.pullback (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        Φ.symm).base := by
  let S : SolutionOn (I := I) (M := M) D := ⟨B.family⟩
  obtain ⟨B', hB', _⟩ := rfs_csf_background (S.pullback Φ.symm)
    (IsSolutionOn.pullback S B.equation Φ.symm) B.lt B.regular
  exact ⟨B', hB'⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
