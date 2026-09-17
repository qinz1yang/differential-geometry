import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.ModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeMonotonicity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval}

theorem redVolume_anti_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Icc (T - tau₂) T ⊆ D.regular) :
    redVolume S T x tau₂ ≤ redVolume S T x tau₁ := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Φ.symm
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  have hU : IsSolutionOn U := hS.pullback S Φ.symm
  have hcomplete : RiemannianMetricComplete (I := J) (U.base.metric T) :=
    RiemannianMetricComplete.pullbackCross (S.base.metric T) Φ.symm hg
  have hRmU : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := J) (U.base.metric t) z 4 (U.base.rm04 t z) ≤ K := by
    intro sigma hsigma hreg
    obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
    refine ⟨K, fun t ht z => ?_⟩
    change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm) z 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm) z) ≤ K
    rw [riemannNormSq_cross]
    exact hK t ht z
  have h := DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm
    U hU T hcomplete x hRmU htau₁ h12 hslab
  change redVolume U T x tau₂ ≤ redVolume U T x tau₁ at h
  rw [redVolume_transContinuousLinearEquiv S e T x tau₂,
    redVolume_transContinuousLinearEquiv S e T x tau₁] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman
