import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MIdentities
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.TensorNabla

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval laplacianAt)
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq
    [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v,
      (S.family.metric clock.time).inner y (e u) (e v) = gSource.inner x u v) :
    metricTracePair0SAt gSource
        (tensor0SPullbackCLE 2 e
          (hamiltonMAt clock (S.family.metric clock.time) y)) =
      (1 / 2 : Real) *
        (deriv (fun t : Real => S.scalar t y) clock.time +
          S.scalar clock.time y / clock.elapsed) := by
  rw [metricTracePair0SAt_tensor0SPullbackCLE gSource (S.family.metric clock.time)
    e hiso]
  exact hamiltonMAt_metricTrace_eq S hS clock ht y

theorem hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq_laplacian_add
    [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (gSource : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v,
      (S.family.metric clock.time).inner y (e u) (e v) = gSource.inner x u v) :
    metricTracePair0SAt gSource
        (tensor0SPullbackCLE 2 e
          (hamiltonMAt clock (S.family.metric clock.time) y)) =
      (1 / 2 : Real) *
          laplacianAt (flowG (I := I) S) clock.time (S.scalar clock.time) y +
        normSq0S gSource x 2 (tensor0SPullbackCLE 2 e (S.ricci clock.time y)) +
        S.scalar clock.time y / (2 * clock.elapsed) := by
  rw [metricTracePair0SAt_tensor0SPullbackCLE gSource (S.family.metric clock.time)
    e hiso]
  have hnorm :
      normSq0S gSource x 2 (tensor0SPullbackCLE 2 e (S.ricci clock.time y)) =
        normSq0S (S.family.metric clock.time) y 2 (S.ricci clock.time y) :=
    DifferentialGeometry.Tensor0SBundle.inner0S_tensor0SPullbackCLE gSource (S.family.metric clock.time)
      x y 2 e hiso _ _
  rw [hnorm]
  rw [hamiltonMAt_metricTrace_eq S hS clock ht y]
  have hevolWithin := scalarEvolution_of_isSolution (I := I) S hS
    (flowG (I := I) S) (fun _ => rfl) (fun _ => rfl) ⟨clock.time, ht⟩ y
  have hevol := hevolWithin.hasDerivAt (D.regular_mem_nhds ht)
  rw [hevol.deriv]
  ring

theorem exists_uhlenbeck_hamiltonM_metricTrace
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) {s : Real}
    (hs : 0 < s) (hst : s < clock.time) (htT : clock.time < T) :
    ∃ φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x,
      ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x))) ∧
      (∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric clock.time).inner x (φ x v) (φ x w) =
          (S.family.metric s).inner x v w) ∧
      ∀ x : M,
        let fixedM := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (hamiltonMAt clock (S.family.metric clock.time) x)
        let fixedRic := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (S.ricci clock.time x)
        metricTracePair0SAt (S.family.metric s) fixedM =
            (1 / 2 : Real) *
                laplacianAt (flowG (I := I) S) clock.time (S.scalar clock.time) x +
              normSq0S (S.family.metric s) x 2 fixedRic +
              S.scalar clock.time x / (2 * clock.elapsed) ∧
          metricTracePair0SAt (S.family.metric s) fixedM =
            (1 / 2 : Real) *
              (deriv (fun t : Real => S.scalar t x) clock.time +
                S.scalar clock.time x / clock.elapsed) := by
  obtain ⟨φ, hφ, hiso, _, _⟩ := exists_uhlenbeck_tensor_covariantDerivative_intertwining
    hT S hS hs hst htT
  have ht : clock.time ∈ (RealTimeInterval.closed 0 T hT.le).regular :=
    ⟨lt_trans hs hst, htT⟩
  refine ⟨φ, hφ, hiso, ?_⟩
  intro x
  dsimp only
  exact ⟨hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq_laplacian_add
      S hS clock ht (S.family.metric s) (φ x).toLinearEquiv (hiso x),
    hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq
      S hS clock ht (S.family.metric s) (φ x).toLinearEquiv (hiso x)⟩

end DifferentialGeometry.PDE.RicciFlow
