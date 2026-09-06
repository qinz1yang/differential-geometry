import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.UhlenbeckTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import DifferentialGeometry.Geometry.Operator.HessianPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval laplacianAt ricciSharp)
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem scalarHessSec_metricTrace_tensor0SPullbackCLE_eq_laplacianAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (gSource : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, (S.family.metric t).inner y (e u) (e v) = gSource.inner x u v) :
    metricTracePair0SAt gSource
        (tensor0SPullbackCLE 2 e (scalarHessSec S t y)) =
      laplacianAt (flowG (I := I) S) t (S.scalar t) y := by
  exact metricTracePair0SAt_tensor0SPullbackCLE_hessianSec
    (S.base.connection t) (ricciCovInf S t) gSource (S.family.metric t)
    (ricciMetricComp S t) (fun z => S.scalar t z) (scalarSmoothSec S t) e hiso

theorem hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq_scalarHessian_trace
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
      (1 / 2 : Real) * metricTracePair0SAt gSource
          (tensor0SPullbackCLE 2 e (scalarHessSec S clock.time y)) +
        normSq0S gSource x 2 (tensor0SPullbackCLE 2 e (S.ricci clock.time y)) +
        S.scalar clock.time y / (2 * clock.elapsed) := by
  rw [scalarHessSec_metricTrace_tensor0SPullbackCLE_eq_laplacianAt
    S clock.time gSource e hiso]
  exact hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq_laplacian_add
    S hS clock ht gSource e hiso

theorem exists_uhlenbeck_hamiltonM_metricTrace_scalarHessian_on_interval
    [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {J : Set Real} {s : Real} (hJ : J.OrdConnected) (hs : s ∈ J)
    (hJD : J ⊆ D.regular) :
    ∃ (ι : Real → ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
      (hι : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun x => (⟨x, (ι t x).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))),
      (∀ x, ι s x = ContinuousLinearEquiv.refl Real (TangentSpace I x)) ∧
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M => (⟨p.2, (ι p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M => (⟨p.2, (ι p.1 p.2).symm.toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))
        (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun r => ι r x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) =
          (S.family.metric s).inner x v w) ∧
      ∀ (clock : HarnackClock) (ht : clock.time ∈ J),
        let φ := ι clock.time
        let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ y).toLinearEquiv)
          ((hι clock.time ht).of_le (by norm_num)).clm_bundle_map
          (S.base.connection clock.time)
        let fixedDu := fun x => tensor0SPullbackCLE 1 (φ x).toLinearEquiv
          (scalarDuSec S clock.time x)
        let fixedHess := fun x => tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (scalarHessSec S clock.time x)
        (∀ (x : M) (X : TangentSpace I x),
          fixedDu x (fun _ => X) = mvfderiv (I := I) (S.scalar clock.time) x (φ x X)) ∧
        (∀ (x : M) (X : TangentSpace I x) (tail : Fin 1 → TangentSpace I x),
          D.multilinear 1 fixedDu x (φ x X) tail = fixedHess x (Fin.cons X tail)) ∧
        ∀ x : M,
          let fixedM := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
            (hamiltonMAt clock (S.family.metric clock.time) x)
          let fixedRic := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
            (S.ricci clock.time x)
          metricTracePair0SAt (S.family.metric s) fixedM =
              (1 / 2 : Real) * metricTracePair0SAt (S.family.metric s) (fixedHess x) +
                normSq0S (S.family.metric s) x 2 fixedRic +
                S.scalar clock.time x / (2 * clock.elapsed) ∧
            metricTracePair0SAt (S.family.metric s) fixedM =
              (1 / 2 : Real) *
                (deriv (fun t : Real => S.scalar t x) clock.time +
                  S.scalar clock.time x / clock.elapsed) := by
  have hid : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x : M => (⟨x, ContinuousLinearMap.id Real (TangentSpace I x)⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))) :=
    contMDiff_id.clm_bundle_id
  obtain ⟨ι, hinit, hjoint, hinv, hderiv, hiso⟩ :=
    exists_uhlenbeck_isometry_on_interval S hS hJ hs hJD
      (S.family.metric s).toRiemannianMetric
      (fun x => ContinuousLinearEquiv.refl Real (TangentSpace I x)) hid
      (fun _ _ _ => rfl)
  have hι : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x => (⟨x, (ι t x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))) := by
    intro t ht
    exact hjoint.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun x => ⟨ht, Set.mem_univ x⟩)
  refine ⟨ι, hι, hinit, hjoint, hinv, hderiv, hiso, ?_⟩
  intro clock ht
  refine ⟨?_, ?_, ?_⟩
  · intro x X
    exact tensor0SPullbackCLE_duSec_apply _ (scalarSmoothSec S clock.time)
      (ι clock.time x).toLinearEquiv X
  · intro x X tail
    exact multilinear_pullback_eq_hessianSec (ι clock.time)
      ((hι clock.time ht).of_le (by norm_num))
      (S.base.connection clock.time) (ricciCovInf S clock.time)
      (fun z => S.scalar clock.time z) (scalarSmoothSec S clock.time) x X tail
  · intro x
    exact ⟨hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq_scalarHessian_trace
        S hS clock (hJD ht) (S.family.metric s) (ι clock.time x).toLinearEquiv
        (hiso clock.time ht x),
      hamiltonMAt_metricTrace_tensor0SPullbackCLE_eq
        S hS clock (hJD ht) (S.family.metric s) (ι clock.time x).toLinearEquiv
        (hiso clock.time ht x)⟩

theorem exists_uhlenbeck_hamiltonM_metricTrace_scalarHessian
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) {s : Real}
    (hs : 0 < s) (hst : s < clock.time) (htT : clock.time < T) :
    ∃ (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
      (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))),
      (∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric clock.time).inner x (φ x v) (φ x w) =
          (S.family.metric s).inner x v w) ∧
      let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) (hφ.of_le (by norm_num)).clm_bundle_map
        (S.base.connection clock.time)
      let fixedDu := fun x => tensor0SPullbackCLE 1 (φ x).toLinearEquiv
        (scalarDuSec S clock.time x)
      let fixedHess := fun x => tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (scalarHessSec S clock.time x)
      (∀ (x : M) (X : TangentSpace I x),
        fixedDu x (fun _ => X) = mvfderiv (I := I) (S.scalar clock.time) x (φ x X)) ∧
      (∀ (x : M) (X : TangentSpace I x) (tail : Fin 1 → TangentSpace I x),
        D.multilinear 1 fixedDu x (φ x X) tail = fixedHess x (Fin.cons X tail)) ∧
      ∀ x : M,
        let fixedM := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (hamiltonMAt clock (S.family.metric clock.time) x)
        let fixedRic := tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (S.ricci clock.time x)
        metricTracePair0SAt (S.family.metric s) fixedM =
            (1 / 2 : Real) * metricTracePair0SAt (S.family.metric s) (fixedHess x) +
              normSq0S (S.family.metric s) x 2 fixedRic +
              S.scalar clock.time x / (2 * clock.elapsed) ∧
          metricTracePair0SAt (S.family.metric s) fixedM =
            (1 / 2 : Real) *
              (deriv (fun t : Real => S.scalar t x) clock.time +
                S.scalar clock.time x / clock.elapsed) := by
  have hsJ : s ∈ Set.Ioo 0 T := ⟨hs, lt_trans hst htT⟩
  have ht : clock.time ∈ (RealTimeInterval.closed 0 T hT.le).regular :=
    ⟨lt_trans hs hst, htT⟩
  obtain ⟨ι, hι, _, _, _, _, hiso, htrace⟩ :=
    exists_uhlenbeck_hamiltonM_metricTrace_scalarHessian_on_interval
      S hS Set.ordConnected_Ioo hsJ (fun _ hr => hr)
  exact ⟨ι clock.time, hι clock.time ht, hiso clock.time ht, htrace clock ht⟩

end DifferentialGeometry.PDE.RicciFlow
