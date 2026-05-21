import RicciFlower.RicciFlow.Basic
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Maximal and Singular Times for Ricci Flow

This file records the interval-changing definitions needed for the appendix
maximal-time discussion.  The genuine theorem that singularity is equivalent
to maximality remains a global extension-criterion frontier.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- Two interval solutions agree on `U` when their stored metric, connection,
and Ricci data agree at every time in `U`.  Ricci equality is explicit because
the current solution predicate does not prove Ricci is uniquely reconstructed
from the metric. -/
def SolutionAgreesOn
    {D Dhat : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Shat : SolutionOn (I := I) (M := M) Dhat)
    (U : Set Real) : Prop :=
  forall t : Real, t ∈ U ->
    S.family.metric t = Shat.family.metric t ∧
      S.family.connection t = Shat.family.connection t ∧
        S.ricci t = Shat.ricci t

/-- The solution on `[alpha, omega)` extends as a Ricci flow past `omega`. -/
def ExtendsPastEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ eps : Real, 0 < eps ∧
    ∃ hwide : alpha < omega + eps,
      ∃ Shat : SolutionOn (I := I) (M := M)
        (Realized.RealTimeInterval.closedOpen alpha (omega + eps) hwide),
        IsSolutionOn (I := I) Shat ∧
          SolutionAgreesOn (I := I) S Shat (Set.Ico alpha omega)

/-- The solution on `[alpha, omega)` is maximal at its finite endpoint. -/
def IsMaximalAtEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ¬ ExtendsPastEndpoint (I := I) hαω S

/-- A time-indexed lowered Riemann tensor realizes the solution curvature on
the interval where the solution is defined. -/
def Rm04RealizesSolutionConnectionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)) : Prop :=
  forall t : Realized.RealTimeInterval.FlowTime D,
    Realized.Rm04RealizesConnection (I := I)
      (S.family.metric (t : Real)) (S.family.connection (t : Real))
      (Rm04 (t : Real))

/-- The canonical lowered Riemann section of a solution's metric realizes its
Levi-Civita connection curvature. -/
theorem rm04Realizes_metric
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Rm04RealizesSolutionConnectionOn (I := I) S S.base.rm04 := by
  intro t
  simpa [SolutionOn.family, SolutionFamily.rm04, SolutionFamily.connection,
    metricCov] using
    (Realized.rm04Section_realizes (I := I) (M := M)
      (S.base.metric (t : Real))
      (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
      (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))))

/-- Metric-induced squared norm of a time-indexed lowered Riemann tensor. -/
def curvatureNormSq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x)

@[simp] theorem curvatureNormSq_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (t : Real) (x : M) :
    curvatureNormSq (I := I) S Rm04 t x =
      Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x) := by
  rfl

/-- The metric-induced squared norm of a supplied lowered Riemann tensor is
unbounded on `M × [alpha, omega)`. -/
def Rm04NormSqUnboundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)) : Prop :=
  forall K : Real, ∃ t : Real, ∃ x : M,
    alpha <= t ∧ t < omega ∧ K < curvatureNormSq (I := I) S Rm04 t x

/-- The metric-induced squared norm of a supplied lowered Riemann tensor is
bounded above on `M × [alpha, omega)`. -/
def Rm04NormSqBoundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)) : Prop :=
  ∃ K : Real, forall t : Real, forall x : M,
    alpha <= t -> t < omega ->
      curvatureNormSq (I := I) S Rm04 t x <= K

/-- Failure of unboundedness gives a finite bound.  This is just classical
logic for the chosen squared-norm formulation. -/
theorem rmBounded_of_not_unbounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    (hnot : ¬ Rm04NormSqUnboundedAt (I := I) S Rm04) :
    Rm04NormSqBoundedAt (I := I) S Rm04 := by
  classical
  unfold Rm04NormSqUnboundedAt at hnot
  simp only [not_forall, not_exists, not_and, not_lt] at hnot
  rcases hnot with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro t x ht hT
  exact hK t x ht hT

/-- Black Box 11.2: bounded curvature on a closed finite-endpoint Ricci flow
lets the flow extend smoothly past the endpoint.  This is global PDE theory,
not local tensor algebra. -/
theorem extends_of_rmBounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    (_hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (_hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    ExtendsPastEndpoint (I := I) hαω S := by
  sorry

/-- Lemma 11.3: a maximal finite-endpoint Ricci flow has unbounded curvature.

This is the consumer proof from Black Box 11.2: if curvature were bounded, the
extension criterion would extend the solution past the endpoint, contradicting
maximality. -/
theorem rmUnbounded_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    Rm04NormSqUnboundedAt (I := I) S Rm04 := by
  by_contra hnot
  exact hmax (extends_of_rmBounded (I := I) hRm
    (rmBounded_of_not_unbounded (I := I) hnot))

/-- A Ricci flow forms a singularity at the finite endpoint when some lowered
Riemann tensor realizing the solution curvature has metric-induced squared
norm unbounded on `M × [alpha, omega)`. -/
def FormsSingularityAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M),
    Rm04RealizesSolutionConnectionOn (I := I) S Rm04 ∧
      Rm04NormSqUnboundedAt (I := I) S Rm04

/-- Existential version of Lemma 11.3 matching `FormsSingularityAt`.  A
separate curvature-realization producer supplies the realizing `Rm04`. -/
theorem formsSing_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)}
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRmEx :
      ∃ Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M),
        Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    FormsSingularityAt (I := I) S := by
  rcases hRmEx with ⟨Rm04, hRm⟩
  exact ⟨Rm04, hRm, rmUnbounded_of_maximal (I := I) hmax hRm⟩

/-- Canonical metric-curvature version of Lemma 11.3. -/
theorem formsSing_of_maximal_metric
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)}
    (hmax : IsMaximalAtEndpoint (I := I) hαω S) :
    FormsSingularityAt (I := I) S := by
  exact formsSing_of_maximal (I := I) hmax
    ⟨S.base.rm04, rm04Realizes_metric (I := I) S⟩

/-- Interface for Lemma 14.27.  Proving this requires the global extension
criterion and compactness/regularity inputs; this file only exposes the target
shape. -/
def SingularIffMaximalAtEndpoint
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  FormsSingularityAt (I := I) S ↔
    IsMaximalAtEndpoint (I := I) hαω S

end RicciFlow
end RicciFlower
