import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lVelocity (gamma : Real -> M) (tau : Real) :
    TangentSpace I (gamma tau) :=
  (mfderiv 𝓘(Real, Real) I gamma tau :
    Real →L[Real] TangentSpace I (gamma tau)) (1 : Real)

noncomputable def lSpeedSq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) : Real :=
  (S.base.metric (T - tau)).inner (gamma tau)
    (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau)

theorem lSpeedSq_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) :
    0 <= lSpeedSq S T gamma tau := by
  unfold lSpeedSq
  by_cases hv : lVelocity (I := I) gamma tau = 0
  · simp [hv]
  · exact ((S.base.metric (T - tau)).pos (gamma tau)
      (lVelocity (I := I) gamma tau) hv).le

variable [FiniteDimensional Real E]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

noncomputable def lDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) : Real :=
  Real.sqrt tau * (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)

noncomputable def lLength
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a b : Real) : Real :=
  ∫ tau in a..b, lDensity S T gamma tau

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem lLength_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a : Real) :
    lLength S T gamma a a = 0 := by
  simp [lLength]

omit [T2Space M] [SigmaCompactSpace M] in
theorem lLength_add_adj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a b c : Real)
    (hab : IntervalIntegrable (lDensity S T gamma) volume a b)
    (hbc : IntervalIntegrable (lDensity S T gamma) volume b c) :
    lLength S T gamma a b + lLength S T gamma b c =
      lLength S T gamma a c := by
  simpa [lLength] using intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [T2Space M] [SigmaCompactSpace M] in
theorem lDensity_congr
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    {gamma delta : Real -> M} (h : gamma =ᶠ[nhds tau] delta) :
    lDensity S T gamma tau = lDensity S T delta tau := by
  have hval : gamma tau = delta tau := h.self_of_nhds
  have hder := Filter.EventuallyEq.mfderiv_eq
    (I := 𝓘(Real, Real)) (I' := I) h
  simp only [lDensity, lSpeedSq, lVelocity]
  rw [hval, hder]

omit [T2Space M] [SigmaCompactSpace M] in
theorem lLength_congr
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    {gamma delta : Real -> M}
    (h : ∀ tau ∈ uIcc a b, gamma =ᶠ[nhds tau] delta) :
    lLength S T gamma a b = lLength S T delta a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro tau htau
  exact lDensity_congr S T tau (h tau htau)

omit [T2Space M] [SigmaCompactSpace M] in
theorem lSpeedSq_contOn
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    ContinuousOn (lSpeedSq S T gamma) (uIcc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {tau : Real // tau ∈ uIcc a b}
  let timeLift : P -> {t : Real // t ∈ D.carrier} :=
    fun tau => ⟨T - tau.1, hback tau.2⟩
  let velocityLift : P -> TangentBundle I M :=
    fun tau => tangentMap 𝓘(Real, Real) I gamma
      (⟨tau.1, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)
  let input : P -> {t : Real // t ∈ D.carrier} × TangentBundle I M :=
    fun tau => (timeLift tau, velocityLift tau)
  have htime : Continuous timeLift := by
    exact ((continuous_const.sub continuous_subtype_val).subtype_mk _)
  have hvel : Continuous velocityLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) hgamma).comp
        continuous_subtype_val
  have hinput : Continuous input := htime.prodMk hvel
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hG (K := D.carrier) (fun _ ht => ht)
  have hcomp := hquad.comp hinput
  apply hcomp.congr
  intro tau
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem lDensity_contOn
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
      (D.carrier ×ˢ (univ : Set M)))
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    ContinuousOn (lDensity S T gamma) (uIcc a b) := by
  have hpair : ContinuousOn (fun tau : Real => (T - tau, gamma tau)) (uIcc a b) :=
    ((continuous_const.sub continuous_id).prodMk hgamma.continuous).continuousOn
  have hmaps : MapsTo (fun tau : Real => (T - tau, gamma tau)) (uIcc a b)
      (D.carrier ×ˢ (univ : Set M)) := by
    intro tau htau
    exact ⟨hback htau, mem_univ _⟩
  have hscalar : ContinuousOn (fun tau : Real => S.scalar (T - tau) (gamma tau))
      (uIcc a b) := by
    simpa [Function.comp_def] using hR.comp hpair hmaps
  have hspeed := lSpeedSq_contOn S T a b gamma hG hgamma hback
  change ContinuousOn (fun tau : Real =>
    Real.sqrt tau *
      (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)) (uIcc a b)
  exact Real.continuous_sqrt.continuousOn.mul (hscalar.add hspeed)

omit [T2Space M] [SigmaCompactSpace M] in
theorem lDensity_integrable
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
      (D.carrier ×ˢ (univ : Set M)))
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    IntervalIntegrable (lDensity S T gamma) volume a b :=
  (lDensity_contOn S T a b gamma hG hR hgamma hback).intervalIntegrable

end DifferentialGeometry.PDE.RicciFlow.Perelman
