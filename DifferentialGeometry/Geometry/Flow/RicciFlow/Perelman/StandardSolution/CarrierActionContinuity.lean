import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegLag_time_cont_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ lRegularizedLagrangian S q.1 alpha q.2)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := by
  let U : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier}
  let P := {q : ℝ × ℝ // q ∈ U}
  let timeLift : P → {t : ℝ // t ∈ D.carrier} := fun q ↦
    ⟨q.1.1 - q.1.2 ^ 2, q.2⟩
  let velLift : P → TangentBundle I M := fun q ↦
    ⟨alpha q.1.2, lVelocity (I := I) alpha q.1.2⟩
  have htime : Continuous timeLift := by
    exact (((continuous_fst.comp continuous_subtype_val).sub
      ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _)
  have hvel : Continuous velLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) halpha).comp
        (continuous_snd.comp continuous_subtype_val)
  have hbase : Continuous (fun q : P ↦ alpha q.1.2) :=
    halpha.continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hMet
      (K := D.carrier) (fun _ ht ↦ ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)) := by
    have heq : (DifferentialGeometry.metricTimeBundleQuad
        (I := I) S.family.metric D.carrier ∘ fun q : P ↦
          (timeLift q, velLift q)) = fun q : P ↦
        (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2) := by
      funext q
      rfl
    rw [heq] at hkin0
    exact hkin0
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P ↦
      (1 / 2 : ℝ) *
          (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2)) :=
    continuous_const.mul hkin |>.add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : U.domRestrict (fun q : ℝ × ℝ ↦
      lRegularizedLagrangian S q.1 alpha q.2) = fun q : P ↦
        (1 / 2 : ℝ) *
            (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2) +
          2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2) := by
    funext q
    rfl
  change Continuous (U.domRestrict (fun q : ℝ × ℝ ↦
    lRegularizedLagrangian S q.1 alpha q.2))
  rw [heq]
  exact hlag

theorem lRegLag_integrable_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hback : MapsTo (fun s : ℝ ↦ T - s ^ 2) (uIcc a b) D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b := by
  have hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (uIcc a b) := by
    have h := (lRegLag_time_cont_on_carrier S hMet hSc alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs ↦ hback hs)
    exact h
  exact hcont.intervalIntegrable

end DifferentialGeometry.PDE.RicciFlow

end
