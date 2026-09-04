import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.AllTimesBounds

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
omit [SigmaCompactSpace M] in
theorem ricciFlow_metric_hasDerivAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    {t : Real} (ht : t ∈ D.regular) (x : M) (v : TangentSpace I x) :
    HasDerivAt
      (fun s : Real => (S.family.metric s).inner x v v)
      ((-2 : Real) *
        S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
      t := by
  have hwithin := hS.equation ⟨t, ht⟩ x v v
  exact hwithin.hasDerivAt (D.regular_mem_nhds ht)
omit [SigmaCompactSpace M] in
theorem ricci_directional_quotient_interval_integrable_of_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) (t0 t : Real)
    (hsub : Set.uIcc t0 t ⊆ D.carrier) :
    IntervalIntegrable
      (fun s : Real =>
        ((-2 : Real) * S.ricciAt s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /
          (S.family.metric s).inner x v v)
      MeasureTheory.volume t0 t := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M; infer_instance
  apply ContinuousOn.intervalIntegrable
  have hnum : ContinuousOn
      (fun s : Real =>
        (-2 : Real) * S.ricciAt s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
      (Set.uIcc t0 t) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hev :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous
      (hA := hS.ricciCont) (P := {s : Real // s ∈ Set.uIcc t0 t})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun p => hsub p.2) continuous_const (v := fun _ _ => v) (fun _ => continuous_const)
    refine continuous_const.mul ?_
    refine hev.congr ?_
    intro p
    rw [show (fun _i : Fin 2 => v) = DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v
      from by
      funext i; fin_cases i <;> rfl]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt]
  have hden : ContinuousOn (fun s : Real => (S.family.metric s).inner x v v) (Set.uIcc t0 t) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hev :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.eval_continuous
      (hA := DifferentialGeometry.Geometry.Curvature.metricTensor_cont_of_metricFamilySmoothOn
        S.family.metric hS.smoothMetric)
      (P := {s : Real // s ∈ Set.uIcc t0 t})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun p => hsub p.2) continuous_const (v := fun _ _ => v) (fun _ => continuous_const)
    refine hev.congr ?_
    intro p
    simp only [Set.domRestrict]
    rw [Tensor0SBundle.metricTensorField_apply]
  exact hnum.div hden (fun s _ => ne_of_gt ((S.family.metric s).pos x v hv))

section FixedDomain

variable [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricLogDerivativeInput_of_solutions
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 A : Real)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (hA : 0 <= A)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i s => (S i).family.metric s)
      (fun i t x => (S i).ricciAt t x) A where
  quad_bound := ⟨hA, fun i t ht x hx v => hquad i t ht x hx v⟩
  metric_deriv := fun i x _hx v _hv _t ht =>
    ricciFlow_metric_hasDerivAt (S i) (hS i) (hwin ht) x v
  log_integrable := fun i x hx v hv t ht => hint i x hx v hv t ht

omit [SigmaCompactSpace M] in
theorem metric_uniform_equivalent_on_window_of_solutions_of_interval_integrable
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hA : 0 <= A)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef ((S i).family.metric t0) C)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i s => (S i).family.metric s)
      (fun t : Real => metricEquivalenceFactor C A t t0) :=
  metricUniformEquivalentOnWindow_of_logDerivativeInput (I := I) K β ψ t0 C A gRef
    (fun i s => (S i).family.metric s) (fun i t x => (S i).ricciAt t x)
    ht0 hC hequiv0
    (metricLogDerivativeInput_of_solutions (I := I) S hS K β ψ t0 A hwin hA hquad hint)

omit [SigmaCompactSpace M] in
theorem metric_uniform_equivalent_on_window_of_solutions
    [hSigma : SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hA : 0 <= A)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef ((S i).family.metric t0) C)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i s => (S i).family.metric s)
      (fun t : Real => metricEquivalenceFactor C A t t0) := by
  let _ := hSigma
  exact metric_uniform_equivalent_on_window_of_solutions_of_interval_integrable S hS K β ψ t0 C A gRef hwin ht0 hC hA hequiv0 hquad
    (fun i _x _hx v hv t ht =>
      ricci_directional_quotient_interval_integrable_of_solution
        (S i) (hS i) _x v hv t0 t
      ((Set.uIcc_subset_Icc ht0 ht).trans (hwin.trans D.regular_subset)))

end FixedDomain

end HCGCompactness
end DifferentialGeometry
