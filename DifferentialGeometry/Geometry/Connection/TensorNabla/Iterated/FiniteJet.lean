import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent

/-!
# Leibniz evaluation of the metric covariant derivative of an arbitrary section

`metricCovariantDerivative` is defined for every section, not only smooth ones. When the chart
representative at the base point is differentiable there, its evaluation on smooth vector fields
is the usual Leibniz expression; only the chart at the base point enters.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter DifferentialGeometry.TensorLieDeriv DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem finiteJet_apply_tangentConstInChart (G : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (x : M) → Tensor0SSpace s I x) (x₀ : M) (X : E) (slots : Fin s → E) :
    metricCovariantDerivative G s T x₀
        (Fin.cons (tangentConstInChart (𝕜 := ℝ) (I := I) x₀ X x₀)
          (fun a : Fin s => tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (slots a) x₀)) =
      covariantDerivTensor0SModelAt (𝕜 := ℝ) (E := E) s
        (fderivWithin ℝ
          (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
          (Set.range I) (extChartAt I x₀ x₀) X)
        (connectionEndomorphismInChartL (𝕜 := ℝ) (I := I)
          (leviCivitaConnectionOfMetric G) x₀ (extChartAt I x₀ x₀) X)
        (tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ x₀ (T x₀))
        slots := by
  simp only [tangentConstInChart_apply]
  have hslots :
      Fin.cons
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀ X)
          (fun a : Fin s =>
            (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀ (slots a)) =
      (fun a : Fin (s + 1) =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀
          ((Fin.cons X slots : Fin (s + 1) → E) a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hslots]
  rw [← tensor0SModelAt_apply (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (s + 1) x₀ x₀ (metricCovariantDerivative G s T x₀) (Fin.cons X slots)]
  unfold metricCovariantDerivative
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [totalCovDeriv_tensor0SModelAt_apply_cons]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem finiteJet_center_symmL (V : (x : M) → TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀
        (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ V (extChartAt I x₀ x₀)) = V x₀ := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  unfold tangentFieldModelInChart
  change e.symmL ℝ x₀
      (e.continuousLinearMapAt ℝ ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀)))) = V x₀
  rw [extChartAt_to_inv]
  exact e.symmL_continuousLinearMapAt (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' x₀) (V x₀)

omit [CompleteSpace E] in
private theorem finiteJet_update_center {s : ℕ} (A : (x : M) → Tensor0SSpace s I x)
    (V : Fin s → (x : M) → TangentSpace I x) (W : (x : M) → TangentSpace I x) (x₀ : M)
    (a : Fin s) :
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ A
        (extChartAt I x₀ x₀)
        (Function.update
          (fun b : Fin s => tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ (V b)
            (extChartAt I x₀ x₀))
          a (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ W (extChartAt I x₀ x₀))) =
      A x₀ (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensor0SModelInChart_apply, extChartAt_to_inv]
  congr
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [Function.update_self]
    exact finiteJet_center_symmL W x₀
  · simp only [Function.update_of_ne hb]
    exact finiteJet_center_symmL (V b) x₀

omit [CompleteSpace E] in
private theorem finiteJet_eval_center_eq_mvfderiv {s : ℕ}
    (X : (x : M) → TangentSpace I x) (β : (x : M) → Tensor0SSpace s I x)
    (V : Fin s → (x : M) → TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p : M => β p (fun a : Fin s => V a p)) x₀) :
    fderivWithin ℝ
        (fun y : E =>
          tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ β y
            (fun a : Fin s => tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x₀
          (X x₀)) =
      mvfderiv I (fun p : M => β p (fun a : Fin s => V a p)) x₀ (X x₀) := by
  let φ : E → ℝ := fun y : E =>
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ β y
      (fun a : Fin s => tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ (V a) y)
  let f : M → ℝ := fun p : M => β p (fun a : Fin s => V a p)
  have hzRange : extChartAt I x₀ x₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have heq : φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)] writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hbase (V a ((extChartAt I x₀).symm y))
  have hX : (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x₀
      (X x₀) = X x₀ := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := x₀) (x := x₀)
      (mem_chart_source H x₀), mfderiv_extChartAt_self]
    rfl
  change fderivWithin ℝ φ (Set.range I) (extChartAt I x₀ x₀) _ = _
  rw [heq.fderivWithin_eq_of_mem hzRange, hX]
  unfold mvfderiv
  rw [hpair.mfderiv]
  rfl

/-- **Leibniz evaluation (G1.a).** For an arbitrary section `T` whose chart representative at
`x₀` is differentiable there, `∇T(x₀)` evaluated on smooth vector fields is the derivative of the
contraction minus the connection terms. -/
theorem metricCovariantDerivative_apply_smooth_slots (G : SmoothRiemannianMetric I M) {s : ℕ}
    (T : (x : M) → Tensor0SSpace s I x) (x₀ : M)
    (hT : DifferentiableWithinAt ℝ
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
      (Set.range I) (extChartAt I x₀ x₀))
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hpair : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p : M => T p (fun a : Fin s => V a p)) x₀) :
    metricCovariantDerivative G s T x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      mvfderiv I (fun p : M => T p (fun a : Fin s => V a p)) x₀ (X x₀) -
        ∑ a : Fin s, T x₀ (Function.update (fun b : Fin s => V b x₀) a
          ((leviCivitaConnectionOfMetric G (fun p : M => V a p) x₀) (X x₀))) := by
  classical
  let cov := leviCivitaConnectionOfMetric G
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let y₀ : E := extChartAt I x₀ x₀
  let Xc : E := e.continuousLinearMapAt ℝ x₀ (X x₀)
  let αm := tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T
  let Vm : Fin s → E → E := fun a =>
    tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ (fun p : M => V a p)
  let slots : Fin s → E := fun a => Vm a y₀
  have hV_at : ∀ a : Fin s, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
    fun a => (V a).contMDiff.contMDiffAt
  have hVmodel : ∀ a : Fin s, DifferentiableWithinAt ℝ (Vm a) (Set.range I) y₀ := fun a =>
    tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x₀ (hV_at a)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun p : M => (Module.finBasis ℝ E).coord i (Vm a (extChartAt I x₀ p))) x₀ := by
    intro a i
    have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun p : M => (e ⟨p, V a p⟩).2) x₀ :=
      (e.contMDiffAt_section_iff hx).mp (hV_at a)
    have hsc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun p : M => (Module.finBasis ℝ E).coord i ((e ⟨p, V a p⟩).2)) x₀ :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiffAt.comp x₀ hc
    have heq : (fun p : M => (Module.finBasis ℝ E).coord i (Vm a (extChartAt I x₀ p)))
        =ᶠ[𝓝 x₀] fun p : M => (Module.finBasis ℝ E).coord i ((e ⟨p, V a p⟩).2) := by
      filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
      have hp_source : p ∈ (extChartAt I x₀).source := by
        simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
      have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
        (extChartAt I x₀).left_inv hp_source
      have hcoe : ⇑(e.linearMapAt ℝ p) = fun z => (e ⟨p, z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := ℝ) hp
      simp only [Vm]
      unfold tangentFieldModelInChart
      rw [hleft]
      change (Module.finBasis ℝ E).coord i (e.linearMapAt ℝ p (V a p)) =
        (Module.finBasis ℝ E).coord i ((e ⟨p, V a p⟩).2)
      rw [hcoe]
    exact (hsc.congr_of_eventuallyEq heq).mdifferentiableAt (by simp)
  have hmpull : tangentSpaceModelContinuousLinearEquiv y₀
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
        (fun y : M => X y) (Set.range I) y₀) = Xc := by
    simp only [y₀, Xc, e, VectorField.mpullbackWithin_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
    rw [extChartAt_to_inv]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (x₀ := x₀) (x := x₀) (mem_chart_source H x₀)]
    rw [mfderiv_extChartAt_self]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀
          (fun p : M => (cov (fun q : M => V a q) p) (X p)) y₀ =
        fderivWithin ℝ (Vm a) (Set.range I) y₀ Xc +
          connectionEndomorphismInChart (𝕜 := ℝ) (I := I) cov (fun x => X x) x₀ y₀
            (slots a) := by
    intro a
    have h := covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
      (I := I) cov X (fun p : M => V a p) x₀ ((hV_at a).mdifferentiableAt (by simp))
      (hVmodel a) (hcoord a)
    rw [h]
    congr 2
  have hslot : (fun a : Fin s => tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (slots a) x₀) =
      fun a : Fin s => V a x₀ := by
    funext a
    rw [tangentConstInChart_apply]
    exact finiteJet_center_symmL (fun p : M => V a p) x₀
  have hXslot : tangentConstInChart (𝕜 := ℝ) (I := I) x₀ Xc x₀ = X x₀ :=
    tangentConstInChart_self_continuousLinearMapAt (I := I) x₀ (X x₀)
  have hΓ (v : E) : connectionEndomorphismInChartL (𝕜 := ℝ) (I := I) cov x₀ y₀ Xc v =
      connectionEndomorphismInChart (𝕜 := ℝ) (I := I) cov (fun x => X x) x₀ y₀ v :=
    connectionEndomorphismInChartL_apply_center_modelVector (I := I) cov (fun x => X x) x₀ v
  have hprod := fderivWithin_tensor0SModel_eval_slots (𝕜 := ℝ) (E := E) (s := s) αm Vm
    (Set.range I) y₀ Xc hT hVmodel
    (I.uniqueDiffOn y₀ (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv := finiteJet_eval_center_eq_mvfderiv (fun p : M => X p) T
    (fun a p => V a p) x₀ hpair
  have hcorr : ∀ a : Fin s,
      αm y₀ (Function.update slots a (fderivWithin ℝ (Vm a) (Set.range I) y₀ Xc +
          connectionEndomorphismInChart (𝕜 := ℝ) (I := I) cov (fun x => X x) x₀ y₀
            (slots a))) =
        T x₀ (Function.update (fun b : Fin s => V b x₀) a
          ((leviCivitaConnectionOfMetric G (fun p : M => V a p) x₀) (X x₀))) := by
    intro a
    rw [← hcov_model a]
    exact finiteJet_update_center T (fun b p => V b p)
      (fun p : M => (cov (fun q : M => V a q) p) (X p)) x₀ a
  have hpd : fderivWithin ℝ (fun y : E => αm y (fun a : Fin s => Vm a y)) (Set.range I) y₀ Xc =
      mvfderiv I (fun p : M => T p (fun a : Fin s => V a p)) x₀ (X x₀) := hpair_deriv
  have key := finiteJet_apply_tangentConstInChart G s T x₀ Xc slots
  rw [hslot, hXslot, covariantDeriv_tensor0SModelAt_apply_slots,
    ← tensor0SModelInChart_center_eq_tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I)
      (M := M) s x₀ T] at key
  rw [key]
  change fderivWithin ℝ αm (Set.range I) y₀ Xc slots -
      ∑ a : Fin s, αm y₀ (Function.update slots a
        (connectionEndomorphismInChartL (𝕜 := ℝ) (I := I) cov x₀ y₀ Xc (slots a))) = _
  simp only [hΓ]
  rw [← hpd, hprod, Finset.sum_congr rfl (fun a _ => (hcorr a).symm)]
  simp only [(αm y₀).map_update_add, Finset.sum_add_distrib]
  abel

end DifferentialGeometry.Geometry.Connection
