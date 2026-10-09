import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The covariant derivative of a raw tensor at an interior coordinate point
depends only on its coordinate jets through order one. No global regularity
of either tensor is required. -/
theorem metricCovariantDerivative_eq_of_coordinate_one_jet
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : (y : M) → Tensor0SSpace s I y) (x : M)
    (hx : Set.range I ∈ 𝓝 (extChartAt I x x))
    (hjet : ∀ k ≤ 1,
      iteratedFDeriv ℝ k (tensor0SModelInChart s x A) (extChartAt I x x) =
        iteratedFDeriv ℝ k (tensor0SModelInChart s x B) (extChartAt I x x)) :
    metricCovariantDerivative g s A x = metricCovariantDerivative g s B x := by
  have hvalue : tensor0SModelAt s x x (A x) = tensor0SModelAt s x x (B x) := by
    have hzero := congrArg (fun T => T (fun i : Fin 0 => Fin.elim0 i))
      (hjet 0 (by omega))
    simpa only [iteratedFDeriv_zero_apply,
      tensor0SModelInChart_center_eq_tensor0SModelAt] using hzero
  have hderiv :
      fderiv ℝ (tensor0SModelInChart s x A) (extChartAt I x x) =
        fderiv ℝ (tensor0SModelInChart s x B) (extChartAt I x x) := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [iteratedFDeriv_one_apply] using
      congrArg (fun T => T (fun _ : Fin 1 => v)) (hjet 1 (by omega))
  unfold metricCovariantDerivative
  rw [fderivWithin_of_mem_nhds hx, fderivWithin_of_mem_nhds hx, hderiv, hvalue]

private theorem tensor0SModelAt_apply_center_coordinates (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) (slots : Fin s → TangentSpace I x) :
    tensor0SModelAt s x x T
        (fun a => (trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
          ℝ x (slots a)) = T slots := by
  rw [tensor0SModelAt_apply]
  congr 1
  funext a
  exact (trivializationAt E (TangentSpace I : M → Type _) x).symmL_continuousLinearMapAt
    (R := ℝ)
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x) (slots a)

private theorem metricCovariantDerivative_apply_eq_local
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : (y : M) → Tensor0SSpace s I y)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x) :
    metricCovariantDerivative g s A x (Fin.cons (X x) slots) =
      localCovariantDerivTensor0SAt s (leviCivitaConnectionOfMetric g) X A x slots := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let z := extChartAt I x x
  let Xm : E := e.continuousLinearMapAt ℝ x (X x)
  let vm : Fin s → E := fun a => e.continuousLinearMapAt ℝ x (slots a)
  have hcons :
      (fun a : Fin (s + 1) => e.continuousLinearMapAt ℝ x
        ((Fin.cons (X x) slots : Fin (s + 1) → TangentSpace I x) a)) =
          Fin.cons Xm vm := by
    funext a
    cases a using Fin.cases <;> rfl
  have htotal :
      metricCovariantDerivative g s A x (Fin.cons (X x) slots) =
        covariantDerivTensor0SModelAt s
          (fderivWithin ℝ (tensor0SModelInChart s x A) (Set.range I) z Xm)
          (connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x z Xm)
          (tensor0SModelAt s x x (A x)) vm := by
    rw [← tensor0SModelAt_apply_center_coordinates (s + 1) x
      (metricCovariantDerivative g s A x) (Fin.cons (X x) slots)]
    change tensor0SModelAt (s + 1) x x (metricCovariantDerivative g s A x)
      (fun a => e.continuousLinearMapAt ℝ x
        ((Fin.cons (X x) slots : Fin (s + 1) → TangentSpace I x) a)) = _
    rw [hcons]
    unfold metricCovariantDerivative
    rw [tensor0SModelAt_trivializationAt_symm, totalCovDeriv_tensor0SModelAt_apply_cons]
  have hlocal :
      localCovariantDerivTensor0SAt s (leviCivitaConnectionOfMetric g) X A x slots =
        covariantDerivTensor0SModelAt s
          (fderivWithin ℝ (tensor0SModelInChart s x A) (Set.range I) z Xm)
          (connectionEndomorphismInChart (leviCivitaConnectionOfMetric g)
            (fun y => X y) x z)
          (tensor0SModelInChart s x A z) vm := by
    rw [← tensor0SModelAt_apply_center_coordinates s x
      (localCovariantDerivTensor0SAt s (leviCivitaConnectionOfMetric g) X A x) slots]
    unfold localCovariantDerivTensor0SAt
    rw [tensor0SModelAt_trivializationAt_symm]
    unfold covariantDerivTensor0SModelWithin
    rw [vector_field_model_pullback_within_eq_mpullback_within]
    have hX : VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
        (fun y : M => X y) (Set.range I) z = Xm := by
      simp only [z, Xm, e, VectorField.mpullbackWithin_apply]
      rw [extChartAt_to_inv]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt
        (I := I) (x₀ := x) (x := x) (mem_chart_source H x)]
      rw [mfderiv_extChartAt_self]
      exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (X x)
    rw [hX]
  have hΓ :
      connectionEndomorphismInChartL (leviCivitaConnectionOfMetric g) x z Xm =
        connectionEndomorphismInChart (leviCivitaConnectionOfMetric g)
          (fun y => X y) x z := by
    apply ContinuousLinearMap.ext
    intro v
    exact connectionEndomorphismInChartL_apply_center_modelVector
      (leviCivitaConnectionOfMetric g) (fun y => X y) x v
  rw [htotal, hlocal, hΓ]
  rw [show z = extChartAt I x x from rfl,
    tensor0SModelInChart_center_eq_tensor0SModelAt]

private theorem tensor0SModelInChart_differentiableWithinAt_of_contMDiffAt_one
    (s : ℕ) (A : (y : M) → Tensor0SSpace s I y) (x : M)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun y => (⟨y, A y⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun z => Tensor0SSpace s I z))) x) :
    DifferentiableWithinAt ℝ (tensor0SModelInChart s x A)
      (Set.range I) (extChartAt I x x) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun y => Tensor0SSpace s I y) x
  have hx : x ∈ e.baseSet :=
    mem_baseSet_trivializationAt (Tensor0SModel s ℝ E) (fun y => Tensor0SSpace s I y) x
  have hcoord : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) 1
      (fun y => (e ⟨y, A y⟩).2) x := (e.contMDiffAt_section_iff hx).mp hA
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I 1 (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 1) x
  have hcoord' : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) 1
      (fun y => (e ⟨y, A y⟩).2) ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hcoord
  have hcomp := hcoord'.comp_contMDiffWithinAt (x := extChartAt I x x) hsymm
  have hmodel : ContDiffWithinAt ℝ 1 (tensor0SModelInChart s x A)
      (Set.range I) (extChartAt I x x) := by
    change ContDiffWithinAt ℝ 1
      ((fun p : M => (e ⟨p, A p⟩).2) ∘ (extChartAt I x).symm)
      (Set.range I) (extChartAt I x x)
    exact hcomp.contDiffWithinAt
  exact hmodel.differentiableWithinAt (by norm_num)

/-- The intrinsic Leibniz formula for the covariant derivative of a raw `C¹`
tensor and `C¹` slot fields at the selected point. -/
theorem metricCovariantDerivative_apply_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : (y : M) → Tensor0SSpace s I y)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin s → (y : M) → TangentSpace I y) (x : M)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun y => (⟨y, A y⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun z => Tensor0SSpace s I z))) x)
    (hV : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    metricCovariantDerivative g s A x (Fin.cons (X x) (fun a => V a x)) =
      mvfderiv (I := I) (fun y => A y (fun a => V a y)) x (X x) -
        ∑ a, A x (Function.update (fun b => V b x) a
          ((leviCivitaConnectionOfMetric g (V a) x) (X x))) := by
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => A y (fun a => V a y)) x :=
    (TensorMultilinear.contMDiffAt_section_apply_one A hA V hV).mdifferentiableAt
      (by norm_num)
  have hmodel := tensor0SModelInChart_differentiableWithinAt_of_contMDiffAt_one s A x hA
  rw [metricCovariantDerivative_apply_eq_local]
  exact localCovariantDerivTensor0SAt_eval_moving
    (leviCivitaConnectionOfMetric g) X A V x hpair hmodel
    (fun a => (hV a).mdifferentiableAt (by norm_num))
    (fun a => tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt_one
      (V a) x (hV a))
    (fun a i => tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt_one
      (V a) x (hV a) i)

end DifferentialGeometry.Geometry.Connection
