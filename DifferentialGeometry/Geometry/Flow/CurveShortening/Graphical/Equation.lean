import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.SmoothData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Connection.ProductAlongCurve
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import DifferentialGeometry.Geometry.Connection.LeviCivita.AddCircle
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.Euclidean

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def graph (f : CurveMap F) : CurveMap (AddCircle (1 : ℝ) × F) :=
  fun z t => (z, f z t)

theorem X_graph (f : CurveMap F) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) :
    (graph f).X (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) x t =
      (AddCircle.parameterTangent (x : AddCircle (1 : ℝ)),
        deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) := by
  unfold X lift graph
  rw [mfderiv_prodMk (AddCircle.contMDiff_coe.mdifferentiableAt (by simp))
    hf.mdifferentiableAt]
  rw [mfderiv_eq_fderiv]
  exact Prod.ext (AddCircle.parameterTangent_coe x).symm rfl

theorem graph_immersedOn (f : CurveMap F) (J : Set ℝ)
    (hf : ∀ x t, t ∈ J →
      DifferentiableAt ℝ (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) :
    (graph f).ImmersedOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) J := by
  intro x t ht hzero
  rw [X_graph f x t (hf x t ht)] at hzero
  exact AddCircle.parameterTangent_ne_zero _ (congrArg Prod.fst hzero)

theorem velocity_graph (f : CurveMap F) (J : Set ℝ) (x t : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hf : DifferentiableWithinAt ℝ (f (x : AddCircle (1 : ℝ))) J t) :
    (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) J x t =
      (0, derivWithin (f (x : AddCircle (1 : ℝ))) J t) := by
  unfold velocity lift graph
  rw [mfderivWithin_prodMk mdifferentiableWithinAt_const hf.mdifferentiableWithinAt hJ.uniqueMDiffWithinAt]
  rw [mfderivWithin_const, mfderivWithin_eq_fderivWithin]
  rfl

end

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem speed_graph_sq (f : CurveMap F) (x t : ℝ)
    (hf : DifferentiableAt ℝ (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) :
    ((graph f).speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F))) x t) ^ 2 =
      1 + ‖deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x‖ ^ 2 := by
  unfold speed
  rw [X_graph f x t hf]
  change Real.sqrt ((AddCircle.flatMetric.prod (euclideanMetric (E := F))).inner
    ((x : AddCircle (1 : ℝ)), f (x : AddCircle (1 : ℝ)) t)
    (AddCircle.parameterTangent (x : AddCircle (1 : ℝ)),
      deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x)
    (AddCircle.parameterTangent (x : AddCircle (1 : ℝ)),
      deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x)) ^ 2 = _
  erw [SmoothRiemannianMetric.prod_inner,
    AddCircle.flatMetric_parameterTangent_unit, euclideanMetric_inner]
  change Real.sqrt (1 + inner ℝ
    (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x)
    (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x)) ^ 2 = _
  rw [real_inner_self_eq_norm_sq, Real.sq_sqrt]
  positivity

theorem Dx_X_graph (f : CurveMap F) (t x : ℝ)
    (hf : ContDiffAt ℝ 2 (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) :
    (graph f).Dx (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
      (graph f).X x t =
        (0, deriv (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t)) x) := by
  have hX : ∀ᶠ y in 𝓝 x,
      (graph f).X (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) y t =
        (AddCircle.parameterTangent (y : AddCircle (1 : ℝ)),
          deriv (fun z : ℝ => f (z : AddCircle (1 : ℝ)) t) y) := by
    filter_upwards [hf.eventually (by decide)] with y hy
    exact X_graph f y t (hy.differentiableAt (by decide))
  unfold Dx
  rw [DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (AddCircle.flatMetric.prod (euclideanMetric (E := F))) _ _
    (Filter.EventuallyEq.refl _ _) hX]
  have hcircle : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent
      (fun y : ℝ => (⟨(y : AddCircle (1 : ℝ)),
        AddCircle.parameterTangent (y : AddCircle (1 : ℝ))⟩ :
          TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) x :=
    (AddCircle.contMDiff_parameterTangent.comp AddCircle.contMDiff_coe).mdifferentiableAt
      (by decide)
  have heuclidean : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F).tangent
      (fun y : ℝ => (⟨f (y : AddCircle (1 : ℝ)) t,
        deriv (fun z : ℝ => f (z : AddCircle (1 : ℝ)) t) y⟩ :
          TangentBundle 𝓘(ℝ, F) F)) x := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨(hf.differentiableAt (by decide)).mdifferentiableAt, ?_⟩
    have heq : (fun y : ℝ =>
        ((trivializationAt F (TangentSpace 𝓘(ℝ, F))
          (f (x : AddCircle (1 : ℝ)) t))
            ⟨f (y : AddCircle (1 : ℝ)) t,
              deriv (fun z : ℝ => f (z : AddCircle (1 : ℝ)) t) y⟩).2) =
        deriv (fun z : ℝ => f (z : AddCircle (1 : ℝ)) t) := by
      funext y
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
        _ (by simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]),
        TangentBundle.continuousLinearMapAt_model_space]
      rfl
    rw [heq]
    exact ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by decide)).mdifferentiableAt
  have hsplit := DifferentialGeometry.Geometry.Connection.covDerivAlong_prod
    AddCircle.flatMetric (euclideanMetric (E := F))
    (fun y : ℝ => (y : AddCircle (1 : ℝ)))
    (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t)
    (fun y : ℝ => AddCircle.parameterTangent (y : AddCircle (1 : ℝ)))
    (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t)) x hcircle heuclidean
  change DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
    (AddCircle.flatMetric.prod (euclideanMetric (E := F)))
    (fun y : ℝ => ((y : AddCircle (1 : ℝ)), f (y : AddCircle (1 : ℝ)) t))
    (fun y : ℝ => (AddCircle.parameterTangent (y : AddCircle (1 : ℝ)),
      deriv (fun z : ℝ => f (z : AddCircle (1 : ℝ)) t) y)) x = _
  rw [hsplit, AddCircle.covDerivAlong_coe_parameterTangent_eq_zero,
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_euclideanMetric_eq_deriv]
  rfl

theorem graph_parabolic_equation_iff (f : CurveMap F) (J : Set ℝ) (x t : ℝ)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (ht : DifferentiableWithinAt ℝ (f (x : AddCircle (1 : ℝ))) J t)
    (hx : ContDiffAt ℝ 2 (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x) :
    (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) J x t =
        ((graph f).speed (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
          x t) ^ (-2 : ℤ) •
            (graph f).Dx (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F)))
              (graph f).X x t ↔
      derivWithin (f (x : AddCircle (1 : ℝ))) J t =
        (1 + ‖deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x‖ ^ 2)⁻¹ •
          deriv (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t)) x := by
  have hs : ((graph f).speed
      (fun _ => AddCircle.flatMetric.prod (euclideanMetric (E := F))) x t) ^ (-2 : ℤ) =
        (1 + ‖deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x‖ ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat, speed_graph_sq f x t (hx.differentiableAt (by decide))]
  rw [velocity_graph f J x t hJ ht, Dx_X_graph f t x hx, hs]
  change (0, derivWithin (f (x : AddCircle (1 : ℝ))) J t) =
    ((1 + ‖deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x‖ ^ 2)⁻¹ • (0 : ℝ),
      (1 + ‖deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t) x‖ ^ 2)⁻¹ •
        deriv (deriv (fun y : ℝ => f (y : AddCircle (1 : ℝ)) t)) x) ↔ _
  simp only [smul_zero, Prod.mk.injEq, true_and]

open Set
open DifferentialGeometry.Analysis.Parabolic

theorem exists_graph_parabolic_curve_of_smooth
    {ι : Type*} [Fintype ι]
    (F₀ : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, EuclideanSpace ℝ ι), EuclideanSpace ℝ ι⟯) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : CurveMap (EuclideanSpace ℝ ι),
      (∀ z, f z 0 = F₀ z) ∧
      (∀ z, graph f z 0 = (z, F₀ z)) ∧
      ContinuousOn (fun p : ℝ × ℝ => f.lift p.2 p.1) (Icc 0 T ×ˢ univ) ∧
      (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (fun x => f.lift x t)) ∧
      (ContinuousOn (fun p : ℝ × ℝ => deriv (fun x => f.lift x p.1) p.2)
          (Icc 0 T ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (fun x => f.lift x p.1)) p.2)
          (Icc 0 T ×ˢ univ)) ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (f.lift x)
        ((1 + ‖deriv (fun y => f.lift y t) x‖ ^ 2)⁻¹ •
          deriv (deriv (fun y => f.lift y t)) x) (Icc 0 T) t) ∧
      (graph f).ImmersedOn (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ ι)) (Icc 0 T) ∧
      (∀ x t, t ∈ Icc 0 T →
        ((graph f).speed (fun _ => AddCircle.flatMetric.prod
          (euclideanMetric (E := EuclideanSpace ℝ ι))) x t) ^ 2 =
            1 + ‖deriv (fun y => f.lift y t) x‖ ^ 2) ∧
      ∀ x t, t ∈ Icc 0 T →
        (graph f).velocity (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ ι)) (Icc 0 T) x t =
          ((graph f).speed (fun _ => AddCircle.flatMetric.prod
            (euclideanMetric (E := EuclideanSpace ℝ ι))) x t) ^ (-2 : ℤ) •
            (graph f).Dx (fun _ => AddCircle.flatMetric.prod
              (euclideanMetric (E := EuclideanSpace ℝ ι))) (graph f).X x t := by
  obtain ⟨T, hT, F, hinit, hperiod, hcont, _, hC2, hjets, hwithin, _⟩ :=
    exists_graphical_curve_shortening_classical_of_smooth F₀
  let f : CurveMap (EuclideanSpace ℝ ι) := fun z t => (hperiod t).lift z
  have hdesc (x t : ℝ) : f.lift x t = F t x := by
    exact (hperiod t).lift_coe x
  have hspace (t : ℝ) : (fun x => f.lift x t) = F t := funext fun x => hdesc x t
  have htime (x : ℝ) : f.lift x = fun t => F t x := funext fun t => hdesc x t
  have hzero (z : AddCircle (1 : ℝ)) : f z 0 = F₀ z := by
    induction z using QuotientAddGroup.induction_on with
    | H x => exact (hdesc x 0).trans (hinit x)
  have hslices (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContDiff ℝ 2 (fun x => f.lift x t) := by
    rw [hspace]
    exact hC2 t ht
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) : HasDerivWithinAt (f.lift x)
      ((1 + ‖deriv (fun y => f.lift y t) x‖ ^ 2)⁻¹ •
        deriv (deriv (fun y => f.lift y t)) x) (Icc 0 T) t := by
    rw [hspace, htime]
    exact hwithin t ht x
  refine ⟨T, hT, f, hzero, ?_, ?_, hslices, ?_, hderiv, ?_, ?_, ?_⟩
  · intro z
    exact congrArg (fun y => (z, y)) (hzero z)
  · have hcont' : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 T ×ˢ univ) := hcont
    simpa only [hdesc] using hcont'
  · simpa only [hspace] using And.intro hjets.1 hjets.2.1
  · exact graph_immersedOn f _ fun x t ht => (hslices t ht).differentiable (by decide) x
  · intro x t ht
    exact speed_graph_sq f x t ((hslices t ht).differentiable (by decide) x)
  · intro x t ht
    have hJ : UniqueDiffWithinAt ℝ (Icc 0 T) t := uniqueDiffOn_Icc hT t ht
    exact (graph_parabolic_equation_iff f (Icc 0 T) x t hJ
      (hderiv t ht x).differentiableWithinAt (hslices t ht).contDiffAt).2
        ((hderiv t ht x).derivWithin hJ)


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
