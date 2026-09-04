import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private lemma metric_conn_model
    (g : SmoothRiemannianMetric I M) (x : M) (X v : E) :
    connectionEndomorphismInChartL (I := I) (LeviCivita (I := I) g) x
        (extChartAt I x x) X v =
      chartChristoffelContraction (I := I) g x X v (extChartAt I x x) := by
  classical
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    mem_extChartAt_target (I := I) x
  rw [connectionEndomorphismInChartL_apply_of_mem
    (I := I) (cov := LeviCivita (I := I) g) (x₀ := x) htarget]
  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) x
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hsmooth : MDiffAt
      (T% (tangentConstInChart (I := I) x v :
        (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (x₀ := x) v hbase
  rw [extChartAt_to_inv]
  rw [LeviCivita_chart_apply (I := I) g x hgood hsmooth]
  rw [chartLeviCivita_apply (I := I) g x _ hgood]
  rw [correction_eq_contr (I := I)]
  rw [trivToE_trivFromE (I := I) x hbase]
  rw [trivToE_trivFromE (I := I) x hbase]
  have hrepr :
      (chartESectionRepr (I := I) x
          (tangentConstInChart (I := I) x v) ∘ (extChartAt I x).symm)
        =ᶠ[𝓝 (extChartAt I x x)] fun _ : E => v := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds htarget] with y hy
    have hsource : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hy
    have hpbase : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hsource
    change
      trivToE (I := I) x ((extChartAt I x).symm y)
          (trivFromE (I := I) x ((extChartAt I x).symm y) v) = v
    exact trivToE_trivFromE (I := I) x hpbase v
  have hrepr_center := hrepr.eq_of_nhds
  simp only [Function.comp_apply, extChartAt_to_inv] at hrepr_center
  rw [hrepr.fderiv_eq, fderiv_const_apply]
  simp only [zero_apply, zero_add, hrepr_center]

omit [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank Real E)] in
private lemma model_eval_deriv {s : ℕ}
    (A : E → Tensor0SModel (𝕜 := Real) (E := E) s)
    (u : Real → E) (V : Fin s → Real → E) (t : Real)
    (hA : DifferentiableAt Real A (u t))
    (hu : DifferentiableAt Real u t)
    (hV : ∀ a, DifferentiableAt Real (V a) t) :
    HasDerivAt (fun r => A (u r) (fun a => V a r))
      (fderiv Real A (u t) (deriv u t) (fun a => V a t) +
        ∑ a, A (u t)
          (Function.update (fun b => V b t) a (deriv (V a) t))) t := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  have hAc := (hA.comp t hu).hasDerivAt
  have h := hAc.hasFDerivAt.continuousMultilinearMap_apply
    (fun a => (hV a).hasDerivAt.hasFDerivAt)
  have hcomp : deriv (A ∘ u) t =
      fderiv Real A (u t) (deriv u t) := by
    exact fderiv_comp_deriv t hA hu
  convert h.hasDerivAt using 1 <;>
    first
    | rfl
    | simp only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousMultilinearMap.apply_apply,
        ContinuousMultilinearMap.toContinuousLinearMap_apply,
        FunLike.coe_sum, Finset.sum_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul, hcomp,
        Function.comp_apply]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem tensor_eval_deriv {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (γ : Real → M) (V : Fin s → (r : Real) → TangentSpace I (γ r))
    (t : Real)
    (hγ : MDifferentiableAt 𝓘(Real, Real) I γ t)
    (hV : ∀ a, DifferentiableAt Real (chartRepAt (I := I) γ (V a) t) t) :
    HasDerivAt (fun r => A (γ r) (fun a => V a r))
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s (LeviCivita (I := I) g) A (γ t)
          (Fin.cons ((mfderiv 𝓘(Real, Real) I γ t) (1 : Real)) (fun a => V a t)) +
        ∑ a, A (γ t)
          (Function.update (fun b => V b t) a
            (covDerivAlong (I := I) g γ (V a) t))) t := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let x : M := γ t
  let e := trivializationAt E (TangentSpace I) x
  let u : Real → E := chartCurve (I := I) x γ
  let Vm : Fin s → Real → E := fun a => chartRepAt (I := I) γ (V a) t
  let Am : E → Tensor0SModel (𝕜 := Real) (E := E) s :=
    tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x (fun p => A p)
  let y : E := extChartAt I x x
  let U : E := deriv u t
  let slots : Fin s → E := fun a => Vm a t
  let Γ : E →L[Real] E :=
    connectionEndomorphismInChartL (I := I) (LeviCivita (I := I) g) x y U
  have hu : DifferentiableAt Real u t := by
    have hchart : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E)
        (fun r => extChartAt I x (γ r)) t :=
      (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t))).comp t hγ
    apply mdifferentiableAt_iff_differentiableAt.mp
    change MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E)
      (fun r => extChartAt I x (γ r)) t
    exact hchart
  have hAm : DifferentiableAt Real Am (u t) := by
    have hcd := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s x A
    have hmdiff := hcd.mdifferentiableWithinAt (by simp)
    have hat : MDifferentiableAt 𝓘(Real, E)
        𝓘(Real, Tensor0SModel (𝕜 := Real) (E := E) s) Am (u t) := by
      rw [Set.preimage_univ, Set.univ_inter,
        ModelWithCorners.Boundaryless.range_eq_univ (I := I)] at hmdiff
      exact mdifferentiableWithinAt_univ.mp hmdiff
    exact mdifferentiableAt_iff_differentiableAt.mp hat
  have hmodel := model_eval_deriv Am u Vm t hAm hu hV
  have hbase : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hsrc : {r : Real | γ r ∈ e.baseSet} ∈ 𝓝 t :=
    hγ.continuousAt (e.open_baseSet.mem_nhds (by simpa [x] using hbase))
  have heval :
      (fun r => A (γ r) (fun a => V a r)) =ᶠ[𝓝 t]
        fun r => Am (u r) (fun a => Vm a r) := by
    filter_upwards [hsrc] with r hr
    rw [tensor0SModelInChart_apply]
    simp only [u, chartCurve_def]
    have hsource : γ r ∈ (extChartAt I x).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hr
    rw [(extChartAt I x).left_inv hsource]
    congr 1
    funext a
    change V a r = e.symmL Real (γ r)
      (e.continuousLinearMapAt Real (γ r) (V a r))
    exact (e.symmL_continuousLinearMapAt (R := Real) hr (V a r)).symm
  refine (hmodel.congr_of_eventuallyEq heval).congr_deriv ?_
  have hy : u t = y := by
    simp only [u, y, x, chartCurve_def]
  have hUcoord : e.continuousLinearMapAt Real x
      ((mfderiv 𝓘(Real, Real) I γ t) (1 : Real)) = U := by
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) hγ x (mem_chart_source H (γ t))
    change e.continuousLinearMapAt Real x
        ((mfderiv 𝓘(Real, Real) I γ t) (1 : Real)) =
      (fderiv Real ((extChartAt I x) ∘ γ) t) (1 : Real)
    exact hbridge
  have hvel : tangentConstInChart (I := I) x U x =
      (mfderiv 𝓘(Real, Real) I γ t) (1 : Real) := by
    rw [← hUcoord]
    exact tangentConstInChart_self_continuousLinearMapAt
      (I := I) x ((mfderiv 𝓘(Real, Real) I γ t) (1 : Real))
  have hslot : ∀ a, tangentConstInChart (I := I) x (slots a) x = V a t := by
    intro a
    exact tangentConstInChart_self_continuousLinearMapAt (I := I) x (V a t)
  have hnabla := totalNabla0SFun_apply_tangentConstInChart
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    s (LeviCivita (I := I) g) A x U slots
  rw [covariantDeriv_tensor0SModelAt_apply_slots,
    ModelWithCorners.Boundaryless.range_eq_univ (I := I), fderivWithin_univ] at hnabla
  rw [← tensor0SModelInChart_center_eq_tensor0SModelAt] at hnabla
  rw [hvel] at hnabla
  simp_rw [hslot] at hnabla
  have hnabla' :
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s (LeviCivita (I := I) g) A x
          (Fin.cons ((mfderiv 𝓘(Real, Real) I γ t) (1 : Real)) (fun a => V a t)) =
        fderiv Real Am y U slots -
          ∑ a, Am y (Function.update slots a (Γ (slots a))) := by
    simpa only [Am, y, Γ] using hnabla
  have hDcoord : ∀ a, e.continuousLinearMapAt Real x
      (covDerivAlong (I := I) g γ (V a) t) =
        deriv (Vm a) t + Γ (slots a) := by
    intro a
    have hcoord := covDerivAlong_chartCoord (I := I) g γ (V a) t
    change e.continuousLinearMapAt Real x
        (covDerivAlong (I := I) g γ (V a) t) = _ at hcoord
    rw [hcoord, chartCovDerivAlong_def]
    change deriv (Vm a) t +
        chartChristoffelContraction (I := I) g x U (slots a) y =
      deriv (Vm a) t + Γ (slots a)
    rw [metric_conn_model]
  have hslotD : ∀ a,
      A x (Function.update (fun b => V b t) a
          (covDerivAlong (I := I) g γ (V a) t)) =
        Am y (Function.update slots a (deriv (Vm a) t + Γ (slots a))) := by
    intro a
    rw [← hDcoord a]
    rw [show Am y = tensor0SModelAt (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) s x x (A x) by
      simpa only [Am, y] using
        tensor0SModelInChart_center_eq_tensor0SModelAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s x (fun p => A p)]
    rw [tensor0SModelAt_apply]
    congr 1
    funext b
    by_cases hb : b = a
    · subst b
      simp only [Function.update_self]
      exact (e.symmL_continuousLinearMapAt (R := Real) hbase _).symm
    · simp only [Function.update_of_ne hb]
      exact (symmL_chartRepAt_self (I := I) γ (V b) t).symm
  change
    fderiv Real Am (u t) U slots +
        ∑ a, Am (u t) (Function.update slots a (deriv (Vm a) t)) = _
  rw [hy, hnabla']
  change _ = _ + ∑ a, A x
    (Function.update (fun b => V b t) a
      (covDerivAlong (I := I) g γ (V a) t))
  simp_rw [hslotD]
  simp_rw [(Am y).map_update_add]
  rw [Finset.sum_add_distrib]
  abel

end CovariantDerivativeAlong
end Riemannian
end Geometry
end DifferentialGeometry
