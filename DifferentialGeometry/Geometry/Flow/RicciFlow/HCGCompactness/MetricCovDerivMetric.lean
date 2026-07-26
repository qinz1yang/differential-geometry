import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivConv
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricGeodesicSpray

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Metric-coefficient convergence and component covariant derivatives

This file connects smooth convergence of metric coefficients to the metric-free
component recurrence in `MetricCovDerivConv`.  The Christoffel coefficients are
read from the proof-independent raised Koszul operator in one fixed basis.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.HCGCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {Idx : Type*} [Fintype Idx]

noncomputable local instance metricBilinNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance metricBilinNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance metricVecBilinNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance metricVecBilinNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] E) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def metricSub :
    ((E →L[Real] E →L[Real] Real) × (E →L[Real] E →L[Real] Real)) →L[Real]
      (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.fst Real _ _ - ContinuousLinearMap.snd Real _ _

private noncomputable def metricComp
    (e : Module.Basis Idx Real E) :
    (E →L[Real] E →L[Real] Real) →L[Real] ((Fin 2 → Idx) → Real) :=
  ContinuousLinearMap.pi fun s =>
    (ContinuousLinearMap.apply Real Real (e (s 1))).comp
      (ContinuousLinearMap.apply Real (E →L[Real] Real) (e (s 0)))

private noncomputable def christoffelComp
    (e : Module.Basis Idx Real E) :
    (E →L[Real] E →L[Real] E) →L[Real] (Idx → Idx → Idx → Real) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.pi fun k =>
        ((e.coord k).toContinuousLinearMap).comp
          ((ContinuousLinearMap.apply Real E (e j)).comp
            (ContinuousLinearMap.apply Real (E →L[Real] E) (e i)))

/-- If two smooth bilinear-form families converge to the same coercive metric,
then every finite component covariant-derivative tower of their difference,
formed with the first family's Levi--Civita Christoffel coefficients, converges
smoothly to zero on compact subsets. -/
theorem metric_tower_conv
    {U : Set E} (hU : IsOpen U) (e : Module.Basis Idx Real E)
    (g q : Nat → E → E →L[Real] E →L[Real] Real)
    (gInf : E → E →L[Real] E →L[Real] Real)
    (hg : MapCInfConvOnCompacts U g gInf)
    (hq : MapCInfConvOnCompacts U q gInf)
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hq_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (q n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n z, z ∈ U → IsCoercive (g n z))
    (hgInf_co : ∀ z, z ∈ U → IsCoercive (gInf z))
    (a : Nat) :
    MapCInfConvOnCompacts U
      (fun n =>
        iterCovComp (I := 𝓘(Real, E)) (fun i _ => e i)
          (fun z i j k =>
            e.coord k
              (MetricKoszul.raisedKoszulOp
                (g n z) (fderiv Real (g n) z) (e i) (e j)))
          (fun z s => (q n z - g n z) (e (s 0)) (e (s 1))) a)
      (fun (_ : E) (_ : Fin (2 + a) → Idx) => (0 : Real)) := by
  let pair : Nat → E →
      (E →L[Real] E →L[Real] Real) × (E →L[Real] E →L[Real] Real) :=
    fun n z => (q n z, g n z)
  let pairInf : E →
      (E →L[Real] E →L[Real] Real) × (E →L[Real] E →L[Real] Real) :=
    fun z => (gInf z, gInf z)
  have hpair : MapCInfConvOnCompacts U pair pairInf := by
    exact mapCInfConv_prodMk hU hq hg hq_cd hgInf_cd hg_cd hgInf_cd
  have hpair_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (pair n) U :=
    fun n => (hq_cd n).prodMk (hg_cd n)
  have hpairInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) pairInf U :=
    hgInf_cd.prodMk hgInf_cd
  let errComp := (metricComp e).comp (metricSub (E := E))
  have hbase : MapCInfConvOnCompacts U
      (fun n z => errComp (pair n z)) (fun z => errComp (pairInf z)) :=
    mapCInfConv_clm hU errComp hpair hpair_cd hpairInf_cd
  have hbase_zero : MapCInfConvOnCompacts U
      (fun n z => errComp (pair n z))
      (fun (_ : E) (_ : Fin 2 → Idx) => (0 : Real)) := by
    simpa [pairInf, errComp, metricSub, metricComp] using hbase
  have hbase_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => errComp (pair n z)) U :=
    fun n => errComp.contDiff.comp_contDiffOn (hpair_cd n)
  let raised : Nat → E → E →L[Real] E →L[Real] E := fun n z =>
    MetricKoszul.raisedKoszulOp (g n z) (fderiv Real (g n) z)
  let raisedInf : E → E →L[Real] E →L[Real] E := fun z =>
    MetricKoszul.raisedKoszulOp (gInf z) (fderiv Real gInf z)
  have hraised : MapCInfConvOnCompacts U raised raisedInf := by
    exact MetricKoszul.raisedKoszulOp_conv hU hg_cd hgInf_cd hg_co hgInf_co hg
  have hraised_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (raised n) U :=
    fun n => MetricKoszul.raisedOp_smooth hU (hg_cd n) (hg_co n)
  have hraisedInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) raisedInf U :=
    MetricKoszul.raisedOp_smooth hU hgInf_cd hgInf_co
  let chr := fun n z => christoffelComp e (raised n z)
  let chrInf := fun z => christoffelComp e (raisedInf z)
  have hchr : MapCInfConvOnCompacts U chr chrInf :=
    mapCInfConv_clm hU (christoffelComp e) hraised hraised_cd hraisedInf_cd
  have hchr_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (chr n) U :=
    fun n => (christoffelComp e).contDiff.comp_contDiffOn (hraised_cd n)
  have hchrInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) chrInf U :=
    (christoffelComp e).contDiff.comp_contDiffOn hraisedInf_cd
  simpa only [pair, pairInf, errComp, metricComp, metricSub,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.pi_apply, sub_self, map_zero, chr, chrInf,
      christoffelComp, raised, raisedInf] using
    iter_comp_zero hU (fun i => e i) chr chrInf
      (fun n z => errComp (pair n z)) hchr hbase_zero hchr_cd hchrInf_cd hbase_cd a

end DifferentialGeometry.PDE.RicciFlow
