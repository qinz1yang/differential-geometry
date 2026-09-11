import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.MapConvergence

import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSpray
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
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

omit [CompleteSpace E] in
theorem metric_tower_convergence
    {U : Set E} (hU : IsOpen U) (e : Module.Basis Idx Real E)
    (g q : Nat → E → E →L[Real] E →L[Real] Real)
    (gInf : E → E →L[Real] E →L[Real] Real)
    (hg : MapCInfConvergenceOnCompacts U g gInf)
    (hq : MapCInfConvergenceOnCompacts U q gInf)
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hq_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (q n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n z, z ∈ U → IsCoercive (g n z))
    (hgInf_co : ∀ z, z ∈ U → IsCoercive (gInf z))
    (a : Nat) :
    MapCInfConvergenceOnCompacts U
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
  have hpair : MapCInfConvergenceOnCompacts U pair pairInf := by
    exact mapCInfConvergence_prodMk hU hq hg hq_cd hgInf_cd hg_cd hgInf_cd
  have hpair_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (pair n) U :=
    fun n => (hq_cd n).prodMk (hg_cd n)
  have hpairInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) pairInf U :=
    hgInf_cd.prodMk hgInf_cd
  let errComp := (metricComp e).comp (metricSub (E := E))
  have hbase : MapCInfConvergenceOnCompacts U
      (fun n z => errComp (pair n z)) (fun z => errComp (pairInf z)) :=
    mapCInfConvergence_clm hU errComp hpair hpair_cd hpairInf_cd
  have hbase_zero : MapCInfConvergenceOnCompacts U
      (fun n z => errComp (pair n z))
      (fun (_ : E) (_ : Fin 2 → Idx) => (0 : Real)) := by
    have hlim : (fun z => errComp (pairInf z)) =
        (fun (_ : E) (_ : Fin 2 → Idx) => (0 : Real)) := by
      funext z i
      unfold pairInf errComp metricSub metricComp
      change (gInf z - gInf z) (e (i 0)) (e (i 1)) = 0
      rw [sub_self]
      rfl
    rw [← hlim]
    exact hbase
  have hbase_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => errComp (pair n z)) U :=
    fun n => errComp.contDiff.comp_contDiffOn (hpair_cd n)
  let raised : Nat → E → E →L[Real] E →L[Real] E := fun n z =>
    MetricKoszul.raisedKoszulOp (g n z) (fderiv Real (g n) z)
  let raisedInf : E → E →L[Real] E →L[Real] E := fun z =>
    MetricKoszul.raisedKoszulOp (gInf z) (fderiv Real gInf z)
  have hraised : MapCInfConvergenceOnCompacts U raised raisedInf := by
    exact MetricKoszul.raisedKoszulOp_convergence hU hg_cd hgInf_cd hg_co hgInf_co hg
  have hraised_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (raised n) U :=
    fun n => MetricKoszul.raisedOp_smooth hU (hg_cd n) (hg_co n)
  have hraisedInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) raisedInf U :=
    MetricKoszul.raisedOp_smooth hU hgInf_cd hgInf_co
  let chr := fun n z => christoffelComp e (raised n z)
  let chrInf := fun z => christoffelComp e (raisedInf z)
  have hchr : MapCInfConvergenceOnCompacts U chr chrInf :=
    mapCInfConvergence_clm hU (christoffelComp e) hraised hraised_cd hraisedInf_cd
  have hchr_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (chr n) U :=
    fun n => (christoffelComp e).contDiff.comp_contDiffOn (hraised_cd n)
  have hchrInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) chrInf U :=
    (christoffelComp e).contDiff.comp_contDiffOn hraisedInf_cd
  have hchr_eq : chr = fun n z i j k =>
      e.coord k (MetricKoszul.raisedKoszulOp (g n z) (fderiv Real (g n) z) (e i) (e j)) := by
    funext n z i j k
    rfl
  have herr_eq : (fun n z => errComp (pair n z)) = fun n z s =>
      (q n z - g n z) (e (s 0)) (e (s 1)) := by
    funext n z s
    rfl
  have hiter := iter_comp_zero hU (fun i => e i) chr chrInf
    (fun n z => errComp (pair n z)) hchr hbase_zero hchr_cd hchrInf_cd hbase_cd a
  rw [hchr_eq] at hiter
  convert hiter using 1
  funext n
  exact congrArg
    (fun B => iterCovComp (I := 𝓘(Real, E)) (fun i _ => e i)
      (fun z i j k =>
        e.coord k (MetricKoszul.raisedKoszulOp (g n z) (fderiv Real (g n) z) (e i) (e j)))
      B a)
    (congrFun herr_eq n).symm

end DifferentialGeometry.PDE.RicciFlow
