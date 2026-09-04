import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.MovingMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.ConnectionBackward
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.Jets
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeDifference
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.TensorDerivativeAlong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lRegJacobiPair
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (s : Real) (W : TangentSpace I (alpha s)) : Real :=
  let t := T - s ^ 2
  let g := S.base.metric t
  let cov := S.base.connection t
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let D2Y := covDerivAlong (I := I) g alpha
    (fun r => covDerivAlong (I := I) g alpha Y r) s
  g.inner (alpha s) W D2Y +
      S.base.rm04 t (alpha s) (vec4 (Y s) A A W) -
    2 * s ^ 2 *
      hessianSec (I := I) cov (metricCov_smooth (I := I) g)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t) (alpha s)
        (vec2 (Y s) W) +
    4 * s * totalNabla0SFun (𝕜 := Real) (I := I)
      2 cov (S.ricci t) (alpha s) (vec3 (Y s) A W) +
    4 * s * S.ricciAt t (alpha s) (vec2 DY W)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lReg_curv_pair
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (Y A W : TangentSpace I x) :
    (S.base.metric (T - s ^ 2)).inner x W
        (riemannOp (LeviCivita (I := I) (S.base.metric (T - s ^ 2))) x Y A A) =
      S.base.rm04 (T - s ^ 2) x (vec4 Y A A W) := by
  let g := S.base.metric (T - s ^ 2)
  have hcov :=
    leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  symm
  change metricRm04 (I := I) (M := M) g x (vec4 Y A A W) = _
  rw [metricRm04_apply,
    metricRm04At_eq_riemannCurvature04At,
    CovariantDerivative.riemannCurvature04At_apply_const,
    riemannCurvatureAux_tangentConst_eq_riemannOp
      (cov := LeviCivita (I := I) g) (hcov := hcov)]

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lReg_accel_var
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f) (s : Real) :
    covFstSnd (I := I) g f
        (varSnd (I := I) f) 0 s =
      covSnd2 (I := I) g f
          (varFst (I := I) f) 0 s +
        riemannOp (LeviCivita (I := I) g) (f 0 s)
          (varFst (I := I) f 0 s)
          (varSnd (I := I) f 0 s)
          (varSnd (I := I) f 0 s) := by
  have hV : ContMDiffAt
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      (I.prod 𝓘(Real, E)) 2
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varSnd (I := I) f q.1 q.2) :
            TangentBundle I M)) (0, s) := by
    simpa only [varSnd] using
      (velocity_totalSpace_contMDiff (I := I) (M := M) f hf).contMDiffAt.of_le
        (by norm_num)
  have hraw := cov_commute_at (I := I) g f
    (varSnd (I := I) f) 0 s hV
  change
    covFstSnd (I := I) g f (varSnd (I := I) f) 0 s -
        covSndFst (I := I) g f (varSnd (I := I) f) 0 s =
      riemannOp (LeviCivita (I := I) g) (f 0 s)
        (varFst (I := I) f 0 s) (varSnd (I := I) f 0 s)
        (varSnd (I := I) f 0 s) at hraw
  have hswap :
      (fun r : Real ↦ covFst (I := I) g f
        (varSnd (I := I) f) 0 r) =
        fun r : Real ↦ covSnd (I := I) g f
          (varFst (I := I) f) 0 r := by
    funext r
    simpa only [covFst, covSnd, varFst, varSnd] using
        commute_ds_dt_intrinsic (I := I) g f hf r
  have hsnd :
      covSndFst (I := I) g f
          (varSnd (I := I) f) 0 s =
        covSnd2 (I := I) g f
          (varFst (I := I) f) 0 s := by
    change
      covDerivAlong (I := I) g (fun r : Real ↦ f 0 r)
          (fun r : Real ↦ covFst (I := I) g f
            (varSnd (I := I) f) 0 r) s =
        covDerivAlong (I := I) g (fun r : Real ↦ f 0 r)
          (fun r : Real ↦ covSnd (I := I) g f
            (varFst (I := I) f) 0 r) s
    rw [hswap]
  rw [hsnd] at hraw
  linear_combination (norm := module) hraw

omit [InnerProductSpace Real E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegVar_reg
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    MDifferentiableAt 𝓘(Real, Real) I (fun r : Real ↦ f 0 r) s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) (fun r : Real ↦ f 0 r)
          (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0) s) s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) (fun r : Real ↦ f 0 r)
          (fun r : Real ↦ covDerivAlong (I := I)
            (S.base.metric (T - s ^ 2)) (fun w : Real ↦ f 0 w)
            (fun w : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u w) 0) r) s) s := by
  have hcentral : MDifferentiableAt 𝓘(Real, Real) I
      (fun r : Real ↦ f 0 r) s := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
        (fun r : Real ↦ ((0 : Real), r)) :=
      contMDiff_const.prodMk contMDiff_id
    exact ((hf : ContMDiff _ _ _ _).comp hincl).mdifferentiableAt
      (by norm_num)
  have hYdiff : DifferentiableAt Real
      (chartRepAt (I := I) (fun r : Real ↦ f 0 r)
        (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0) s) s := by
    simpa only [lVelocity, varFst] using
      variationField_chartRep_differentiableAt (I := I) f hf s
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real ↦ f b a) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hVfstAll : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) (7 : Nat)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varFst (I := I) f q.1 q.2) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real ↦ f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_snd.prodMk contMDiff_fst :
        ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real))
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : Nat)
          (fun q : Real × Real ↦ (q.2, q.1)))
    simpa only [Function.comp_def, varFst] using hcomp
  have hVfst : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) 2
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varFst (I := I) f q.1 q.2) : TangentBundle I M))
      (0, s) := hVfstAll.contMDiffAt.of_le (by norm_num)
  have hDYdiff : DifferentiableAt Real
      (chartRepAt (I := I) (fun r : Real ↦ f 0 r)
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) (fun w : Real ↦ f 0 w)
          (fun w : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u w) 0) r) s) s := by
    simpa only [lVelocity, varFst] using
      cov_snd_diff_at (I := I) (S.base.metric (T - s ^ 2)) f
        (varFst (I := I) f) 0 s hVfst
  exact ⟨hcentral, hYdiff, hDYdiff⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lReg_du_deriv
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (beta : Real → M) (W : ∀ u, TangentSpace I (beta u))
    (hbeta : MDifferentiableAt 𝓘(Real, Real) I beta 0)
    (hW : DifferentiableAt Real (chartRepAt (I := I) beta W 0) 0) :
    HasDerivAt
      (fun u : Real ↦
        duSec (I := I) (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (beta u)
          (fun _ : Fin 1 ↦ W u))
      (hessianSec (I := I)
          (LeviCivita (I := I) (S.base.metric (T - s ^ 2)))
          (leviCivita_contMDiffCovariantDerivativeLocally
            (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (beta 0)
          (vec2 (lVelocity (I := I) beta 0) (W 0)) +
        duSec (I := I) (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (beta 0)
          (fun _ : Fin 1 ↦ covDerivAlong (I := I)
            (S.base.metric (T - s ^ 2)) beta W 0)) 0 := by
  have h := tensor_eval_deriv (I := I)
    (S.base.metric (T - s ^ 2))
    (duSec (I := I) (S.scalar (T - s ^ 2))
      (scalarSmoothOfSol (I := I) S (T - s ^ 2)))
    beta (fun _ : Fin 1 ↦ W) 0 hbeta (fun _ ↦ hW)
  convert h using 1
  rw [← hessianSec_apply (cov :=
    LeviCivita (I := I) (S.base.metric (T - s ^ 2))) (hcov :=
      leviCivita_contMDiffCovariantDerivativeLocally
        (I := I) (S.base.metric (T - s ^ 2)))]
  congr 1
  · apply congrArg
    funext q
    fin_cases q <;> rfl
  · rw [Fin.sum_univ_one]
    congr 1
    funext q
    fin_cases q
    simp [Function.update]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lReg_ricci_deriv
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (beta : Real → M)
    (A W : ∀ u, TangentSpace I (beta u))
    (hbeta : MDifferentiableAt 𝓘(Real, Real) I beta 0)
    (hA : DifferentiableAt Real (chartRepAt (I := I) beta A 0) 0)
    (hW : DifferentiableAt Real (chartRepAt (I := I) beta W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ S.ricci (T - s ^ 2) (beta u) (vec2 (A u) (W u)))
      (totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (beta 0)
          (vec3 (lVelocity (I := I) beta 0) (A 0) (W 0)) +
        (S.ricci (T - s ^ 2) (beta 0)
            (vec2 (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              beta A 0) (W 0)) +
          S.ricci (T - s ^ 2) (beta 0)
            (vec2 (A 0) (covDerivAlong (I := I)
              (S.base.metric (T - s ^ 2)) beta W 0)))) 0 := by
  let slots : Fin 2 → (u : Real) → TangentSpace I (beta u) :=
    fun q u ↦ vec2 (A u) (W u) q
  have hslot0 : slots 0 = A := by
    funext u
    rfl
  have hslot1 : slots 1 = W := by
    funext u
    rfl
  let DA := covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta A 0
  let DW := covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta W 0
  have hupdate0 :
      Function.update (fun b ↦ slots b 0) 0
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta
            (slots 0) 0) =
        vec2 DA (W 0) := by
    rw [hslot0]
    change Function.update (fun b ↦ slots b 0) 0 DA = vec2 DA (W 0)
    funext q
    fin_cases q <;> rfl
  have hupdate1 :
      Function.update (fun b ↦ slots b 0) 1
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta
            (slots 1) 0) =
        vec2 (A 0) DW := by
    rw [hslot1]
    change Function.update (fun b ↦ slots b 0) 1 DW = vec2 (A 0) DW
    funext q
    fin_cases q <;> rfl
  have h := tensor_eval_deriv (I := I)
    (S.base.metric (T - s ^ 2)) (S.ricci (T - s ^ 2))
    beta slots 0 hbeta (fun q ↦ by
      fin_cases q
      · change DifferentiableAt Real (chartRepAt (I := I) beta (slots 0) 0) 0
        rw [hslot0]
        exact hA
      · change DifferentiableAt Real (chartRepAt (I := I) beta (slots 1) 0) 0
        rw [hslot1]
        exact hW)
  convert h using 1
  congr 1
  · apply congrArg
    funext q
    fin_cases q <;> rfl
  · rw [Fin.sum_univ_two, hupdate0, hupdate1]

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lReg_test_field
    (beta : Real → M) (s : Real) (hbeta : ContinuousAt beta s)
    (W0 : TangentSpace I (beta s)) :
    ∃ W : (u : Real) → TangentSpace I (beta u),
      W s = W0 ∧
        DifferentiableAt Real (chartRepAt (I := I) beta W s) s := by
  let x : M := beta s
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let w : E := e.continuousLinearMapAt Real x W0
  let W : (u : Real) → TangentSpace I (beta u) :=
    fun u ↦ tangentConstInChart (I := I) x w (beta u)
  have hxbase : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E
      (TangentSpace I : M → Type _) x
  have hWzero : W s = W0 := by
    change tangentConstInChart (I := I) x
      (e.continuousLinearMapAt Real x W0) x = W0
    exact tangentConstInChart_self_continuousLinearMapAt (I := I) x W0
  have hpre : {u : Real | beta u ∈ e.baseSet} ∈ 𝓝 s :=
    hbeta.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (by simpa only [x] using hxbase))
  have hWrep : chartRepAt (I := I) beta W s =ᶠ[𝓝 s]
      fun _ : Real ↦ w := by
    filter_upwards [hpre] with u hu
    change e.continuousLinearMapAt Real (beta u)
      (e.symmL Real (beta u) w) = w
    exact e.continuousLinearMapAt_symmL (R := Real) hu w
  refine ⟨W, hWzero, ?_⟩
  exact (differentiableAt_const (c := w)).congr_of_eventuallyEq hWrep

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lReg_chart_diff
    (gamma : Real → M) (V : ∀ r, TangentSpace I (gamma r)) (t : Real)
    (hV : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 1
      (fun r : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma r) (V r) : TangentBundle I M)) t) :
    DifferentiableAt Real (chartRepAt (I := I) gamma V t) t := by
  let Q : Real → TangentBundle I M := fun r ↦
    TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (gamma r) (V r)
  have hAt : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 1 Q t := by
    simpa only [Q] using hV
  rw [Bundle.contMDiffAt_totalSpace] at hAt
  have hbase := hAt.1
  have hfiber := hAt.2
  have hmem :
      gamma t ∈ (trivializationAt E (TangentSpace I) (gamma t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)
  have hpre :
      gamma ⁻¹' (trivializationAt E (TangentSpace I) (gamma t)).baseSet ∈
        𝓝 t :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (gamma t)).open_baseSet.mem_nhds hmem)
  have heq :
      (fun r : Real ↦
        ((trivializationAt E (TangentSpace I) (gamma t)) (Q r)).2) =ᶠ[𝓝 t]
      fun r : Real ↦
        (trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
          Real (gamma r) (V r) := by
    filter_upwards [hpre] with r hr
    simp only [Q, TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt_apply
      (R := Real)]
    rw [(trivializationAt E (TangentSpace I) (gamma t)).coe_linearMapAt_of_mem hr]
  have hfiber' := hfiber.congr_of_eventuallyEq heq.symm
  have hfiberDiff : ContDiffAt Real 1
      (fun r : Real ↦
        (trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
          Real (gamma r) (V r)) t := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact hfiber'
  change DifferentiableAt Real
    (fun r : Real ↦
      (trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
        Real (gamma r) (V r)) t
  exact hfiberDiff.differentiableAt (by norm_num)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lReg_vsnd_at
    (f : Real → Real → M) (s : Real)
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ f q.1 q.2) (0, s)) :
    ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) 2
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varSnd (I := I) f q.1 q.2) : TangentBundle I M))
      (0, s) := by
  change ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real))
    (I.prod 𝓘(Real, E)) ((2 : Nat) : ℕ∞)
    (fun q : Real × Real ↦
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (f q.1 q.2) (varSnd (I := I) f q.1 q.2) : TangentBundle I M))
    (0, s)
  simpa only [varSnd] using
    velocity_mdiff_at (I := I) (M := M) ((2 : Nat) : ℕ∞) f (0, s) hf

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lReg_vfst_at
    (f : Real → Real → M) (s : Real)
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ f q.1 q.2) (0, s)) :
    ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) 2
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varFst (I := I) f q.1 q.2) : TangentBundle I M))
      (0, s) := by
  let ft : Real → Real → M := fun a u ↦ f u a
  have hswap : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 3
      (fun q : Real × Real ↦ (q.2, q.1)) (s, 0) :=
    (contMDiff_snd.prodMk contMDiff_fst).contMDiffAt
  have hft : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ ft q.1 q.2) (s, 0) := by
    simpa only [ft, Function.comp_def] using hf.comp (s, 0) hswap
  have hvel := velocity_mdiff_at (I := I) (M := M) 2 ft (s, 0) hft
  have hback : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
      (fun q : Real × Real ↦ (q.2, q.1)) (0, s) :=
    (contMDiff_snd.prodMk contMDiff_fst).contMDiffAt
  simpa only [Function.comp_def, ft, varFst] using
    hvel.comp (0, s) hback

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lReg_var_comm
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M) (s : Real)
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2
      (fun q : Real × Real ↦ f q.1 q.2) (0, s)) :
    covDerivAlong (I := I) g (fun u : Real ↦ f u s)
        (fun u : Real ↦ lVelocity (I := I) (f u) s) 0 =
      covDerivAlong (I := I) g (fun r : Real ↦ f 0 r)
        (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0) s := by
  let F : Real × Real → M := fun q ↦ f q.1 q.2
  have hfev : ∀ᶠ q in 𝓝 ((0 : Real), s),
      ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2 F q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp (by
      simpa only [F] using hf)
  have hlineU : Tendsto (fun u : Real ↦ (u, s)) (𝓝 0) (𝓝 (0, s)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hlineR : Tendsto (fun r : Real ↦ ((0 : Real), r))
      (𝓝 s) (𝓝 (0, s)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hslice_u : ∀ᶠ u in 𝓝 (0 : Real),
      ContMDiffAt 𝓘(Real, Real) I 2 (fun r : Real ↦ f u r) s := by
    filter_upwards [hlineU.eventually hfev] with u hu
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun r : Real ↦ (u, r)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    simpa only [F, Function.comp_def] using hu.comp s hincl
  have hslice_v : ∀ᶠ r in 𝓝 s,
      ContMDiffAt 𝓘(Real, Real) I 2 (fun u : Real ↦ f u r) 0 := by
    filter_upwards [hlineR.eventually hfev] with r hr
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun u : Real ↦ (u, r)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    simpa only [F, Function.comp_def] using hr.comp 0 hincl
  have htrans : ContinuousAt (fun u : Real ↦ f u s) 0 := by
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun u : Real ↦ (u, s)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact (hf.comp 0 hincl).continuousAt
  have hcentral : ContinuousAt (fun r : Real ↦ f 0 r) s := by
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun r : Real ↦ ((0 : Real), r)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hf.comp s hincl).continuousAt
  have hsrc : f 0 s ∈ (chartAt H (f 0 s)).source :=
    mem_chart_source H (f 0 s)
  have hext : ContMDiffAt I 𝓘(Real, E) 2
      (extChartAt I (f 0 s)) (f 0 s) :=
    contMDiffAt_extChartAt' (I := I) (n := 2) (x := f 0 s) hsrc
  have hpull : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, E) 2
      (fun q : Real × Real ↦ extChartAt I (f 0 s) (f q.1 q.2))
      (0, s) := by
    simpa only [Function.comp_def] using hext.comp (0, s) hf
  have hF2 : ContDiffAt Real 2
      (fun q : Real × Real ↦ extChartAt I (f 0 s) (f q.1 q.2))
      (0, s) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hpull
  simpa only [lVelocity] using
    covDerivAlong_commute_transverse_longitudinal_of_variation
      (I := I) g f s hF2 hslice_u hslice_v htrans hcentral

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lReg_accel_var_at
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M) (s : Real)
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2
      (fun q : Real × Real ↦ f q.1 q.2) (0, s))
    (hV : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) 2
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (varSnd (I := I) f q.1 q.2) : TangentBundle I M))
      (0, s)) :
    covFstSnd (I := I) g f (varSnd (I := I) f) 0 s =
      covSnd2 (I := I) g f (varFst (I := I) f) 0 s +
        riemannOp (LeviCivita (I := I) g) (f 0 s)
          (varFst (I := I) f 0 s)
          (varSnd (I := I) f 0 s)
          (varSnd (I := I) f 0 s) := by
  have hraw := cov_commute_at (I := I) g f
    (varSnd (I := I) f) 0 s hV
  change
    covFstSnd (I := I) g f (varSnd (I := I) f) 0 s -
        covSndFst (I := I) g f (varSnd (I := I) f) 0 s =
      riemannOp (LeviCivita (I := I) g) (f 0 s)
        (varFst (I := I) f 0 s) (varSnd (I := I) f 0 s)
        (varSnd (I := I) f 0 s) at hraw
  let F : Real × Real → M := fun q ↦ f q.1 q.2
  have hfev : ∀ᶠ q in 𝓝 ((0 : Real), s),
      ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2 F q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp (by
      simpa only [F] using hf)
  have hlineR : Tendsto (fun r : Real ↦ ((0 : Real), r))
      (𝓝 s) (𝓝 (0, s)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hcomm : ∀ᶠ r in 𝓝 s,
      covFst (I := I) g f (varSnd (I := I) f) 0 r =
        covSnd (I := I) g f (varFst (I := I) f) 0 r := by
    filter_upwards [hlineR.eventually hfev] with r hr
    simpa only [covFst, covSnd, varFst, varSnd, lVelocity,
      Function.comp_def] using
      lReg_var_comm (I := I) g f r
        (by simpa only [F, Function.comp_def] using hr)
  have hsnd :
      covSndFst (I := I) g f (varSnd (I := I) f) 0 s =
        covSnd2 (I := I) g f (varFst (I := I) f) 0 s := by
    change covDerivAlong (I := I) g (fun r : Real ↦ f 0 r)
        (fun r : Real ↦ covFst (I := I) g f (varSnd (I := I) f) 0 r) s =
      covDerivAlong (I := I) g (fun r : Real ↦ f 0 r)
        (fun r : Real ↦ covSnd (I := I) g f (varFst (I := I) f) 0 r) s
    exact covDerivAlong_congr_of_eventuallyEq (I := I) g
      (fun r : Real ↦ f 0 r) hcomm
  rw [hsnd] at hraw
  linear_combination (norm := module) hraw

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lReg_ricci_apply
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (A W : TangentSpace I x) :
    S.ricci t x (vec2 A W) = S.ricciAt t x (vec2 A W) := by
  change metricRicci (I := I) (S.base.metric t) x (vec2 A W) =
    metricRicciAt (I := I) (S.base.metric t) x (vec2 A W)
  rw [metricRicci_apply]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lReg_ricci_symm
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (A W : TangentSpace I x) :
    S.ricciAt t x (vec2 A W) = S.ricciAt t x (vec2 W A) := by
  change metricRicciAt (I := I) (S.base.metric t) x (vec2 A W) =
    metricRicciAt (I := I) (S.base.metric t) x (vec2 W A)
  rw [metricRicciAt_apply_eq_ricciTensor,
    metricRicciAt_apply_eq_ricciTensor, ricciTensor_symm]

noncomputable def lRegEulerPair
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real)
    (W : TangentSpace I (alpha s)) : Real :=
  let g := S.base.metric (T - s ^ 2)
  g.inner (alpha s) W
    (covDerivAlong (I := I) g alpha
        (fun r ↦ lVelocity (I := I) alpha r) s -
      lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegEuler_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (s : Real)
    (Y : TangentSpace I (gamma (s ^ 2))) (hs : 0 < s)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hvel : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun tau : Real ↦ lVelocity (I := I) gamma tau) (s ^ 2))
        (s ^ 2)) :
    4 * s ^ 2 * lEulerPair S T gamma (s ^ 2) Y =
      lRegEulerPair S T (squareReparametrization gamma) s Y := by
  rw [lEuler_sq (I := I) S T gamma s Y hs hgamma hvel]
  simp only [lRegEulerPair, squareReparametrization]
  have hsub :
      (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) Y
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (squareReparametrization gamma)
              (fun r ↦ lVelocity (I := I) (squareReparametrization gamma) r) s -
            lRegAccel S T s (squareReparametrization gamma s)
              (lVelocity (I := I) (squareReparametrization gamma) s)) =
        (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) Y
            (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (squareReparametrization gamma)
              (fun r ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) -
          (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) Y
            (lRegAccel S T s (squareReparametrization gamma s)
              (lVelocity (I := I) (squareReparametrization gamma) s)) :=
    ((S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) Y).map_sub _ _
  change _ =
    (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) Y
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (squareReparametrization gamma)
          (fun r ↦ lVelocity (I := I) (squareReparametrization gamma) r) s -
        lRegAccel S T s (squareReparametrization gamma s)
          (lVelocity (I := I) (squareReparametrization gamma) s))
  conv_rhs =>
    rw [hsub]
    rw [lRegAccel_inner (I := I) S T s (squareReparametrization gamma s)
      (lVelocity (I := I) (squareReparametrization gamma) s) Y]
  simp only [squareReparametrization]
  ring_nf
  rfl

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegEuler_deriv
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (f : Real → Real → M)
    (W : (u : Real) → TangentSpace I (f u s))
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ f q.1 q.2) (0, s))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u s) W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ lRegEulerPair S T (f u) s (W u))
      (lRegJacobiPair S T (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0)
          s (W 0) +
        lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ f u s) W 0))
      0 := by
  classical
  let g := S.base.metric (T - s ^ 2)
  let alpha : Real → M := fun r ↦ f 0 r
  let Y : (r : Real) → TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0
  let beta : Real → M := fun u ↦ f u s
  let A : (u : Real) → TangentSpace I (beta u) :=
    fun u ↦ lVelocity (I := I) (f u) s
  let B : (u : Real) → TangentSpace I (beta u) := fun u ↦
    covDerivAlong (I := I) g (f u)
      (fun r ↦ lVelocity (I := I) (f u) r) s
  have hbeta : ContMDiffAt 𝓘(Real, Real) I 3 beta 0 := by
    have hline : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 3
        (fun u : Real ↦ (u, s)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    simpa only [beta, Function.comp_def] using hf.comp 0 hline
  have hbetaAt : MDifferentiableAt 𝓘(Real, Real) I beta 0 :=
    hbeta.mdifferentiableAt (by norm_num)
  have hVsnd := lReg_vsnd_at (I := I) f s hf
  have hVfst := lReg_vfst_at (I := I) f s hf
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) beta B 0) 0 := by
    simpa only [beta, B, g, lVelocity, varSnd] using
      cov_snd_fst_at (I := I) g f (varSnd (I := I) f) 0 s hVsnd
  have hAtotal : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 1
      (fun u : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f u s) (varSnd (I := I) f u s) : TangentBundle I M)) 0 := by
    have hline : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun u : Real ↦ (u, s)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    simpa only [Function.comp_def] using
      (hVsnd.comp 0 hline).of_le (by norm_num)
  have hAdiff : DifferentiableAt Real
      (chartRepAt (I := I) beta A 0) 0 := by
    simpa only [beta, A, lVelocity, varSnd] using
      lReg_chart_diff (I := I) beta A 0 hAtotal
  have hDA :
      covDerivAlong (I := I) g beta A 0 =
        covDerivAlong (I := I) g alpha Y s := by
    simpa only [g, beta, A, alpha, Y, lVelocity, varFst, varSnd] using
      lReg_var_comm (I := I) g f s (hf.of_le (by norm_num))
  have hacc :
      covDerivAlong (I := I) g beta B 0 =
        covDerivAlong (I := I) g alpha
            (fun r ↦ covDerivAlong (I := I) g alpha Y r) s +
          riemannOp (LeviCivita (I := I) g) (beta 0)
            (Y s) (A 0) (A 0) := by
    simpa only [g, beta, B, alpha, Y, A, covFstSnd, covFst,
      covSnd2, covSnd, varFst, varSnd, lVelocity] using
      lReg_accel_var_at (I := I) g f s (hf.of_le (by norm_num)) hVsnd
  have hinner := inner_deriv_at
    (I := I) (n := (3 : WithTop ENat)) (by norm_num)
    g beta W B 0 hbeta hW hBdiff
  have hdu := lReg_du_deriv (I := I) S T s beta W hbetaAt hW
  have hric := lReg_ricci_deriv
    (I := I) S T s beta A W hbetaAt hAdiff hW
  let F : Real → Real := fun u ↦
    g.inner (beta u) (W u) (B u) -
      2 * s ^ 2 *
        duSec (I := I) (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (beta u)
          (fun _ : Fin 1 ↦ W u) +
      4 * s * S.ricci (T - s ^ 2) (beta u) (vec2 (A u) (W u))
  have hcalc :=
    (hinner.sub (hdu.const_mul (2 * s ^ 2))).add
      (hric.const_mul (4 * s))
  have hfun :
      (fun u : Real ↦ lRegEulerPair S T (f u) s (W u)) = F := by
    funext u
    simp only [lRegEulerPair, F, g, beta, A, B]
    rw [((S.base.metric (T - s ^ 2)).inner (f u s) (W u)).map_sub,
      lRegAccel_inner, duSec_apply,
      differential1FormFun_apply_eq_inner_gradientFun,
      lReg_ricci_apply,
      lReg_ricci_symm (S := S) (t := T - s ^ 2) (x := f u s)
        (A := A u) (W := W u)]
    ring
  have hHess :
      hessianSec (I := I) (S.base.connection (T - s ^ 2))
          (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (f 0 s)
          (vec2 (lVelocity (I := I) (fun u ↦ f u s) 0) (W 0)) =
        hessianSec (I := I)
          (LeviCivita (I := I) (S.base.metric (T - s ^ 2)))
          (leviCivita_contMDiffCovariantDerivativeLocally
            (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2))
          (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (f 0 s)
          (vec2 (lVelocity (I := I) (fun u ↦ f u s) 0) (W 0)) := by
    rfl
  rw [hfun]
  apply hcalc.congr_deriv
  rw [hacc, hDA,
    (g.inner (beta 0) (W 0)).map_add,
    lReg_curv_pair (I := I) S T s (beta 0) (Y s) (A 0) (W 0),
    duSec_apply,
    differential1FormFun_apply_eq_inner_gradientFun,
    lReg_ricci_apply, lReg_ricci_apply,
    lReg_ricci_symm (S := S) (t := T - s ^ 2) (x := beta 0)
      (A := A 0) (W := covDerivAlong (I := I) g beta W 0)]
  · rw [show beta 0 = f 0 s by rfl, ← hHess]
    simp only [lRegJacobiPair, lRegEulerPair, g, alpha, Y, beta, A, B]
    rw [((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun u ↦ f u s) W 0)).map_sub,
      lRegAccel_inner]
    ring

def HasLRegJacobiAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (s : Real) : Prop :=
  let g := S.base.metric (T - s ^ 2)
  MDifferentiableAt 𝓘(Real, Real) I alpha s ∧
    DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s ∧
    DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r => covDerivAlong (I := I) g alpha Y r) s) s ∧
    ∀ W : TangentSpace I (alpha s), lRegJacobiPair S T alpha Y s W = 0

def IsLRegJacobi
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (J : Set Real) : Prop :=
  ∀ s ∈ J, HasLRegJacobiAt S T alpha Y s

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem HasLRegJacobiAt.congr_of_eqOn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha beta : Real → M}
    (Y : ∀ r, TangentSpace I (alpha r))
    (Y' : ∀ r, TangentSpace I (beta r))
    (s : Real) (U : Set Real) (hU : IsOpen U) (hsU : s ∈ U)
    (hcurve : Set.EqOn alpha beta U)
    (hfield : ∀ r ∈ U, (Y r : E) = (Y' r : E))
    (h : HasLRegJacobiAt S T alpha Y s) :
    HasLRegJacobiAt S T beta Y' s := by
  let g := S.base.metric (T - s ^ 2)
  have hcurveEv : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    exact hcurve hr
  have hfieldEv : ∀ᶠ r in 𝓝 s, (Y r : E) = (Y' r : E) := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    exact hfield r hr
  have hD1Ev : ∀ᶠ r in 𝓝 s,
      (covDerivAlong (I := I) g alpha Y r : E) =
        (covDerivAlong (I := I) g beta Y' r : E) := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    apply DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) g Y Y'
    · filter_upwards [hU.mem_nhds hr] with q hq
      exact hcurve hq
    · filter_upwards [hU.mem_nhds hr] with q hq
      exact hfield q hq
  rcases h with ⟨halpha, hYdiff, hDYdiff, hzero⟩
  refine ⟨halpha.congr_of_eventuallyEq hcurveEv.symm, ?_, ?_, ?_⟩
  · have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := I) Y Y' hcurveEv hfieldEv
    exact hrep.differentiableAt_iff.mp hYdiff
  · have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := I) (fun r ↦ covDerivAlong (I := I) g alpha Y r)
        (fun r ↦ covDerivAlong (I := I) g beta Y' r) hcurveEv hD1Ev
    exact hrep.differentiableAt_iff.mp hDYdiff
  · intro W
    have hcurve0 : alpha s = beta s := hcurve hsU
    have hfield0 : (Y s : E) = (Y' s : E) := hfield s hsU
    have hvel0 : (lVelocity (I := I) alpha s : E) =
        (lVelocity (I := I) beta s : E) := by
      exact congrArg (fun L : Real →L[Real] E ↦ L (1 : Real))
        (Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)
          hcurveEv)
    have hD10 := hD1Ev.self_of_nhds
    have hD2 :
        (covDerivAlong (I := I) g alpha
          (fun r ↦ covDerivAlong (I := I) g alpha Y r) s : E) =
        (covDerivAlong (I := I) g beta
          (fun r ↦ covDerivAlong (I := I) g beta Y' r) s : E) := by
      exact DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
        (I := I) g
        (fun r ↦ covDerivAlong (I := I) g alpha Y r)
        (fun r ↦ covDerivAlong (I := I) g beta Y' r) hcurveEv hD1Ev
    unfold lRegJacobiPair at hzero ⊢
    dsimp only at hzero ⊢
    rw [hcurve0] at hzero
    have hzero' := hzero W
    rw [← hfield0, ← hvel0, ← hD10, ← hD2]
    exact hzero'

noncomputable def lRegEnergy
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (s : Real) : Real :=
  let q := S.base.metric (T - s ^ 2)
  let P := covDerivAlong (I := I) q alpha Y s
  q.inner (alpha s) (Y s) (Y s) + q.inner (alpha s) P P

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegEnergy_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (s : Real) : 0 ≤ lRegEnergy S T alpha Y s := by
  unfold lRegEnergy
  dsimp only
  have hYnonneg : 0 ≤
      (S.base.metric (T - s ^ 2)).inner (alpha s) (Y s) (Y s) := by
    by_cases hzero : Y s = 0
    · simpa only [hzero, map_zero] using (le_refl (0 : Real))
    · exact ((S.base.metric (T - s ^ 2)).pos (alpha s) (Y s) hzero).le
  have hPnonneg : 0 ≤
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s) := by
    by_cases hzero :
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s = 0
    · simpa only [hzero, map_zero] using (le_refl (0 : Real))
    · exact ((S.base.metric (T - s ^ 2)).pos (alpha s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
        hzero).le
  exact add_nonneg hYnonneg hPnonneg

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegVar_jacobiAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M) (s : Real)
    (hf : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ f q.1 q.2) (0, s))
    (hgeo : ∀ᶠ u in 𝓝 (0 : Real),
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f u)
          (fun r ↦ lVelocity (I := I) (f u) r) s =
        lRegAccel S T s (f u s) (lVelocity (I := I) (f u) s)) :
    HasLRegJacobiAt S T (fun r ↦ f 0 r)
      (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s := by
  classical
  let g := S.base.metric (T - s ^ 2)
  let alpha : Real → M := fun r ↦ f 0 r
  let Y : (r : Real) → TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0
  let beta : Real → M := fun u ↦ f u s
  let A : (u : Real) → TangentSpace I (beta u) :=
    fun u ↦ lVelocity (I := I) (f u) s
  let B : (u : Real) → TangentSpace I (beta u) := fun u ↦
    covDerivAlong (I := I) g (f u)
      (fun r ↦ lVelocity (I := I) (f u) r) s
  have hcentral : MDifferentiableAt 𝓘(Real, Real) I alpha s := by
    have hline : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 3
        (fun r : Real ↦ ((0 : Real), r)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hf.comp s hline).mdifferentiableAt (by norm_num)
  have hbeta : ContMDiffAt 𝓘(Real, Real) I 3 beta 0 := by
    have hline : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 3
        (fun u : Real ↦ (u, s)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    simpa only [beta, Function.comp_def] using hf.comp 0 hline
  have hbetaAt : MDifferentiableAt 𝓘(Real, Real) I beta 0 :=
    hbeta.mdifferentiableAt (by norm_num)
  have hVsnd := lReg_vsnd_at (I := I) f s hf
  have hVfst := lReg_vfst_at (I := I) f s hf
  have hYtotal : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 1
      (fun r : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f 0 r) (varFst (I := I) f 0 r) : TangentBundle I M)) s := by
    have hline : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun r : Real ↦ ((0 : Real), r)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    simpa only [Function.comp_def] using
      (hVfst.comp s hline).of_le (by norm_num)
  have hYdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s := by
    simpa only [alpha, Y, lVelocity, varFst] using
      lReg_chart_diff (I := I) alpha Y s hYtotal
  have hDYdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I) g alpha Y r) s) s := by
    simpa only [alpha, Y, g, lVelocity, varFst] using
      cov_snd_diff_at (I := I) g f (varFst (I := I) f) 0 s hVfst
  unfold HasLRegJacobiAt
  dsimp only
  refine ⟨hcentral, hYdiff, hDYdiff, ?_⟩
  intro W0
  rcases lReg_test_field (I := I) beta 0 hbeta.continuousAt W0 with
    ⟨W, hWzero, hWdiff⟩
  have hderiv := lRegEuler_deriv (I := I) S T s f W hf hWdiff
  have hEulerZero :
      (fun u : Real ↦ lRegEulerPair S T (f u) s (W u)) =ᶠ[𝓝 0]
        (fun _ ↦ 0) := by
    filter_upwards [hgeo] with u hu
    simp only [lRegEulerPair]
    rw [hu, sub_self, map_zero]
  have hconst : HasDerivAt (fun _ : Real ↦ (0 : Real)) 0 0 :=
    hasDerivAt_const (x := 0) (c := 0)
  have hzero : HasDerivAt
      (fun u : Real ↦ lRegEulerPair S T (f u) s (W u)) 0 0 :=
    hconst.congr_of_eventuallyEq hEulerZero
  have heq := hderiv.unique hzero
  have hgeo0 := hgeo.self_of_nhds
  have htail :
      lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ f u s) W 0) = 0 := by
    simp only [lRegEulerPair]
    rw [hgeo0, sub_self, map_zero]
  rw [hWzero, htail, add_zero] at heq
  exact heq

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegVar_jacobi
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (J : Set Real)
    (hgeo : ∀ u s, s ∈ J →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f u)
          (fun r ↦ lVelocity (I := I) (f u) r) s =
        lRegAccel S T s (f u s) (lVelocity (I := I) (f u) s)) :
    IsLRegJacobi S T (fun s ↦ f 0 s)
      (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) J := by
  intro s hs
  apply lRegVar_jacobiAt (I := I) S T f s
  · exact (hf : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
  · exact Filter.Eventually.of_forall (fun u ↦ hgeo u s hs)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
noncomputable def lRegJacobiField
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (s : Real) :
    TangentSpace I (lRegCurve S T x Z s) :=
  mfderiv 𝓘(Real, E) I
    (fun W : E ↦ lRegCurve S T x W s) Z V

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lExpJacobi_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real) :
    mfderiv 𝓘(Real, E) I (fun W : E ↦ lExp S T x W tau) Z V =
      lRegJacobiField S T x Z V (Real.sqrt tau) := by
  rfl

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lReg_curve_accel
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : TangentSpace I x) (s : Real)
    (hs : s ∈ lRegDomain S T x Z) :
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (lRegCurve S T x Z)
        (fun r ↦ lVelocity (I := I) (lRegCurve S T x Z) r) s =
      lRegAccel S T s (lRegCurve S T x Z s)
        (lVelocity (I := I) (lRegCurve S T x Z) s) := by
  obtain ⟨K, hKopen, hKconn, h0K, hsK, hchosen⟩ :=
    lRegChosen_spec S T x Z hs
  let gamma : Real → M := lRegCurve S T x Z
  let alpha : Real → M := lRegChosen S T x Z hs
  have heqOn : Set.EqOn gamma alpha K := by
    simpa only [gamma, alpha] using
      lRegCurve_eqOn S hS T hKopen hKconn h0K hchosen
  have heq : gamma =ᶠ[𝓝 s] alpha := by
    filter_upwards [hKopen.mem_nhds hsK] with r hr
    exact heqOn hr
  have hvel : ∀ᶠ r in 𝓝 s,
      (lVelocity (I := I) gamma r : E) =
        (lVelocity (I := I) alpha r : E) := by
    filter_upwards [hKopen.mem_nhds hsK] with r hr
    have her : gamma =ᶠ[𝓝 r] alpha := by
      filter_upwards [hKopen.mem_nhds hr] with q hq
      exact heqOn hq
    exact congrArg (fun L : Real →L[Real] E ↦ L (1 : Real))
      (Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) her)
  have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := I)
    (S.base.metric (T - s ^ 2))
    (fun r ↦ lVelocity (I := I) gamma r)
    (fun r ↦ lVelocity (I := I) alpha r) heq hvel
  have hacc := (hchosen.2.2 s hsK).2.2.2
  change
    (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun r ↦ lVelocity (I := I) gamma r) s : E) =
      (lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) : E)
  rw [hcov, heq.self_of_nhds, hvel.self_of_nhds]
  exact congrArg (fun v : TangentSpace I (alpha s) ↦ (v : E)) hacc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegJacobi_affine
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (s : Real)
    (hs : s ∈ lRegDomain S T x Z) :
    lVelocity (I := I)
        (fun u : Real ↦ lRegCurve S T x (Z + u • V) s) 0 =
      lRegJacobiField S T x Z V s := by
  let z : E := Z
  let v : E := V
  let line : Real → E := fun u ↦ z + u • v
  let phi : E → M := fun W ↦ lRegCurve S T x W s
  have hfoot : line 0 = z := by
    simp only [line, zero_smul, add_zero]
  have hslice : ContMDiffAt 𝓘(Real, E) I ∞ phi z := by
    have hincl : ContMDiffAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun W : E ↦ (W, s)) z :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    simpa only [phi, z, Function.comp_def] using
      (lRegCurve_smooth (I := I) (M := M) S hS T x hs).comp z hincl
  have hphi : MDifferentiableAt 𝓘(Real, E) I phi z :=
    hslice.mdifferentiableAt (by simp)
  have hphi' : MDifferentiableAt 𝓘(Real, E) I phi (line 0) := by
    rw [hfoot]
    exact hphi
  have hline : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) line 0 := by
    have hlineCD : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
      refine (contMDiff_const.add (contMDiff_id.smul contMDiff_const) :
          ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
            ((fun _ : Real ↦ z) + fun u : Real ↦ u • v)).congr ?_
      intro u
      simp only [line, Pi.add_apply]
    exact hlineCD.contMDiffAt.mdifferentiableAt (by simp)
  have hline_apply :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) line 0 (1 : Real) = v := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt line
        (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) v) 0 := by
      have hadd : HasFDerivAt line
          ((0 : Real →L[Real] E) +
            (1 : Real →L[Real] Real).smulRight v) 0 := by
        change HasFDerivAt (fun u : Real ↦ z + u • v)
          ((0 : Real →L[Real] E) +
            (1 : Real →L[Real] Real).smulRight v) 0
        refine HasFDerivAt.add (hasFDerivAt_const (x := (0 : Real)) z) ?_
        refine (((1 : Real →L[Real] Real).smulRight v).hasFDerivAt
          (x := (0 : Real))).congr_of_eventuallyEq ?_
        filter_upwards with r
        simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
      rw [zero_add] at hadd
      exact hadd
    rw [hfd.fderiv]
    change (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) v)
      (1 : Real) = v
    rw [ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
  have hcomp := mfderiv_comp_apply (f := line) (g := phi) (x := (0 : Real))
    hphi' hline (1 : Real)
  unfold lRegJacobiField lVelocity
  change mfderiv 𝓘(Real, Real) I (phi ∘ line) 0 (1 : Real) =
    mfderiv 𝓘(Real, E) I phi z v
  rw [hcomp, hline_apply, hfoot]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lReg_jacobi_congr
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y Y' : ∀ r, TangentSpace I (alpha r)) (s : Real)
    (h : HasLRegJacobiAt S T alpha Y s)
    (hY : Y =ᶠ[𝓝 s] Y')
    (hDY : (fun r ↦ covDerivAlong (I := I)
        (S.base.metric (T - s ^ 2)) alpha Y r) =ᶠ[𝓝 s]
      fun r ↦ covDerivAlong (I := I)
        (S.base.metric (T - s ^ 2)) alpha Y' r) :
    HasLRegJacobiAt S T alpha Y' s := by
  unfold HasLRegJacobiAt at h ⊢
  dsimp only at h ⊢
  rcases h with ⟨halpha, hYdiff, hDYdiff, heq⟩
  refine ⟨halpha, ?_, ?_, ?_⟩
  · exact hYdiff.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hY).symm
  · exact hDYdiff.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hDY).symm
  · intro W
    have hYzero := hY.self_of_nhds
    have hDYzero := hDY.self_of_nhds
    change covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y' s
      at hDYzero
    have hD2 := covDerivAlong_congr_of_eventuallyEq (I := I)
      (S.base.metric (T - s ^ 2)) alpha hDY
    have hzero := heq W
    unfold lRegJacobiPair at hzero ⊢
    dsimp only at hzero ⊢
    rw [← hD2, ← hDYzero, ← hYzero]
    exact hzero

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_jacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (J : Set Real)
    (hJ : J ⊆ lRegDomain S T x Z) :
    IsLRegJacobi S T (lRegCurve S T x Z)
      (lRegJacobiField S T x Z V) J := by
  classical
  intro s hs
  have hsdom : s ∈ lRegDomain S T x Z := hJ hs
  let z : E := Z
  let v : E := V
  let line : Real → E := fun u ↦ z + u • v
  let f : Real → Real → M := fun u r ↦ lRegCurve S T x (line u) r
  have hline0 : line 0 = Z := by
    change Z + (0 : Real) • V = Z
    rw [zero_smul]
    exact add_zero Z
  have hparam : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun q : Real × Real ↦ (z + q.1 • v, q.2)) (0, s) := by
    exact ((contMDiff_const.add
      (contMDiff_fst.smul contMDiff_const)).prodMk
        contMDiff_snd).contMDiffAt
  have hfInf : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
      (fun q : Real × Real ↦ f q.1 q.2) (0, s) := by
    have hsmooth : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
        (fun p : E × Real ↦ lRegCurve S T x p.1 p.2) (z, s) := by
      simpa only [z] using
        lRegCurve_smooth (I := I) (M := M) S hS T x hsdom
    have hsmooth' : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
        (fun p : E × Real ↦ lRegCurve S T x p.1 p.2)
        (z + (0 : Real) • v, s) := by
      simpa only [zero_smul, add_zero] using hsmooth
    have hcomp := hsmooth'.comp (0, s) hparam
    simpa only [f, line, z, zero_smul, add_zero, Function.comp_def] using hcomp
  have hf : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ f q.1 q.2) (0, s) :=
    hfInf.of_le (by
      change (↑(3 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hlinePair : ContinuousAt (fun u : Real ↦ (line u, s)) 0 := by
    have hcd : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun u : Real ↦ (line u, s)) := by
      exact (contMDiff_const.add
        (contMDiff_id.smul contMDiff_const)).prodMk contMDiff_const
    exact hcd.continuous.continuousAt
  have hcenter : (line 0, s) ∈ lRegJointDom S T x := by
    change s ∈ lRegDomain S T x (line 0)
    rw [hline0]
    exact hsdom
  have hnear : ∀ᶠ u in 𝓝 (0 : Real),
      s ∈ lRegDomain S T x (line u) := by
    have hpre := hlinePair.preimage_mem_nhds
      ((lRegJointDom_open S hS T x).mem_nhds hcenter)
    filter_upwards [hpre] with u hu
    exact hu
  have hgeo : ∀ᶠ u in 𝓝 (0 : Real),
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f u)
          (fun r ↦ lVelocity (I := I) (f u) r) s =
        lRegAccel S T s (f u s) (lVelocity (I := I) (f u) s) := by
    filter_upwards [hnear] with u hu
    simpa only [f] using
      lReg_curve_accel (I := I) S hS T x (line u) s hu
  have hraw := lRegVar_jacobiAt (I := I) S T f s hf hgeo
  let Ya : (r : Real) → TangentSpace I (lRegCurve S T x Z r) :=
    fun r ↦ (lVelocity (I := I) (fun u : Real ↦ f u r) 0 : E)
  let Yj : (r : Real) → TangentSpace I (lRegCurve S T x Z r) :=
    fun r ↦ lRegJacobiField S T x Z V r
  have hraw' : HasLRegJacobiAt S T (lRegCurve S T x Z) Ya s := by
    have hfzero : (fun r : Real ↦ f 0 r) = lRegCurve S T x Z := by
      funext r
      change lRegCurve S T x (line 0) r = lRegCurve S T x Z r
      rw [hline0]
    rw [hfzero] at hraw
    simpa only [Ya] using hraw
  have hdomOpen : IsOpen (lRegDomain S T x Z) :=
    lRegDomain_isOpen S T x Z
  have hEqOn : Set.EqOn Ya Yj (lRegDomain S T x Z) := by
    intro r hr
    change (lVelocity (I := I) (fun u : Real ↦ f u r) 0 : E) =
      (lRegJacobiField S T x Z V r : E)
    dsimp only [f, line, z, v]
    exact congrArg (fun q => (q : E))
      (lRegJacobi_affine (I := I) S hS T x Z V r hr)
  have hY : Ya =ᶠ[𝓝 s] Yj := by
    filter_upwards [hdomOpen.mem_nhds hsdom] with r hr
    exact hEqOn hr
  have hDY : (fun r ↦ covDerivAlong (I := I)
      (S.base.metric (T - s ^ 2)) (lRegCurve S T x Z) Ya r) =ᶠ[𝓝 s]
      fun r ↦ covDerivAlong (I := I)
        (S.base.metric (T - s ^ 2)) (lRegCurve S T x Z) Yj r := by
    filter_upwards [hdomOpen.mem_nhds hsdom] with r hr
    apply covDerivAlong_congr_of_eventuallyEq (I := I)
    filter_upwards [hdomOpen.mem_nhds hr] with q hq
    exact hEqOn hq
  simpa only [Yj] using
    lReg_jacobi_congr (I := I) S T (lRegCurve S T x Z) Ya Yj s
      hraw' hY hDY

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegJacobi_d0
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z V : TangentSpace I x) (hT : T ∈ D.regular) :
    covDerivAlong (I := I) (S.base.metric T) (lRegCurve S T x Z)
        (lRegJacobiField S T x Z V) 0 =
      (2 : Real) • V := by
  classical
  let z : E := Z
  let v : E := V
  let line : Real → E := fun u ↦ z + u • v
  let F : Real → Real → M := fun u r ↦ lRegCurve S T x (line u) r
  let g := S.base.metric T
  have h0dom : (0 : Real) ∈ lRegDomain S T x Z :=
    zero_mem_lRegDomain S hS T x Z hT
  have hparam : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun q : Real × Real ↦ (z + q.1 • v, q.2)) (0, 0) := by
    exact ((contMDiff_const.add
      (contMDiff_fst.smul contMDiff_const)).prodMk
        contMDiff_snd).contMDiffAt
  have hFInf : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
      (fun q : Real × Real ↦ F q.1 q.2) (0, 0) := by
    have hsmooth : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
        (fun p : E × Real ↦ lRegCurve S T x p.1 p.2) (z, 0) := by
      simpa only [z] using
        lRegCurve_smoothAt (I := I) (M := M) S hS T x Z hT
    have hsmooth' : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
        (fun p : E × Real ↦ lRegCurve S T x p.1 p.2)
        (z + (0 : Real) • v, (0 : Real)) := by
      simpa only [zero_smul, add_zero] using hsmooth
    have hcomp := hsmooth'.comp ((0 : Real), (0 : Real)) hparam
    simpa only [F, line, z, zero_smul, add_zero, Function.comp_def] using hcomp
  have hF2 : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2
      (fun q : Real × Real ↦ F q.1 q.2) (0, 0) :=
    hFInf.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFzero : ∀ u : Real, F u 0 = x := by
    intro u
    exact lRegCurve_zero S T x (line u)
  have hlaunch : ∀ u : Real,
      (lVelocity (I := I) (F u) 0 : E) = (2 : Real) • line u := by
    intro u
    exact congrArg (fun q : TangentSpace I x ↦ (q : E))
      (lRegCurve_vel_zero (I := I) S hS T x (line u) hT)
  have hFzeroEv : (fun u : Real ↦ F u 0) =ᶠ[𝓝 (0 : Real)]
      fun _ : Real ↦ x :=
    Filter.Eventually.of_forall hFzero
  have hlaunchEv : ∀ᶠ u in 𝓝 (0 : Real),
      (lVelocity (I := I) (F u) 0 : E) = (2 : Real) • line u :=
    Filter.Eventually.of_forall hlaunch
  have hlineDeriv : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul] using
      ((hasDerivAt_id (0 : Real)).smul_const v).const_add z
  have hlaunchDeriv : HasDerivAt (fun u : Real ↦ (2 : Real) • line u)
      ((2 : Real) • v) 0 := by
    exact hlineDeriv.const_smul (2 : Real)
  have hLHS := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := I) g
    (fun u ↦ lVelocity (I := I) (F u) 0)
    (fun u ↦ ((2 : Real) • line u : E)) hFzeroEv hlaunchEv
  have hdiff : DifferentiableAt Real
      (fun u : Real ↦ ((2 : Real) • line u : E)) 0 :=
    hlaunchDeriv.differentiableAt
  have hconst := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_const
    (I := I) g x (fun u ↦ ((2 : Real) • line u : E)) 0 hdiff
  have hderiv : deriv (fun u : Real ↦ ((2 : Real) • line u : E)) 0 =
      (2 : Real) • v :=
    hlaunchDeriv.deriv
  have hcomm := lReg_var_comm (I := I) g F 0 hF2
  have hcommE :
      (covDerivAlong (I := I) g (fun u : Real ↦ F u 0)
          (fun u ↦ lVelocity (I := I) (F u) 0) 0 : E) =
        (covDerivAlong (I := I) g (fun r : Real ↦ F 0 r)
          (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) 0 : E) := by
    simpa only [g, zero_pow, sub_zero] using
      congrArg (fun q : TangentSpace I (F 0 0) ↦ (q : E)) hcomm
  have hfinal :
      (covDerivAlong (I := I) g (fun r : Real ↦ F 0 r)
          (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) 0 : E) =
        (2 : Real) • v :=
    hcommE.symm.trans (hLHS.trans (hconst.trans hderiv))
  have hcentralEv : (fun r : Real ↦ F 0 r) =ᶠ[𝓝 (0 : Real)]
      lRegCurve S T x Z := by
    filter_upwards with r
    change lRegCurve S T x (line 0) r = lRegCurve S T x Z r
    rw [show line 0 = Z by
      change Z + (0 : Real) • V = Z
      rw [zero_smul]
      exact add_zero Z]
  have hfieldEv : ∀ᶠ r in 𝓝 (0 : Real),
      (lVelocity (I := I) (fun u ↦ F u r) 0 : E) =
        (lRegJacobiField S T x Z V r : E) := by
    filter_upwards [(lRegDomain_isOpen S T x Z).mem_nhds h0dom] with r hr
    exact congrArg
      (fun q : TangentSpace I (lRegCurve S T x Z r) ↦ (q : E))
      (by
        exact lRegJacobi_affine (I := I) S hS T x Z V r hr)
  have hRHS := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := I) g
    (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0)
    (lRegJacobiField S T x Z V) hcentralEv hfieldEv
  change
    (covDerivAlong (I := I) g (lRegCurve S T x Z)
      (lRegJacobiField S T x Z V) 0 : E) = (2 : Real) • v
  exact hRHS.symm.trans hfinal

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lRegJacobi_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) :
    lRegJacobiField S T x Z V 0 = 0 := by
  have hconst : (fun W : E ↦ lRegCurve S T x W 0) = fun _ ↦ x := by
    funext W
    exact lRegCurve_zero S T x W
  unfold lRegJacobiField
  rw [hconst]
  change mfderiv 𝓘(Real, E) I (fun _ : E ↦ x) (show E from Z)
    (show E from V) = 0
  rw [mfderiv_const]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem lRegJacobiPair_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y : ∀ s, TangentSpace I (alpha s))
    (W : TangentSpace I (alpha 0)) :
    lRegJacobiPair S T alpha Y 0 W =
      (S.base.metric T).inner (alpha 0) W
          (covDerivAlong (I := I) (S.base.metric T) alpha
            (fun r => covDerivAlong (I := I) (S.base.metric T) alpha Y r) 0) +
        S.base.rm04 T (alpha 0) (vec4 (Y 0)
          (lVelocity (I := I) alpha 0) (lVelocity (I := I) alpha 0) W) := by
  simp [lRegJacobiPair]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegJacobi_eq_zero
    {S : SolutionOn (I := I) (M := M) D} {T s : Real}
    {alpha : Real → M} {Y : ∀ r, TangentSpace I (alpha r)}
    (hY : HasLRegJacobiAt S T alpha Y s)
    (W : TangentSpace I (alpha s)) :
    lRegJacobiPair S T alpha Y s W = 0 :=
  hY.2.2.2 W

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegJacobiPair_sub
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y Y' : ∀ r, TangentSpace I (alpha r)) (s : Real)
    (W : TangentSpace I (alpha s))
    (hD : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
        (fun r ↦ Y r - Y' r) s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s -
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y' s)
    (hD2 : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha (fun u ↦ Y u - Y' u) r) s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun r ↦ covDerivAlong (I := I)
            (S.base.metric (T - s ^ 2)) alpha Y r) s -
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun r ↦ covDerivAlong (I := I)
            (S.base.metric (T - s ^ 2)) alpha Y' r) s) :
    lRegJacobiPair S T alpha (fun r ↦ Y r - Y' r) s W =
      lRegJacobiPair S T alpha Y s W -
        lRegJacobiPair S T alpha Y' s W := by
  let t := T - s ^ 2
  let g := S.base.metric t
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let DY' := covDerivAlong (I := I) g alpha Y' s
  have hcurv :
      S.base.rm04 t (alpha s) (vec4 (Y s - Y' s) A A W) =
        S.base.rm04 t (alpha s) (vec4 (Y s) A A W) -
          S.base.rm04 t (alpha s) (vec4 (Y' s) A A W) := by
    let m := vec4 (Y s) A A W
    have hmap := (S.base.rm04 t (alpha s)).map_update_sub
      m (0 : Fin 4) (Y s) (Y' s)
    have hleft : Function.update m (0 : Fin 4) (Y s - Y' s) =
        vec4 (Y s - Y' s) A A W := by
      funext i
      fin_cases i <;> simp [m, vec4]
    have hright : Function.update m (0 : Fin 4) (Y s) =
        vec4 (Y s) A A W := by
      funext i
      fin_cases i <;> simp [m, vec4]
    have hright' : Function.update m (0 : Fin 4) (Y' s) =
        vec4 (Y' s) A A W := by
      funext i
      fin_cases i <;> simp [m, vec4]
    rwa [hleft, hright, hright'] at hmap
  have hhess :
      hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g) (S.scalar t)
          (scalarSmoothOfSol (I := I) S t) (alpha s)
          (vec2 (Y s - Y' s) W) =
        hessianSec (I := I) (S.base.connection t)
            (metricCov_smooth (I := I) g) (S.scalar t)
            (scalarSmoothOfSol (I := I) S t) (alpha s) (vec2 (Y s) W) -
          hessianSec (I := I) (S.base.connection t)
            (metricCov_smooth (I := I) g) (S.scalar t)
            (scalarSmoothOfSol (I := I) S t) (alpha s) (vec2 (Y' s) W) := by
    let Hs := hessianSec (I := I) (S.base.connection t)
      (metricCov_smooth (I := I) g) (S.scalar t)
      (scalarSmoothOfSol (I := I) S t) (alpha s)
    let m := vec2 (Y s) W
    have hmap := Hs.map_update_sub m (0 : Fin 2) (Y s) (Y' s)
    have hleft : Function.update m (0 : Fin 2) (Y s - Y' s) =
        vec2 (Y s - Y' s) W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    have hright : Function.update m (0 : Fin 2) (Y s) = vec2 (Y s) W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    have hright' : Function.update m (0 : Fin 2) (Y' s) = vec2 (Y' s) W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    change Hs (vec2 (Y s - Y' s) W) =
      Hs (vec2 (Y s) W) - Hs (vec2 (Y' s) W)
    rwa [hleft, hright, hright'] at hmap
  have hnabla :
      totalNabla0SFun (𝕜 := Real) (I := I) 2 (S.base.connection t)
          (S.ricci t) (alpha s) (vec3 (Y s - Y' s) A W) =
        totalNabla0SFun (𝕜 := Real) (I := I) 2 (S.base.connection t)
            (S.ricci t) (alpha s) (vec3 (Y s) A W) -
          totalNabla0SFun (𝕜 := Real) (I := I) 2 (S.base.connection t)
            (S.ricci t) (alpha s) (vec3 (Y' s) A W) := by
    let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.base.connection t) (S.ricci t) (alpha s)
    let m := vec3 (Y s) A W
    have hmap := N.map_update_sub m (0 : Fin 3) (Y s) (Y' s)
    have hleft : Function.update m (0 : Fin 3) (Y s - Y' s) =
        vec3 (Y s - Y' s) A W := by
      funext i
      fin_cases i <;> simp [m, vec3]
    have hright : Function.update m (0 : Fin 3) (Y s) = vec3 (Y s) A W := by
      funext i
      fin_cases i <;> simp [m, vec3]
    have hright' : Function.update m (0 : Fin 3) (Y' s) = vec3 (Y' s) A W := by
      funext i
      fin_cases i <;> simp [m, vec3]
    change N (vec3 (Y s - Y' s) A W) =
      N (vec3 (Y s) A W) - N (vec3 (Y' s) A W)
    rwa [hleft, hright, hright'] at hmap
  have hric :
      S.ricciAt t (alpha s) (vec2 (DY - DY') W) =
        S.ricciAt t (alpha s) (vec2 DY W) -
          S.ricciAt t (alpha s) (vec2 DY' W) := by
    let R := S.ricciAt t (alpha s)
    let m := vec2 DY W
    have hmap := R.map_update_sub m (0 : Fin 2) DY DY'
    have hleft : Function.update m (0 : Fin 2) (DY - DY') =
        vec2 (DY - DY') W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    have hright : Function.update m (0 : Fin 2) DY = vec2 DY W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    have hright' : Function.update m (0 : Fin 2) DY' = vec2 DY' W := by
      funext i
      fin_cases i <;> simp [m, vec2]
    change R (vec2 (DY - DY') W) = R (vec2 DY W) - R (vec2 DY' W)
    rwa [hleft, hright, hright'] at hmap
  simp only [lRegJacobiPair]
  change
    g.inner (alpha s) W _ + S.base.rm04 t (alpha s) _ -
        2 * s ^ 2 * hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g) (S.scalar t)
          (scalarSmoothOfSol (I := I) S t) (alpha s) _ +
        4 * s * totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.base.connection t) (S.ricci t) (alpha s) _ +
        4 * s * S.ricciAt t (alpha s) _ = _
  rw [hD2, hD, (g.inner (alpha s) W).map_sub,
    hcurv, hhess, hnabla, hric]
  dsimp only [t, g, A, DY, DY']
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem IsLRegJacobi.sub
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    {alpha : Real → M} {Y Y' : ∀ r, TangentSpace I (alpha r)}
    {J : Set Real} (hJ : IsOpen J)
    (hY : IsLRegJacobi S T alpha Y J)
    (hY' : IsLRegJacobi S T alpha Y' J) :
    IsLRegJacobi S T alpha (fun r ↦ Y r - Y' r) J := by
  intro s hs
  have hYs := hY s hs
  have hY's := hY' s hs
  unfold HasLRegJacobiAt at hYs hY's ⊢
  dsimp only at hYs hY's ⊢
  rcases hYs with ⟨halpha, hYdiff, hDYdiff, hYeq⟩
  rcases hY's with ⟨_, hY'diff, hDY'diff, hY'eq⟩
  let g := S.base.metric (T - s ^ 2)
  let DY : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ covDerivAlong (I := I) g alpha Y r
  let DY' : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ covDerivAlong (I := I) g alpha Y' r
  let Dsub : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ covDerivAlong (I := I) g alpha (fun u ↦ Y u - Y' u) r
  have hrepSub :
      chartRepAt (I := I) alpha (fun r ↦ Y r - Y' r) s =
        fun r ↦ chartRepAt (I := I) alpha Y s r -
          chartRepAt (I := I) alpha Y' s r := by
    rw [show (fun r ↦ Y r - Y' r) =
        fun r ↦ Y r + (-1 : Real) • Y' r by
      funext r
      module]
    rw [chartRepAt_add, chartRepAt_smul]
    funext r
    module
  have hsubDiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ Y r - Y' r) s) s := by
    rw [hrepSub]
    exact hYdiff.sub hY'diff
  have hDev : Dsub =ᶠ[𝓝 s] fun r ↦ DY r - DY' r := by
    filter_upwards [hJ.mem_nhds hs] with r hr
    have hYr := (hY r hr).2.1
    have hY'r := (hY' r hr).2.1
    have hneg : DifferentiableAt Real
        (chartRepAt (I := I) alpha (fun u ↦ (-1 : Real) • Y' u) r) r := by
      rw [chartRepAt_smul]
      exact hY'r.const_smul (-1 : Real)
    change covDerivAlong (I := I) g alpha (fun u ↦ Y u - Y' u) r =
      covDerivAlong (I := I) g alpha Y r -
        covDerivAlong (I := I) g alpha Y' r
    rw [show (fun u ↦ Y u - Y' u) =
        fun u ↦ Y u + (-1 : Real) • Y' u by
      funext u
      module]
    rw [covDerivAlong_add (I := I) g alpha Y
      (fun u ↦ (-1 : Real) • Y' u) r hYr hneg,
      covDerivAlong_smul]
    module
  have hrepD :
      chartRepAt (I := I) alpha (fun r ↦ DY r - DY' r) s =
        fun r ↦ chartRepAt (I := I) alpha DY s r -
          chartRepAt (I := I) alpha DY' s r := by
    rw [show (fun r ↦ DY r - DY' r) =
        fun r ↦ DY r + (-1 : Real) • DY' r by
      funext r
      module]
    rw [chartRepAt_add, chartRepAt_smul]
    funext r
    module
  have hDtarget : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ DY r - DY' r) s) s := by
    rw [hrepD]
    have hDY : DifferentiableAt Real (chartRepAt (I := I) alpha DY s) s := by
      simpa only [DY, g] using hDYdiff
    have hDY' : DifferentiableAt Real (chartRepAt (I := I) alpha DY' s) s := by
      simpa only [DY', g] using hDY'diff
    exact hDY.sub hDY'
  have hDsubDiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Dsub s) s := by
    exact hDtarget.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hDev)
  have hD : covDerivAlong (I := I) g alpha (fun r ↦ Y r - Y' r) s =
      covDerivAlong (I := I) g alpha Y s -
        covDerivAlong (I := I) g alpha Y' s := by
    exact hDev.eq_of_nhds
  have hD2lin : covDerivAlong (I := I) g alpha
        (fun r ↦ DY r - DY' r) s =
      covDerivAlong (I := I) g alpha DY s -
        covDerivAlong (I := I) g alpha DY' s := by
    have hDY : DifferentiableAt Real (chartRepAt (I := I) alpha DY s) s := by
      simpa only [DY, g] using hDYdiff
    have hDY' : DifferentiableAt Real (chartRepAt (I := I) alpha DY' s) s := by
      simpa only [DY', g] using hDY'diff
    have hneg : DifferentiableAt Real
        (chartRepAt (I := I) alpha (fun r ↦ (-1 : Real) • DY' r) s) s := by
      rw [chartRepAt_smul]
      exact hDY'.const_smul (-1 : Real)
    rw [show (fun r ↦ DY r - DY' r) =
        fun r ↦ DY r + (-1 : Real) • DY' r by
      funext r
      module]
    rw [covDerivAlong_add (I := I) g alpha DY
      (fun r ↦ (-1 : Real) • DY' r) s hDY hneg,
      covDerivAlong_smul]
    module
  have hD2 : covDerivAlong (I := I) g alpha Dsub s =
      covDerivAlong (I := I) g alpha DY s -
        covDerivAlong (I := I) g alpha DY' s :=
    (covDerivAlong_congr_of_eventuallyEq (I := I) g alpha hDev).trans hD2lin
  refine ⟨halpha, hsubDiff, ?_, ?_⟩
  · simpa only [Dsub, g] using hDsubDiff
  · intro W
    have hpair := lRegJacobiPair_sub (I := I) S T alpha Y Y' s W
      (by simpa only [g] using hD) (by simpa only [Dsub, DY, DY', g] using hD2)
    rw [hpair, hYeq W, hY'eq W, sub_self]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegJacobiVel_diff
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hY : DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s) :
    DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - r ^ 2)) alpha Y r) s) s := by
  let q := S.base.metric (T - s ^ 2)
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  let Z : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) q alpha Y r
  let C : ∀ r, TangentSpace I (alpha r) := fun r ↦
    CovariantDerivative.difference
      (metricCov (I := I) (S.base.metric (T - r ^ 2)))
      (metricCov (I := I) q) (alpha r) (Y r) (A r)
  have hC : DifferentiableAt Real
      (chartRepAt (I := I) alpha C s) s := by
    simpa only [C, q, A] using
      connBack_vec_sq (I := I) S hS T alpha A Y s ht
        halpha.self_of_nhds (by simpa only [A] using hA)
        hY
  have hPZ : P =ᶠ[nhds s] fun r ↦ Z r + C r := by
    filter_upwards [halpha] with r halpha_r
    have hdiff := covAlong_diff (I := I)
      (S.base.metric (T - r ^ 2)) q alpha Y r halpha_r
    have hdiff' : P r - Z r = C r := by
      simpa only [P, Z, C, A, lVelocity] using hdiff
    exact (sub_eq_iff_eq_add.mp hdiff').trans (add_comm _ _)
  have hsum : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ Z r + C r) s) s := by
    rw [chartRepAt_add]
    have hZ' : DifferentiableAt Real
        (chartRepAt (I := I) alpha Z s) s := by
      simpa only [Z, q] using hZ
    exact hZ'.add hC
  have hP : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s :=
    hsum.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hPZ)
  simpa only [P] using hP

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegJacobi_dyn_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s)
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s)
    (W : TangentSpace I (alpha s)) :
    let q := S.base.metric (T - s ^ 2)
    let A := lVelocity (I := I) alpha s
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
    q.inner (alpha s)
        (covDerivAlong (I := I) q alpha P s) W =
      lRegJacobiPair S T alpha Y s W -
        S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A W) +
        2 * s ^ 2 *
          hessianSec (I := I) (S.base.connection (T - s ^ 2))
            (metricCov_smooth (I := I) q) (S.scalar (T - s ^ 2))
            (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (alpha s)
            (vec2 (Y s) W) -
        4 * s * S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) W) +
        2 * s * N (vec3 A (Y s) W) -
        2 * s * N (vec3 (Y s) A W) -
        2 * s * N (vec3 W A (Y s)) := by
  let q := S.base.metric (T - s ^ 2)
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  let Z : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) q alpha Y r
  have halpha_s := halpha.self_of_nhds
  have hYdiff := hY
  have hZdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Z s) s := by
    simpa only [Z, q] using hZ
  have hPdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    simpa only [P] using lRegJacobiVel_diff (I := I) S hS T alpha Y s ht
      halpha hYdiff hA hZ
  have hPZ : P s = Z s := by
    rfl
  obtain ⟨Wb, hWs, hWdiff⟩ :=
    lReg_test_field (I := I) alpha s halpha_s.continuousAt W
  have hchart : DifferentiableAt Real
      (chartCurve (I := I) (alpha s) alpha) s := by
    change DifferentiableAt Real (extChartAt I (alpha s) ∘ alpha) s
    exact mdifferentiableAt_iff_differentiableAt.mp
      (mdifferentiableAt_iff_target.mp halpha_s).2
  have hmetricP :=
    metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) q alpha P Wb s halpha_s.continuousAt hchart hPdiff hWdiff
  have hmetricZ :=
    metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) q alpha Z Wb s halpha_s.continuousAt hchart hZdiff hWdiff
  let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
    (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
  let C : Real := (2 * s) *
    (N (vec3 (A s) (Y s) (Wb s)) +
      N (vec3 (Y s) (A s) (Wb s)) -
      N (vec3 (Wb s) (A s) (Y s)))
  have hconn : HasDerivAt
      (fun r : Real ↦ q.inner (alpha r)
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Y r) (A r))
        (Wb r)) C s := by
    simpa only [q, C, N, A] using
      connBack_along_sq (I := I) S hS T alpha A Y Wb s ht halpha_s
        (by simpa only [A] using hA) hYdiff hWdiff
  have hscalar :
      (fun r : Real ↦ q.inner (alpha r)
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Y r) (A r))
        (Wb r)) =ᶠ[nhds s]
      fun r : Real ↦
        q.inner (alpha r) (P r) (Wb r) -
          q.inner (alpha r) (Z r) (Wb r) := by
    filter_upwards [halpha] with r halpha_r
    have hdiff := covAlong_diff (I := I)
      (S.base.metric (T - r ^ 2)) q alpha Y r halpha_r
    have hdiff' : P r - Z r =
        CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Y r) (A r) := by
      simpa only [P, Z, A, lVelocity] using hdiff
    rw [← hdiff']
    rw [ContinuousLinearMap.map_sub, sub_apply]
  have hmetric := (hmetricP.sub hmetricZ).congr_of_eventuallyEq hscalar
  have huniq := hmetric.unique hconn
  have hD2 :
      q.inner (alpha s) (covDerivAlong (I := I) q alpha Z s) (Wb s) =
        q.inner (alpha s) (covDerivAlong (I := I) q alpha P s) (Wb s) - C := by
    rw [hPZ] at huniq
    linarith
  have hD2W :
      q.inner (alpha s) (covDerivAlong (I := I) q alpha Z s) W =
        q.inner (alpha s) (covDerivAlong (I := I) q alpha P s) W -
          (2 * s) *
            (N (vec3 (A s) (Y s) W) +
              N (vec3 (Y s) (A s) W) -
              N (vec3 W (A s) (Y s))) := by
    simpa only [hWs, C] using hD2
  unfold lRegJacobiPair
  dsimp only
  rw [q.symm (alpha s) W
      (covDerivAlong (I := I) q alpha Z s)]
  rw [hD2W]
  rw [show covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s =
      P s by rfl]
  dsimp only [q, A, P, N]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegJacobi_dyn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : HasLRegJacobiAt S T alpha Y s)
    (W : TangentSpace I (alpha s)) :
    let q := S.base.metric (T - s ^ 2)
    let A := lVelocity (I := I) alpha s
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
    q.inner (alpha s)
        (covDerivAlong (I := I) q alpha P s) W =
      -S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A W) +
        2 * s ^ 2 *
          hessianSec (I := I) (S.base.connection (T - s ^ 2))
            (metricCov_smooth (I := I) q) (S.scalar (T - s ^ 2))
            (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (alpha s)
            (vec2 (Y s) W) -
        4 * s * S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) W) +
        2 * s * N (vec3 A (Y s) W) -
        2 * s * N (vec3 (Y s) A W) -
        2 * s * N (vec3 W A (Y s)) := by
  have h := lRegJacobi_dyn_eq (I := I) S hS T alpha Y s ht halpha hA
    hY.2.1 hY.2.2.1 W
  rw [hY.2.2.2 W] at h
  simpa only [zero_sub] using h

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegEnergy_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : HasLRegJacobiAt S T alpha Y s) :
    let q := S.base.metric (T - s ^ 2)
    let A := lVelocity (I := I) alpha s
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
    HasDerivAt (lRegEnergy S T alpha Y)
      (2 * q.inner (alpha s) (Y s) (P s) +
        4 * s * S.ricciAt (T - s ^ 2) (alpha s) (vec2 (Y s) (Y s)) -
        2 * S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A (P s)) +
        4 * s ^ 2 *
          hessianSec (I := I) (S.base.connection (T - s ^ 2))
            (metricCov_smooth (I := I) q) (S.scalar (T - s ^ 2))
            (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (alpha s)
            (vec2 (Y s) (P s)) -
        4 * s * S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s)) +
        4 * s * N (vec3 A (Y s) (P s)) -
        4 * s * N (vec3 (Y s) A (P s)) -
        4 * s * N (vec3 (P s) A (Y s))) s := by
  let q := S.base.metric (T - s ^ 2)
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
    (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
  have halpha_s := halpha.self_of_nhds
  have hYdiff := hY.2.1
  have hPdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    simpa only [P] using lRegJacobiVel_diff (I := I) S hS T alpha Y s ht
      halpha hYdiff hA hY.2.2.1
  have hYinner := lRegInner_deriv (I := I) S hS T alpha Y Y s ht
    halpha_s hYdiff hYdiff
  have hPinner := lRegInner_deriv (I := I) S hS T alpha P P s ht
    halpha_s hPdiff hPdiff
  have hdyn :
      q.inner (alpha s) (covDerivAlong (I := I) q alpha P s) (P s) =
        -S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) (A s) (A s) (P s)) +
          2 * s ^ 2 *
            hessianSec (I := I) (S.base.connection (T - s ^ 2))
              (metricCov_smooth (I := I) q) (S.scalar (T - s ^ 2))
              (scalarSmoothOfSol (I := I) S (T - s ^ 2)) (alpha s)
              (vec2 (Y s) (P s)) -
          4 * s * S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s)) +
          2 * s * N (vec3 (A s) (Y s) (P s)) -
          2 * s * N (vec3 (Y s) (A s) (P s)) -
          2 * s * N (vec3 (P s) (A s) (Y s)) := by
    simpa only [q, A, P, N] using
      lRegJacobi_dyn (I := I) S hS T alpha Y s ht halpha hA hY (P s)
  have hsum := hYinner.add hPinner
  apply hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ rfl) |>.congr_deriv
  rw [show covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s =
      P s by rfl]
  rw [q.symm (alpha s) (P s) (Y s)]
  rw [q.symm (alpha s) (P s) (covDerivAlong (I := I) q alpha P s)]
  rw [hdyn]
  dsimp only [q, A, P, N]
  ring

private noncomputable def lCovLast2
    {x : M} (B : Tensor0SSpace 2 I x)
    (X : TangentSpace I x) : Module.Dual Real (TangentSpace I x) :=
  cotangentToDual (I := I)
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x B X)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lCovLast2_apply
    {x : M} (B : Tensor0SSpace 2 I x)
    (X W : TangentSpace I x) :
    lCovLast2 (I := I) B X W = B (vec2 X W) := by
  rw [lCovLast2, cotangentToDual_apply, tensor0S_curry_one_apply]
  rfl

private noncomputable def lCovLast3
    {x : M} (C : Tensor0SSpace 3 I x)
    (X Y : TangentSpace I x) : Module.Dual Real (TangentSpace I x) :=
  lCovLast2 (I := I)
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x C X) Y

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lCovLast3_apply
    {x : M} (C : Tensor0SSpace 3 I x)
    (X Y W : TangentSpace I x) :
    lCovLast3 (I := I) C X Y W = C (vec3 X Y W) := by
  rw [lCovLast3, lCovLast2_apply, tensor0S_curry_apply_cons]
  congr 1
  funext i
  fin_cases i <;> rfl

private noncomputable def lCovLast4
    {x : M} (R : Tensor0SSpace 4 I x)
    (X Y Z : TangentSpace I x) : Module.Dual Real (TangentSpace I x) :=
  lCovLast3 (I := I)
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 3 x R X) Y Z

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lCovLast4_apply
    {x : M} (R : Tensor0SSpace 4 I x)
    (X Y Z W : TangentSpace I x) :
    lCovLast4 (I := I) R X Y Z W = R (vec4 X Y Z W) := by
  rw [lCovLast4, lCovLast3_apply, tensor0S_curry_apply_cons]
  congr 1
  funext i
  fin_cases i <;> rfl

private noncomputable def lCovFirst3
    {x : M} (N : Tensor0SSpace 3 I x)
    (A Y : TangentSpace I x) : Module.Dual Real (TangentSpace I x) :=
  lCovLast3 (I := I)
    (Tensor0SSpace.domDomCongr N
      (Equiv.swap (0 : Fin 3) (2 : Fin 3))) Y A

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lCovFirst3_apply
    {x : M} (N : Tensor0SSpace 3 I x)
    (A Y W : TangentSpace I x) :
    lCovFirst3 (I := I) N A Y W = N (vec3 W A Y) := by
  rw [lCovFirst3, lCovLast3_apply, Tensor0SSpace.domDomCongr_apply]
  change N (fun i ↦ vec3 Y A W ((Equiv.swap (0 : Fin 3) (2 : Fin 3)) i)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

noncomputable def lRegJacobiCov
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (Y A P : TangentSpace I x) : Module.Dual Real (TangentSpace I x) :=
  let t := T - s ^ 2
  let q := S.base.metric t
  let Hs := hessianSec (I := I) (S.base.connection t)
    (metricCov_smooth (I := I) q) (S.scalar t)
    (scalarSmoothOfSol (I := I) S t) x
  let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
    (S.base.connection t) (S.ricci t) x
  (-lCovLast4 (I := I) (S.base.rm04 t x) Y A A +
    (2 * s ^ 2) • lCovLast2 (I := I) Hs Y -
    (4 * s) • lCovLast2 (I := I) (S.ricciAt t x) P +
    (2 * s) • lCovLast3 (I := I) N A Y -
    (2 * s) • lCovLast3 (I := I) N Y A -
    (2 * s) • lCovFirst3 (I := I) N A Y)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem lRegJacobiCov_apply
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (Y A P W : TangentSpace I x) :
    lRegJacobiCov S T s x Y A P W =
      -S.base.rm04 (T - s ^ 2) x (vec4 Y A A W) +
        2 * s ^ 2 *
          hessianSec (I := I) (S.base.connection (T - s ^ 2))
            (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
            (S.scalar (T - s ^ 2))
            (scalarSmoothOfSol (I := I) S (T - s ^ 2)) x (vec2 Y W) -
        4 * s * S.ricciAt (T - s ^ 2) x (vec2 P W) +
        2 * s * totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) x
          (vec3 A Y W) -
        2 * s * totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) x
          (vec3 Y A W) -
        2 * s * totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) x
          (vec3 W A Y) := by
  simp only [lRegJacobiCov, lCovLast2_apply, lCovLast3_apply,
    lCovLast4_apply, lCovFirst3_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]

noncomputable def lRegJacobiForce
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (Y A P : TangentSpace I x) : TangentSpace I x :=
  metricSharp (I := I) (S.base.metric (T - s ^ 2)) x
    (lRegJacobiCov S T s x Y A P)

private noncomputable def lFix2LM
    {x : M} (X : TangentSpace I x) :
    Tensor0SSpace 2 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  { toFun := fun B ↦ lCovLast2 (I := I) B X
    map_add' := by
      intro B C
      ext W
      simp only [lCovLast2_apply, Tensor0SSpace.add_apply, LinearMap.add_apply]
    map_smul' := by
      intro c B
      ext W
      simp only [lCovLast2_apply, Tensor0SSpace.smul_apply,
        LinearMap.smul_apply, smul_eq_mul]
      simp }

private noncomputable def lFix3LM
    {x : M} (X Y : TangentSpace I x) :
    Tensor0SSpace 3 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  { toFun := fun C ↦ lCovLast3 (I := I) C X Y
    map_add' := by
      intro B C
      ext W
      simp only [lCovLast3_apply, Tensor0SSpace.add_apply, LinearMap.add_apply]
    map_smul' := by
      intro c B
      ext W
      simp only [lCovLast3_apply, Tensor0SSpace.smul_apply,
        LinearMap.smul_apply, smul_eq_mul]
      simp }

private noncomputable def lRegJacobiCovLM
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A : TangentSpace I x) :
    (TangentSpace I x × TangentSpace I x) →ₗ[Real]
      Module.Dual Real (TangentSpace I x) :=
  let t := T - s ^ 2
  let Hs := hessianSec (I := I) (S.base.connection t)
    (metricCov_smooth (I := I) (S.base.metric t)) (S.scalar t)
    (scalarSmoothOfSol (I := I) S t) x
  let N := totalNabla0SFun (𝕜 := Real) (I := I) 2
    (S.base.connection t) (S.ricci t) x
  let toDual := cotangentToDualLinear (I := I) (x := x)
  let curvY := (lFix3LM (I := I) A A).comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 3 x
      (S.base.rm04 t x)).toLinearMap)
  let hessY := toDual.comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x Hs).toLinearMap)
  let ricP := toDual.comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
      (S.ricciAt t x)).toLinearMap)
  let nabAY := toDual.comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
      ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x N) A)).toLinearMap)
  let nabYA := (lFix2LM (I := I) A).comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x N).toLinearMap)
  let nabWA := (lFix2LM (I := I) A).comp
    ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
      (Tensor0SSpace.domDomCongr N
        (Equiv.swap (0 : Fin 3) (2 : Fin 3)))).toLinearMap)
  ((-curvY + (2 * s ^ 2) • hessY + (2 * s) • nabAY -
      (2 * s) • nabYA - (2 * s) • nabWA).comp
      (LinearMap.fst Real (TangentSpace I x) (TangentSpace I x))) +
    (-(4 * s) • ricP).comp
      (LinearMap.snd Real (TangentSpace I x) (TangentSpace I x))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegJacobiCovLM_apply
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A Y P : TangentSpace I x) :
    lRegJacobiCovLM (I := I) S T s x A (Y, P) =
      lRegJacobiCov S T s x Y A P := by
  ext W
  simp [lRegJacobiCovLM, lRegJacobiCov, lFix2LM, lFix3LM,
    lCovLast2, lCovLast3, lCovLast4, lCovFirst3,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, smul_eq_mul]
  ring

noncomputable def lRegForceTan
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A : TangentSpace I x) :
    (TangentSpace I x × TangentSpace I x) →L[Real] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    ((metricFlatMap (I := I) (S.base.metric (T - s ^ 2)) x).symm.toLinearMap.comp
      (lRegJacobiCovLM (I := I) S T s x A))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem lRegForceTan_apply
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x : M)
    (A Y P : TangentSpace I x) :
    lRegForceTan S T s x A (Y, P) = lRegJacobiForce S T s x Y A P := by
  change metricSharp (I := I) (S.base.metric (T - s ^ 2)) x
      (lRegJacobiCovLM (I := I) S T s x A (Y, P)) = _
  rw [lRegJacobiCovLM_apply]
  rfl

noncomputable def lRegForceChart
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x0 x : M)
    (A : TangentSpace I x) : (E × E) →L[Real] E :=
  (trivToE (I := I) x0 x).comp
    ((lRegForceTan S T s x A).comp
      ((trivFromE (I := I) x0 x).prodMap (trivFromE (I := I) x0 x)))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem lRegForceChart_apply
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x0 x : M)
    (A : TangentSpace I x) (Y P : E) :
    lRegForceChart S T s x0 x A (Y, P) =
      trivToE (I := I) x0 x
        (lRegJacobiForce S T s x (trivFromE (I := I) x0 x Y) A
          (trivFromE (I := I) x0 x P)) := by
  change trivToE (I := I) x0 x
      (lRegForceTan S T s x A
        (trivFromE (I := I) x0 x Y, trivFromE (I := I) x0 x P)) = _
  rw [lRegForceTan_apply]

noncomputable def lRegJacobiCLM
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x0 x : M)
    (A : TangentSpace I x) (a u : E) : (E × E) →L[Real] (E × E) :=
  let G := Geometry.Riemannian.AlongCurve.chartChristoffelContractionRightCLM
    (I := I) (S.base.metric (T - s ^ 2)) x0 a u
  ((ContinuousLinearMap.snd Real E E -
      G.comp (ContinuousLinearMap.fst Real E E)).prod
    (lRegForceChart S T s x0 x A -
      G.comp (ContinuousLinearMap.snd Real E E)))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem lRegJacobiCLM_apply
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (x0 x : M)
    (A : TangentSpace I x) (a u : E) (Z : E × E) :
    lRegJacobiCLM S T s x0 x A a u Z =
      (Z.2 - Geometry.Riemannian.Geodesic.chartChristoffelContraction
          (I := I) (S.base.metric (T - s ^ 2)) x0 a Z.1 u,
        lRegForceChart S T s x0 x A Z -
          Geometry.Riemannian.Geodesic.chartChristoffelContraction
            (I := I) (S.base.metric (T - s ^ 2)) x0 a Z.2 u) := by
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegJacobi_dyn_vec
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : HasLRegJacobiAt S T alpha Y s) :
    let q := S.base.metric (T - s ^ 2)
    let A := lVelocity (I := I) alpha s
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    covDerivAlong (I := I) q alpha P s =
      lRegJacobiForce S T s (alpha s) (Y s) A (P s) := by
  let q := S.base.metric (T - s ^ 2)
  let A := lVelocity (I := I) alpha s
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  apply metricFlatLinear_injective (I := I) q (alpha s)
  ext W
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [lRegJacobiForce, inner_metricSharp, lRegJacobiCov_apply]
  simpa only [q, A, P] using
    lRegJacobi_dyn (I := I) S hS T alpha Y s ht halpha hA hY W

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegJacobi_state
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x0 : M)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (hsrc : alpha s ∈ (chartAt H x0).source)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : HasLRegJacobiAt S T alpha Y s) :
    let q := S.base.metric (T - s ^ 2)
    let A : ∀ r, TangentSpace I (alpha r) := fun r ↦
      lVelocity (I := I) alpha r
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    let y := chartRepAtBase (I := I) x0 alpha Y
    let a := chartRepAtBase (I := I) x0 alpha A
    let p := chartRepAtBase (I := I) x0 alpha P
    HasDerivAt (fun r ↦ (y r, p r))
      (p s - Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I) q x0
          (a s) (y s) (chartCurve (I := I) x0 alpha s),
        trivToE (I := I) x0 (alpha s)
            (lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s)) -
          Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I) q x0
            (a s) (p s) (chartCurve (I := I) x0 alpha s)) s := by
  let q := S.base.metric (T - s ^ 2)
  let A : ∀ r, TangentSpace I (alpha r) := fun r ↦
    lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  let y := chartRepAtBase (I := I) x0 alpha Y
  let a := chartRepAtBase (I := I) x0 alpha A
  let p := chartRepAtBase (I := I) x0 alpha P
  have halpha_s := halpha.self_of_nhds
  have hPdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    simpa only [P] using lRegJacobiVel_diff (I := I) S hS T alpha Y s ht
      halpha hY.2.1 hA hY.2.2.1
  have hydiff : DifferentiableAt Real y s := by
    simpa only [y] using chartRep_base_diff (I := I) alpha Y s x0
      halpha_s hsrc hY.2.1
  have hpdiff : DifferentiableAt Real p s := by
    simpa only [p] using chartRep_base_diff (I := I) alpha P s x0
      halpha_s hsrc hPdiff
  have hqcoord : deriv (chartCurve (I := I) x0 alpha) s = a s := by
    have hcoord :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) halpha_s x0 hsrc
    rw [fderiv_apply_one_eq_deriv] at hcoord
    change deriv ((extChartAt I x0) ∘ alpha) s = a s
    simpa only [a, A, chartRepAtBase_apply, lVelocity] using hcoord.symm
  have hbase :
      alpha s ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc
  have hYcov : chartCovDerivAlong (I := I) q x0 alpha y s = p s := by
    have hinv := covDeriv_chartAt (I := I) q alpha Y s x0
      halpha_s hsrc hY.2.1
    have hcoord := congrArg
      (fun V : TangentSpace I (alpha s) ↦ trivToE (I := I) x0 (alpha s) V) hinv
    change trivToE (I := I) x0 (alpha s)
        (trivFromE (I := I) x0 (alpha s)
          (chartCovDerivAlong (I := I) q x0 alpha y s)) =
      trivToE (I := I) x0 (alpha s)
        (covDerivAlong (I := I) q alpha Y s) at hcoord
    rw [trivToE_trivFromE (I := I) x0 hbase] at hcoord
    change chartCovDerivAlong (I := I) q x0 alpha y s = p s at hcoord
    exact hcoord
  have hDP : covDerivAlong (I := I) q alpha P s =
      lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s) := by
    simpa only [q, A, P] using
      lRegJacobi_dyn_vec (I := I) S hS T alpha Y s ht halpha hA hY
  have hPcov : chartCovDerivAlong (I := I) q x0 alpha p s =
      trivToE (I := I) x0 (alpha s)
        (lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s)) := by
    have hinv := covDeriv_chartAt (I := I) q alpha P s x0
      halpha_s hsrc hPdiff
    have hcoord := congrArg
      (fun V : TangentSpace I (alpha s) ↦ trivToE (I := I) x0 (alpha s) V) hinv
    change trivToE (I := I) x0 (alpha s)
        (trivFromE (I := I) x0 (alpha s)
          (chartCovDerivAlong (I := I) q x0 alpha p s)) =
      trivToE (I := I) x0 (alpha s)
        (covDerivAlong (I := I) q alpha P s) at hcoord
    rw [trivToE_trivFromE (I := I) x0 hbase, hDP] at hcoord
    exact hcoord
  have hyderiv : deriv y s =
      p s - Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I) q x0
        (a s) (y s) (chartCurve (I := I) x0 alpha s) := by
    rw [chartCovDerivAlong_def, hqcoord] at hYcov
    rw [← hYcov]
    abel
  have hpderiv : deriv p s =
      trivToE (I := I) x0 (alpha s)
          (lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s)) -
        Geometry.Riemannian.Geodesic.chartChristoffelContraction (I := I) q x0
          (a s) (p s) (chartCurve (I := I) x0 alpha s) := by
    rw [chartCovDerivAlong_def, hqcoord] at hPcov
    rw [← hPcov]
    abel
  exact (hydiff.hasDerivAt.congr_deriv hyderiv).prodMk
    (hpdiff.hasDerivAt.congr_deriv hpderiv)

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegJacobi_state_clm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x0 : M)
    (alpha : Real → M) (Y : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (hsrc : alpha s ∈ (chartAt H x0).source)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : HasLRegJacobiAt S T alpha Y s) :
    let A : ∀ r, TangentSpace I (alpha r) := fun r ↦
      lVelocity (I := I) alpha r
    let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
      covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
    let y := chartRepAtBase (I := I) x0 alpha Y
    let a := chartRepAtBase (I := I) x0 alpha A
    let p := chartRepAtBase (I := I) x0 alpha P
    let z := fun r ↦ (y r, p r)
    HasDerivAt z
      (lRegJacobiCLM S T s x0 (alpha s) (A s) (a s)
        (chartCurve (I := I) x0 alpha s) (z s)) s := by
  let q := S.base.metric (T - s ^ 2)
  let A : ∀ r, TangentSpace I (alpha r) := fun r ↦
    lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  let y := chartRepAtBase (I := I) x0 alpha Y
  let a := chartRepAtBase (I := I) x0 alpha A
  let p := chartRepAtBase (I := I) x0 alpha P
  let z := fun r ↦ (y r, p r)
  have hbase :
      alpha s ∈ (trivializationAt E (TangentSpace I) x0).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsrc
  have hstate : HasDerivAt z
      (p s - Geometry.Riemannian.Geodesic.chartChristoffelContraction
          (I := I) q x0 (a s) (y s) (chartCurve (I := I) x0 alpha s),
        trivToE (I := I) x0 (alpha s)
            (lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s)) -
          Geometry.Riemannian.Geodesic.chartChristoffelContraction
            (I := I) q x0 (a s) (p s)
              (chartCurve (I := I) x0 alpha s)) s := by
    simpa only [q, A, P, y, a, p, z] using
      lRegJacobi_state (I := I) S hS T x0 alpha Y s ht hsrc halpha hA hY
  have hcoeff :
      lRegJacobiCLM S T s x0 (alpha s) (A s) (a s)
          (chartCurve (I := I) x0 alpha s) (z s) =
        (p s - Geometry.Riemannian.Geodesic.chartChristoffelContraction
            (I := I) q x0 (a s) (y s) (chartCurve (I := I) x0 alpha s),
          trivToE (I := I) x0 (alpha s)
              (lRegJacobiForce S T s (alpha s) (Y s) (A s) (P s)) -
            Geometry.Riemannian.Geodesic.chartChristoffelContraction
              (I := I) q x0 (a s) (p s)
                (chartCurve (I := I) x0 alpha s)) := by
    rw [lRegJacobiCLM_apply, lRegForceChart_apply]
    simp only [q, z, y, p, chartRepAtBase_apply]
    rw [trivFromE_trivToE (I := I) x0 hbase,
      trivFromE_trivToE (I := I) x0 hbase]
  exact hstate.congr_deriv hcoeff.symm

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
