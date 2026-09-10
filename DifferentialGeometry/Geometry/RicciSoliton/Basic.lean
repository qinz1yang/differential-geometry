import DifferentialGeometry.Geometry.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Operator.HessianDivergence
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.RicciSoliton

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem scalar_add_laplacian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (h : isGradientRicciSoliton g f σ) (x : M) :
    metricScalarAt (I := I) g x +
      laplacian (I := I) (metricCov (I := I) g) g f x =
      (Module.finrank ℝ E : ℝ) * σ / 2 := by
  have htrace := congrArg (metricTracePair0SAt (I := I) g) (h x)
  rw [metricTracePair0SAt_add, metricTracePair0SAt_smul,
    metricTracePair0SAt_metric] at htrace
  have hlap := (scalarLap_smooth (I := I) (metricCov (I := I) g)
    (metricCov_smooth (I := I) g) g
    (Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    (x := x) f f.contMDiff).eq_trace
      (metricCov (I := I) g) g f _
  rw [scalarLapTraceAt_eq_pair] at hlap
  rw [← metricScalarAt_def, ← hlap] at htrace
  calc
    _ = σ / 2 * (Module.finrank ℝ E : ℝ) := htrace
    _ = (Module.finrank ℝ E : ℝ) * σ / 2 := by ring

theorem scalar_add_delta [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (h : isGradientRicciSoliton g f σ) (x : M) :
    metricScalarAt (I := I) g x + ΔG (I := I) g f x =
      (Module.finrank ℝ E : ℝ) * σ / 2 := by
  have hlap := laplacian_levi_eq (I := I) g f.contMDiff x
  change laplacian (I := I) (metricCov (I := I) g) g f x
    = ΔG (I := I) g f x at hlap
  rw [← hlap]
  exact scalar_add_laplacian h x

omit [T2Space M] in
private theorem metricTensorField_eq_metricTensor0S
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x) :=
    Module.finBasis ℝ (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  simp [component0S_apply]

private theorem totalNabla_metricTensorField_zero
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : Connection.IsMetricCompatible (I := I) cov g)
    (x : M) :
    totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 cov
      (metricTensorField (I := I) g) x = 0 := by
  classical
  let basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x) :=
    Module.finBasis ℝ (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin 3 => basis (idx a))
        = Fin.cons (X x) (fun a : Fin 2 => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons,
    totalNabla0SFun_apply_section, nabla_metric_zero (I := I) cov g hmc X x]
  simp

omit [T2Space M] in
private theorem traceFirstTwo_zero
    (g : SmoothRiemannianMetric I M) {x : M} (Y : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g
        (0 : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3 x)
        (fun _ : Fin 1 => Y) = 0 := by
  have hneg := metricTraceFirstTwo0SAt_neg (I := I) g
    (0 : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3 x)
    (fun _ : Fin 1 => Y)
  rw [neg_zero] at hneg
  linarith

theorem dScalar_eq_two_ricci_grad
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (h : isGradientRicciSoliton g f σ) (x : M) (Y : TangentSpace I x) :
    differential1FormFun (I := I) (fun y : M => metricScalarAt (I := I) g y) x
        (fun _ : Fin 1 => Y) =
      2 * metricRicciAt (I := I) g x
        (Curvature.vec2 Y (gradientFun (I := I) g f x)) := by
  classical
  have hmc := Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hsec :
      metricRicci (I := I) g
          + hessianSec (I := I) (metricCov (I := I) g)
              (metricCov_smooth (I := I) g) f f.contMDiff
        = (σ / 2 : ℝ) • metricTensorField (I := I) g := by
    apply ContMDiffSection.ext
    intro y
    have hy := h y
    change metricRicci (I := I) g y
        + hessianSec (I := I) (metricCov (I := I) g)
            (metricCov_smooth (I := I) g) f f.contMDiff y
      = (σ / 2 : ℝ) • metricTensorField (I := I) g y
    rw [metricTensorField_eq_metricTensor0S, metricRicci_apply]
    exact hy
  have hnab :
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) g) (metricRicci (I := I) g) x
        + totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (metricCov (I := I) g)
          (hessianSec (I := I) (metricCov (I := I) g)
            (metricCov_smooth (I := I) g) f f.contMDiff) x = 0 := by
    rw [← totalNabla0SFun_add, totalNabla0SFun_congr 2 rfl hsec,
      totalNabla0SFun_smul,
      totalNabla_metricTensorField_zero (metricCov (I := I) g) g hmc x,
      smul_zero]
  have htr := congrArg
    (fun T => metricTraceFirstTwo0SAt (I := I) g T (fun _ : Fin 1 => Y)) hnab
  simp only [metricTraceFirstTwo0SAt_add, traceFirstTwo_zero] at htr
  rw [show totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) g) (metricRicci (I := I) g) x
      = metricNablaRic (I := I) g x from rfl,
    show totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (metricCov (I := I) g)
        (hessianSec (I := I) (metricCov (I := I) g)
          (metricCov_smooth (I := I) g) f f.contMDiff) x
      = nablaHessSec (I := I) (metricCov (I := I) g)
          (metricCov_smooth (I := I) g) f f.contMDiff x from rfl] at htr
  rw [metricRicci_divergence, hessian_divergence] at htr
  have hR : MDifferentiable I 𝓘(ℝ, ℝ)
      (fun y : M => metricScalarAt (I := I) g y) :=
    (metricScalar_smooth (I := I) g).mdifferentiable (by simp)
  have hdlap :
      differential1FormFun (I := I)
          (laplacian (I := I) (metricCov (I := I) g) g f) x (fun _ : Fin 1 => Y)
        = - differential1FormFun (I := I)
            (fun y : M => metricScalarAt (I := I) g y) x (fun _ : Fin 1 => Y) := by
    have hfun : (laplacian (I := I) (metricCov (I := I) g) g f)
        = (fun _ : M => (Module.finrank ℝ E : ℝ) * σ / 2)
          - (fun y : M => metricScalarAt (I := I) g y) := by
      funext y
      have := scalar_add_laplacian h y
      simp only [Pi.sub_apply]
      linarith
    rw [differential1FormFun_apply_eq_mvfderiv,
      differential1FormFun_apply_eq_mvfderiv, hfun,
      mvfderiv_sub mdifferentiable_const.mdifferentiableAt (hR x),
      mvfderiv_const]
    simp
  rw [hdlap] at htr
  linarith

omit [T2Space M] in
private theorem gradNormSq_smooth
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (gradNormSq (I := I) g f) :=
  contMDiff_g_inner_of_smooth_sections (I := I) g
    ⟨fun y : M => gradientFun (I := I) g f y,
      gradientFun_smooth (I := I) g f.contMDiff⟩
    ⟨fun y : M => gradientFun (I := I) g f y,
      gradientFun_smooth (I := I) g f.contMDiff⟩

private theorem dGradNormSq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (x : M) (Y : TangentSpace I x) :
    differential1FormFun (I := I) (gradNormSq (I := I) g f) x
        (fun _ : Fin 1 => Y) =
      2 * hessianSec (I := I) (metricCov (I := I) g)
        (metricCov_smooth (I := I) g) f f.contMDiff x
        (Curvature.vec2 Y (gradientFun (I := I) g f x)) := by
  classical
  have hmc := Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hGdiff : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x :=
    gradientFun_mdiffAt (I := I) g f.contMDiff x
  have hcomp := hmc.mvfderiv_inner (x := x) Y hGdiff hGdiff
  rw [differential1FormFun_apply_eq_mvfderiv,
    hessSec_inner_cov (I := I) (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) g hmc f f.contMDiff x Y
      (gradientFun (I := I) g f x)]
  rw [show gradNormSq (I := I) g f
      = fun y : M => g.inner y (gradientFun (I := I) g f y)
          (gradientFun (I := I) g f y) from rfl, hcomp]
  simp only [metricCov]
  rw [g.symm x (gradientFun (I := I) g f x)
    (Connection.leviCivitaConnectionOfMetric (I := I) g
      (fun y : M => gradientFun (I := I) g f y) x Y)]
  ring

theorem exists_hamilton_constant [I.Boundaryless] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (h : isGradientRicciSoliton g f σ) :
    ∃ C : ℝ, ∀ x : M,
      metricScalarAt (I := I) g x + gradNormSq (I := I) g f x - σ * f x = C := by
  classical
  have hRs := metricScalar_smooth (I := I) g
  have hNs := gradNormSq_smooth (I := I) g f
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => σ * f y) :=
    contMDiff_const.mul f.contMDiff
  have hFs : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((fun y : M => metricScalarAt (I := I) g y + gradNormSq (I := I) g f y)
        - fun y : M => σ * f y) := (hRs.add hNs).sub hfs
  have hFd : MDifferentiable I 𝓘(ℝ, ℝ)
      ((fun y : M => metricScalarAt (I := I) g y + gradNormSq (I := I) g f y)
        - fun y : M => σ * f y) := hFs.mdifferentiable (by simp)
  have hzero : ∀ y : M, mfderiv I 𝓘(ℝ, ℝ)
      ((fun z : M => metricScalarAt (I := I) g z + gradNormSq (I := I) g f z)
        - fun z : M => σ * f z) y = 0 := by
    intro y
    ext Y
    have hRd : MDiffAt (fun z : M => metricScalarAt (I := I) g z) y :=
      (hRs.mdifferentiable (by simp)) y
    have hNd : MDiffAt (fun z : M => gradNormSq (I := I) g f z) y :=
      (hNs.mdifferentiable (by simp)) y
    have hfd : MDiffAt (fun z : M => σ * f z) y :=
      (hfs.mdifferentiable (by simp)) y
    have hdR : mvfderiv (I := I)
        (fun z : M => metricScalarAt (I := I) g z) y Y
        = 2 * metricRicciAt (I := I) g y
            (Curvature.vec2 Y (gradientFun (I := I) g f y)) := by
      rw [← differential1FormFun_apply_eq_mvfderiv]
      exact dScalar_eq_two_ricci_grad h y Y
    have hdN : mvfderiv (I := I)
        (fun z : M => gradNormSq (I := I) g f z) y Y
        = 2 * hessianSec (I := I) (metricCov (I := I) g)
            (metricCov_smooth (I := I) g) f f.contMDiff y
            (Curvature.vec2 Y (gradientFun (I := I) g f y)) := by
      rw [← differential1FormFun_apply_eq_mvfderiv]
      exact dGradNormSq g f y Y
    have hdf : mvfderiv (I := I) (fun z : M => σ * f z) y Y
        = σ * g.inner y (gradientFun (I := I) g f y) Y := by
      rw [mvfderiv_const_mul (I := I) σ (f := fun z : M => f z)
        (f.contMDiff.mdifferentiable (by simp) y)]
      have hdfu : mvfderiv (I := I) (fun z : M => f z) y Y
          = g.inner y (gradientFun (I := I) g f y) Y := by
        rw [← differential1FormFun_apply_eq_mvfderiv]
        exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g f y Y
      simp [hdfu]
    have hsoleval := congrArg
      (fun T => T (Curvature.vec2 (I := I) Y (gradientFun (I := I) g f y))) (h y)
    simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      metricTensor0S_apply, smul_eq_mul] at hsoleval
    have hmv : mvfderiv (I := I)
        ((fun z : M => metricScalarAt (I := I) g z
            + gradNormSq (I := I) g f z) - fun z : M => σ * f z) y Y = 0 := by
      change mvfderiv (I := I)
        (((fun z : M => metricScalarAt (I := I) g z)
            + fun z : M => gradNormSq (I := I) g f z)
          - fun z : M => σ * f z) y Y = 0
      rw [mvfderiv_sub (hRd.add hNd) hfd, mvfderiv_add hRd hNd]
      simp only [sub_apply, add_apply, hdR, hdN, hdf]
      rw [g.symm y (gradientFun (I := I) g f y) Y]
      have hv0 : Curvature.vec2 (I := I) Y (gradientFun (I := I) g f y) 0 = Y := rfl
      have hv1 : Curvature.vec2 (I := I) Y (gradientFun (I := I) g f y) 1
          = gradientFun (I := I) g f y := rfl
      rw [hv0, hv1] at hsoleval
      linarith
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv] at hmv
    simpa using hmv
  have hloc : IsLocallyConstant
      ((fun y : M => metricScalarAt (I := I) g y + gradNormSq (I := I) g f y)
        - fun y : M => σ * f y) :=
    DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero (I := I) hFd hzero
  by_cases hne : Nonempty M
  · let x0 : M := Classical.choice hne
    refine ⟨metricScalarAt (I := I) g x0 + gradNormSq (I := I) g f x0
      - σ * f x0, fun x => ?_⟩
    let : PreconnectedSpace M := inferInstance
    exact hloc.apply_eq_of_preconnectedSpace x x0
  · exact ⟨0, fun x => False.elim (hne ⟨x⟩)⟩

end DifferentialGeometry.Geometry.RicciSoliton
