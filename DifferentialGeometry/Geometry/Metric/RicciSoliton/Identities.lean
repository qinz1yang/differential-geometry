import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Drift
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Operator.Hessian.TraceFormula
import DifferentialGeometry.Geometry.Operator.WeightedLaplacian
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_divergence
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    {W : ∀ b : M, TangentSpace I b} {x : M}
    (hW : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% W)) :
    (∑ j : Fin (Module.finrank Real E),
        nablaRicci (I := I) g
          (smoothOrthoFrame (I := I) g x j)
          (smoothOrthoFrame (I := I) g x j) W x) +
      g.inner x
        (connLaplacianVector (I := I) g
          (fun b => gradFun (I := I) g f b) x) (W x) = 0 := by
  classical
  let cov := LeviCivita (I := I) g
  let Gf : ∀ b : M, TangentSpace I b := fun b => gradFun (I := I) g f b
  let B : Fin (Module.finrank Real E) → ∀ b : M, TangentSpace I b :=
    fun j => smoothOrthoFrame (I := I) g x j
  have hGf : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g f.contMDiff
  have hB : ∀ j, ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% (B j)) :=
    fun j => smoothOrthoFrame_smooth (I := I) g x j
  have hper : ∀ j,
      nablaRicci (I := I) g (B j) (B j) W x =
        -(g.inner x (cov.toFun (covApply cov (B j) Gf) x (B j x)) (W x) -
          g.inner x (cov.toFun Gf x (cov.toFun (B j) x (B j x))) (W x)) := by
    intro j
    have hQ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞
        (T% (covApply cov (B j) Gf)) :=
      covApply_contMDiff (cov := cov) (hB j) hGf
    have hRic : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun b => ricciTensor (I := I) g b (B j b) (W b)) x :=
      ((ricciTensor_pairing_contMDiff (I := I) g (hB j) hW) x).mdifferentiableAt (by simp)
    have hHess : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun b => g.inner b (covApply cov (B j) Gf b) (W b)) x :=
      ((Operator.contMDiff_g_inner_of_smooth_sections (I := I) g
        ⟨_, hQ⟩ ⟨_, hW⟩) x).mdifferentiableAt (by simp)
    have hMetric : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun b => g.inner b (B j b) (W b)) x :=
      ((Operator.contMDiff_g_inner_of_smooth_sections (I := I) g
        ⟨_, hB j⟩ ⟨_, hW⟩) x).mdifferentiableAt (by simp)
    have hfun :
        (fun b => ricciTensor (I := I) g b (B j b) (W b) +
          g.inner b (covApply cov (B j) Gf b) (W b)) =
        (fun b => (σ / 2) * g.inner b (B j b) (W b)) := by
      funext b
      rw [show g.inner b (covApply cov (B j) Gf b) (W b) =
          hessFun (I := I) g f b (B j b) (W b) by
        exact (hessFun_eq_cov_local (I := I) g isOpen_univ
          f.contMDiff.contMDiffOn (mem_univ b) (B j b) (W b)).symm]
      exact h b (B j b) (W b)
    have hd := congrArg
      (fun q : M → Real => mvfderiv (I := I) q x (B j x)) hfun
    have hdLhs := DFunLike.congr_fun (_root_.mvfderiv_add hRic hHess) (B j x)
    change mvfderiv (I := I)
        (fun b => ricciTensor (I := I) g b (B j b) (W b) +
          g.inner b (covApply cov (B j) Gf b) (W b)) x (B j x) =
      mvfderiv (I := I) (fun b => ricciTensor (I := I) g b (B j b) (W b))
          x (B j x) +
        mvfderiv (I := I) (fun b => g.inner b (covApply cov (B j) Gf b) (W b))
          x (B j x) at hdLhs
    rw [hdLhs] at hd
    have hQat : MDiffAt (T% (covApply cov (B j) Gf)) x :=
      (hQ x).mdifferentiableAt (by simp)
    have hWat : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
    have hBat : MDiffAt (T% (B j)) x := ((hB j) x).mdifferentiableAt (by simp)
    have hdHess := (LeviCivita_isMetricCompatible (I := I) g).apply
      hQat hWat (B j x)
    have hdMetric := (LeviCivita_isMetricCompatible (I := I) g).apply
      hBat hWat (B j x)
    have hdRhs :
        mvfderiv (I := I) (fun b => (σ / 2) * g.inner b (B j b) (W b)) x (B j x) =
          (σ / 2) * mvfderiv (I := I)
            (fun b => g.inner b (B j b) (W b)) x (B j x) :=
      mvfderiv_const_mul_apply (I := I) (σ / 2) (B j x) hMetric
    rw [hdRhs] at hd
    have hdHess' :
        mvfderiv (I := I)
            (fun b => g.inner b (covApply cov (B j) Gf b) (W b)) x (B j x) =
          g.inner x (cov.toFun (covApply cov (B j) Gf) x (B j x)) (W x) +
            g.inner x (covApply cov (B j) Gf x) (cov.toFun W x (B j x)) := by
      rw [show mvfderiv (I := I)
          (fun b => g.inner b (covApply cov (B j) Gf b) (W b)) x (B j x) =
        (mfderiv I (modelWithCornersSelf Real Real)
          (fun b => g.inner b (covApply cov (B j) Gf b) (W b)) x) (B j x) from rfl,
        hdHess]
    have hdMetric' :
        mvfderiv (I := I) (fun b => g.inner b (B j b) (W b)) x (B j x) =
          g.inner x (cov.toFun (B j) x (B j x)) (W x) +
            g.inner x (B j x) (cov.toFun W x (B j x)) := by
      rw [show mvfderiv (I := I) (fun b => g.inner b (B j b) (W b)) x (B j x) =
        (mfderiv I (modelWithCornersSelf Real Real)
          (fun b => g.inner b (B j b) (W b)) x) (B j x) from rfl,
        hdMetric]
    rw [hdHess', hdMetric'] at hd
    have hc1 := h x (cov.toFun (B j) x (B j x)) (W x)
    have hc2 := h x (B j x) (cov.toFun W x (B j x))
    rw [hessFun_eq_cov_local (I := I) g isOpen_univ f.contMDiff.contMDiffOn
      (mem_univ x)] at hc1
    rw [hessFun_eq_cov_local (I := I) g isOpen_univ f.contMDiff.contMDiffOn
      (mem_univ x)] at hc2
    rw [nablaRicci_def]
    change mvfderiv (I := I)
        (fun b => ricciTensor (I := I) g b (B j b) (W b)) x (B j x) -
          ricciTensor (I := I) g x (cov.toFun (B j) x (B j x)) (W x) -
          ricciTensor (I := I) g x (B j x) (cov.toFun W x (B j x)) = _
    dsimp only [covApply, cov, Gf, B] at hd hc1 hc2 ⊢
    linarith
  rw [connLaplacian_grad_inner (I := I) g x]
  change (∑ j, nablaRicci (I := I) g (B j) (B j) W x) +
      ∑ j, (g.inner x (cov.toFun (covApply cov (B j) Gf) x (B j x)) (W x) -
        g.inner x (cov.toFun Gf x (cov.toFun (B j) x (B j x))) (W x)) = 0
  rw [Finset.sum_congr rfl (fun j _ => hper j)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_trace
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M) :
    metricScalarAt (I := I) g x + ΔG (I := I) g f x =
      (Module.finrank Real E : Real) * σ / 2 := by
  classical
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => centeredChartTangentBasis (I := I) x i
  let G : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  have hs :
      (∑ i, ∑ j, G i j *
        (ricciTensor (I := I) g x (B i) (B j) +
          hessFun (I := I) g f x (B i) (B j))) =
      ∑ i, ∑ j, G i j * ((σ / 2) * g.inner x (B i) (B j)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [h x (B i) (B j)]
  have hRic : ∑ i, ∑ j, G i j * ricciTensor (I := I) g x (B i) (B j) =
      metricScalarAt (I := I) g x := by
    exact (metric_scalar_at_eq_chart_ricci_sum (I := I) g x).symm
  have hHess : ∑ i, ∑ j, G i j * hessFun (I := I) g f x (B i) (B j) =
      ΔG (I := I) g f x := by
    change (∑ i, ∑ j, G i j * hessFun (I := I) g f x (B i) (B j)) =
      ΔG (I := I) g ⟨f, f.contMDiff⟩ x
    simpa only [B, G, hessFun_basis_apply] using
      chartInvGram_trace_hessianTensor_eq_laplacian_of_boundaryless
        (I := I) g f.contMDiff x
  have hMetric : ∑ i, ∑ j, G i j * g.inner x (B i) (B j) =
      (Module.finrank Real E : Real) := by
    have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      mem_baseSet_trivializationAt' x
    calc
      ∑ i, ∑ j, G i j * g.inner x (B i) (B j) =
          ∑ i, ∑ j, G i j * chartGramMatrix (I := I) g x x j i := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [chartGramMatrix_apply, chartBasisVecFiber_self,
              chartBasisVecFiber_self, g.symm]
      _ = ∑ i, (1 : Matrix (Fin (Module.finrank Real E))
          (Fin (Module.finrank Real E)) Real) i i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← Matrix.mul_apply,
              chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase]
      _ = (Module.finrank Real E : Real) := by simp
  rw [show (∑ i, ∑ j, G i j *
      (ricciTensor (I := I) g x (B i) (B j) +
        hessFun (I := I) g f x (B i) (B j))) =
      (∑ i, ∑ j, G i j * ricciTensor (I := I) g x (B i) (B j)) +
        ∑ i, ∑ j, G i j * hessFun (I := I) g f x (B i) (B j) by
      simp only [mul_add, Finset.sum_add_distrib], hRic, hHess] at hs
  rw [show (∑ i, ∑ j, G i j * ((σ / 2) * g.inner x (B i) (B j))) =
      (σ / 2) * ∑ i, ∑ j, G i j * g.inner x (B i) (B j) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring, hMetric] at hs
  linarith

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_trace_differential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    {W : ∀ b : M, TangentSpace I b} {x : M} :
    nablaScalar (I := I) g W x +
      mvfderiv (I := I) (ΔG (I := I) g f) x (W x) = 0 := by
  have hScalarFun :
      (fun b : M => scalarCurv (I := I) g b) =
        fun b => metricScalarAt (I := I) g b := by
    funext b
    exact (metricScalar_eq_scal (I := I) g b).symm
  have hScalar : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun b : M => scalarCurv (I := I) g b) x := by
    rw [hScalarFun]
    exact (metricScalar_smooth (I := I) (M := M) g x).mdifferentiableAt (by simp)
  have hLap : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (ΔG (I := I) g f) x :=
    ((Δ_g_contMDiff (I := I) g f) x).mdifferentiableAt (by simp)
  have hfun :
      (fun b : M => scalarCurv (I := I) g b + ΔG (I := I) g f b) =
        fun _ : M => (Module.finrank Real E : Real) * σ / 2 := by
    funext b
    rw [← metricScalar_eq_scal (I := I) g b]
    exact gradientRicciSoliton_trace h b
  have hd := congrArg (fun q : M → Real => mvfderiv (I := I) q x (W x)) hfun
  have hdLhs := DFunLike.congr_fun (_root_.mvfderiv_add hScalar hLap) (W x)
  change mvfderiv (I := I)
      (fun b : M => scalarCurv (I := I) g b + ΔG (I := I) g f b) x (W x) =
    mvfderiv (I := I) (fun b : M => scalarCurv (I := I) g b) x (W x) +
      mvfderiv (I := I) (ΔG (I := I) g f) x (W x) at hdLhs
  rw [hdLhs] at hd
  have hdRhs : mvfderiv (I := I)
      (fun _ : M => (Module.finrank Real E : Real) * σ / 2) x (W x) = 0 := by
    rw [_root_.mvfderiv_const]
    rfl
  rw [hdRhs] at hd
  rw [nablaScalar_def]
  exact hd

omit [SigmaCompactSpace M] in
private theorem gradientRicciSoliton_differential_scalar_of_neZero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I)
        (fun b : M => metricScalarAt (I := I) g b) x (fun _ : Fin 1 => v) =
      2 * ricciTensor (I := I) g x (gradFun (I := I) g f x) v := by
  let Wsec := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose
  let W : ∀ b : M, TangentSpace I b := fun b => Wsec b
  have hWx : W x = v := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose_spec
  have hW : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% W) :=
    Wsec.contMDiff
  have hdiv := gradientRicciSoliton_divergence h (x := x) hW
  rw [contracted_second_bianchi (I := I) g hW] at hdiv
  have htrace := gradientRicciSoliton_trace_differential h (W := W) (x := x)
  have hheart := heartOfBochnerInner_holds (I := I) g f.contMDiff x v
  have hfMap : (⟨(f : M → Real), f.contMDiff⟩ : C^∞⟮I, M; Real⟯) = f := by
    apply ContMDiffMap.ext
    intro b
    rfl
  rw [hfMap] at hheart
  have hlap :
      g.inner x (gradFun (I := I) g (ΔG (I := I) g f) x) v =
        mvfderiv (I := I) (ΔG (I := I) g f) x v := by
    rw [inner_gradFun]
    rfl
  rw [hWx, hheart, hlap,
    inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) v] at hdiv
  rw [differential1FormFun_apply_eq_mvfderiv]
  have hScalarFun :
      (fun b : M => metricScalarAt (I := I) g b) =
        fun b => scalarCurv (I := I) g b := by
    funext b
    exact metricScalar_eq_scal (I := I) g b
  rw [hScalarFun]
  rw [nablaScalar_def] at htrace
  rw [hWx] at htrace
  rw [nablaScalar_def, hWx] at hdiv
  linarith

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open Curvature Operator Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [I.Boundaryless]

theorem gradientRicciSoliton_differential_scalar
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I)
        (fun b : M => metricScalarAt (I := I) g b) x (fun _ : Fin 1 => v) =
      2 * ricciTensor (I := I) g x (gradFun (I := I) g f x) v := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have hE : Subsingleton E := (Module.finrank_zero_iff (R := Real) (M := E)).mp hdim
    have hv : v = 0 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
      exact hE.elim _ _
    rw [hv]
    rw [differential1FormFun_apply_eq_mvfderiv]
    simp
  · let _ : NeZero (Module.finrank Real E) := ⟨hdim⟩
    exact gradientRicciSoliton_differential_scalar_of_neZero h x v

private theorem gradientRicciSoliton_hamilton_differential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (x : M) (v : TangentSpace I x) :
    mvfderiv (I := I) (fun b : M =>
      metricScalarAt (I := I) g b +
        g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b) - σ * f b) x v = 0 := by
  let V : ∀ b : M, TangentSpace I b := fun b => gradFun (I := I) g f b
  have hV : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% V) :=
    gradFun_contMDiff_total_section (I := I) g f.contMDiff
  have hR := gradientRicciSoliton_differential_scalar h x v
  rw [differential1FormFun_apply_eq_mvfderiv] at hR
  have hNorm := Connection.mvfderiv_inner_self (I := I) g hV x v
  have hSol := h x v (V x)
  rw [hessFun_eq_cov_local (I := I) g isOpen_univ f.contMDiff.contMDiffOn
    (mem_univ x)] at hSol
  rw [Curvature.ricciTensor_symm (I := I) g x v (V x),
    g.symm x v (V x)] at hSol
  have hdf := inner_gradFun (I := I) g f x v
  have hdf' : mvfderiv (I := I) f x v = g.inner x (V x) v := by
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv, ← hdf]
    rfl
  have hScalarDiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun b : M => metricScalarAt (I := I) g b) x :=
    (metricScalar_smooth (I := I) (M := M) g x).mdifferentiableAt (by simp)
  have hNormDiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun b : M => g.inner b (V b) (V b)) x :=
    ((normGradSq_contMDiff (I := I) g f.contMDiff) x).mdifferentiableAt (by simp)
  have hfDiff : MDifferentiableAt I (modelWithCornersSelf Real Real) f x :=
    (f.contMDiff x).mdifferentiableAt (by simp)
  have hSigmaDiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun b : M => σ * f b) x :=
    (mdifferentiableAt_const (c := σ)).mul hfDiff
  change mvfderiv (I := I)
      ((fun b : M => metricScalarAt (I := I) g b) +
        (fun b : M => g.inner b (V b) (V b)) - (fun b : M => σ * f b)) x v = 0
  rw [_root_.mvfderiv_sub (hScalarDiff.add hNormDiff) hSigmaDiff,
    _root_.mvfderiv_add hScalarDiff hNormDiff]
  change mvfderiv (I := I) (fun b : M => metricScalarAt (I := I) g b) x v +
      mvfderiv (I := I) (fun b : M => g.inner b (V b) (V b)) x v -
        mvfderiv (I := I) (fun b : M => σ * f b) x v = 0
  rw [mvfderiv_const_mul_apply (I := I) σ v hfDiff]
  dsimp only [V] at hNorm hSol hdf' ⊢
  rw [hR, hNorm, hdf']
  nlinarith [hSol]

theorem gradientRicciSoliton_hamilton_constant [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) :
    ∃ C : Real, ∀ x : M,
      metricScalarAt (I := I) g x +
          g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) - σ * f x = C := by
  let Q : M → Real := fun b =>
    metricScalarAt (I := I) g b +
      g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b) - σ * f b
  have hQ : ContMDiff I (modelWithCornersSelf Real Real) ∞ Q :=
    ((metricScalar_smooth (I := I) (M := M) g).add
      (normGradSq_contMDiff (I := I) g f.contMDiff)).sub
        (contMDiff_const.mul f.contMDiff)
  have hmdiff : MDifferentiable I (modelWithCornersSelf Real Real) Q :=
    hQ.mdifferentiable (by simp)
  have hzero : ∀ x : M, mfderiv I (modelWithCornersSelf Real Real) Q x = 0 := by
    intro x
    ext v
    apply (NormedSpace.fromTangentSpace (Q x)).injective
    simp only [zero_apply, map_zero]
    rw [← DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    exact gradientRicciSoliton_hamilton_differential h x v
  have hloc : IsLocallyConstant Q :=
    DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero (I := I) hmdiff hzero
  obtain ⟨C, hC⟩ := hloc.exists_eq_const
  refine ⟨C, fun x => ?_⟩
  exact congrFun hC x

theorem gradientRicciSoliton_weightedLaplacian_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ C : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (hC : ∀ x : M,
      metricScalarAt (I := I) g x +
          g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) - σ * f x = C)
    (x : M) :
    weightedLaplacian (I := I) g f f x =
      (Module.finrank Real E : Real) * σ / 2 - σ * f x - C := by
  rw [weightedLaplacian_apply]
  have htrace := gradientRicciSoliton_trace h x
  nlinarith [hC x]

private theorem gradientRicciSoliton_laplacian_scalar
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M) :
    ΔG (I := I) g
        ⟨(fun b : M => metricScalarAt (I := I) g b),
          metricScalar_smooth (I := I) (M := M) g⟩ x =
      mvfderiv (I := I) (fun b : M => metricScalarAt (I := I) g b) x
          (gradFun (I := I) g f x) +
        2 * inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) f f.contMDiff x) := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨(fun b : M => metricScalarAt (I := I) g b),
      metricScalar_smooth (I := I) (M := M) g⟩
  let RG := Curvature.ricGradVec (I := I) g f.contMDiff
  have hfMap : (⟨(f : M → Real), f.contMDiff⟩ : C^∞⟮I, M; Real⟯) = f := by
    apply ContMDiffMap.ext
    intro b
    rfl
  have hgrad : gradG (I := I) g R = RG + RG := by
    ext y
    apply metricFlatLinear_injective (I := I) g y
    ext w
    simp only [metricFlatLinear_apply]
    rw [grad_g_apply]
    change g.inner y (gradientFun (I := I) g R y) w =
      g.inner y (RG y + RG y) w
    rw [map_add, add_apply, inner_gradientFun]
    have hscalar := gradientRicciSoliton_differential_scalar h y w
    rw [differential1FormFun_apply_eq_mvfderiv] at hscalar
    have hgradf :
        gradG (I := I) g
            (⟨(f : M → Real), f.contMDiff⟩ : C^∞⟮I, M; Real⟯) y =
          gradFun (I := I) g f y := by
      rw [hfMap, grad_g_apply]
    rw [Curvature.ricGradVec_apply, cotangentSharp_inner_eval,
      Curvature.ricGradForm_apply, tensor0S_curry_one_apply, hgradf]
    change mvfderiv (I := I) R y w =
      metricRicciAt (I := I) (M := M) g y
          (vec2 (I := I) (gradFun (I := I) g f y) w) +
        metricRicciAt (I := I) (M := M) g y
          (vec2 (I := I) (gradFun (I := I) g f y) w)
    rw [metricRicciAt_apply_eq_ricciTensor]
    dsimp only [R]
    change mvfderiv (I := I)
        (fun b : M => metricScalarAt (I := I) g b) y w =
      ricciTensor (I := I) g y (gradFun (I := I) g f y) w +
        ricciTensor (I := I) g y (gradFun (I := I) g f y) w
    linarith
  have hlap : ΔG (I := I) g R x =
      divergenceG (I := I) g RG x + divergenceG (I := I) g RG x := by
    change divergenceG (I := I) g (gradG (I := I) g R) x = _
    rw [hgrad, divergence_g_add]
  have hdiv := Curvature.divergence_ricGradVec (I := I) g f.contMDiff x
  have hbridge := divergence_levi_eq (I := I) g RG x
  rw [hfMap] at hdiv
  rw [grad_g_apply] at hdiv
  change divergence (I := I) (LeviCivita (I := I) g) RG.toFun x = _ at hdiv
  rw [hbridge] at hdiv
  change ΔG (I := I) g R x = _
  rw [hlap, hdiv]
  ring

theorem gradientRicciSoliton_weightedLaplacian_scalar
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (x : M) :
    weightedLaplacian (I := I) g f
        ⟨(fun b : M => metricScalarAt (I := I) g b),
          metricScalar_smooth (I := I) (M := M) g⟩ x =
      σ * metricScalarAt (I := I) g x -
        2 * Tensor0SBundle.normSq0S (I := I) g x 2
          (metricRicciAt (I := I) (M := M) g x) := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨(fun b : M => metricScalarAt (I := I) g b),
      metricScalar_smooth (I := I) (M := M) g⟩
  let Ric := metricRicciAt (I := I) (M := M) g x
  let Hess := hessianSec (I := I) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) f f.contMDiff x
  have hlap := gradientRicciSoliton_laplacian_scalar h x
  have hdrift :
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g R x) =
        mvfderiv (I := I) R x (gradFun (I := I) g f x) := by
    rw [g.symm x, ← Connection.gradient_eq_gradFun, inner_gradientFun]
  have hmc : IsMetricCompatible (I := I)
      (metricCov (I := I) (M := M) g) g := by
    rw [show metricCov (I := I) (M := M) g =
      leviCivitaConnectionOfMetric (I := I) g by rfl]
    exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  have hGradEq : (fun y : M => gradientFun (I := I) g f y) =
      fun y : M => gradFun (I := I) g f y := by
    funext y
    exact Connection.gradient_eq_gradFun (I := I) g f y
  have hTensor : Hess =
      (σ / 2) • metricTensor0S (I := I) g x - Ric := by
    ext slots
    have hslots : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots, Tensor0SBundle.Tensor0SSpace.sub_apply,
      Tensor0SBundle.Tensor0SSpace.smul_apply,
      metricTensor0S_apply, metricRicciAt_apply_eq_ricciTensor]
    change hessianSec (I := I) (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g) f f.contMDiff x
          (vec2 (I := I) (slots 0) (slots 1)) = _
    rw [hessSec_inner_cov (I := I) (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g) g hmc f f.contMDiff x]
    rw [show metricCov (I := I) (M := M) g = LeviCivita (I := I) g by rfl]
    rw [hGradEq]
    rw [← hessFun_eq_cov_local (I := I) g isOpen_univ f.contMDiff.contMDiffOn
      (mem_univ x)]
    change hessFun (I := I) g f x (slots 0) (slots 1) =
      σ / 2 * g.inner x (slots 0) (slots 1) -
        ricciTensor (I := I) g x (slots 0) (slots 1)
    linarith [h x (slots 0) (slots 1)]
  have htrace : inner02 (I := I) g x Ric (metricTensor0S (I := I) g x) =
      metricScalarAt (I := I) g x := by
    rw [inner02_symm]
    rfl
  have hnorm : inner02 (I := I) g x Ric Ric =
      Tensor0SBundle.normSq0S (I := I) g x 2 Ric := by
    rfl
  have hinner : inner02 (I := I) g x Ric Hess =
      (σ / 2) * metricScalarAt (I := I) g x -
        Tensor0SBundle.normSq0S (I := I) g x 2 Ric := by
    change Tensor0SBundle.inner0S (I := I) g x 2 Ric Hess = _
    rw [hTensor, Tensor0SBundle.inner0S_sub_right,
      Tensor0SBundle.inner0S_smul_right]
    change (σ / 2) * inner02 (I := I) g x Ric (metricTensor0S (I := I) g x) -
        inner02 (I := I) g x Ric Ric = _
    rw [htrace, hnorm]
  change weightedLaplacian (I := I) g f R x = _
  change g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g (fun b : M => metricScalarAt (I := I) g b) x) =
    mvfderiv (I := I) (fun b : M => metricScalarAt (I := I) g b) x
      (gradFun (I := I) g f x) at hdrift
  rw [weightedLaplacian_apply]
  change ΔG (I := I) g R x -
      g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g
          (fun b : M => metricScalarAt (I := I) g b) x) = _
  rw [hlap, hdrift]
  dsimp only [Ric, Hess] at hinner ⊢
  rw [hinner]
  ring

omit [T2Space M] [I.Boundaryless] in
def hamiltonNormalized
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (σ : Real) : Prop :=
  ∀ x : M,
    metricScalarAt (I := I) g x +
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = σ * f x

omit [T2Space M] [I.Boundaryless] in
private theorem gradFun_add_const
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (c : Real) (x : M) :
    gradFun (I := I) g
      ((f + ContMDiffMap.const (I := I) (I' := modelWithCornersSelf Real Real)
        (M := M) (n := ∞) c) : C^∞⟮I, M; Real⟯) x =
        gradFun (I := I) g f x := by
  change gradFun (I := I) g ((f : M → Real) + fun _ : M => c) x =
    gradFun (I := I) g f x
  rw [Operator.gradFun_add (I := I) g
    ((f.contMDiff x).mdifferentiableAt (by simp)) (mdifferentiableAt_const (c := c)),
    Operator.gradFun_const, add_zero]

theorem gradientRicciSoliton_existsUnique_hamiltonNormalized_add_const
    [ConnectedSpace M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (hσ : σ ≠ 0) :
    ∃! c : Real, hamiltonNormalized (I := I) g (f + ContMDiffMap.const c) σ := by
  obtain ⟨C, hC⟩ := gradientRicciSoliton_hamilton_constant h
  let c := C / σ
  have hc : hamiltonNormalized (I := I) g (f + ContMDiffMap.const c) σ := by
    intro x
    rw [gradFun_add_const]
    change metricScalarAt (I := I) g x +
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
      σ * (f x + c)
    calc
      _ = σ * f x + C := by linarith [hC x]
      _ = σ * (f x + c) := by
        dsimp only [c]
        field_simp
  refine ⟨c, hc, ?_⟩
  intro d hd
  let x : M := Classical.choice inferInstance
  have hc' := hc x
  have hd' := hd x
  rw [gradFun_add_const] at hc' hd'
  change metricScalarAt (I := I) g x +
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
    σ * (f x + c) at hc'
  change metricScalarAt (I := I) g x +
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
    σ * (f x + d) at hd'
  have heq : σ * c = σ * d := by nlinarith [hc', hd']
  exact (mul_left_cancel₀ hσ heq).symm

theorem gradientRicciSoliton_fundamental_identities [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) :
    (metricScalarAt (I := I) g + ΔG (I := I) g f =
        fun _ : M => (Module.finrank Real E : Real) * σ / 2) ∧
      (∀ x : M, ∀ v : TangentSpace I x,
        differential1FormFun (I := I)
            (fun b : M => metricScalarAt (I := I) g b) x
            (fun _ : Fin 1 => v) =
          2 * ricciTensor (I := I) g x (gradFun (I := I) g f x) v) ∧
      (∃ C : Real, (∀ x : M,
          metricScalarAt (I := I) g x +
              g.inner x (gradFun (I := I) g f x)
                (gradFun (I := I) g f x) - σ * f x = C) ∧
        (∀ x : M,
          weightedLaplacian (I := I) g f f x =
            (Module.finrank Real E : Real) * σ / 2 - σ * f x - C)) ∧
      (∀ x : M,
        weightedLaplacian (I := I) g f
            ⟨(fun b : M => metricScalarAt (I := I) g b),
              metricScalar_smooth (I := I) (M := M) g⟩ x =
          σ * metricScalarAt (I := I) g x -
            2 * Tensor0SBundle.normSq0S (I := I) g x 2
              (metricRicciAt (I := I) (M := M) g x)) := by
  have htrace : ∀ x : M,
      metricScalarAt (I := I) g x + ΔG (I := I) g f x =
        (Module.finrank Real E : Real) * σ / 2 :=
    gradientRicciSoliton_trace h
  have hdiff : ∀ x : M, ∀ v : TangentSpace I x,
      differential1FormFun (I := I)
          (fun b : M => metricScalarAt (I := I) g b) x
          (fun _ : Fin 1 => v) =
        2 * ricciTensor (I := I) g x (gradFun (I := I) g f x) v :=
    gradientRicciSoliton_differential_scalar h
  obtain ⟨C, hC⟩ := gradientRicciSoliton_hamilton_constant h
  have hpot : ∀ x : M,
      weightedLaplacian (I := I) g f f x =
        (Module.finrank Real E : Real) * σ / 2 - σ * f x - C :=
    fun x => gradientRicciSoliton_weightedLaplacian_potential h hC x
  have hscalar : ∀ x : M,
      weightedLaplacian (I := I) g f
          ⟨(fun b : M => metricScalarAt (I := I) g b),
            metricScalar_smooth (I := I) (M := M) g⟩ x =
        σ * metricScalarAt (I := I) g x -
          2 * Tensor0SBundle.normSq0S (I := I) g x 2
            (metricRicciAt (I := I) (M := M) g x) :=
    gradientRicciSoliton_weightedLaplacian_scalar h
  refine ⟨?_, hdiff, ⟨C, hC, hpot⟩, hscalar⟩
  funext x
  exact htrace x

end DifferentialGeometry.Geometry
