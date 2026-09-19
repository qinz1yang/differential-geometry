import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Prod
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Manifold
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem mfderiv_comp_extChartAt_basis
    (a : M) {f : E → ℝ} {x : M} (hx : x ∈ (chartAt H a).source)
    (hxint : extChartAt I a x ∈ interior (extChartAt I a).target)
    (hf : DifferentiableAt ℝ f (extChartAt I a x)) (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) (f ∘ extChartAt I a) x (chartBasisVecFiber a i x) =
      fderiv ℝ f (extChartAt I a x) (chartModelBasis E i) := by
  have hfM := hf.mdifferentiableAt.comp x (mdifferentiableAt_extChartAt (I := I) hx)
  have heq : scalarOnE (I := I) a (f ∘ extChartAt I a) =ᶠ[𝓝 (extChartAt I a x)] f := by
    filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
    exact congrArg f ((extChartAt I a).right_inv (interior_subset hy))
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt a hfM hx hxint i]
  exact congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) heq.fderiv_eq

variable [I.Boundaryless] [T2Space M]

private theorem inner_cov_gradient_comp_extChartAt_basis
    (g : SmoothRiemannianMetric I M) (a : M) {f : E → ℝ} {x : M}
    (hx : x ∈ (chartAt H a).source) (hf : ContDiffAt ℝ 2 f (extChartAt I a x))
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g)
        (fun y => gradientFun g (f ∘ extChartAt I a) y) x (chartBasisVecFiber a i x))
        (chartBasisVecFiber a j x) =
      fderiv ℝ (fderiv ℝ f) (extChartAt I a x) (chartModelBasis E i) (chartModelBasis E j) -
        ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g a i j k (extChartAt I a x) *
          fderiv ℝ f (extChartAt I a x) (chartModelBasis E k) := by
  classical
  have hxsrc : x ∈ (extChartAt I a).source := by simpa only [extChartAt_source] using hx
  have hxint : extChartAt I a x ∈ interior (extChartAt I a).target := by
    rw [(isOpen_extChartAt_target (I := I) a).interior_eq]
    exact (extChartAt I a).map_source hxsrc
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) a :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hxsrc,
      by simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx, hxint⟩
  have hfM : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f ∘ extChartAt I a) x :=
    hf.contMDiffAt.comp x (contMDiffAt_extChartAt' hx)
  have hgrad := (gradientFun_contMDiffAt_one g hfM).mdifferentiableAt (by norm_num)
  have hY := chartBasisVec_alpha_mdifferentiableAt (I := I) a j hxgood
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply hgrad hY
    (chartBasisVecFiber a i x)
  have heq : (fun y => g.inner y (gradientFun g (f ∘ extChartAt I a) y)
      (chartBasisVecFiber a j y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f (extChartAt I a y) (chartModelBasis E j)) := by
    have hc := (mdifferentiableAt_extChartAt (I := I) hx).continuousAt
    filter_upwards [hc.tendsto.eventually (hf.eventually (by norm_num)),
      (chartLeviCivitaGoodSet_isOpen (I := I) a).mem_nhds hxgood] with y hfy hy
    rw [inner_gradientFun]
    exact mfderiv_comp_extChartAt_basis a
      (chartLeviCivitaGoodSet_mem_chartAt_source hy)
      (chartLeviCivitaGoodSet_extChartAt_mem_interior hy) (hfy.differentiableAt (by norm_num)) j
  have hdf := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hdfj := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const (chartModelBasis E j) (extChartAt I a x))
  have hsecond : mfderiv I 𝓘(ℝ, ℝ)
      (fun y => g.inner y (gradientFun g (f ∘ extChartAt I a) y) (chartBasisVecFiber a j y)) x
        (chartBasisVecFiber a i x) =
      fderiv ℝ (fderiv ℝ f) (extChartAt I a x) (chartModelBasis E i) (chartModelBasis E j) := by
    have hder : (mfderiv I 𝓘(ℝ, ℝ)
        (fun y => g.inner y (gradientFun g (f ∘ extChartAt I a) y) (chartBasisVecFiber a j y)) x :
          TangentSpace I x →L[ℝ] ℝ) =
        mfderiv I 𝓘(ℝ, ℝ)
          ((fun y => fderiv ℝ f y (chartModelBasis E j)) ∘ extChartAt I a) x := heq.mfderiv_eq
    calc
      _ = (mfderiv I 𝓘(ℝ, ℝ)
          ((fun y => fderiv ℝ f y (chartModelBasis E j)) ∘ extChartAt I a) x)
          (chartBasisVecFiber a i x) := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ =>
            L (chartBasisVecFiber a i x)) hder
      _ = _ := by
        rw [mfderiv_comp_extChartAt_basis a hx hxint hdfj.differentiableAt i, hdfj.fderiv]
        simp only [add_apply, ContinuousLinearMap.comp_apply,
          zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
        rfl
  have hconnection : g.inner x (gradientFun g (f ∘ extChartAt I a) x)
      ((LeviCivita (I := I) g) (fun y => chartBasisVecFiber a j y) x (chartBasisVecFiber a i x)) =
      ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g a i j k (extChartAt I a x) *
        fderiv ℝ f (extChartAt I a x) (chartModelBasis E k) := by
    rw [inner_gradientFun, LeviCivita_chartBasisVec_alpha_basis_apply g a i j hxgood]
    change (mfderiv I 𝓘(ℝ, ℝ) (f ∘ extChartAt I a) x : TangentSpace I x →L[ℝ] ℝ)
      (∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g a i j k (extChartAt I a x) •
        chartBasisVecFiber a k x) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul]
    rw [mfderiv_comp_extChartAt_basis a hx hxint (hf.differentiableAt (by norm_num)) k]
    rfl
  rw [hsecond, hconnection] at hmc
  exact (eq_sub_iff_add_eq).mpr hmc.symm

theorem laplacian_comp_extChartAt
    (g : SmoothRiemannianMetric I M) (a : M) {f : E → ℝ} {x : M}
    (hx : x ∈ (chartAt H a).source) (hf : ContDiffAt ℝ 2 f (extChartAt I a x)) :
    laplacian (I := I) (LeviCivita (I := I) g) g (f ∘ extChartAt I a) x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g a i j (extChartAt I a x) *
          (fderiv ℝ (fderiv ℝ f) (extChartAt I a x) (chartModelBasis E i) (chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g a i j k (extChartAt I a x) *
              fderiv ℝ f (extChartAt I a x) (chartModelBasis E k)) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  let basis := chartBasisFamily (I := I) a hbase
  let gInv := fun i j => chartInvGramMatrix (I := I) g a x i j
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g a hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv, chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g a hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv, chartBasisFamily_apply] using hmatrix
  unfold laplacian divergence
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis gInv hinv]
  have hxsrc : x ∈ (extChartAt I a).source := by simpa only [extChartAt_source] using hx
  simp only [chartInvGramOnE_def, (extChartAt I a).left_inv hxsrc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change gInv i j * g.inner x
    ((LeviCivita (I := I) g) (fun y => gradientFun g (f ∘ extChartAt I a) y) x (basis i))
    (basis j) = _
  dsimp only [gInv, basis]
  rw [chartBasisFamily_apply, chartBasisFamily_apply]
  rw [inner_cov_gradient_comp_extChartAt_basis g a hx hf i j]

theorem laplacian_time_slice_comp_extChartAt
    (g : SmoothRiemannianMetric I M) (a : M) {t : ℝ} {x : M}
    (hx : x ∈ (chartAt H a).source) (phi : ℝ × E → ℝ)
    (hphi : ContDiffAt ℝ 2 phi (t, extChartAt I a x)) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => phi (t, extChartAt I a y)) x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g a i j (extChartAt I a x) *
          (fderiv ℝ (fderiv ℝ phi) (t, extChartAt I a x) (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g a i j k (extChartAt I a x) *
              fderiv ℝ phi (t, extChartAt I a x) (0, chartModelBasis E k)) := by
  have hs : ContDiffAt ℝ 2 (fun y => phi (t, y)) (extChartAt I a x) :=
    hphi.comp (extChartAt I a x) (contDiffAt_const.prodMk contDiffAt_id)
  have hd := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp (extChartAt I a x)
    ((hasFDerivAt_const t (extChartAt I a x)).prodMk (hasFDerivAt_id (extChartAt I a x)))
  simp only [Function.comp_def] at hd
  have hh := laplacian_comp_extChartAt g a hx hs
  change laplacian (I := I) (LeviCivita (I := I) g) g
    ((fun y => phi (t, y)) ∘ extChartAt I a) x = _
  rw [hh]
  simp only [Analysis.fderiv_fderiv_const_prod_apply hphi, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply]
end DifferentialGeometry.Geometry.Operator
