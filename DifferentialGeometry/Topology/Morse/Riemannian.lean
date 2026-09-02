import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Analysis.Integration.CauchyPeak
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity
import DifferentialGeometry.Geometry.Operator.NormGradSq
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Matrix MeasureTheory Set
open scoped Manifold Matrix Topology ContDiff

private abbrev Plane := EuclideanSpace Real (Fin 2)

section Model

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private noncomputable def modelToPlane
    (hdim : Module.finrank Real E = 2) :
    E ≃L[Real] Plane :=
  (toEuclidean (E := E)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 Real Real (finCongr hdim)).toContinuousLinearEquiv

private lemma modelToPlane_measurePreserving
    (hdim : Module.finrank Real E = 2) :
    MeasurePreserving (modelToPlane (E := E) hdim)
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)) volume := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 Real Real (finCongr hdim)
  have hfirst : MeasurePreserving (toEuclidean (E := E))
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)) volume := by
    refine ⟨(toEuclidean (E := E)).continuous.measurable, ?_⟩
    exact DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
  refine ⟨(modelToPlane (E := E) hdim).continuous.measurable, ?_⟩
  change Measure.map (e ∘ toEuclidean (E := E))
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)) = volume
  rw [← Measure.map_map
    e.continuous.measurable (toEuclidean (E := E)).continuous.measurable,
    hfirst.map_eq, e.measurePreserving.map_eq]

private lemma modelToPlane_symm_basis
    (hdim : Module.finrank Real E = 2) (i : Fin 2) :
    (modelToPlane (E := E) hdim).symm
        ((EuclideanSpace.basisFun (Fin 2) Real).toBasis i) =
      DifferentialGeometry.Integral.Measure.chartModelBasis E ((finCongr hdim).symm i) := by
  simp [modelToPlane, EuclideanSpace.basisFun_apply,
    DifferentialGeometry.Integral.Measure.chartModelBasis_apply]

end Model

private def choleskyMatrix (A : Matrix (Fin 2) (Fin 2) Real) :
    Matrix (Fin 2) (Fin 2) Real :=
  !![Real.sqrt (A 0 0), A 0 1 / Real.sqrt (A 0 0);
     0, Real.sqrt (A.det / A 0 0)]

private noncomputable def matrixToPlaneCLM :
    Matrix (Fin 2) (Fin 2) Real ≃L[Real] (Plane →L[Real] Plane) :=
  ((Matrix.toEuclideanLin (𝕜 := Real) (m := Fin 2) (n := Fin 2)).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

private lemma matrixToPlaneCLM_apply
    (A : Matrix (Fin 2) (Fin 2) Real) (x : Plane) :
    matrixToPlaneCLM A x = Matrix.toEuclideanLin A x :=
  rfl

private lemma matrixToPlaneCLM_det
    (A : Matrix (Fin 2) (Fin 2) Real) :
    (matrixToPlaneCLM A).det = A.det := by
  rw [ContinuousLinearMap.det]
  change LinearMap.det (Matrix.toLpLin 2 2 A) = A.det
  rw [Matrix.toLpLin_eq_toLin, LinearMap.det_toLin]

private lemma choleskyMatrix_norm_sq
    {A : Matrix (Fin 2) (Fin 2) Real} (hA : A.PosDef)
    (x : EuclideanSpace Real (Fin 2)) :
    ‖Matrix.toEuclideanLin (choleskyMatrix A) x‖ ^ 2 =
      star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
  have h00 : 0 < A 0 0 := hA.diag_pos
  have hdet : 0 < A.det := hA.det_pos
  have hsymm : A 1 0 = A 0 1 := by
    simpa using (congrFun (congrFun hA.isHermitian.eq 1) 0).symm
  have hsqrt00 : Real.sqrt (A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt h00.le
  have hsqrtdet : Real.sqrt (A.det / A 0 0) ^ 2 = A.det / A 0 0 :=
    Real.sq_sqrt (div_nonneg hdet.le h00.le)
  have hsqrt00_ne : Real.sqrt (A 0 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h00)
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  simp only [Matrix.mulVec, dotProduct, choleskyMatrix, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two,
    Matrix.cons_val_one, zero_mul, zero_add, Pi.star_apply, star_trivial]
  rw [Matrix.det_fin_two, hsymm] at hsqrtdet
  rw [Matrix.det_fin_two, hsymm]
  field_simp [hsqrt00_ne, ne_of_gt h00]
  rw [hsqrt00]
  rw [show A 0 1 * A 0 1 = A 0 1 ^ 2 by ring] at hsqrtdet
  rw [hsqrtdet]
  field_simp [ne_of_gt h00]
  ring

private lemma choleskyMatrix_det
    {A : Matrix (Fin 2) (Fin 2) Real} (hA : A.PosDef) :
    (choleskyMatrix A).det = Real.sqrt A.det := by
  have h00 : 0 < A 0 0 := hA.diag_pos
  have hdet : 0 < A.det := hA.det_pos
  simp only [choleskyMatrix, Fin.isValue, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    mul_zero, sub_zero]
  rw [← Real.sqrt_mul (le_of_lt h00)]
  congr 1
  field_simp [ne_of_gt h00]

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private def planeGram (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (z : Plane) :
    Matrix (Fin 2) (Fin 2) Real :=
  fun i j => chartGramOnE (I := I) g p
    ((finCongr hdim).symm i) ((finCongr hdim).symm j)
    ((modelToPlane (E := E) hdim).symm z)

private def planeGradientCoordinates (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (f : M → Real) (z : Plane) : Plane :=
  WithLp.toLp 2 fun i => gradChartCoeffOnE (I := I) g p f
    ((finCongr hdim).symm i) ((modelToPlane (E := E) hdim).symm z)

private def choleskyGradientCoordinates (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (f : M → Real) (z : Plane) : Plane :=
  Matrix.toEuclideanLin (choleskyMatrix (planeGram (I := I) hdim g p z))
    (planeGradientCoordinates (I := I) hdim g p f z)

omit [I.Boundaryless] in
private lemma planeGram_posDef (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) {z : Plane}
    (hz : (modelToPlane (E := E) hdim).symm z ∈ (extChartAt I p).target) :
    (planeGram (I := I) hdim g p z).PosDef := by
  let y := (modelToPlane (E := E) hdim).symm z
  let x := (extChartAt I p).symm y
  have hxsource : x ∈ (extChartAt I p).source := (extChartAt I p).map_target hz
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hxsource
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hpos := chartGramMatrix_posDef (I := I) g p hxbase
  exact hpos.submatrix (finCongr hdim).symm.injective

private lemma partialDeriv_gradChartCoeffOnE_at_critical_of_hessFun_eq_smul_metric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) {c : Real}
    (hhess : ∀ v w : TangentSpace I p,
      hessFun (I := I) g f p v w = c * g.inner p v w)
    (k i : Fin (Module.finrank Real E)) :
    partialDeriv (E := E) k (gradChartCoeffOnE (I := I) g p f i)
        (extChartAt I p p) = if i = k then c else 0 := by
  let y := extChartAt I p p
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hytarget : y ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hpsource_ext
  have hyint : y ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hytarget
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hpartial : ∀ j : Fin (Module.finrank Real E),
      partialDeriv (E := E) j (scalarOnE (I := I) p f) y = 0 := by
    intro j
    have hbridge :=
      mfderiv_scalar_eq_chart_fderiv
        (I := I) p f hpsource hyint
          (f.contMDiff.mdifferentiable (by simp) p)
          (centeredChartTangentBasis (I := I) p j)
    have hzero : mvfderiv (I := I) f p
        (centeredChartTangentBasis (I := I) p j) = 0 := by
      change (mfderiv I 𝓘(Real, Real) f p)
        (centeredChartTangentBasis (I := I) p j) = 0
      rw [hcrit]
      rfl
    rw [hzero, trivToE_self_apply, centeredChartTangentBasis_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hbridge
    unfold partialDeriv scalarOnE
    simpa [Function.comp_def, y] using hbridge.symm
  have hiter : ∀ a b : Fin (Module.finrank Real E),
      chartIteratedPartialDeriv (I := I) p f a b y =
        c * chartGramMatrix (I := I) g p p a b := by
    intro a b
    have hab := hhess (centeredChartTangentBasis (I := I) p a)
      (centeredChartTangentBasis (I := I) p b)
    rw [hessFun_basis_apply, chartHessianTensor_def] at hab
    have hgram :
        g.inner p (centeredChartTangentBasis (I := I) p a)
            (centeredChartTangentBasis (I := I) p b) =
          chartGramMatrix (I := I) g p p a b := by
      rw [chartGramMatrix_apply, chartBasisVecFiber_self, chartBasisVecFiber_self]
    rw [hgram] at hab
    simpa only [y, hpartial, mul_zero, Finset.sum_const_zero, sub_zero] using hab
  rw [partialDeriv_gradChartCoeffOnE (I := I) g p f.contMDiff k i hyint]
  simp only [hpartial, mul_zero, zero_add, hiter, ← mul_assoc]
  have hsymmy : (extChartAt I p).symm y = p := (extChartAt I p).left_inv hpsource_ext
  simp only [chartInvGramOnE, hsymmy]
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g p hbase
  have hentry := congrFun (congrFun hmul i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  have hsymm : ∀ j, chartGramMatrix (I := I) g p p k j =
      chartGramMatrix (I := I) g p p j k := by
    intro j
    exact g.symm p _ _
  calc
    (∑ j, chartInvGramMatrix (I := I) g p p i j * c *
        chartGramMatrix (I := I) g p p k j) =
        c * (∑ j, chartInvGramMatrix (I := I) g p p i j *
          chartGramMatrix (I := I) g p p j k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [← hsymm j]; ring
    _ = c * (if i = k then 1 else 0) := by rw [hentry]
    _ = if i = k then c else 0 := by split_ifs <;> simp

private lemma planeGradientCoordinates_hasFDerivAt
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) {c : Real}
    (hhess : ∀ v w : TangentSpace I p,
      hessFun (I := I) g f p v w = c * g.inner p v w) :
    HasFDerivAt (planeGradientCoordinates (I := I) hdim g p f)
      (c • (1 : Plane →L[Real] Plane))
      (modelToPlane (E := E) hdim (extChartAt I p p)) := by
  let e := modelToPlane (E := E) hdim
  let z₀ : Plane := e (extChartAt I p p)
  let y₀ : E := extChartAt I p p
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hy₀target : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hpsource_ext
  have hy₀int : y₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hy₀target
  have hcoeffSmooth : ∀ i : Fin 2, ContDiffAt Real ∞
      (fun z : Plane => gradChartCoeffOnE (I := I) g p f
        ((finCongr hdim).symm i) (e.symm z)) z₀ := by
    intro i
    have hbase := gradChartCoeffOnE_contDiffOn_interior (I := I) g p f.contMDiff
      ((finCongr hdim).symm i)
    have hat : ContDiffAt Real ∞
        (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) y₀ :=
      hbase.contDiffAt (isOpen_interior.mem_nhds hy₀int)
    have hat' : ContDiffAt Real ∞
        (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i))
          (e.symm z₀) := by
      simpa only [z₀, y₀, ContinuousLinearEquiv.symm_apply_apply] using hat
    exact hat'.comp z₀ e.symm.contDiff.contDiffAt
  have hsmooth : ContDiffAt Real ∞
      (planeGradientCoordinates (I := I) hdim g p f) z₀ := by
    apply contDiffAt_piLp'
    intro i
    simpa only [planeGradientCoordinates] using hcoeffSmooth i
  have hdiff : DifferentiableAt Real
      (planeGradientCoordinates (I := I) hdim g p f) z₀ :=
    hsmooth.differentiableAt (by simp)
  have hfd : fderiv Real (planeGradientCoordinates (I := I) hdim g p f) z₀ =
      c • (1 : Plane →L[Real] Plane) := by
    apply ContinuousLinearMap.ext
    intro v
    have hlin :
        (fderiv Real (planeGradientCoordinates (I := I) hdim g p f) z₀).toLinearMap =
          (c • (1 : Plane →L[Real] Plane)).toLinearMap := by
      apply (EuclideanSpace.basisFun (Fin 2) Real).toBasis.ext
      intro k
      ext i
      let proj : Plane →L[Real] Real := PiLp.proj 2 (fun _ : Fin 2 => Real) i
      have hproj := fderiv_comp z₀ proj.differentiableAt hdiff
      have hprojApply := congrArg
        (fun L : Plane →L[Real] Real =>
          L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hproj
      have hcoeffDiff : DifferentiableAt Real
          (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) y₀ :=
        ((gradChartCoeffOnE_contDiffOn_interior (I := I) g p f.contMDiff
          ((finCongr hdim).symm i)).contDiffAt
            (isOpen_interior.mem_nhds hy₀int)).differentiableAt (by simp)
      have hcoeffDiff' : DifferentiableAt Real
          (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) (e.symm z₀) := by
        simpa only [z₀, y₀, ContinuousLinearEquiv.symm_apply_apply] using hcoeffDiff
      have hcomp := fderiv_comp z₀ hcoeffDiff' e.symm.differentiableAt
      have hcompApply := congrArg
        (fun L : Plane →L[Real] Real =>
          L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hcomp
      rw [e.symm.fderiv] at hcompApply
      simp only [ContinuousLinearMap.comp_apply] at hcompApply
      have hpartial :=
        partialDeriv_gradChartCoeffOnE_at_critical_of_hessFun_eq_smul_metric
          (I := I) g f p hcrit hhess ((finCongr hdim).symm k)
            ((finCongr hdim).symm i)
      simp only [Function.comp_def, planeGradientCoordinates,
        proj, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply] at hprojApply
      have hbasis : (e.symm : Plane →L[Real] E)
          ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) =
            chartModelBasis E ((finCongr hdim).symm k) := by
        simpa only [e, ContinuousLinearEquiv.coe_coe] using
          modelToPlane_symm_basis (E := E) hdim k
      rw [hbasis] at hcompApply
      rw [show e.symm z₀ = y₀ by simp only [z₀, y₀,
        ContinuousLinearEquiv.symm_apply_apply]] at hcompApply
      change _ = partialDeriv (E := E) ((finCongr hdim).symm k)
        (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) y₀
        at hcompApply
      rw [hpartial] at hcompApply
      change proj
          ((fderiv Real (planeGradientCoordinates (I := I) hdim g p f) z₀)
            ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) =
        proj ((c • (1 : Plane →L[Real] Plane))
          ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k))
      rw [← hprojApply]
      change (fderiv Real
        (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i) ∘ e.symm) z₀)
          ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) = _
      rw [hcompApply]
      simp [EuclideanSpace.basisFun_apply, proj, PiLp.proj_apply]
    exact DFunLike.congr_fun hlin v
  change HasFDerivAt (planeGradientCoordinates (I := I) hdim g p f)
    (c • (1 : Plane →L[Real] Plane)) z₀
  rw [← hfd]
  exact hdiff.hasFDerivAt

private lemma planeGradientCoordinates_at_critical
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) :
    planeGradientCoordinates (I := I) hdim g p f
        (modelToPlane (E := E) hdim (extChartAt I p p)) = 0 := by
  let e := modelToPlane (E := E) hdim
  let y₀ : E := extChartAt I p p
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hy₀target : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hpsource_ext
  have hy₀int : y₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hy₀target
  have hpartial : ∀ j : Fin (Module.finrank Real E),
      partialDeriv (E := E) j (scalarOnE (I := I) p f) y₀ = 0 := by
    intro j
    have hbridge :=
      mfderiv_scalar_eq_chart_fderiv
        (I := I) p f hpsource hy₀int
          (f.contMDiff.mdifferentiable (by simp) p)
          (centeredChartTangentBasis (I := I) p j)
    have hzero : mvfderiv (I := I) f p
        (centeredChartTangentBasis (I := I) p j) = 0 := by
      change (mfderiv I 𝓘(Real, Real) f p)
        (centeredChartTangentBasis (I := I) p j) = 0
      rw [hcrit]
      rfl
    rw [hzero, trivToE_self_apply, centeredChartTangentBasis_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hbridge
    unfold partialDeriv scalarOnE
    simpa [Function.comp_def, y₀] using hbridge.symm
  ext i
  simp only [planeGradientCoordinates]
  unfold gradChartCoeffOnE
  rw [show e.symm (e y₀) = y₀ by exact e.symm_apply_apply y₀]
  simp [hpartial]

private lemma planeGradientCoordinates_contDiffAt
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M) :
    ContDiffAt Real ∞ (planeGradientCoordinates (I := I) hdim g p f)
      (modelToPlane (E := E) hdim (extChartAt I p p)) := by
  let e := modelToPlane (E := E) hdim
  let z₀ : Plane := e (extChartAt I p p)
  let y₀ : E := extChartAt I p p
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hy₀target : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hpsource_ext
  have hy₀int : y₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hy₀target
  change ContDiffAt Real ∞ (planeGradientCoordinates (I := I) hdim g p f) z₀
  apply contDiffAt_piLp'
  intro i
  have hbase := gradChartCoeffOnE_contDiffOn_interior (I := I) g p f.contMDiff
    ((finCongr hdim).symm i)
  have hat : ContDiffAt Real ∞
      (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) y₀ :=
    hbase.contDiffAt (isOpen_interior.mem_nhds hy₀int)
  have hat' : ContDiffAt Real ∞
      (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i))
        (e.symm z₀) := by
    simpa only [z₀, y₀, ContinuousLinearEquiv.symm_apply_apply] using hat
  simpa only [planeGradientCoordinates, Function.comp_def, e] using
    hat'.comp z₀ e.symm.contDiff.contDiffAt

private lemma choleskyPlaneGram_entry_contDiffAt
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (i j : Fin 2) :
    ContDiffAt Real ∞
      (fun z : Plane => choleskyMatrix (planeGram (I := I) hdim g p z) i j)
      (modelToPlane (E := E) hdim (extChartAt I p p)) := by
  let e := modelToPlane (E := E) hdim
  let z₀ : Plane := e (extChartAt I p p)
  let y₀ : E := extChartAt I p p
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hy₀target : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hpsource_ext
  have hy₀int : y₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hy₀target
  have hz₀target : e.symm z₀ ∈ (extChartAt I p).target := by
    simpa only [z₀, y₀, ContinuousLinearEquiv.symm_apply_apply] using hy₀target
  have hpos := planeGram_posDef (I := I) hdim g p hz₀target
  have h00 : 0 < planeGram (I := I) hdim g p z₀ 0 0 := hpos.diag_pos
  have hdet : 0 < (planeGram (I := I) hdim g p z₀).det := hpos.det_pos
  have hentry : ∀ i j : Fin 2, ContDiffAt Real ∞
      (fun z : Plane => planeGram (I := I) hdim g p z i j) z₀ := by
    intro i j
    have hbase := chartGramOnE_contDiffOn (I := I) g p
      ((finCongr hdim).symm i) ((finCongr hdim).symm j)
    have hat : ContDiffAt Real ∞
        (chartGramOnE (I := I) g p ((finCongr hdim).symm i)
          ((finCongr hdim).symm j)) y₀ :=
      (hbase.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hy₀int)
    have hat' : ContDiffAt Real ∞
        (chartGramOnE (I := I) g p ((finCongr hdim).symm i)
          ((finCongr hdim).symm j)) (e.symm z₀) := by
      simpa only [z₀, y₀, ContinuousLinearEquiv.symm_apply_apply] using hat
    simpa only [Function.comp_def, planeGram, e] using
      hat'.comp z₀ e.symm.contDiff.contDiffAt
  have hdetSmooth : ContDiffAt Real ∞
      (fun z : Plane => (planeGram (I := I) hdim g p z).det) z₀ := by
    simpa only [Matrix.det_fin_two] using
      ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
  have hratioSmooth : ContDiffAt Real ∞
      (fun z : Plane =>
        (planeGram (I := I) hdim g p z).det /
          planeGram (I := I) hdim g p z 0 0) z₀ :=
    hdetSmooth.div (hentry 0 0) (ne_of_gt h00)
  have hratio : 0 < (planeGram (I := I) hdim g p z₀).det /
      planeGram (I := I) hdim g p z₀ 0 0 := div_pos hdet h00
  change ContDiffAt Real ∞
    (fun z : Plane => choleskyMatrix (planeGram (I := I) hdim g p z) i j) z₀
  fin_cases i <;> fin_cases j
  · simpa [choleskyMatrix] using (hentry 0 0).sqrt (ne_of_gt h00)
  · change ContDiffAt Real ∞
      ((fun z : Plane => planeGram (I := I) hdim g p z 0 1) /
        (fun z : Plane => Real.sqrt (planeGram (I := I) hdim g p z 0 0))) z₀
    exact (hentry 0 1).div ((hentry 0 0).sqrt (ne_of_gt h00))
      (Real.sqrt_pos.2 h00).ne'
  · simpa [choleskyMatrix] using (contDiffAt_const :
      ContDiffAt Real ∞ (fun _ : Plane => (0 : Real)) z₀)
  · simpa [choleskyMatrix] using hratioSmooth.sqrt hratio.ne'

private lemma choleskyGradientCoordinates_contDiffAt
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M) :
    ContDiffAt Real ∞ (choleskyGradientCoordinates (I := I) hdim g p f)
      (modelToPlane (E := E) hdim (extChartAt I p p)) := by
  let z₀ := modelToPlane (E := E) hdim (extChartAt I p p)
  have hgrad := planeGradientCoordinates_contDiffAt (I := I) hdim g f p
  change ContDiffAt Real ∞
    (choleskyGradientCoordinates (I := I) hdim g p f) z₀
  apply contDiffAt_piLp'
  intro i
  have hsum : ContDiffAt Real ∞
      (fun z : Plane => ∑ j : Fin 2,
        choleskyMatrix (planeGram (I := I) hdim g p z) i j *
          WithLp.ofLp (planeGradientCoordinates (I := I) hdim g p f z) j) z₀ := by
    apply ContDiffAt.sum
    intro j _
    exact (choleskyPlaneGram_entry_contDiffAt (I := I) hdim g p i j).mul
      ((contDiffAt_piLp 2).mp hgrad j)
  simpa only [choleskyGradientCoordinates, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec, dotProduct] using hsum

private lemma planeGradientCoordinates_contDiffAt_of_mem_target
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    {z : Plane}
    (hz : (modelToPlane (E := E) hdim).symm z ∈ (extChartAt I p).target) :
    ContDiffAt Real ∞ (planeGradientCoordinates (I := I) hdim g p f) z := by
  let e := modelToPlane (E := E) hdim
  let y : E := e.symm z
  have hyint : y ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hz
  apply contDiffAt_piLp'
  intro i
  have hbase := gradChartCoeffOnE_contDiffOn_interior (I := I) g p f.contMDiff
    ((finCongr hdim).symm i)
  have hat : ContDiffAt Real ∞
      (gradChartCoeffOnE (I := I) g p f ((finCongr hdim).symm i)) y :=
    hbase.contDiffAt (isOpen_interior.mem_nhds hyint)
  simpa only [planeGradientCoordinates, Function.comp_def, e, y] using
    hat.comp z e.symm.contDiff.contDiffAt

private lemma choleskyPlaneGram_entry_contDiffAt_of_mem_target
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) {z : Plane}
    (hz : (modelToPlane (E := E) hdim).symm z ∈ (extChartAt I p).target)
    (i j : Fin 2) :
    ContDiffAt Real ∞
      (fun w : Plane => choleskyMatrix (planeGram (I := I) hdim g p w) i j) z := by
  let e := modelToPlane (E := E) hdim
  let y : E := e.symm z
  have hyint : y ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hz
  have hpos := planeGram_posDef (I := I) hdim g p hz
  have h00 : 0 < planeGram (I := I) hdim g p z 0 0 := hpos.diag_pos
  have hdet : 0 < (planeGram (I := I) hdim g p z).det := hpos.det_pos
  have hentry : ∀ k l : Fin 2, ContDiffAt Real ∞
      (fun w : Plane => planeGram (I := I) hdim g p w k l) z := by
    intro k l
    have hbase := chartGramOnE_contDiffOn (I := I) g p
      ((finCongr hdim).symm k) ((finCongr hdim).symm l)
    have hat : ContDiffAt Real ∞
        (chartGramOnE (I := I) g p ((finCongr hdim).symm k)
          ((finCongr hdim).symm l)) y :=
      (hbase.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hyint)
    simpa only [Function.comp_def, planeGram, e, y] using
      hat.comp z e.symm.contDiff.contDiffAt
  have hdetSmooth : ContDiffAt Real ∞
      (fun w : Plane => (planeGram (I := I) hdim g p w).det) z := by
    simpa only [Matrix.det_fin_two] using
      ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
  have hratioSmooth : ContDiffAt Real ∞
      (fun w : Plane =>
        (planeGram (I := I) hdim g p w).det /
          planeGram (I := I) hdim g p w 0 0) z :=
    hdetSmooth.div (hentry 0 0) (ne_of_gt h00)
  have hratio : 0 < (planeGram (I := I) hdim g p z).det /
      planeGram (I := I) hdim g p z 0 0 := div_pos hdet h00
  fin_cases i <;> fin_cases j
  · simpa [choleskyMatrix] using (hentry 0 0).sqrt (ne_of_gt h00)
  · change ContDiffAt Real ∞
      ((fun w : Plane => planeGram (I := I) hdim g p w 0 1) /
        (fun w : Plane => Real.sqrt (planeGram (I := I) hdim g p w 0 0))) z
    exact (hentry 0 1).div ((hentry 0 0).sqrt (ne_of_gt h00))
      (Real.sqrt_pos.2 h00).ne'
  · simpa [choleskyMatrix] using (contDiffAt_const :
      ContDiffAt Real ∞ (fun _ : Plane => (0 : Real)) z)
  · simpa [choleskyMatrix] using hratioSmooth.sqrt hratio.ne'

private lemma choleskyGradientCoordinates_contDiffAt_of_mem_target
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    {z : Plane}
    (hz : (modelToPlane (E := E) hdim).symm z ∈ (extChartAt I p).target) :
    ContDiffAt Real ∞ (choleskyGradientCoordinates (I := I) hdim g p f) z := by
  have hgrad :=
    planeGradientCoordinates_contDiffAt_of_mem_target (I := I) hdim g f p hz
  apply contDiffAt_piLp'
  intro i
  have hsum : ContDiffAt Real ∞
      (fun w : Plane => ∑ j : Fin 2,
        choleskyMatrix (planeGram (I := I) hdim g p w) i j *
          WithLp.ofLp (planeGradientCoordinates (I := I) hdim g p f w) j) z := by
    apply ContDiffAt.sum
    intro j _
    exact
      (choleskyPlaneGram_entry_contDiffAt_of_mem_target (I := I) hdim g p hz i j).mul
        ((contDiffAt_piLp 2).mp hgrad j)
  simpa only [choleskyGradientCoordinates, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec, dotProduct] using hsum

private lemma choleskyGradientCoordinates_hasFDerivAt
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) {c : Real}
    (hhess : ∀ v w : TangentSpace I p,
      hessFun (I := I) g f p v w = c * g.inner p v w) :
    HasFDerivAt (choleskyGradientCoordinates (I := I) hdim g p f)
      (c • matrixToPlaneCLM
        (choleskyMatrix (planeGram (I := I) hdim g p
          (modelToPlane (E := E) hdim (extChartAt I p p)))))
      (modelToPlane (E := E) hdim (extChartAt I p p)) := by
  let z₀ : Plane := modelToPlane (E := E) hdim (extChartAt I p p)
  let u : Plane → Plane := planeGradientCoordinates (I := I) hdim g p f
  let ψ : Plane → Plane := choleskyGradientCoordinates (I := I) hdim g p f
  have hψdiff : DifferentiableAt Real ψ z₀ :=
    (choleskyGradientCoordinates_contDiffAt (I := I) hdim g f p).differentiableAt
      (by simp)
  have hud : HasFDerivAt u (c • (1 : Plane →L[Real] Plane)) z₀ := by
    simpa only [u, z₀] using
      planeGradientCoordinates_hasFDerivAt (I := I) hdim g f p hcrit hhess
  have hu0 : u z₀ = 0 := by
    simpa only [u, z₀] using
      planeGradientCoordinates_at_critical (I := I) hdim g f p hcrit
  have hudCoord : ∀ j k : Fin 2,
      (fderiv Real (fun z : Plane => WithLp.ofLp (u z) j) z₀)
          ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) =
        if j = k then c else 0 := by
    intro j k
    let proj : Plane →L[Real] Real := PiLp.proj 2 (fun _ : Fin 2 => Real) j
    have hcomp := fderiv_comp z₀ proj.differentiableAt hud.differentiableAt
    have hcompApply := congrArg
      (fun L : Plane →L[Real] Real =>
        L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hcomp
    rw [proj.fderiv, hud.fderiv] at hcompApply
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply, proj,
      EuclideanSpace.basisFun_apply, PiLp.proj_apply] using hcompApply
  have hfd : fderiv Real ψ z₀ =
      c • matrixToPlaneCLM
        (choleskyMatrix (planeGram (I := I) hdim g p z₀)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hlin : (fderiv Real ψ z₀).toLinearMap =
        (c • matrixToPlaneCLM
          (choleskyMatrix (planeGram (I := I) hdim g p z₀))).toLinearMap := by
      apply (EuclideanSpace.basisFun (Fin 2) Real).toBasis.ext
      intro k
      ext i
      let proj : Plane →L[Real] Real := PiLp.proj 2 (fun _ : Fin 2 => Real) i
      have hproj := fderiv_comp z₀ proj.differentiableAt hψdiff
      have hprojApply := congrArg
        (fun L : Plane →L[Real] Real =>
          L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hproj
      simp only [Function.comp_def, proj, ContinuousLinearMap.fderiv,
        ContinuousLinearMap.comp_apply] at hprojApply
      have hentryDiff : ∀ j : Fin 2, DifferentiableAt Real
          (fun z : Plane =>
            choleskyMatrix (planeGram (I := I) hdim g p z) i j) z₀ := by
        intro j
        exact (choleskyPlaneGram_entry_contDiffAt (I := I) hdim g p i j).differentiableAt
          (by simp)
      have huCoordDiff : ∀ j : Fin 2, DifferentiableAt Real
          (fun z : Plane => WithLp.ofLp (u z) j) z₀ := by
        intro j
        exact ((contDiffAt_piLp 2).mp
          (planeGradientCoordinates_contDiffAt (I := I) hdim g f p) j).differentiableAt
            (by simp)
      have hsum := fderiv_fun_sum (u := Finset.univ)
        (fun j _ => (hentryDiff j).mul (huCoordDiff j))
      have hsumApply := congrArg
        (fun L : Plane →L[Real] Real =>
          L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hsum
      rw [_root_.sum_apply] at hsumApply
      have hterm : ∀ j : Fin 2,
          (fderiv Real
            (fun z : Plane =>
              choleskyMatrix (planeGram (I := I) hdim g p z) i j *
                WithLp.ofLp (u z) j) z₀)
              ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) =
            choleskyMatrix (planeGram (I := I) hdim g p z₀) i j *
              (if j = k then c else 0) := by
        intro j
        have hmul := fderiv_fun_mul (𝕜 := Real) (hentryDiff j) (huCoordDiff j)
        have hmulApply := congrArg
          (fun L : Plane →L[Real] Real =>
            L ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) hmul
        have huj0 : WithLp.ofLp (u z₀) j = 0 := by rw [hu0]; rfl
        rw [huj0] at hmulApply
        simp only [_root_.add_apply, _root_.smul_apply,
          smul_eq_mul, zero_mul, add_zero] at hmulApply
        rw [hudCoord j k] at hmulApply
        exact hmulApply
      have hsumValue : (fderiv Real
          (fun z : Plane => ∑ j : Fin 2,
            choleskyMatrix (planeGram (I := I) hdim g p z) i j *
              WithLp.ofLp (u z) j) z₀)
            ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) =
          choleskyMatrix (planeGram (I := I) hdim g p z₀) i k * c := by
        calc
          _ = ∑ j : Fin 2,
                (fderiv Real
                  (fun z : Plane =>
                    choleskyMatrix (planeGram (I := I) hdim g p z) i j *
                      WithLp.ofLp (u z) j) z₀)
                    ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) := hsumApply
          _ = ∑ j : Fin 2,
                choleskyMatrix (planeGram (I := I) hdim g p z₀) i j *
                  (if j = k then c else 0) :=
            Finset.sum_congr rfl fun j _ => hterm j
          _ = choleskyMatrix (planeGram (I := I) hdim g p z₀) i k * c := by simp
      have hprojApply' : (fderiv Real
        (fun z : Plane => ∑ j : Fin 2,
          choleskyMatrix (planeGram (I := I) hdim g p z) i j *
            WithLp.ofLp (u z) j) z₀)
          ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k) =
          (fderiv Real ψ z₀
            ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)).ofLp i := by
        simpa only [ψ, u, choleskyGradientCoordinates, Matrix.toLpLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, PiLp.proj_apply] using hprojApply
      have hleft : WithLp.ofLp
          (fderiv Real ψ z₀
            ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) i =
          choleskyMatrix (planeGram (I := I) hdim g p z₀) i k * c :=
        hprojApply'.symm.trans hsumValue
      change WithLp.ofLp
          (fderiv Real ψ z₀
            ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) i =
        WithLp.ofLp
          ((c • matrixToPlaneCLM
            (choleskyMatrix (planeGram (I := I) hdim g p z₀)))
              ((EuclideanSpace.basisFun (Fin 2) Real).toBasis k)) i
      rw [hleft]
      simp [matrixToPlaneCLM_apply, Matrix.toLpLin_apply,
        EuclideanSpace.basisFun_apply, mul_comm]
    exact DFunLike.congr_fun hlin v
  change HasFDerivAt ψ
    (c • matrixToPlaneCLM
      (choleskyMatrix (planeGram (I := I) hdim g p z₀))) z₀
  rw [← hfd]
  exact hψdiff.hasFDerivAt

omit [I.Boundaryless] in
private lemma choleskyGradientCoordinates_fderiv_abs_det
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (c : Real) :
    |(c • matrixToPlaneCLM
      (choleskyMatrix (planeGram (I := I) hdim g p
        (modelToPlane (E := E) hdim (extChartAt I p p))))).det| =
      c ^ 2 * Real.sqrt
        (planeGram (I := I) hdim g p
          (modelToPlane (E := E) hdim (extChartAt I p p))).det := by
  let e := modelToPlane (E := E) hdim
  let z₀ : Plane := e (extChartAt I p p)
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have htarget : e.symm z₀ ∈ (extChartAt I p).target := by
    simpa only [z₀, ContinuousLinearEquiv.symm_apply_apply] using
      (extChartAt I p).map_source hpsource_ext
  have hpos := planeGram_posDef (I := I) hdim g p htarget
  change |(c • matrixToPlaneCLM
    (choleskyMatrix (planeGram (I := I) hdim g p z₀))).det| =
      c ^ 2 * Real.sqrt (planeGram (I := I) hdim g p z₀).det
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show LinearMap.det
      (matrixToPlaneCLM
        (choleskyMatrix (planeGram (I := I) hdim g p z₀))).toLinearMap =
      (choleskyMatrix (planeGram (I := I) hdim g p z₀)).det by
        exact matrixToPlaneCLM_det _]
  rw [choleskyMatrix_det hpos, abs_mul, abs_pow,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [sq_abs]

private lemma exists_choleskyGradientCoordinates_openPartialHomeomorph
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) {c : Real} (hc : c ≠ 0)
    (hhess : ∀ v w : TangentSpace I p,
      hessFun (I := I) g f p v w = c * g.inner p v w) :
    ∃ e : OpenPartialHomeomorph Plane Plane,
      (e : Plane → Plane) = choleskyGradientCoordinates (I := I) hdim g p f ∧
      modelToPlane (E := E) hdim (extChartAt I p p) ∈ e.source ∧
      e (modelToPlane (E := E) hdim (extChartAt I p p)) = 0 := by
  let z₀ : Plane := modelToPlane (E := E) hdim (extChartAt I p p)
  let D : Plane →L[Real] Plane := c • matrixToPlaneCLM
    (choleskyMatrix (planeGram (I := I) hdim g p z₀))
  have hDabs : |D.det| =
      c ^ 2 * Real.sqrt (planeGram (I := I) hdim g p z₀).det := by
    simpa only [D, z₀] using
      choleskyGradientCoordinates_fderiv_abs_det (I := I) hdim g p c
  have hpsource : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpsource_ext : p ∈ (extChartAt I p).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have htarget : (modelToPlane (E := E) hdim).symm z₀ ∈
      (extChartAt I p).target := by
    simpa only [z₀, ContinuousLinearEquiv.symm_apply_apply] using
      (extChartAt I p).map_source hpsource_ext
  have hpos := planeGram_posDef (I := I) hdim g p htarget
  have hDabs_pos : 0 < |D.det| := by
    rw [hDabs]
    exact mul_pos (sq_pos_of_ne_zero hc) (Real.sqrt_pos.2 hpos.det_pos)
  have hDne : D.det ≠ 0 := abs_pos.mp hDabs_pos
  let D' : Plane ≃L[Real] Plane := D.toContinuousLinearEquivOfDetNeZero hDne
  have hfd : HasFDerivAt
      (choleskyGradientCoordinates (I := I) hdim g p f) (D' : Plane →L[Real] Plane) z₀ := by
    rw [show (D' : Plane →L[Real] Plane) = D by
      exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero D hDne]
    simpa only [D, z₀] using
      choleskyGradientCoordinates_hasFDerivAt (I := I) hdim g f p hcrit hhess
  have hsmooth : ContDiffAt Real ∞
      (choleskyGradientCoordinates (I := I) hdim g p f) z₀ := by
    simpa only [z₀] using choleskyGradientCoordinates_contDiffAt (I := I) hdim g f p
  let e : OpenPartialHomeomorph Plane Plane :=
    hsmooth.toOpenPartialHomeomorph
      (choleskyGradientCoordinates (I := I) hdim g p f) hfd (by simp)
  refine ⟨e, rfl, ?_, ?_⟩
  · exact hsmooth.mem_toOpenPartialHomeomorph_source hfd (by simp)
  · change choleskyGradientCoordinates (I := I) hdim g p f z₀ = 0
    rw [choleskyGradientCoordinates]
    rw [show planeGradientCoordinates (I := I) hdim g p f z₀ = 0 by
      simpa only [z₀] using
        planeGradientCoordinates_at_critical (I := I) hdim g f p hcrit]
    exact LinearMap.map_zero _

private lemma choleskyGradientCoordinates_norm_sq
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) {z : Plane}
    (hz : (modelToPlane (E := E) hdim).symm z ∈ (extChartAt I p).target) :
    ‖choleskyGradientCoordinates (I := I) hdim g p f z‖ ^ 2 =
      normGradSqFun (I := I) g f
        ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)) := by
  let q := finCongr hdim
  let y := (modelToPlane (E := E) hdim).symm z
  let x := (extChartAt I p).symm y
  let c : Fin (Module.finrank Real E) → Real := fun i =>
    gradChartCoeffOnE (I := I) g p f i y
  have hxsource : x ∈ (extChartAt I p).source := (extChartAt I p).map_target hz
  have hxchart : x ∈ (chartAt H p).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxsource
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hchartx : extChartAt I p x = y := (extChartAt I p).right_inv hz
  have hyint : extChartAt I p x ∈ interior (extChartAt I p).target := by
    rw [hchartx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p hz
  have hgrad := gradChartLocal_eq_gradFun (I := I) g p
    ((hf x).mdifferentiableAt (by simp)) hxbase hyint
  rw [choleskyGradientCoordinates]
  rw [choleskyMatrix_norm_sq (planeGram_posDef (I := I) hdim g p hz)]
  have hreindex :
      star (WithLp.ofLp (planeGradientCoordinates (I := I) hdim g p f z)) ⬝ᵥ
          (planeGram (I := I) hdim g p z *ᵥ
            WithLp.ofLp (planeGradientCoordinates (I := I) hdim g p f z)) =
        star c ⬝ᵥ (chartGramMatrix (I := I) g p x *ᵥ c) := by
    simp only [dotProduct, Matrix.mulVec, planeGradientCoordinates,
      planeGram, WithLp.ofLp_toLp, Pi.star_apply, star_trivial, c, y, x]
    rw [← (finCongr hdim).sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (finCongr hdim).sum_comp]
    rfl
  rw [hreindex, chartGramMatrix_dotProduct_mulVec]
  have hc : ∀ i, c i = gradChartCoeff (I := I) g p f i x := by
    intro i
    simp only [c, gradChartCoeffOnE, gradChartCoeff, chartInvGramOnE, y, x]
    rw [hchartx]
  rw [show (∑ i, c i • chartBasisVecFiber (I := I) p i x) =
      gradChartLocal (I := I) g p f x by
        unfold gradChartLocal
        exact Finset.sum_congr rfl fun i _ => by rw [hc i], hgrad]
  rfl

omit [I.Boundaryless] in
private lemma planeGram_det
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M) (z : Plane) :
    (planeGram (I := I) hdim g p z).det =
      (chartGramMatrix (I := I) g p
        ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z))).det := by
  change (Matrix.submatrix
      (chartGramMatrix (I := I) g p
        ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)))
      (finCongr hdim).symm (finCongr hdim).symm).det = _
  exact Matrix.det_submatrix_equiv_self (finCongr hdim).symm _

omit [I.Boundaryless] in
private lemma integral_chartLocalMeasure_eq_plane
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (p : M)
    (F : M → Real) (hF : Measurable F) :
    ∫ x, F x ∂(chartLocalMeasure (I := I) g p) =
      ∫ z in (modelToPlane (E := E) hdim).symm ⁻¹' (extChartAt I p).target,
        chartDensity g p
            ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)) *
          F ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)) := by
  let e := modelToPlane (E := E) hdim
  let t : Set Plane := e.symm ⁻¹' (extChartAt I p).target
  let q : Plane → Real := fun z =>
    chartDensity g p ((extChartAt I p).symm (e.symm z)) *
      F ((extChartAt I p).symm (e.symm z))
  rw [integral_chartLocalMeasure (I := I) g p F hF]
  have ht : MeasurableSet t :=
    (measurableSet_extChartAt_target (I := I) p).preimage e.symm.continuous.measurable
  have htarget : MeasurableSet (extChartAt I p).target :=
    measurableSet_extChartAt_target (I := I) p
  calc
    ∫ y in (extChartAt I p).target,
        chartDensity g p ((extChartAt I p).symm y) *
          F ((extChartAt I p).symm y) ∂modelHaar =
        ∫ y : E, t.indicator q (e y) ∂modelHaar := by
      rw [← integral_indicator htarget]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ (extChartAt I p).target
      · have hey : e y ∈ t := by
          simpa only [t, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy
        rw [indicator_of_mem hy, indicator_of_mem hey]
        simp only [q, e, ContinuousLinearEquiv.symm_apply_apply]
      · have hey : e y ∉ t := by
          simpa only [t, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy
        rw [indicator_of_notMem hy, indicator_of_notMem hey]
    _ = ∫ z : Plane, t.indicator q z :=
      (modelToPlane_measurePreserving (E := E) hdim).integral_comp
        e.toHomeomorph.measurableEmbedding (t.indicator q)
    _ = ∫ z in t, q z := integral_indicator ht
    _ = ∫ z in (modelToPlane (E := E) hdim).symm ⁻¹' (extChartAt I p).target,
        chartDensity g p
            ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)) *
          F ((extChartAt I p).symm ((modelToPlane (E := E) hdim).symm z)) := rfl

theorem exists_nhds_tendsto_integral_regularized_normGradSqFun_inv_sq_mul_of_hessFun_eq_smul_metric_of_finrank_eq_two
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (p : M)
    (hcrit : IsCriticalPointAt I f p) {c : Real} (hc : c ≠ 0)
    (hhess : ∀ v w : TangentSpace I p,
      hessFun (I := I) g f p v w = c * g.inner p v w) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ b : M → Real,
      Continuous b → tsupport b ⊆ U →
        Tendsto
          (fun ε : Real => ∫ x,
            ε * b x * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
              ∂riemannianVolumeMeasure (I := I) (M := M) g)
          (𝓝[>] 0) (𝓝 (Real.pi / c ^ 2 * b p)) := by
  let e := modelToPlane (E := E) hdim
  let z₀ : Plane := e (extChartAt I p p)
  let ψ : Plane → Plane := choleskyGradientCoordinates (I := I) hdim g p f
  obtain ⟨φ, hφfun, hz₀source, hφz₀⟩ :=
    exists_choleskyGradientCoordinates_openPartialHomeomorph
      (I := I) hdim g f p hcrit hc hhess
  have hφψ : (φ : Plane → Plane) = ψ := by
    simpa only [ψ] using hφfun
  have hpsource : p ∈ (extChartAt I p).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact mem_chart_source H p
  have hz₀target : e.symm z₀ ∈ (extChartAt I p).target := by
    simpa only [z₀, ContinuousLinearEquiv.symm_apply_apply] using
      (extChartAt I p).map_source hpsource
  have hψsmooth₀ : ContDiffAt Real ∞ ψ z₀ := by
    exact choleskyGradientCoordinates_contDiffAt_of_mem_target
      (I := I) hdim g f p hz₀target
  have hψderiv₀ :=
    choleskyGradientCoordinates_hasFDerivAt
      (I := I) hdim g f p hcrit hhess
  have hJ₀ : |(fderiv Real ψ z₀).det| =
      c ^ 2 * Real.sqrt (planeGram (I := I) hdim g p z₀).det := by
    rw [hψderiv₀.fderiv]
    simpa only [ψ, z₀] using
      choleskyGradientCoordinates_fderiv_abs_det (I := I) hdim g p c
  have hplanePos : (planeGram (I := I) hdim g p z₀).PosDef :=
    planeGram_posDef (I := I) hdim g p hz₀target
  have hJ₀pos : 0 < |(fderiv Real ψ z₀).det| := by
    rw [hJ₀]
    exact mul_pos (sq_pos_of_ne_zero hc) (Real.sqrt_pos.2 hplanePos.det_pos)
  have hJcont₀ : ContinuousAt (fun z : Plane => |(fderiv Real ψ z).det|) z₀ :=
    continuous_abs.continuousAt.comp
      (ContinuousLinearMap.continuous_det.continuousAt.comp
        (hψsmooth₀.continuousAt_fderiv (by simp)))
  have hJnhds : {z : Plane | |(fderiv Real ψ z).det| ≠ 0} ∈ 𝓝 z₀ :=
    hJcont₀.eventually_ne (ne_of_gt hJ₀pos)
  have htargetNhds : e.symm ⁻¹' (extChartAt I p).target ∈ 𝓝 z₀ :=
    e.symm.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hz₀target)
  have hsourceNhds : φ.source ∈ 𝓝 z₀ := φ.open_source.mem_nhds hz₀source
  let T : Set Plane :=
    (φ.source ∩ (e.symm ⁻¹' (extChartAt I p).target) ∩
      {z : Plane | |(fderiv Real ψ z).det| ≠ 0})
  have hTnhds : T ∈ 𝓝 z₀ := by
    exact inter_mem (inter_mem hsourceNhds htargetNhds) hJnhds
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hTnhds
  let s : Set Plane := Metric.closedBall z₀ r
  let B : Set Plane := Metric.ball z₀ r
  let coord : M → Plane := fun x => e (extChartAt I p x)
  let U : Set M := (extChartAt I p).source ∩ coord ⁻¹' B
  have hcoordContinuous : ContinuousOn coord (extChartAt I p).source :=
    e.continuous.comp_continuousOn (continuousOn_extChartAt (I := I) p)
  have hUopen : IsOpen U := by
    exact hcoordContinuous.isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) p) Metric.isOpen_ball
  have hpU : p ∈ U := by
    refine ⟨hpsource, ?_⟩
    change dist (coord p) z₀ < r
    simp only [coord, z₀, dist_self]
    exact hr
  refine ⟨U, hUopen.mem_nhds hpU, ?_⟩
  intro b hb hbU
  let xOf : Plane → M := fun z => (extChartAt I p).symm (e.symm z)
  let J : Plane → Real := fun z => |(fderiv Real ψ z).det|
  let A : Plane → Real := fun z => chartDensity g p (xOf z) * b (xOf z)
  let Q : Plane → Real := fun z => A z / J z
  let G : Plane → Real := fun w => Q (φ.symm w)
  have hsT : s ⊆ T := by
    simpa only [s] using hrs
  have hsSource : s ⊆ φ.source := fun z hz => (hsT hz).1.1
  have hsTarget : ∀ z ∈ s, e.symm z ∈ (extChartAt I p).target :=
    fun z hz => (hsT hz).1.2
  have hsJ : ∀ z ∈ s, J z ≠ 0 := fun z hz => (hsT hz).2
  have hsMeas : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hsCompact : IsCompact s := isCompact_closedBall z₀ r
  have hψDeriv : ∀ z ∈ s,
      HasFDerivWithinAt ψ (fderiv Real ψ z) s z := by
    intro z hz
    exact ((choleskyGradientCoordinates_contDiffAt_of_mem_target
      (I := I) hdim g f p (hsTarget z hz)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hψInj : InjOn ψ s := by
    rw [← hφψ]
    exact φ.injOn.mono hsSource
  have hψImageNhds : ψ '' s ∈ 𝓝 (0 : Plane) := by
    have himage := φ.image_mem_nhds hz₀source (Metric.closedBall_mem_nhds z₀ hr)
    rw [hφz₀] at himage
    simpa only [hφψ, s] using himage
  have hxOfMaps : MapsTo xOf s (extChartAt I p).source := by
    intro z hz
    exact (extChartAt I p).map_target (hsTarget z hz)
  have hxOfMapsBase :
      MapsTo xOf s (trivializationAt E (TangentSpace I) p).baseSet := by
    intro z hz
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact hxOfMaps hz
  have hxOfContinuous : ContinuousOn xOf s := by
    exact (continuousOn_extChartAt_symm (I := I) p).comp
      e.symm.continuous.continuousOn hsTarget
  have hAContinuous : ContinuousOn A s := by
    exact ((chartDensity_continuousOn (I := I) g p).comp
      hxOfContinuous hxOfMapsBase).mul (hb.comp_continuousOn hxOfContinuous)
  have hJContinuous : ContinuousOn J s := by
    intro z hz
    exact continuous_abs.continuousAt.comp_continuousWithinAt
      (ContinuousLinearMap.continuous_det.continuousAt.comp_continuousWithinAt
        ((choleskyGradientCoordinates_contDiffAt_of_mem_target
          (I := I) hdim g f p (hsTarget z hz)).continuousAt_fderiv
            (by simp)).continuousWithinAt)
  have hQContinuous : ContinuousOn Q s :=
    hAContinuous.div hJContinuous hsJ
  have hφImageTarget : φ '' s ⊆ φ.target := by
    rintro w ⟨z, hz, rfl⟩
    exact φ.map_source (hsSource hz)
  have hφsymmMaps : MapsTo (φ.symm : Plane → Plane) (φ '' s) s := by
    rintro w ⟨z, hz, rfl⟩
    simpa only [φ.left_inv (hsSource hz)] using hz
  have hGContinuous : ContinuousOn G (φ '' s) := by
    exact hQContinuous.comp
      (φ.continuousOn_symm.mono hφImageTarget) hφsymmMaps
  have hφContinuous : ContinuousOn (φ : Plane → Plane) s :=
    φ.continuousOn.mono hsSource
  have hφImageCompact : IsCompact (φ '' s) :=
    hsCompact.image_of_continuousOn hφContinuous
  have hGIntegrable : IntegrableOn G (ψ '' s) volume := by
    rw [← hφψ]
    exact hGContinuous.integrableOn_compact hφImageCompact
  have hφImageNhds : φ '' s ∈ 𝓝 (0 : Plane) := by
    simpa only [hφψ] using hψImageNhds
  have hGAtZero : G 0 = b p / c ^ 2 := by
    have hφsymmZero : φ.symm 0 = z₀ := by
      rw [← hφz₀]
      exact φ.left_inv hz₀source
    have hxOfz₀ : xOf z₀ = p := by
      simp only [xOf, z₀, e, ContinuousLinearEquiv.symm_apply_apply]
      exact (extChartAt I p).left_inv hpsource
    have hdetDensity : Real.sqrt (planeGram (I := I) hdim g p z₀).det =
        chartDensity g p p := by
      rw [planeGram_det (I := I)]
      rw [show (extChartAt I p).symm
          ((modelToPlane (E := E) hdim).symm z₀) = p by
        simpa only [z₀, e, ContinuousLinearEquiv.symm_apply_apply] using
          (extChartAt I p).left_inv hpsource]
      rfl
    have hdensityPos : 0 < chartDensity g p p := by
      apply chartDensity_pos (I := I)
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact mem_chart_source H p
    simp only [G, Q, A, J, hφsymmZero, hxOfz₀]
    rw [hJ₀, hdetDensity]
    field_simp [hc, ne_of_gt hdensityPos]
  have hbase :=
    DifferentialGeometry.Analysis.Integration.tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero_of_finrank_eq_two
      (F := Plane) (by simp) (a := (1 : Real)) one_ne_zero hsMeas hψDeriv hψInj
        hψImageNhds hGIntegrable (hGContinuous.continuousAt hφImageNhds)
  have hbase' : Tendsto
      (fun ε : Real => ∫ z in s,
        J z * (ε * G (ψ z) * (‖ψ z‖ ^ 2 + ε)⁻¹ ^ 2))
      (𝓝[>] 0) (𝓝 (Real.pi / c ^ 2 * b p)) := by
    have hlimit : Real.pi / (1 : Real) ^ 2 * G 0 =
        Real.pi / c ^ 2 * b p := by
      rw [hGAtZero]
      field_simp [hc]
    rw [hlimit] at hbase
    simpa only [one_pow, one_mul, J, mul_assoc] using hbase
  apply hbase'.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  let Fε : M → Real := fun x =>
    ε * b x * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
  have hdenNe : ∀ x : M, normGradSqFun (I := I) g f x + ε ≠ 0 := by
    intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (normGradSqFun_nonneg (I := I) g f x) hε)
  have hFεContinuous : Continuous Fε := by
    have hdenContinuous : Continuous
        (fun x : M => normGradSqFun (I := I) g f x + ε) :=
      (normGradSqFun_continuous (I := I) g f.contMDiff).add continuous_const
    have hinvContinuous : Continuous
        (fun x : M => (normGradSqFun (I := I) g f x + ε)⁻¹) :=
      hdenContinuous.inv₀ hdenNe
    exact (continuous_const.mul hb).mul (hinvContinuous.pow 2)
  have hFεSupport : tsupport Fε ⊆ tsupport b := by
    calc
      tsupport Fε ⊆ tsupport (fun x : M => ε * b x) := tsupport_mul_subset_left
      _ ⊆ tsupport b := tsupport_mul_subset_right
  have hUSource : U ⊆ (chartAt H p).source := by
    intro x hx
    simpa only [extChartAt_source_eq_chartAt_source] using hx.1
  have hglobal :=
    integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
      (I := I) g p hFεContinuous
        (hFεSupport.trans (hbU.trans hUSource))
  have hchart := integral_chartLocalMeasure_eq_plane
    (I := I) hdim g p Fε hFεContinuous.measurable
  have hsSubsetPlaneTarget :
      s ⊆ e.symm ⁻¹' (extChartAt I p).target := hsTarget
  have hzeroOutside : ∀ z ∈
      (e.symm ⁻¹' (extChartAt I p).target) \ s,
      chartDensity g p (xOf z) * Fε (xOf z) = 0 := by
    intro z hz
    have hzxSource : xOf z ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hz.1
    have hcoordx : coord (xOf z) = z := by
      simp only [coord, xOf]
      rw [(extChartAt I p).right_inv hz.1]
      exact e.apply_symm_apply z
    have hbzero : b (xOf z) = 0 := by
      by_contra hbne
      have hxtsupport : xOf z ∈ tsupport b := subset_tsupport b hbne
      have hxU := hbU hxtsupport
      have hzB : z ∈ B := by
        rw [← hcoordx]
        exact hxU.2
      exact hz.2 (Metric.ball_subset_closedBall hzB)
    simp only [Fε, hbzero, mul_zero, zero_mul]
  have hplaneRestrict :
      (∫ z in e.symm ⁻¹' (extChartAt I p).target,
        chartDensity g p (xOf z) * Fε (xOf z)) =
      ∫ z in s, chartDensity g p (xOf z) * Fε (xOf z) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      ((measurableSet_extChartAt_target (I := I) p).preimage
        e.symm.continuous.measurable)
      hsSubsetPlaneTarget hzeroOutside
  have hpoint : ∀ z ∈ s,
      chartDensity g p (xOf z) * Fε (xOf z) =
        J z * (ε * G (ψ z) * (‖ψ z‖ ^ 2 + ε)⁻¹ ^ 2) := by
    intro z hz
    have hφsymmψ : φ.symm (ψ z) = z := by
      rw [← hφψ]
      exact φ.left_inv (hsSource hz)
    have hnorm := choleskyGradientCoordinates_norm_sq
      (I := I) hdim g p f.contMDiff (hsTarget z hz)
    have hnorm' : ‖ψ z‖ ^ 2 = normGradSqFun (I := I) g f (xOf z) := by
      simpa only [ψ, xOf, e] using hnorm
    have hG : G (ψ z) = Q z := by
      simp only [G, hφsymmψ]
    have hJQ : J z * Q z = A z := by
      dsimp only [Q]
      exact mul_div_cancel₀ _ (hsJ z hz)
    calc
      chartDensity g p (xOf z) * Fε (xOf z) =
          ε * A z * (normGradSqFun (I := I) g f (xOf z) + ε)⁻¹ ^ 2 := by
        simp only [Fε, A]
        ring
      _ = J z * (ε * Q z *
          (normGradSqFun (I := I) g f (xOf z) + ε)⁻¹ ^ 2) := by
        rw [← hJQ]
        ring
      _ = J z * (ε * G (ψ z) * (‖ψ z‖ ^ 2 + ε)⁻¹ ^ 2) := by
        rw [hG, hnorm']
  symm
  calc
    (∫ x, ε * b x * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2
        ∂riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, Fε x ∂riemannianVolumeMeasure (I := I) (M := M) g := rfl
    _ = ∫ x, Fε x ∂chartLocalMeasure (I := I) g p := hglobal
    _ = ∫ z in e.symm ⁻¹' (extChartAt I p).target,
        chartDensity g p (xOf z) * Fε (xOf z) := by
      simpa only [e, xOf] using hchart
    _ = ∫ z in s, chartDensity g p (xOf z) * Fε (xOf z) := hplaneRestrict
    _ = ∫ z in s,
        J z * (ε * G (ψ z) * (‖ψ z‖ ^ 2 + ε)⁻¹ ^ 2) :=
      setIntegral_congr_fun hsMeas hpoint

theorem isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M)
    (hcrit : IsCriticalPointAt I f x) {c : Real} (hc : c ≠ 0)
    (hhess : ∀ v w : TangentSpace I x,
      hessFun (I := I) g f x v w = c * g.inner x v w) :
    IsNondegenerateCriticalPointAt I f x := by
  let F : E → Real := f ∘ (extChartAt I x).symm
  let y : E := extChartAt I x x
  let e := centeredChartTangentEquiv (I := I) x
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact hxsrc
  have hytgt : y ∈ (extChartAt I x).target := by
    exact (extChartAt I x).map_source hxsrc_ext
  have hyint : y ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hytgt
  have hFsmooth : ContDiffOn Real ∞ F (interior ((extChartAt I x).target : Set E)) :=
    (scalarOnE_contDiffOn (I := I) x f.contMDiff).mono interior_subset
  have hFderiv : DifferentiableAt Real (fderiv Real F) y := by
    have hsmooth : ContDiffOn Real ∞ (fderiv Real F)
        (interior ((extChartAt I x).target : Set E)) :=
      hFsmooth.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    exact (hsmooth.contDiffAt (isOpen_interior.mem_nhds hyint)).differentiableAt (by simp)
  have hpartial : ∀ k : Fin (Module.finrank Real E),
      partialDeriv (E := E) k F y = 0 := by
    intro k
    have hbridge :=
      mfderiv_scalar_eq_chart_fderiv
        (I := I) x f hxsrc hyint
          (f.contMDiff.mdifferentiable (by simp) x)
          (centeredChartTangentBasis (I := I) x k)
    have hzero : mvfderiv (I := I) f x
        (centeredChartTangentBasis (I := I) x k) = 0 := by
      change (mfderiv I 𝓘(Real, Real) f x)
        (centeredChartTangentBasis (I := I) x k) = 0
      rw [hcrit]
      rfl
    rw [hzero, trivToE_self_apply, centeredChartTangentBasis_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hbridge
    unfold partialDeriv
    simpa [F, y] using hbridge.symm
  have hiter : ∀ i j : Fin (Module.finrank Real E),
      chartIteratedPartialDeriv (I := I) x f i j y =
        chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j) := by
    intro i j
    let L : (E →L[Real] Real) →L[Real] Real :=
      ContinuousLinearMap.apply Real Real (chartModelBasis E j)
    have hcomp : (fun z : E => fderiv Real F z (chartModelBasis E j)) =
        L ∘ fderiv Real F := rfl
    change partialDeriv (E := E) i (partialDeriv (E := E) j F) y =
      chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j)
    unfold partialDeriv
    rw [hcomp, fderiv_comp y L.differentiableAt hFderiv, L.fderiv]
    rfl
  have hform : chartHessianBilinAt F y =
      (hessFun (I := I) g f x).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap := by
    apply (LinearMap.ext_iff_basis (chartModelBasis E) (chartModelBasis E)).2
    intro i j
    change chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j) =
      hessFun (I := I) g f x (e.symm (chartModelBasis E i))
        (e.symm (chartModelBasis E j))
    rw [show e.symm (chartModelBasis E i) =
          centeredChartTangentBasis (I := I) x i by rfl,
      show e.symm (chartModelBasis E j) =
          centeredChartTangentBasis (I := I) x j by rfl,
      hessFun_basis_apply, ← hiter, chartHessianTensor_def]
    change chartIteratedPartialDeriv (I := I) x f i j y =
      chartIteratedPartialDeriv (I := I) x f i j y -
        ∑ k, chartChristoffel (I := I) g x i j k y * partialDeriv k F y
    simp [hpartial]
  refine ⟨hcrit, ?_⟩
  apply QuadraticMap.separatingLeft_of_anisotropic
  intro u hu
  have hHessZero : hessFun (I := I) g f x (e.symm u) (e.symm u) = 0 := by
    have hraw : chartHessianBilinAt F y u u = 0 := by
      have hraw' : chartHessianBilinAt
          (fun z : E => f ((extChartAt I x).symm z)) (extChartAt I x x) u u = 0 := by
        simpa [chartHessianAt] using hu
      have hfun : (fun z : E => f ((extChartAt I x).symm z)) = F := by
        funext z
        rfl
      rw [hfun] at hraw'
      simpa [y] using hraw'
    rw [hform] at hraw
    exact hraw
  rw [hhess] at hHessZero
  have hinner : g.inner x (e.symm u) (e.symm u) = 0 :=
    (mul_eq_zero.mp hHessZero).resolve_left hc
  have htangent : e.symm u = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos x (e.symm u) hne)) hinner
  apply e.symm.injective
  simpa using htangent

theorem tendsto_setIntegral_regularized_normGradSqFun_inv_sq_smul_of_compact_of_disjoint_criticalPoints
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [T2Space M]
    {μ : Measure M} {s : Set M} (hs : IsCompact s)
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (hdisjoint : Disjoint s (criticalPoints I f))
    {b : M → V} (hb : IntegrableOn b s μ) :
    Tendsto
      (fun ε : Real => ∫ x in s,
        (ε * (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2) • b x ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hs_nonempty : s.Nonempty
  · let U : M → Real := normGradSqFun (I := I) g (f : M → Real)
    have hU_cont : Continuous U := normGradSqFun_continuous (I := I) g f.contMDiff
    obtain ⟨x₀, hx₀, hmin⟩ := hs.exists_isMinOn hs_nonempty hU_cont.continuousOn
    let δ : Real := U x₀
    have hδ_nonneg : 0 ≤ δ := normGradSqFun_nonneg (I := I) g f x₀
    have hδ_ne : δ ≠ 0 := by
      intro hδ_zero
      have hx₀_critical : x₀ ∈ criticalPoints I f := by
        change mfderiv I 𝓘(Real, Real) f x₀ = 0
        exact (normGradSqFun_eq_zero_iff (I := I)).mp hδ_zero
      exact Set.disjoint_left.1 hdisjoint hx₀ hx₀_critical
    have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg hδ_ne.symm
    have hU_meas : AEMeasurable U (μ.restrict s) :=
      hU_cont.aemeasurable.mono_measure Measure.restrict_le_self
    have hδ_le : ∀ᵐ x ∂(μ.restrict s), δ ≤ U x := by
      refine (ae_restrict_iff' hs.measurableSet).2 ?_
      exact Filter.Eventually.of_forall fun x hx => hmin hx
    simpa only [U] using
      DifferentialGeometry.Analysis.Integration.tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound
        hU_meas hb hδ_pos hδ_le
  · have hs_empty : s = ∅ := not_nonempty_iff_eq_empty.mp hs_nonempty
    subst s
    simp

end DifferentialGeometry.Topology.Morse
