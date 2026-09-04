import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Matrix MeasureTheory
open scoped ContDiff ENNReal Manifold RealInnerProductSpace

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem lSrcGram_eq_gramMatrixAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    lSrcGram S T x =
      DifferentialGeometry.Integral.L2.gramMatrixAt
        (I := I) (M := M) (S.base.metric T) x := by
  ext i j
  simp only [lSrcGram, Matrix.of_apply,
    DifferentialGeometry.Integral.L2.gramMatrixAt_apply,
    DifferentialGeometry.Integral.L2.modelInnerAt_apply]
  with_unfolding_all
    simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSrcGram_pd
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    (lSrcGram S T x).PosDef := by
  rw [lSrcGram_eq_gramMatrixAt S T x]
  exact DifferentialGeometry.Integral.L2.gramMatrixAt_posDef
    (I := I) (M := M) (S.base.metric T) x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSrcGram_quad
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) (Z : E) :
    inner Real (toEuclidean Z)
        (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
          (𝕜 := Real) (lSrcGram S T x) (toEuclidean Z)) =
      (S.base.metric T).inner x Z Z := by
  classical
  let v := toEuclidean Z
  let w : E := ∑ i : Fin (Module.finrank Real E),
    v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i
  have hw : w = Z := by
    have hvsum :
        v = ∑ i : Fin (Module.finrank Real E),
          v i • EuclideanSpace.single i (1 : Real) := by
      let b := (EuclideanSpace.basisFun
        (Fin (Module.finrank Real E)) Real).toBasis
      simpa [b, EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
    calc
      w = (toEuclidean (E := E)).symm v := by
        rw [hvsum]
        rw [map_sum]
        simp only [w, map_smul, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
      _ = Z := by
        simpa only [v] using (toEuclidean (E := E)).symm_apply_apply Z
  let g := S.base.metric T
  calc
    inner Real v
        (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
          (𝕜 := Real) (lSrcGram S T x) v) =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            v i * v j *
              DifferentialGeometry.Integral.L2.modelInnerAt
                (I := I) (M := M) g x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
      rw [lSrcGram_eq_gramMatrixAt S T x]
      rw [Matrix.inner_toEuclideanCLM]
      simp only [dotProduct, Matrix.mulVec,
        DifferentialGeometry.Integral.L2.gramMatrixAt_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = DifferentialGeometry.Integral.L2.modelInnerAt
        (I := I) (M := M) g x w w := by
      symm
      change DifferentialGeometry.Integral.L2.modelInnerAt
          (I := I) (M := M) g x
          (∑ i : Fin (Module.finrank Real E),
            v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
          (∑ j : Fin (Module.finrank Real E),
            v j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsm1 :
          DifferentialGeometry.Integral.L2.modelInnerAt
              (I := I) (M := M) g x
              (∑ i : Fin (Module.finrank Real E),
                v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (v j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
            v j * DifferentialGeometry.Integral.L2.modelInnerAt
              (I := I) (M := M) g x
              (∑ i : Fin (Module.finrank Real E),
                v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
        have h := ContinuousLinearMap.map_smul
          (DifferentialGeometry.Integral.L2.modelInnerAt
            (I := I) (M := M) g x
            (∑ i : Fin (Module.finrank Real E),
              v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
          (v j) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
        simpa only [smul_eq_mul] using h
      rw [hsm1]
      rw [map_sum, _root_.sum_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsm2 :
          DifferentialGeometry.Integral.L2.modelInnerAt
              (I := I) (M := M) g x (v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
            v i * DifferentialGeometry.Integral.L2.modelInnerAt
              (I := I) (M := M) g x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
        have h :
            DifferentialGeometry.Integral.L2.modelInnerAt
                (I := I) (M := M) g x (v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
              v i • DifferentialGeometry.Integral.L2.modelInnerAt
                (I := I) (M := M) g x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) :=
          ContinuousLinearMap.map_smul
            (DifferentialGeometry.Integral.L2.modelInnerAt
              (I := I) (M := M) g x) (v i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
        rw [h, _root_.smul_apply, smul_eq_mul]
      rw [hsm2]
      rw [DifferentialGeometry.Integral.L2.modelInnerAt_symm
        (I := I) (M := M) g x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)]
      ring
    _ = DifferentialGeometry.Integral.L2.modelInnerAt
        (I := I) (M := M) g x Z Z := by rw [hw]
    _ = (S.base.metric T).inner x Z Z := by
      simp only [DifferentialGeometry.Integral.L2.modelInnerAt_apply,
        g]
      with_unfolding_all
        simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply]

noncomputable def lSrcGauss
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) (Z : E) : Real :=
  ((Real.pi : Real) ^
      ((Module.finrank Real E : Real) / 2))⁻¹ *
    lSrcDensity S T x *
    Real.exp (-inner Real (toEuclidean Z)
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
        (𝕜 := Real) (lSrcGram S T x) (toEuclidean Z)))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSrcGauss_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) (Z : E) :
    lSrcGauss S T x Z =
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        lSrcDensity S T x *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
  rw [lSrcGauss, lSrcGram_quad]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSrcGauss_mass
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    ∫⁻ Z : E, ENNReal.ofReal (lSrcGauss S T x Z)
      ∂(modelHaar (E := E)) = 1 := by
  classical
  let A := lSrcGram S T x
  let L := spdSqrtEquiv A (lSrcGram_pd S T x)
  let f : EuclideanSpace Real (Fin (Module.finrank Real E)) → Real :=
    fun y ↦ Real.exp (-‖y‖ ^ 2)
  let q : EuclideanSpace Real (Fin (Module.finrank Real E)) → Real :=
    fun y ↦ Real.exp (-inner Real y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
        (𝕜 := Real) A y))
  have hf : Integrable f := by
    have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace Real (Fin (Module.finrank Real E)))
      (b := (1 : Complex)) (by norm_num) (0 : Complex) 0
    have hn := hc.norm
    refine hn.congr ?_
    filter_upwards with y
    simp only [f, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.one_re, zero_mul, add_zero]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [Complex.neg_im, Complex.one_im, neg_zero,
      Complex.ofReal_im, mul_zero, sub_zero, neg_one_mul]
  have hdet : LinearMap.det
      ((L : EuclideanSpace Real (Fin (Module.finrank Real E)) →L[Real]
        EuclideanSpace Real (Fin (Module.finrank Real E))) :
          EuclideanSpace Real (Fin (Module.finrank Real E)) →ₗ[Real]
            EuclideanSpace Real (Fin (Module.finrank Real E))) =
      Real.sqrt A.det := spdSqrt_det A (lSrcGram_pd S T x)
  have hdet_pos : 0 < LinearMap.det
      ((L : EuclideanSpace Real (Fin (Module.finrank Real E)) →L[Real]
        EuclideanSpace Real (Fin (Module.finrank Real E))) :
          EuclideanSpace Real (Fin (Module.finrank Real E)) →ₗ[Real]
            EuclideanSpace Real (Fin (Module.finrank Real E))) := by
    rw [hdet]
    exact Real.sqrt_pos.2 (lSrcGram_pd S T x).det_pos
  have hmap : Measure.map
      (L : EuclideanSpace Real (Fin (Module.finrank Real E)) →ₗ[Real]
        EuclideanSpace Real (Fin (Module.finrank Real E)))
      (volume : Measure (EuclideanSpace Real (Fin (Module.finrank Real E)))) =
        ENNReal.ofReal ((LinearMap.det
          ((L : EuclideanSpace Real (Fin (Module.finrank Real E)) →L[Real]
            EuclideanSpace Real (Fin (Module.finrank Real E))) :
              EuclideanSpace Real (Fin (Module.finrank Real E)) →ₗ[Real]
                EuclideanSpace Real (Fin (Module.finrank Real E))))⁻¹) • volume := by
    have hout := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (EuclideanSpace Real (Fin (Module.finrank Real E))))
      hdet_pos.ne'
    rw [abs_of_pos (inv_pos.mpr hdet_pos)] at hout
    exact hout
  have hq : Integrable q := by
    have hfmap : Integrable f
        (Measure.map
          (L : EuclideanSpace Real (Fin (Module.finrank Real E)) →ₗ[Real]
            EuclideanSpace Real (Fin (Module.finrank Real E))) volume) := by
      rw [hmap]
      exact hf.smul_measure (by simp)
    have hcomp := hfmap.comp_measurable
      (L : EuclideanSpace Real (Fin (Module.finrank Real E)) →L[Real]
        EuclideanSpace Real (Fin (Module.finrank Real E))).continuous.measurable
    have heq : (f ∘ L) = q := by
      funext y
      simp only [Function.comp_apply, q, f, L]
      rw [spdSqrt_norm_sq]
    exact heq ▸ hcomp
  let c : Real := ((Real.pi : Real) ^
      ((Module.finrank Real E : Real) / 2))⁻¹ * lSrcDensity S T x
  have hc0 : 0 ≤ c := mul_nonneg
    (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
    (lSrcDensity_pos S T x).le
  have hF : Integrable (fun y ↦ c * q y) := hq.const_mul c
  have hFn : ∀ y, 0 ≤ c * q y := fun y ↦ mul_nonneg hc0 (Real.exp_pos _).le
  have hFint : ∫ y, c * q y = 1 := by
    rw [integral_const_mul, gaussSPD_int A (lSrcGram_pd S T x)]
    simp only [c, A, Fintype.card_fin]
    rw [show lSrcDensity S T x = Real.sqrt (lSrcGram S T x).det from rfl]
    have hsqrt : Real.sqrt (lSrcGram S T x).det ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (lSrcGram_pd S T x).det_pos)
    have hpi : (Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
    field_simp
  calc
    ∫⁻ Z : E, ENNReal.ofReal (lSrcGauss S T x Z)
        ∂(modelHaar (E := E)) =
        ∫⁻ Z : E, ENNReal.ofReal (c * q (toEuclidean Z))
          ∂(modelHaar (E := E)) := by
      refine lintegral_congr fun Z ↦ congrArg ENNReal.ofReal ?_
      rfl
    _ = ∫⁻ y, ENNReal.ofReal (c * q y)
          ∂(Measure.map (toEuclidean (E := E)) (modelHaar (E := E))) := by
      symm
      exact (toEuclidean (E := E)).toHomeomorph.measurableEmbedding.lintegral_map _
    _ = ∫⁻ y, ENNReal.ofReal (c * q y)
          ∂(volume : Measure (EuclideanSpace Real
            (Fin (Module.finrank Real E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ENNReal.ofReal (∫ y, c * q y) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF
        (ae_of_all _ hFn)).symm
    _ = 1 := by rw [hFint]; norm_num

end DifferentialGeometry.PDE.RicciFlow.Perelman
