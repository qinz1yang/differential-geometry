import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold ContDiff Matrix MatrixOrder Topology

namespace DifferentialGeometry.Integral.Measure

section MatrixDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma eigenvalues_le_of_rayleigh
    {A : Matrix ι ι Real} {a : Real} (hA : A.IsHermitian)
    (hray : ∀ v : EuclideanSpace Real ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ a) :
    ∀ i, hA.eigenvalues i ≤ a := by
  intro i
  rw [hA.eigenvalues_eq i]
  exact hray (hA.eigenvectorBasis i) (hA.eigenvectorBasis.norm_eq_one i)

private lemma det_le_one_of_rayleigh
    {A : Matrix ι ι Real} (hA : A.PosSemidef)
    (hray : ∀ v : EuclideanSpace Real ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ 1) :
    A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one (fun i _ ↦ ?_) (fun i _ ↦ ?_)
  · exact_mod_cast hA.eigenvalues_nonneg i
  · exact_mod_cast eigenvalues_le_of_rayleigh hA.isHermitian hray i

private lemma det_le_one_of_dotProduct
    {A : Matrix ι ι Real} (hA : A.PosSemidef)
    (hray : ∀ x : ι → Real, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) :
    A.det ≤ 1 := by
  refine det_le_one_of_rayleigh hA (fun v hv ↦ ?_)
  have hnorm : (⇑v : ι → Real) ⬝ᵥ ⇑v = 1 := by
    have h1 := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := Real) v v
    rw [star_trivial] at h1
    have h2 : (⇑v : ι → Real) ⬝ᵥ ⇑v = ‖v‖ ^ 2 := by
      rw [← h1]
      exact real_inner_self_eq_norm_sq v
    rw [h2, hv, one_pow]
  simp only [star_trivial, RCLike.re_to_real]
  exact (hray ⇑v).trans hnorm.le

private lemma det_le_of_quad_le
    {A B : Matrix ι ι Real} (hA : A.PosSemidef) (hB : B.PosDef)
    (hAB : ∀ x : ι → Real, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  classical
  have quad_symm : ∀ (S : Matrix ι ι Real), Sᵀ = S → ∀ x z : ι → Real,
      x ⬝ᵥ (S *ᵥ z) = (S *ᵥ x) ⬝ᵥ z := by
    intro S hS x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
  set P := CFC.sqrt B with hP_def
  have hP_nonneg : (0 : Matrix ι ι Real) ≤ P := by
    rw [hP_def]
    exact CFC.sqrt_nonneg B
  have hP_psd : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hP_herm : Pᴴ = P := hP_psd.isHermitian
  have hPsymm : Pᵀ = P := by
    ext i j
    simpa [Matrix.transpose_apply, star_trivial] using hP_psd.isHermitian.apply i j
  have hPP : P * P = B := by
    rw [hP_def]
    exact CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
  have hdetB_pos : 0 < B.det := hB.det_pos
  have hdetPP : P.det * P.det = B.det := by rw [← Matrix.det_mul, hPP]
  have hdetP_ne : P.det ≠ 0 := fun h0 ↦
    hdetB_pos.ne' (by rw [← hdetPP, h0, zero_mul])
  have hdetP_unit : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP_ne
  have hPinv_r : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdetP_unit
  have hPinv_l : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdetP_unit
  have hPinvsymm : (P⁻¹)ᵀ = P⁻¹ := by rw [Matrix.transpose_nonsing_inv, hPsymm]
  have hC_psd : (P⁻¹ * A * P⁻¹).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same P⁻¹
    rwa [Matrix.conjTranspose_nonsing_inv, hP_herm] at h
  have hC_ray : ∀ x : ι → Real,
      x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hPw : P *ᵥ (P⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hPinv_r, Matrix.one_mulVec]
    have e1 : x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) =
        (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact quad_symm P⁻¹ hPinvsymm x (A *ᵥ (P⁻¹ *ᵥ x))
    have e3 : (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) = x ⬝ᵥ x := by
      rw [← hPP, ← Matrix.mulVec_mulVec,
        quad_symm P hPsymm (P⁻¹ *ᵥ x) (P *ᵥ (P⁻¹ *ᵥ x)), hPw]
    calc
      x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) =
          (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := e1
      _ ≤ (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) := hAB (P⁻¹ *ᵥ x)
      _ = x ⬝ᵥ x := e3
  have hdetC : (P⁻¹ * A * P⁻¹).det ≤ 1 :=
    det_le_one_of_dotProduct hC_psd hC_ray
  have hACM : P * (P⁻¹ * A * P⁻¹) * P = A := by
    rw [show P * (P⁻¹ * A * P⁻¹) * P =
      (P * P⁻¹) * A * (P⁻¹ * P) by simp only [mul_assoc]]
    rw [hPinv_r, hPinv_l, one_mul, mul_one]
  have hdetA : A.det = B.det * (P⁻¹ * A * P⁻¹).det := by
    have hcongr := congrArg Matrix.det hACM
    rw [Matrix.det_mul, Matrix.det_mul] at hcongr
    rw [← hcongr, ← hdetPP]
    ring
  rw [hdetA]
  exact mul_le_of_le_one_right hdetB_pos.le hdetC

end MatrixDet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chartDensity_le
    (g h : SmoothRiemannianMetric I M) {Q : Real} (hQ : 0 < Q)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hcomp : ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    chartDensity (I := I) h x₀ x ≤
      Real.sqrt (Q ^ Module.finrank Real E) * chartDensity (I := I) g x₀ x := by
  have hA : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) h x₀ x).PosSemidef :=
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef (I := I) h x₀ hx).posSemidef
  have hB : (Q • DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).PosDef :=
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_posDef (I := I) g x₀ hx).smul hQ
  have hAB : ∀ v : Fin (Module.finrank Real E) → Real,
      v ⬝ᵥ (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) h x₀ x) *ᵥ v ≤
        v ⬝ᵥ (Q • DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x) *ᵥ v := by
    intro v
    have hh : v ⬝ᵥ (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) h x₀ x) *ᵥ v =
        h.inner x (∑ i, v i • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, v j • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x) := by
      rw [← DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_dotProduct_mulVec (I := I) h x₀ x v, star_trivial]
    have hg : v ⬝ᵥ (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x) *ᵥ v =
        g.inner x (∑ i, v i • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, v j • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x) := by
      rw [← DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x v, star_trivial]
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hh, hg]
    exact hcomp (∑ i, v i • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i x)
  have hdet : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) h x₀ x).det ≤
      Q ^ Module.finrank Real E * (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det := by
    have hle := det_le_of_quad_le hA hB hAB
    rwa [Matrix.det_smul, Fintype.card_fin] at hle
  change Real.sqrt ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) h x₀ x).det) ≤
    Real.sqrt (Q ^ Module.finrank Real E) *
      Real.sqrt ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det)
  rw [← Real.sqrt_mul (pow_nonneg hQ.le _)]
  exact Real.sqrt_le_sqrt hdet

section VolumeMeasure

variable [T2Space M] [SigmaCompactSpace M]

open scoped ENNReal

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma chart_setLIntegral_le
    (q h : SmoothRiemannianMetric I M) (alpha : M) (C : ℝ) (hC : 0 ≤ C)
    {s : Set M} (hs : MeasurableSet s)
    (hdensity : ∀ x ∈ tsupport
      (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
      x ∈ s →
      chartDensity (I := I) h alpha x ≤ C * chartDensity (I := I) q alpha x)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in s, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
        ∂(chartLocalMeasure (I := I) h alpha) ≤
      ENNReal.ofReal C *
        ∫⁻ x in s, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) q alpha) := by
  let rho : M → ℝ := fun x => (chartAtlasPOU I M alpha : M → ℝ) x
  have hrho_meas : Measurable (fun x : M => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp ((chartAtlasPOU I M alpha).contMDiff.continuous.measurable
      )
  have hprod_meas : Measurable (fun x : M => ENNReal.ofReal (rho x) * F x) :=
    hrho_meas.mul hF
  have hind_meas : Measurable
      (s.indicator fun x : M => ENNReal.ofReal (rho x) * F x) :=
    hprod_meas.indicator hs
  rw [← lintegral_indicator hs, ← lintegral_indicator hs,
    chartLocalMeasure_lintegral (I := I) h alpha hind_meas,
    chartLocalMeasure_lintegral (I := I) q alpha hind_meas]
  let target : Set E := (extChartAt I alpha).target
  let symm : E → M := fun y => (extChartAt I alpha).symm y
  calc
    ∫⁻ y in target,
        ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) *
          s.indicator (fun x : M => ENNReal.ofReal (rho x) * F x) (symm y)
        ∂(modelHaar (E := E)) ≤
      ∫⁻ y in target, ENNReal.ofReal C *
        (ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) *
          s.indicator (fun x : M => ENNReal.ofReal (rho x) * F x) (symm y))
        ∂(modelHaar (E := E)) := by
          refine lintegral_mono fun y => ?_
          by_cases hys : symm y ∈ s
          · rw [Set.indicator_of_mem hys]
            by_cases hrho : rho (symm y) = 0
            · simp [hrho]
            · have hsymm_tsupp : symm y ∈ tsupport rho :=
                subset_tsupport rho hrho
              have hd := hdensity (symm y) hsymm_tsupp hys
              have hd_en :
                  ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) ≤
                    ENNReal.ofReal C *
                      ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) := by
                have := ENNReal.ofReal_le_ofReal hd
                rw [ENNReal.ofReal_mul hC] at this
                exact this
              have hmul := mul_le_mul_left
                hd_en (ENNReal.ofReal (rho (symm y)) * F (symm y))
              simpa only [mul_assoc] using hmul
          · rw [Set.indicator_of_notMem hys]
            simp only [mul_zero, zero_le]
    _ = ENNReal.ofReal C *
        ∫⁻ y in target,
          ENNReal.ofReal (chartDensity (I := I) q alpha (symm y)) *
            s.indicator (fun x : M => ENNReal.ofReal (rho x) * F x) (symm y)
          ∂(modelHaar (E := E)) := by
        rw [MeasureTheory.lintegral_const_mul'
          (μ := (modelHaar (E := E)).restrict target)
          (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]

lemma chart_lintegral_le
    (q h : SmoothRiemannianMetric I M) (alpha : M) (C : ℝ) (hC : 0 ≤ C)
    (hdensity : ∀ x ∈ tsupport
      (fun y : M => (chartAtlasPOU I M alpha : M → ℝ) y),
      chartDensity (I := I) h alpha x ≤ C * chartDensity (I := I) q alpha x)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
        ∂(chartLocalMeasure (I := I) h alpha) ≤
      ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) q alpha) := by
  simpa only [Measure.restrict_univ] using
    chart_setLIntegral_le (I := I) (M := M) q h alpha C hC MeasurableSet.univ
      (fun x hx _ ↦ hdensity x hx) hF

theorem volumeMeasure_restrict_le
    (g h : SmoothRiemannianMetric I M) {Q : Real} (hQ : 0 < Q)
    {s : Set M} (hs : MeasurableSet s)
    (hcomp : ∀ x ∈ s, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    (riemannianVolumeMeasure (I := I) (M := M) h).restrict s ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
        (riemannianVolumeMeasure (I := I) (M := M) g).restrict s := by
  classical
  have hbase : ∀ (x₀ : M), ∀ x ∈
      tsupport (fun y : M ↦ (chartAtlasPOU I M x₀ : M → Real) y),
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro x₀ x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) x₀ hx
  have hlin : ∀ (F : M → ℝ≥0∞), Measurable F →
      (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h).restrict s) ≤
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
          ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g).restrict s := by
    intro F hF
    change (∫⁻ x in s, F x ∂riemannianMeasure (I := I) h (chartAtlasPOU I M)) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        ∫⁻ x in s, F x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M)
    rw [← lintegral_indicator hs, ← lintegral_indicator hs,
      riemannianMeasure_lintegral_eq (I := I) h (chartAtlasPOU I M)
        (hF.indicator hs),
      riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M)
        (hF.indicator hs)]
    calc
      (∑' x₀ : M, ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) * s.indicator F x
            ∂(chartLocalMeasure (I := I) h x₀)) ≤
          ∑' x₀ : M, ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
            ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) *
                s.indicator F x
              ∂(chartLocalMeasure (I := I) g x₀) := by
        refine ENNReal.tsum_le_tsum fun x₀ ↦ ?_
        have hlocal := chart_setLIntegral_le (I := I) (M := M) g h x₀
          (Real.sqrt (Q ^ Module.finrank Real E)) (Real.sqrt_nonneg _)
          hs (fun x hx hxs ↦
            chartDensity_le (I := I) g h hQ x₀ (hbase x₀ x hx) (hcomp x hxs)) hF
        simpa only [← lintegral_indicator hs, indicator_mul_right] using hlocal
      _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
          ∑' x₀ : M, ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) * s.indicator F x
              ∂(chartLocalMeasure (I := I) g x₀) := ENNReal.tsum_mul_left
  rw [Measure.le_iff]
  intro t ht
  have h := hlin (Set.indicator t (1 : M → ℝ≥0∞))
    (measurable_const.indicator ht)
  rw [lintegral_indicator_one ht, lintegral_indicator_one ht] at h
  simpa only [Measure.smul_apply, smul_eq_mul] using h

theorem volumeMeasure_le
    (g h : SmoothRiemannianMetric I M) {Q : Real} (hQ : 0 < Q)
    (hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := M) h ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
        riemannianVolumeMeasure (I := I) (M := M) g := by
  simpa only [Measure.restrict_univ] using
    volumeMeasure_restrict_le (I := I) (M := M) g h hQ MeasurableSet.univ
      (fun x _ ↦ hcomp x)

end VolumeMeasure

end DifferentialGeometry.Integral.Measure
