import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv
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
  have hA : (chartGramMatrix (I := I) h x₀ x).PosSemidef :=
    (chartGramMatrix_posDef (I := I) h x₀ hx).posSemidef
  have hB : (Q • chartGramMatrix (I := I) g x₀ x).PosDef :=
    (chartGramMatrix_posDef (I := I) g x₀ hx).smul hQ
  have hAB : ∀ v : Fin (Module.finrank Real E) → Real,
      v ⬝ᵥ (chartGramMatrix (I := I) h x₀ x) *ᵥ v ≤
        v ⬝ᵥ (Q • chartGramMatrix (I := I) g x₀ x) *ᵥ v := by
    intro v
    have hh : v ⬝ᵥ (chartGramMatrix (I := I) h x₀ x) *ᵥ v =
        h.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
      rw [← chartGramMatrix_dotProduct_mulVec (I := I) h x₀ x v, star_trivial]
    have hg : v ⬝ᵥ (chartGramMatrix (I := I) g x₀ x) *ᵥ v =
        g.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
      rw [← chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x v, star_trivial]
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hh, hg]
    exact hcomp (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
  have hdet : (chartGramMatrix (I := I) h x₀ x).det ≤
      Q ^ Module.finrank Real E * (chartGramMatrix (I := I) g x₀ x).det := by
    have hle := det_le_of_quad_le hA hB hAB
    rwa [Matrix.det_smul, Fintype.card_fin] at hle
  change Real.sqrt ((chartGramMatrix (I := I) h x₀ x).det) ≤
    Real.sqrt (Q ^ Module.finrank Real E) *
      Real.sqrt ((chartGramMatrix (I := I) g x₀ x).det)
  rw [← Real.sqrt_mul (pow_nonneg hQ.le _)]
  exact Real.sqrt_le_sqrt hdet

section VolumeMeasure

variable [T2Space M] [SigmaCompactSpace M]

open scoped ENNReal

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem volumeMeasure_le
    (g h : SmoothRiemannianMetric I M) {Q : Real} (hQ : 0 < Q)
    (hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := M) h ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
        riemannianVolumeMeasure (I := I) (M := M) g := by
  classical
  have hbase : ∀ (x₀ : M), ∀ x ∈
      tsupport (fun y : M ↦ (chartAtlasPOU I M x₀ : M → Real) y),
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro x₀ x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) x₀ hx
  have hlin : ∀ (F : M → ℝ≥0∞), Measurable F →
      (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h)) ≤
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
          ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro F hF
    change (∫⁻ x, F x ∂riemannianMeasure (I := I) h (chartAtlasPOU I M)) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        ∫⁻ x, F x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M)
    rw [
      riemannianMeasure_lintegral_eq (I := I) h (chartAtlasPOU I M) hF,
      riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF]
    calc
      (∑' x₀ : M, ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) * F x
            ∂(chartLocalMeasure (I := I) h x₀)) ≤
          ∑' x₀ : M, ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
            ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) * F x
              ∂(chartLocalMeasure (I := I) g x₀) := by
        refine ENNReal.tsum_le_tsum fun x₀ ↦ ?_
        exact chart_lintegral_le (I := I) (M := M) g h x₀
          (Real.sqrt (Q ^ Module.finrank Real E)) (Real.sqrt_nonneg _)
          (fun x hx ↦ chartDensity_le (I := I) g h hQ x₀ (hbase x₀ x hx) (hcomp x)) hF
      _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
          ∑' x₀ : M, ∫⁻ x,
            ENNReal.ofReal ((chartAtlasPOU I M x₀ : M → Real) x) * F x
              ∂(chartLocalMeasure (I := I) g x₀) := ENNReal.tsum_mul_left
  rw [Measure.le_iff]
  intro s hs
  have h := hlin (Set.indicator s (1 : M → ℝ≥0∞))
    (measurable_const.indicator hs)
  rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
  simpa only [Measure.smul_apply, smul_eq_mul] using h

end VolumeMeasure

end DifferentialGeometry.Integral.Measure
