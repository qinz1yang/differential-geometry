import DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparison
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# DensityComparisonC11X（S-CH11-EXT2，extension of 已跟踪宿主
`Analysis/Integration/Measure/Parametric/DensityComparison.lean`）

astra（`chapter11-astra` @ a73e4bdbfd）新增 `paramDensity_le_of_inner_mfderiv_le`：
目标 differential 允许 singular，用 quadratic contraction `h(dv z, dv z) ≤ g(du z, du z)`
与 `du` injective 得 `paramDensity h v x ≤ paramDensity g u x`。W8 宿主（
`rpow_mul_sqrt_det_le_paramDensity` 等 5 个声明）保持不变，不替换已跟踪文件；
本文件逐字抄写 donor 的新增声明（6 个 private helper + 1 个 public theorem），证明体不改，
只在 import 里加宿主。直接用户：`Analysis/Integration/Measure/Riemannian/LipschitzImage`
（EXT1 的 port）。
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Matrix
open scoped Manifold ContDiff Matrix MatrixOrder

namespace DifferentialGeometry.Integral.Measure

-- The determinant argument is adapted from the private positive-semidefinite /
-- positive-definite comparison in Riemannian/MetricComparison.lean.
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
  refine Finset.prod_le_one₀ (fun i _ ↦ ?_) (fun i _ ↦ ?_)
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem paramGramMatrix_isHermitian_of_map
    (g : SmoothRiemannianMetric I M) (u : E → M) (x : E) :
    (paramGramMatrix g u x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp only [paramGramMatrix_apply, star_trivial]
  exact g.symm _ _ _

private theorem paramGramMatrix_quad_of_map
    (g : SmoothRiemannianMetric I M) (u : E → M) (x : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    c ⬝ᵥ ((paramGramMatrix g u x) *ᵥ c) =
      g.inner (u x)
        (mfderiv 𝓘(ℝ, E) I u x ((Tensor.Coordinates.chartModelBasis E).equivFun.symm c))
        (mfderiv 𝓘(ℝ, E) I u x ((Tensor.Coordinates.chartModelBasis E).equivFun.symm c)) := by
  let b := Tensor.Coordinates.chartModelBasis E
  let D := mfderiv 𝓘(ℝ, E) I u x
  let B := (g.inner (u x)).toBilinForm.comp D.toLinearMap D.toLinearMap
  have hgram : paramGramMatrix g u x = LinearMap.BilinForm.toMatrix b B := by
    ext i j
    calc
      paramGramMatrix g u x i j = g.inner (u x) (D (b i)) (D (b j)) :=
        paramGramMatrix_apply g u x i j
      _ = B (b i) (b j) := rfl
      _ = LinearMap.BilinForm.toMatrix b B i j :=
        (LinearMap.BilinForm.toMatrix_apply b B i j).symm
  calc
    c ⬝ᵥ ((paramGramMatrix g u x) *ᵥ c) =
        c ⬝ᵥ ((LinearMap.BilinForm.toMatrix b B) *ᵥ c) := by rw [hgram]
    _ = B (b.equivFun.symm c) (b.equivFun.symm c) :=
      B.dotProduct_toMatrix_mulVec b c c
    _ = _ := rfl

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A quadratic contraction between the actual parametric differentials
contracts their volume densities. The target differential may be singular.
The algebra is valid also in dimension zero and for boundary models. -/
theorem paramDensity_le_of_inner_mfderiv_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {u : E → M} {v : E → N} {x : E}
    (huinj : Function.Injective (mfderiv 𝓘(ℝ, E) I u x))
    (hcomp : ∀ z : E,
      h.inner (v x) (mfderiv 𝓘(ℝ, E) J v x z) (mfderiv 𝓘(ℝ, E) J v x z) ≤
        g.inner (u x) (mfderiv 𝓘(ℝ, E) I u x z) (mfderiv 𝓘(ℝ, E) I u x z)) :
    paramDensity h v x ≤ paramDensity g u x := by
  classical
  let b := Tensor.Coordinates.chartModelBasis E
  have hA : (paramGramMatrix h v x).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (paramGramMatrix_isHermitian_of_map h v x) ?_
    intro c
    rw [star_trivial, paramGramMatrix_quad_of_map]
    exact metric_inner_self_nonneg h _ _
  have hB : (paramGramMatrix g u x).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (paramGramMatrix_isHermitian_of_map g u x) ?_
    intro c hc
    rw [star_trivial, paramGramMatrix_quad_of_map]
    apply g.pos
    intro hz
    have heq : mfderiv 𝓘(ℝ, E) I u x (b.equivFun.symm c) =
        mfderiv 𝓘(ℝ, E) I u x 0 := by simpa only [map_zero] using hz
    apply hc
    calc
      c = b.equivFun (b.equivFun.symm c) := (b.equivFun.apply_symm_apply c).symm
      _ = b.equivFun (0 : E) := congrArg b.equivFun (huinj heq)
      _ = 0 := b.equivFun.map_zero
  have hAB : ∀ c : Fin (Module.finrank ℝ E) → ℝ,
      c ⬝ᵥ ((paramGramMatrix h v x) *ᵥ c) ≤
        c ⬝ᵥ ((paramGramMatrix g u x) *ᵥ c) := by
    intro c
    rw [paramGramMatrix_quad_of_map, paramGramMatrix_quad_of_map]
    exact hcomp _
  exact Real.sqrt_le_sqrt (det_le_of_quad_le hA hB hAB)

end DifferentialGeometry.Integral.Measure
