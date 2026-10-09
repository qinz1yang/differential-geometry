import DifferentialGeometry.Geometry.Collapse.BoundaryScale.TorusAngleArea
import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.LinearAlgebra.Matrix.LoewnerDeterminant

/-!
# The cusp volume density in angle coordinates (statement V.1, step 3)

The collar model space is `E₃ = ℝ³`; the coordinates `cuspCoordEquiv v = ((v₀, v₁), v₂)` identify it
linearly with `E₂ × ℝ`, `E₂ = ℝ¹ × ℝ¹` the model space of the torus. For a metric `g_T` on the torus,
a point `(u, s)` and `D = mfderiv torusAngleParam u`, the model cusp metric `dz² + e^{-s} g_T`
pulled back by the angle parametrisation is the bilinear form
`cuspModelForm g_T u s ((x, t), (y, t')) = t t' + e^{-s} g_T(D x, D y)` on `E₂ × ℝ`.

* `det_toMatrix_cuspModelForm`: in the product basis `(chartModelBasis E₂) × {1}` its Gram matrix is
  block diagonal, with determinant `e^{-2s} det G_T(u)`, `G_T = paramGramMatrix g_T torusAngleParam`;
* `sqrt_det_toMatrix_cuspModelForm_comp`: in the basis `chartModelBasis E₃` of the Gram matrices of
  `paramDensity`, `√det = c · e^{-s} · ρ_T(u)`, `c = cuspAngleConstant` (a change-of-basis
  determinant, PROVED from `BilinForm.sqrt_det_toMatrix_basis_change`, not unfolded);
* `smul_modelHaar_eq_map_prod`: with the SAME constant, `c • modelHaar_{E₃}` is the image of
  `modelHaar_{E₂} ⊗ volume` under the inverse coordinates (`Basis.det_smul_addHaar`,
  `Basis.map_addHaar`, `Basis.prod_addHaar`); hence the constants cancel
  (`setLIntegral_smul_modelHaar_eq`).

The σ-algebras of `E₂`, `E₃` are their Borel σ-algebras (local instances, those of `modelHaar`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function Matrix
open DifferentialGeometry.Integral.Measure GC.Endpoint
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

local notation "E₂" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance instMeasE₂ : MeasurableSpace E₂ := borel E₂
private local instance instBorelE₂ : BorelSpace E₂ := ⟨rfl⟩
private local instance instMeasE₃ : MeasurableSpace E₃ := borel E₃
private local instance instBorelE₃ : BorelSpace E₃ := ⟨rfl⟩

/-- The linear coordinates `v ↦ ((v₀, v₁), v₂)` of the collar model space `ℝ³`. -/
def cuspCoordEquiv : E₃ ≃L[ℝ] E₂ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun v => ((WithLp.toLp 2 (fun _ => v 0), WithLp.toLp 2 (fun _ => v 1)), v 2)
    invFun := fun p => WithLp.toLp 2 ![p.1.1 0, p.1.2 0, p.2]
    map_add' := fun v w => by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · ext i; simp
      · ext i; simp
      · simp
    map_smul' := fun c v => by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · ext i; simp
      · ext i; simp
      · simp
    left_inv := fun v => by
      ext i
      fin_cases i <;> simp
    right_inv := fun p => by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · ext i; rw [Subsingleton.elim i 0]; simp
      · ext i; rw [Subsingleton.elim i 0]; simp
      · simp }

@[simp] theorem cuspCoordEquiv_apply_snd (v : E₃) : (cuspCoordEquiv v).2 = v 2 := rfl

/-- The model cusp metric `dz² + e^{-s} g_T` pulled back to `E₂ × ℝ` by the angle parametrisation
at `(u, s)`. -/
def cuspModelForm (gT : SmoothRiemannianMetric torusModel Torus) (u : E₂) (s : ℝ) :
    LinearMap.BilinForm ℝ (E₂ × ℝ) :=
  Real.exp (-s) • ((gT.inner (torusAngleParam u)).toLinearMap₁₂.compl₁₂
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u).toLinearMap
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u).toLinearMap).compl₁₂
      (LinearMap.fst ℝ E₂ ℝ) (LinearMap.fst ℝ E₂ ℝ) +
    (LinearMap.mul ℝ ℝ).compl₁₂ (LinearMap.snd ℝ E₂ ℝ) (LinearMap.snd ℝ E₂ ℝ)

theorem cuspModelForm_apply (gT : SmoothRiemannianMetric torusModel Torus) (u : E₂) (s : ℝ)
    (x y : E₂ × ℝ) :
    cuspModelForm gT u s x y = Real.exp (-s) * gT.inner (torusAngleParam u)
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u x.1)
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u y.1) + x.2 * y.2 :=
  rfl

/-- The product basis `(chartModelBasis E₂) × {1}` of `E₂ × ℝ`. -/
def cuspProdBasis : Module.Basis (Fin (Module.finrank ℝ E₂) ⊕ Fin 1) ℝ (E₂ × ℝ) :=
  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₂).prod (Module.Basis.singleton (Fin 1) ℝ)

theorem torusAngle_inner_zero_right (gT : SmoothRiemannianMetric torusModel Torus) (u x : E₂) :
    gT.inner (torusAngleParam u) (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u x)
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u 0) = 0 := by
  rw [ContinuousLinearMap.map_zero, ContinuousLinearMap.map_zero]

theorem torusAngle_inner_zero_left (gT : SmoothRiemannianMetric torusModel Torus) (u x : E₂) :
    gT.inner (torusAngleParam u) (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u 0)
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u x) = 0 := by
  rw [ContinuousLinearMap.map_zero, ContinuousLinearMap.map_zero, _root_.zero_apply]

theorem toMatrix_cuspModelForm (gT : SmoothRiemannianMetric torusModel Torus) (u : E₂) (s : ℝ) :
    LinearMap.BilinForm.toMatrix cuspProdBasis (cuspModelForm gT u s) =
      fromBlocks (Real.exp (-s) • paramGramMatrix gT torusAngleParam u) 0 0 1 := by
  ext (i | i) (j | j)
  · simp [LinearMap.BilinForm.toMatrix_apply, cuspModelForm_apply, cuspProdBasis]
  · rw [LinearMap.BilinForm.toMatrix_apply, cuspModelForm_apply, fromBlocks_apply₁₂]
    simp only [cuspProdBasis, Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd]
    erw [torusAngle_inner_zero_right]
    simp
  · rw [LinearMap.BilinForm.toMatrix_apply, cuspModelForm_apply, fromBlocks_apply₂₁]
    simp only [cuspProdBasis, Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd]
    erw [torusAngle_inner_zero_left]
    simp
  · rw [LinearMap.BilinForm.toMatrix_apply, cuspModelForm_apply, fromBlocks_apply₂₂]
    simp only [cuspProdBasis, Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd]
    erw [torusAngle_inner_zero_left]
    obtain rfl := Subsingleton.elim i j
    simp

theorem finrank_torusModelSpace' : Module.finrank ℝ E₂ = 2 := by
  simp [Module.finrank_prod]

theorem det_toMatrix_cuspModelForm (gT : SmoothRiemannianMetric torusModel Torus) (u : E₂) (s : ℝ) :
    (LinearMap.BilinForm.toMatrix cuspProdBasis (cuspModelForm gT u s)).det =
      Real.exp (-s) ^ 2 * (paramGramMatrix gT torusAngleParam u).det := by
  have h2 : Real.exp (-s) ^ Module.finrank ℝ E₂ = Real.exp (-s) ^ 2 := by
    rw [finrank_torusModelSpace']
  rw [toMatrix_cuspModelForm, det_fromBlocks_zero₂₁, det_one, mul_one, det_smul, Fintype.card_fin,
    h2]

/-- The index equivalence `Fin (dim E₂) ⊕ Fin 1 ≃ Fin (dim E₃)`. -/
def cuspIndexEquiv : Fin (Module.finrank ℝ E₂) ⊕ Fin 1 ≃ Fin (Module.finrank ℝ E₃) :=
  Fintype.equivOfCardEq (by simp [Module.finrank_prod])

/-- The product basis transported to `E₃` by the inverse coordinates. -/
def cuspAngleBasis : Module.Basis (Fin (Module.finrank ℝ E₃)) ℝ E₃ :=
  (cuspProdBasis.map cuspCoordEquiv.symm.toLinearEquiv).reindex cuspIndexEquiv

/-- The change-of-basis constant between `cuspAngleBasis` and `chartModelBasis E₃`. -/
def cuspAngleConstant : ℝ :=
  |cuspAngleBasis.det (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₃)|

theorem cuspAngleConstant_nonneg : 0 ≤ cuspAngleConstant := abs_nonneg _

theorem det_toMatrix_cuspAngleBasis (B : LinearMap.BilinForm ℝ (E₂ × ℝ)) :
    (LinearMap.BilinForm.toMatrix cuspAngleBasis
        (B.compl₁₂ cuspCoordEquiv.toLinearMap cuspCoordEquiv.toLinearMap)).det =
      (LinearMap.BilinForm.toMatrix cuspProdBasis B).det := by
  have h : LinearMap.BilinForm.toMatrix cuspAngleBasis
      (B.compl₁₂ cuspCoordEquiv.toLinearMap cuspCoordEquiv.toLinearMap) =
      reindex cuspIndexEquiv cuspIndexEquiv (LinearMap.BilinForm.toMatrix cuspProdBasis B) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, cuspAngleBasis]
  rw [h, det_reindex_self]

/-- **The model density in angle coordinates**: in the basis `chartModelBasis E₃`,
`√det Gram(dz² + e^{-s} g_T) = c · e^{-s} · ρ_T(u)`. -/
theorem sqrt_det_toMatrix_cuspModelForm_comp (gT : SmoothRiemannianMetric torusModel Torus)
    (u : E₂) (s : ℝ) :
    Real.sqrt (LinearMap.BilinForm.toMatrix (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₃)
        ((cuspModelForm gT u s).compl₁₂ cuspCoordEquiv.toLinearMap cuspCoordEquiv.toLinearMap)).det =
      cuspAngleConstant * (Real.exp (-s) * paramDensity gT torusAngleParam u) := by
  rw [LinearMap.BilinForm.sqrt_det_toMatrix_basis_change _ cuspAngleBasis, det_toMatrix_cuspAngleBasis,
    det_toMatrix_cuspModelForm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
  rfl

theorem addHaar_basis_singleton_real : (Module.Basis.singleton (Fin 1) ℝ).addHaar = volume := by
  rw [Module.Basis.addHaar_eq_iff, Module.Basis.coe_parallelepiped]
  have h := parallelepiped_orthonormalBasis_one_dim (OrthonormalBasis.singleton (Fin 1) ℝ)
  have hc : ⇑(OrthonormalBasis.singleton (Fin 1) ℝ) = ⇑(Module.Basis.singleton (Fin 1) ℝ) := by
    funext i
    simp
  rw [hc] at h
  rcases h with h | h <;> erw [h] <;> simp

/-- **Haar normalisation**: `c • modelHaar_{E₃}` is the image of `modelHaar_{E₂} ⊗ volume` under the
inverse coordinates, with the constant `c` of `sqrt_det_toMatrix_cuspModelForm_comp`. -/
theorem smul_modelHaar_eq_map_prod :
    ENNReal.ofReal cuspAngleConstant • modelHaar (E := E₃) =
      Measure.map cuspCoordEquiv.symm ((modelHaar (E := E₂)).prod volume) := by
  have h1 : ENNReal.ofReal cuspAngleConstant • modelHaar (E := E₃) = cuspAngleBasis.addHaar :=
    Module.Basis.det_smul_addHaar cuspAngleBasis _
  rw [h1, cuspAngleBasis, Module.Basis.addHaar_reindex, ← Module.Basis.map_addHaar,
    cuspProdBasis, Module.Basis.prod_addHaar, addHaar_basis_singleton_real]
  rfl

/-- The change of variables of V.1: integrals against `c • modelHaar_{E₃}` of functions of the
coordinates are integrals against `modelHaar_{E₂} ⊗ volume`. -/
theorem setLIntegral_smul_modelHaar_eq {K : Set E₃} (hK : MeasurableSet K)
    {F : E₂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v in K, F (cuspCoordEquiv v) ∂(ENNReal.ofReal cuspAngleConstant • modelHaar (E := E₃)) =
      ∫⁻ w in cuspCoordEquiv.symm ⁻¹' K, F w ∂((modelHaar (E := E₂)).prod volume) := by
  rw [smul_modelHaar_eq_map_prod]
  have h := setLIntegral_map (μ := (modelHaar (E := E₂)).prod volume) hK
    (hF.comp cuspCoordEquiv.continuous.measurable) cuspCoordEquiv.symm.continuous.measurable
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
