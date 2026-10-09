import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspAngleDensity
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparison
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductUpperDistance
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch

/-!
# The collar density in angle coordinates (statement V.1, step 4)

The angle parametrisation `cuspAngleParam v = ((exp v₀, exp v₁), lift v₂)` of the collar
`T² × [0, ∞)` from its model space `E₃ = ℝ³` is smooth on `{v₂ ≥ 0}`; at positive heights its
differential is explicit (`hasMFDerivAt_cuspAngleParam`), and the model cusp metric pulls back to
`cuspModelForm` (`metric_inner_mfderiv_cuspAngleParam`).

For a cusp embedding `e : CuspEmbedding W g K δ X` and `Ψ = e ∘ cuspAngleParam`, the order-0
comparison `(1 - δ) H ≤ e*g ≤ (1 + δ) H` on the cusp domain (`CuspMetricEquivalence.lean`) and the
determinant monotonicity in the Loewner order (`DensityComparison.lean`) give, at heights in
`(0, 100)`:
`(1 - δ)^{3/2} c e^{-s} ρ_T(u) ≤ paramDensity g Ψ v ≤ (1 + δ)^{3/2} c e^{-s} ρ_T(u)`
(`CuspEmbedding.paramDensity_cuspAngle_bounds`), with `c = cuspAngleConstant`,
`u = (v₀, v₁)`, `s = v₂`, `ρ_T = paramDensity g_T torusAngleParam`. The finite-order pull-back
`e*g` never appears as a metric.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry DifferentialGeometry.Integral.Measure GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

local notation "E₂" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

universe u

/-- The angle parametrisation of the collar from its model space `ℝ³`:
`v ↦ ((exp v₀, exp v₁), lift v₂)`. -/
def cuspAngleParam (v : E₃) : CuspHalfSpace :=
  (torusAngleParam (cuspCoordEquiv v).1, halfSpaceOneLift (v 2))

theorem cuspAngleParam_height (v : E₃) : (cuspAngleParam v).2.val 0 = max (v 2) 0 := rfl

theorem contMDiffOn_cuspAngleParam :
    ContMDiffOn 𝓘(ℝ, E₃) halfCollarModel ∞ cuspAngleParam {v | 0 ≤ v 2} := by
  have h1 : ContMDiff 𝓘(ℝ, E₃) torusModel ∞ (fun v : E₃ => torusAngleParam (cuspCoordEquiv v).1) :=
    contMDiff_torusAngleParam.comp
      ((ContinuousLinearMap.fst ℝ E₂ ℝ).comp cuspCoordEquiv.toContinuousLinearMap).contDiff.contMDiff
  have h2 : ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, ℝ) ∞ (fun v : E₃ => v 2) :=
    (by fun_prop : ContDiff ℝ ∞ (fun v : E₃ => v 2)).contMDiff
  exact h1.contMDiffOn.prodMk (contMDiffOn_halfSpaceOneLift.comp h2.contMDiffOn fun v hv => hv)

theorem hasMFDerivAt_halfSpaceOneLift_of_pos {t : ℝ} (ht : 0 < t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift t
      (ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)))) := by
  have h := hasMFDerivAt_halfPoint_affine 0 1 t (by simpa using ht)
  have heq : (fun r : ℝ => halfPoint (max (0 + r * 1) 0) (le_max_right _ _)) = halfSpaceOneLift := by
    funext r
    apply Subtype.ext
    ext i
    rw [Subsingleton.elim i 0]
    change max (0 + r * 1) 0 = max r 0
    simp
  rwa [heq] at h

/-- The derivative of the angle parametrisation at a point of positive height. -/
theorem hasMFDerivAt_cuspAngleParam {v : E₃} (hv : 0 < v 2) :
    HasMFDerivAt 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v
      (((mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam (cuspCoordEquiv v).1).comp
          ((ContinuousLinearMap.fst ℝ E₂ ℝ).comp cuspCoordEquiv.toContinuousLinearMap)).prod
        ((ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)))).comp
          (EuclideanSpace.proj (2 : Fin 3)))) := by
  have hL1 : HasMFDerivAt 𝓘(ℝ, E₃) 𝓘(ℝ, E₂) (fun v : E₃ => (cuspCoordEquiv v).1) v
      ((ContinuousLinearMap.fst ℝ E₂ ℝ).comp cuspCoordEquiv.toContinuousLinearMap) :=
    ((ContinuousLinearMap.fst ℝ E₂ ℝ).comp cuspCoordEquiv.toContinuousLinearMap).hasFDerivAt.hasMFDerivAt
  have hφ : HasMFDerivAt 𝓘(ℝ, E₂) torusModel torusAngleParam (cuspCoordEquiv v).1
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam (cuspCoordEquiv v).1) :=
    (contMDiff_torusAngleParam.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL2 : HasMFDerivAt 𝓘(ℝ, E₃) 𝓘(ℝ, ℝ) (EuclideanSpace.proj (2 : Fin 3) : E₃ → ℝ) v
      (EuclideanSpace.proj (2 : Fin 3)) :=
    HasFDerivAt.hasMFDerivAt (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (2 : Fin 3) : E₃ →L[ℝ] ℝ))
  exact (hφ.comp v hL1).prodMk ((hasMFDerivAt_halfSpaceOneLift_of_pos hv).comp v hL2)

theorem mfderiv_cuspAngleParam_fst {v : E₃} (hv : 0 < v 2) (x : E₃) :
    (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x).1 =
      mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam (cuspCoordEquiv v).1 (cuspCoordEquiv x).1 := by
  rw [(hasMFDerivAt_cuspAngleParam hv).mfderiv]
  rfl

theorem mfderiv_cuspAngleParam_snd {v : E₃} (hv : 0 < v 2) (x : E₃) :
    (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x).2 0 = x 2 := by
  rw [(hasMFDerivAt_cuspAngleParam hv).mfderiv]
  change (x 2 • WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))).ofLp 0 = x 2
  simp

/-- The model cusp metric pulled back by the angle parametrisation is `cuspModelForm`. -/
theorem metric_inner_mfderiv_cuspAngleParam (Hc : HyperbolicCusp) {v : E₃} (hv : 0 < v 2)
    (x y : E₃) :
    Hc.metric.inner (cuspAngleParam v) (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x)
        (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v y) =
      cuspModelForm Hc.torusMetric (cuspCoordEquiv v).1 (v 2) (cuspCoordEquiv x)
        (cuspCoordEquiv y) := by
  rw [Hc.metric_formula, cuspModelForm_apply, mfderiv_cuspAngleParam_fst hv,
    mfderiv_cuspAngleParam_fst hv, mfderiv_cuspAngleParam_snd hv, mfderiv_cuspAngleParam_snd hv,
    cuspAngleParam_height, max_eq_left hv.le, cuspCoordEquiv_apply_snd, cuspCoordEquiv_apply_snd]
  rw [add_comm]
  rfl

theorem finrank_euclideanSpace_three_div_two :
    (Module.finrank ℝ E₃ : ℝ) / 2 = 3 / 2 := by
  simp

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

theorem CuspEmbedding.mdifferentiableAt_toFun (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) : MDifferentiableAt halfCollarModel W.model e.toFun p :=
  (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)

theorem cuspAngleParam_mem_cuspDomain {v : E₃} (hv : v 2 < cuspDepth) :
    cuspAngleParam v ∈ cuspDomain := by
  change max (v 2) 0 < cuspDepth
  exact max_lt hv (by norm_num [cuspDepth])

/-- **Density comparison in angle coordinates (V.1, step 4).** At positive heights `< 100`, the
density of `g` along `Ψ = e ∘ cuspAngleParam` is `c e^{-s} ρ_T(u)` up to `(1 ± δ)^{3/2}`. -/
theorem CuspEmbedding.paramDensity_cuspAngle_bounds (e : CuspEmbedding W g K δ X) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) {v : E₃} (hv0 : 0 < v 2) (hv : v 2 < cuspDepth) :
    (1 - δ) ^ ((3 : ℝ) / 2) * (cuspAngleConstant * (Real.exp (-v 2) *
        paramDensity e.cusp.torusMetric torusAngleParam (cuspCoordEquiv v).1)) ≤
        paramDensity g (e.toFun ∘ cuspAngleParam) v ∧
      paramDensity g (e.toFun ∘ cuspAngleParam) v ≤ (1 + δ) ^ ((3 : ℝ) / 2) *
        (cuspAngleConstant * (Real.exp (-v 2) *
          paramDensity e.cusp.torusMetric torusAngleParam (cuspCoordEquiv v).1)) := by
  set gT := e.cusp.torusMetric
  set u := (cuspCoordEquiv v).1
  set B : LinearMap.BilinForm ℝ E₃ :=
    (cuspModelForm gT u (v 2)).compl₁₂ cuspCoordEquiv.toLinearMap cuspCoordEquiv.toLinearMap
    with hB
  have hBapp : ∀ x y : E₃, B x y = cuspModelForm gT u (v 2) (cuspCoordEquiv x) (cuspCoordEquiv y) :=
    fun x y => rfl
  have hsqrt : Real.sqrt (LinearMap.BilinForm.toMatrix
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₃) B).det =
      cuspAngleConstant * (Real.exp (-v 2) * paramDensity gT torusAngleParam u) :=
    sqrt_det_toMatrix_cuspModelForm_comp gT u (v 2)
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hBapp, hBapp, cuspModelForm_apply, cuspModelForm_apply, gT.symm]
    ring
  have hpos : ∀ x, 0 ≤ B x x := by
    intro x
    rw [hBapp, cuspModelForm_apply]
    have := metric_inner_self_nonneg gT (torusAngleParam u)
      (mfderiv 𝓘(ℝ, E₂) torusModel torusAngleParam u (cuspCoordEquiv x).1)
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le this) (mul_self_nonneg _)
  have hp := cuspAngleParam_mem_cuspDomain hv
  have hparam : MDifferentiableAt 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v :=
    (hasMFDerivAt_cuspAngleParam hv0).mdifferentiableAt
  have hchain : ∀ x : E₃, mfderiv 𝓘(ℝ, E₃) W.model (e.toFun ∘ cuspAngleParam) v x =
      mfderiv halfCollarModel W.model e.toFun (cuspAngleParam v)
        (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x) := by
    intro x
    rw [mfderiv_comp v (e.mdifferentiableAt_toFun hp) hparam]
    rfl
  have hH : ∀ x : E₃, e.cusp.metric.inner (cuspAngleParam v)
      (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x)
      (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x) = B x x :=
    fun x => metric_inner_mfderiv_cuspAngleParam e.cusp hv0 x x
  constructor
  · have h := rpow_mul_sqrt_det_le_paramDensity g (e.toFun ∘ cuspAngleParam) v hsymm hpos
      (sub_nonneg.mpr hδ.le) (fun x => by
        rw [hchain, ← hH]
        exact e.one_sub_mul_le_pullback_inner hp _)
    rwa [finrank_euclideanSpace_three_div_two, hsqrt] at h
  · have h := paramDensity_le_rpow_mul_sqrt_det g (e.toFun ∘ cuspAngleParam) v hsymm
      (by linarith : (0 : ℝ) ≤ 1 + δ) (fun x => by
        rw [hchain, ← hH]
        exact e.pullback_inner_le_one_add_mul hp _)
    rwa [finrank_euclideanSpace_three_div_two, hsqrt] at h

end DifferentialGeometry.Geometry.Collapse
