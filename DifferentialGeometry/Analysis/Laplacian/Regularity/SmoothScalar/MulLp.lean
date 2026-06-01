import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.L2Inclusion

/-!
# Multiplication of `Lp ℝ 2 μ_g` by a smooth scalar function

For a closed Riemannian manifold `(M, g)` and a fixed smooth real-valued
function `φ : C^∞⟮I, M; ℝ⟯`, the pointwise product `f ↦ φ · f` extends to a
continuous linear map

```
smoothMulLp g φ : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g
```

with operator norm bounded by the supremum `‖φ‖_∞ := sup_{x ∈ M} |φ x|`,
which is finite because `M` is compact and `φ` is continuous.

The construction proceeds via the standard pattern:

1. Pick a non-negative real bound `C` with `|φ x| ≤ C` for every `x ∈ M`
   (continuity of `φ` on a compact `M`, here `gradSupBound`-style).
2. For every `f ∈ Lp ℝ 2 μ_g`, the pointwise product `x ↦ φ x · f x` is in
   `Lp ℝ 2 μ_g` because `‖φ · f‖_{L²} ≤ C · ‖f‖_{L²}` follows from
   `MemLp.of_le_mul`.
3. Linearity in `f` is pointwise distributivity.
4. The operator-norm bound is exactly `C`, packaged via
   `LinearMap.mkContinuous`.

## Main definitions

* `smoothMulLp g φ` — the continuous linear multiplication operator
  `Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g`.

## Main theorems

* `smoothMulLp_norm_le` — there exists a non-negative `C` bounding `|φ|`
  pointwise on `M` and `‖smoothMulLp g φ‖ ≤ C`.
* `smoothMulLp_apply_coeFn` — the underlying function of
  `smoothMulLp g φ f` agrees a.e. with the pointwise product
  `x ↦ φ x · f x`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- Existence of a non-negative real bound for `|φ x|` on `M`. -/
private lemma exists_phiSupBound
    (_g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |((φ : M → ℝ) x)| ≤ C := by
  classical
  have hcont : Continuous (fun x : M => |((φ : M → ℝ) x)|) :=
    continuous_abs.comp φ.contMDiff.continuous
  have hCpt := (isCompact_univ (X := M)).image hcont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  have hxC : |((φ : M → ℝ) x)| ≤ C₀ := hC₀ ⟨x, Set.mem_univ _, rfl⟩
  exact hxC.trans (le_max_left _ _)

/-- A non-negative real number bounding `|φ x|` for every `x : M`. Defined
as `Classical.choose` of the existence proof, ensuring non-negativity
even in degenerate cases. -/
noncomputable def phiSupBound
    (_g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Classical.choose (exists_phiSupBound (I := I) (M := M) _g φ)

lemma phiSupBound_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    0 ≤ phiSupBound (I := I) (M := M) g φ :=
  (Classical.choose_spec
    (exists_phiSupBound (I := I) (M := M) g φ)).1

/-- Pointwise: `|φ x| ≤ phiSupBound g φ`. -/
lemma abs_phi_le_phiSupBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    |((φ : M → ℝ) x)| ≤ phiSupBound (I := I) (M := M) g φ :=
  (Classical.choose_spec
    (exists_phiSupBound (I := I) (M := M) g φ)).2 x

/-- The pointwise product `x ↦ φ x · f x` is `MemLp 2`. -/
lemma memLp_phi_mul_lp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemLp (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hf_memLp : MemLp (f : M → ℝ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := Lp.memLp f
  set C : ℝ := phiSupBound (I := I) (M := M) g φ with hC_def
  have hφ_cont : Continuous (φ : M → ℝ) := φ.contMDiff.continuous
  have hφ_aesm : AEStronglyMeasurable (φ : M → ℝ)
      (riemannianVolumeMeasure (I := I) (M := M) g) := hφ_cont.aestronglyMeasurable
  have hprod_aesm : AEStronglyMeasurable
      (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hφ_aesm.mul hf_memLp.1
  have hpt : ∀ x : M, ‖(φ : M → ℝ) x * (f : M → ℝ) x‖ ≤
      C * ‖(f : M → ℝ) x‖ := by
    intro x
    have h1 : ‖(φ : M → ℝ) x * (f : M → ℝ) x‖ =
        |((φ : M → ℝ) x)| * ‖(f : M → ℝ) x‖ := by
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    rw [h1]
    exact mul_le_mul_of_nonneg_right
      (abs_phi_le_phiSupBound (I := I) (M := M) g φ x)
      (norm_nonneg _)
  exact hf_memLp.of_le_mul hprod_aesm (Filter.Eventually.of_forall hpt)

/-- The pointwise product `x ↦ φ x · f x` packaged as an element of
`Lp ℝ 2 μ_g`. -/
noncomputable def smoothMulLpFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (memLp_phi_mul_lp (I := I) (M := M) g φ f).toLp _

/-- A.e. unfolding identity for the multiplication on `Lp`. -/
lemma smoothMulLpFun_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (smoothMulLpFun (I := I) (M := M) g φ f :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) :=
  MemLp.coeFn_toLp _

/-- Additivity of `smoothMulLpFun` in the second argument. -/
theorem smoothMulLpFun_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f₁ f₂ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    smoothMulLpFun (I := I) (M := M) g φ (f₁ + f₂) =
      smoothMulLpFun (I := I) (M := M) g φ f₁ +
        smoothMulLpFun (I := I) (M := M) g φ f₂ := by
  apply MeasureTheory.Lp.ext
  have h_lhs := smoothMulLpFun_coeFn (I := I) (M := M) g φ (f₁ + f₂)
  have h_f₁ := smoothMulLpFun_coeFn (I := I) (M := M) g φ f₁
  have h_f₂ := smoothMulLpFun_coeFn (I := I) (M := M) g φ f₂
  have h_sum_coe := MeasureTheory.Lp.coeFn_add
    (smoothMulLpFun (I := I) (M := M) g φ f₁)
    (smoothMulLpFun (I := I) (M := M) g φ f₂)
  have h_arg_sum := MeasureTheory.Lp.coeFn_add f₁ f₂
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_sum_coe, h_f₁, h_f₂, h_arg_sum]
    with x hx_sum hx_f₁ hx_f₂ hx_arg
  rw [hx_sum, Pi.add_apply, hx_f₁, hx_f₂]
  rw [hx_arg, Pi.add_apply, mul_add]

/-- Homogeneity of `smoothMulLpFun` in the second argument. -/
theorem smoothMulLpFun_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    smoothMulLpFun (I := I) (M := M) g φ (c • f) =
      c • smoothMulLpFun (I := I) (M := M) g φ f := by
  apply MeasureTheory.Lp.ext
  have h_lhs := smoothMulLpFun_coeFn (I := I) (M := M) g φ (c • f)
  have h_f := smoothMulLpFun_coeFn (I := I) (M := M) g φ f
  have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
    (smoothMulLpFun (I := I) (M := M) g φ f)
  have h_arg_smul := MeasureTheory.Lp.coeFn_smul c f
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_smul_coe, h_f, h_arg_smul]
    with x hx_smul hx_f hx_arg
  rw [hx_smul, Pi.smul_apply, hx_f]
  rw [hx_arg, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- The multiplication map `f ↦ φ · f` packaged as a linear map. -/
noncomputable def smoothMulLpLin
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun f := smoothMulLpFun (I := I) (M := M) g φ f
  map_add' f₁ f₂ := smoothMulLpFun_add (I := I) (M := M) g φ f₁ f₂
  map_smul' c f := smoothMulLpFun_smul (I := I) (M := M) g φ c f

@[simp] lemma smoothMulLpLin_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    smoothMulLpLin (I := I) (M := M) g φ f =
      smoothMulLpFun (I := I) (M := M) g φ f := rfl

/-- `eLpNorm` bound: `eLpNorm (φ · f) 2 ≤ ofReal (phiSupBound g φ) · eLpNorm f 2`. -/
private lemma eLpNorm_smoothMulLp_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    eLpNorm (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (phiSupBound (I := I) (M := M) g φ) *
        eLpNorm (f : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := phiSupBound (I := I) (M := M) g φ)
    (Filter.Eventually.of_forall ?_) 2
  intro x
  have h1 : ‖(φ : M → ℝ) x * (f : M → ℝ) x‖ =
      |((φ : M → ℝ) x)| * ‖(f : M → ℝ) x‖ := by
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  rw [h1]
  exact mul_le_mul_of_nonneg_right
    (abs_phi_le_phiSupBound (I := I) (M := M) g φ x)
    (norm_nonneg _)

/-- Norm bound: `‖smoothMulLpFun g φ f‖ ≤ phiSupBound g φ · ‖f‖`. -/
theorem norm_smoothMulLpFun_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖smoothMulLpFun (I := I) (M := M) g φ f‖ ≤
      phiSupBound (I := I) (M := M) g φ * ‖f‖ := by
  have h_norm_eq : ‖smoothMulLpFun (I := I) (M := M) g φ f‖ =
      (eLpNorm (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [show smoothMulLpFun (I := I) (M := M) g φ f =
        (memLp_phi_mul_lp (I := I) (M := M) g φ f).toLp _ from rfl]
    exact Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_f_norm : ‖f‖ = (eLpNorm (f : M → ℝ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
    Lp.norm_def f
  rw [h_f_norm]
  have h_le := eLpNorm_smoothMulLp_le (I := I) (M := M) g φ f
  have h_f_lt : eLpNorm (f : M → ℝ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
    (Lp.memLp f).2
  have h_C_nn : 0 ≤ phiSupBound (I := I) (M := M) g φ :=
    phiSupBound_nonneg (I := I) (M := M) g φ
  have h_finite_ofReal : (ENNReal.ofReal (phiSupBound (I := I) (M := M) g φ)).toReal =
      phiSupBound (I := I) (M := M) g φ :=
    ENNReal.toReal_ofReal h_C_nn
  have h_prod_lt :
      ENNReal.ofReal (phiSupBound (I := I) (M := M) g φ) *
        eLpNorm (f : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_f_lt
  have h_lhs_lt :
      eLpNorm (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
    lt_of_le_of_lt h_le h_prod_lt
  have h_le_real := ENNReal.toReal_mono h_prod_lt.ne h_le
  rw [ENNReal.toReal_mul, h_finite_ofReal] at h_le_real
  exact h_le_real

/-- There exists a non-negative `C`, bounding `|φ|` pointwise, with
`‖smoothMulLpFun g φ f‖ ≤ C · ‖f‖` for every `f`. -/
theorem smoothMulLpFun_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x : M, |((φ : M → ℝ) x)| ≤ C) ∧
      ∀ (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)),
        ‖smoothMulLpFun (I := I) (M := M) g φ f‖ ≤ C * ‖f‖ :=
  ⟨phiSupBound (I := I) (M := M) g φ,
    phiSupBound_nonneg (I := I) (M := M) g φ,
    abs_phi_le_phiSupBound (I := I) (M := M) g φ,
    norm_smoothMulLpFun_le (I := I) (M := M) g φ⟩

/-- The multiplication operator `f ↦ φ · f`, packaged as a continuous
linear map `Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g`. The operator norm is at most
`phiSupBound g φ`, the supremum of `|φ|` on the compact manifold `M`. -/
noncomputable def smoothMulLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothMulLpLin (I := I) (M := M) g φ).mkContinuous
    (phiSupBound (I := I) (M := M) g φ)
    (fun f => norm_smoothMulLpFun_le (I := I) (M := M) g φ f)

@[simp] lemma smoothMulLp_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    smoothMulLp (I := I) (M := M) g φ f =
      smoothMulLpFun (I := I) (M := M) g φ f := rfl

/-- Existence of a non-negative `C` with `|φ x| ≤ C` for every `x ∈ M`,
and `‖smoothMulLp g φ‖ ≤ C`. -/
theorem smoothMulLp_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x : M, |((φ : M → ℝ) x)| ≤ C) ∧
      ‖smoothMulLp (I := I) (M := M) g φ‖ ≤ C := by
  refine ⟨phiSupBound (I := I) (M := M) g φ,
    phiSupBound_nonneg (I := I) (M := M) g φ,
    abs_phi_le_phiSupBound (I := I) (M := M) g φ, ?_⟩
  exact LinearMap.mkContinuous_norm_le (smoothMulLpLin (I := I) (M := M) g φ)
    (phiSupBound_nonneg (I := I) (M := M) g φ)
    (fun f => norm_smoothMulLpFun_le (I := I) (M := M) g φ f)

/-- A.e. unfolding identity: the coefficient function of
`smoothMulLp g φ f` equals the pointwise product `φ · f`. -/
theorem smoothMulLp_apply_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (smoothMulLp (I := I) (M := M) g φ f :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) := by
  rw [smoothMulLp_apply]
  exact smoothMulLpFun_coeFn (I := I) (M := M) g φ f

end Laplacian
end Analysis
end DifferentialGeometry

end
