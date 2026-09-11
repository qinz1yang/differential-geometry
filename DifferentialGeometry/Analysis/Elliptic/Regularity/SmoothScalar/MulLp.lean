import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [CompactSpace M]

omit [Module.Finite ℝ E] [T2Space M] in
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

noncomputable def phiSupBound
    (_g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Classical.choose (exists_phiSupBound (I := I) (M := M) _g φ)

omit [Module.Finite ℝ E] [T2Space M] in
lemma phiSupBound_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    0 ≤ phiSupBound (I := I) (M := M) g φ :=
  (Classical.choose_spec
    (exists_phiSupBound (I := I) (M := M) g φ)).1

omit [Module.Finite ℝ E] [T2Space M] in
lemma abs_phi_le_phiSupBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    |((φ : M → ℝ) x)| ≤ phiSupBound (I := I) (M := M) g φ :=
  (Classical.choose_spec
    (exists_phiSupBound (I := I) (M := M) g φ)).2 x

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

noncomputable def smoothMulLpFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (memLp_phi_mul_lp (I := I) (M := M) g φ f).toLp _

lemma smoothMulLpFun_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (smoothMulLpFun (I := I) (M := M) g φ f :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) :=
  MemLp.coeFn_toLp _

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

theorem smoothMulLpFun_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x : M, |((φ : M → ℝ) x)| ≤ C) ∧
      ∀ (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)),
        ‖smoothMulLpFun (I := I) (M := M) g φ f‖ ≤ C * ‖f‖ :=
  ⟨phiSupBound (I := I) (M := M) g φ,
    phiSupBound_nonneg (I := I) (M := M) g φ,
    abs_phi_le_phiSupBound (I := I) (M := M) g φ,
    norm_smoothMulLpFun_le (I := I) (M := M) g φ⟩

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

theorem smoothMulLp_apply_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (smoothMulLp (I := I) (M := M) g φ f :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * (f : M → ℝ) x) := by
  rw [smoothMulLp_apply]
  exact smoothMulLpFun_coeFn (I := I) (M := M) g φ f

theorem smoothMulLp_injective
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g), φ x ≠ 0) :
    Function.Injective (smoothMulLp (I := I) (M := M) g φ) := by
  intro u v huv
  apply Lp.ext
  filter_upwards [hφ, smoothMulLp_apply_coeFn g φ u, smoothMulLp_apply_coeFn g φ v]
    with x hx hux hvx
  have heq := congrArg
    (fun f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => f x) huv
  rw [hux, hvx] at heq
  exact mul_left_cancel₀ hx heq

theorem norm_smoothMulLp_le_of_bound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ x : M, |φ x| ≤ C) :
    ‖smoothMulLp (I := I) (M := M) g φ‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [smoothMulLp_apply_coeFn (I := I) (M := M) g φ f] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _)

private theorem dist_smoothMulLp_le_continuousMap_dist
    (g : SmoothRiemannianMetric I M) (φ ψ : C^∞⟮I, M; ℝ⟯) :
    dist (smoothMulLp (I := I) (M := M) g φ)
        (smoothMulLp (I := I) (M := M) g ψ) ≤
      dist (⟨φ, φ.contMDiff.continuous⟩ : C(M, ℝ))
        (⟨ψ, ψ.contMDiff.continuous⟩ : C(M, ℝ)) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [sub_apply]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hsub := Lp.coeFn_sub
    (smoothMulLp (I := I) (M := M) g φ f)
    (smoothMulLp (I := I) (M := M) g ψ f)
  have hφ := smoothMulLp_apply_coeFn (I := I) (M := M) g φ f
  have hψ := smoothMulLp_apply_coeFn (I := I) (M := M) g ψ f
  filter_upwards [hsub, hφ, hψ] with x hsubx hφx hψx
  rw [hsubx, Pi.sub_apply, hφx, hψx]
  calc
    ‖φ x * f x - ψ x * f x‖ = ‖φ x - ψ x‖ * ‖f x‖ := by
      rw [← sub_mul, norm_mul]
    _ ≤ ‖(⟨φ, φ.contMDiff.continuous⟩ : C(M, ℝ)) -
          (⟨ψ, ψ.contMDiff.continuous⟩ : C(M, ℝ))‖ * ‖f x‖ := by
      gcongr
      exact ContinuousMap.norm_coe_le_norm
        ((⟨φ, φ.contMDiff.continuous⟩ : C(M, ℝ)) -
          (⟨ψ, ψ.contMDiff.continuous⟩ : C(M, ℝ))) x

theorem continuousOn_smoothMulLp_apply
    (g : SmoothRiemannianMetric I M) {K : Set ℝ}
    (φ : ℝ → C^∞⟮I, M; ℝ⟯)
    (hφ : ContinuousOn (fun p : ℝ × M => φ p.1 p.2)
      (K ×ˢ (Set.univ : Set M)))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContinuousOn f K) :
    ContinuousOn (fun t => smoothMulLp (I := I) (M := M) g (φ t) (f t)) K := by
  let Φ : ℝ → C(M, ℝ) := fun t => ⟨φ t, (φ t).contMDiff.continuous⟩
  have hΦ : ContinuousOn Φ K := by
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    change ContinuousOn (fun p : ℝ × M => φ p.1 p.2)
      (K ×ˢ (Set.univ : Set M))
    exact hφ
  have hmul : ContinuousOn
      (fun t => smoothMulLp (I := I) (M := M) g (φ t)) K := by
    rw [Metric.continuousOn_iff]
    intro t ht ε hε
    obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousOn_iff.mp hΦ) t ht ε hε
    refine ⟨δ, hδ, fun s hs hst => ?_⟩
    exact (dist_smoothMulLp_le_continuousMap_dist
      (I := I) (M := M) g (φ s) (φ t)).trans_lt (hclose s hs hst)
  exact hmul.clm_apply hf

theorem smoothMulLp_mul
    (g : SmoothRiemannianMetric I M) (φ ψ : C^∞⟮I, M; ℝ⟯) :
    (smoothMulLp (I := I) (M := M) g φ).comp
        (smoothMulLp (I := I) (M := M) g ψ) =
      smoothMulLp (I := I) (M := M) g (φ * ψ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hφ := smoothMulLp_apply_coeFn (I := I) (M := M) g φ
    (smoothMulLp (I := I) (M := M) g ψ f)
  have hψ := smoothMulLp_apply_coeFn (I := I) (M := M) g ψ f
  have hmul := smoothMulLp_apply_coeFn (I := I) (M := M) g (φ * ψ) f
  filter_upwards [hφ, hψ, hmul] with x hφx hψx hmulx
  rw [ContinuousLinearMap.comp_apply, hφx, hψx, hmulx]
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
  ring

@[simp] theorem smoothMulLp_one
    (g : SmoothRiemannianMetric I M) :
    smoothMulLp (I := I) (M := M) g 1 =
      ContinuousLinearMap.id ℝ
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hone := smoothMulLp_apply_coeFn (I := I) (M := M) g 1 f
  filter_upwards [hone] with x honex
  rw [honex, ContinuousLinearMap.id_apply]
  simp only [ContMDiffMap.coe_one, Pi.one_apply, one_mul]

end Laplacian
end Analysis
end DifferentialGeometry

end
