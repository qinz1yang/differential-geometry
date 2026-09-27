import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.UniformCutoff
import DifferentialGeometry.Geometry.Operator.Gradient.ProductEstimate
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.CovariantSlotNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_weighted_cutoff_energy_uniform_bound_on_Ioo
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (η : C^∞⟮I, M; ℝ⟯) {A : ℝ} (hA : 0 ≤ A)
    (hηgrad : ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) η x) ≤ A * η x ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (χ : C^∞⟮I, M; ℝ⟯), HasCompactSupport (χ : M → ℝ) →
      ∀ t ∈ Ioo a b,
      deriv (fun s => ∫ x, (η x * χ x) ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily g₁ s) t ≤
        K * (∫ x, (η x * χ x) ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
          ∂riemannianMeasureFamily g₁ t) -
        (∫ x, (η x * χ x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x)
          ∂riemannianMeasureFamily g₁ t) +
        20 * (∫ x, η x ^ 2 * normSq0S (I := I) (g₁ t) x 1
          (differential1FormFun (I := I) χ x) * forwardUniqueDensity (I := I) g₁ g₂ t x
          ∂riemannianMeasureFamily g₁ t) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK, henergy⟩ := forward_uniqueness_cutoff_energy_uniform_bound_on_Ioo
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
  refine ⟨K + 20 * A, by positivity, fun χ hχ t ht => ?_⟩
  let ψ : C^∞⟮I, M; ℝ⟯ := η * χ
  have hψ : HasCompactSupport (ψ : M → ℝ) := by
    apply HasCompactSupport.mono hχ
    intro x hx hzero
    apply hx
    simp [ψ, hzero]
  have he := henergy ψ hψ t ht
  dsimp only at he
  simp_rw [normSq0S_covGradBundleEquiv_smulRight, unitScalarRSLiftSection_apply_unit] at he
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
  let d := forwardUniqueDensity (I := I) g₁ g₂ t
  let w := fun x => normSq0S (I := I) (g₁ t) x 4
    (forwardUniquenessSfield (I := I) g₁ g₂ t x)
  let q := fun x => normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) χ x)
  have hq0 (x : M) : 0 ≤ q x := normSq0S_nonneg (I := I) (g₁ t) x 1 _
  have hw0 (x : M) : 0 ≤ w x := normSq0S_nonneg (I := I) (g₁ t) x 4 _
  have hwle (x : M) : w x ≤ d x := rmDiffSq_le_dens (I := I) g₁ g₂ t x
  have hbound (x : M) :
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) ψ x) * w x ≤
        2 * A * ((η x * χ x) ^ 2 * d x) + 2 * (η x ^ 2 * q x * d x) := by
    have hp := normSq0S_differential1FormFun_mul_le (I := I) (g₁ t)
      (η.contMDiff.mdifferentiable (by simp) x) (χ.contMDiff.mdifferentiable (by simp) x)
    have hgrad := hηgrad t ht x
    have hp' : normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) ψ x) ≤
        2 * η x ^ 2 * q x + 2 * χ x ^ 2 * (A * η x ^ 2) :=
      hp.trans (add_le_add_right (mul_le_mul_of_nonneg_left hgrad
        (show 0 ≤ 2 * χ x ^ 2 by positivity)) _)
    have hb := mul_le_mul_of_nonneg_right hp' (hw0 x)
    have hw := mul_le_mul_of_nonneg_left (hwle x)
      (show 0 ≤ 2 * η x ^ 2 * q x + 2 * χ x ^ 2 * (A * η x ^ 2) from
        add_nonneg (mul_nonneg (by positivity) (hq0 x)) (by positivity))
    exact (hb.trans hw).trans_eq (by ring)
  have hdc : Continuous d := dens_continuous (I := I) g₁ g₂ t
  have hqc : Continuous q := normSq0S_cont (I := I) (g₁ t) (duSec (I := I) χ χ.contMDiff)
  have hEi : Integrable (fun x => (η x * χ x) ^ 2 * d x) μ := by
    apply Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (g₁ t)
      ((η.contMDiff.continuous.mul χ.contMDiff.continuous).pow 2 |>.mul hdc)
    apply HasCompactSupport.mono hχ
    intro x hx hzero
    apply hx
    simp [hzero]
  have hqi : Integrable (fun x => η x ^ 2 * q x * d x) μ := by
    apply Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (g₁ t)
      (((η.contMDiff.continuous.pow 2).mul hqc).mul hdc)
    apply hχ.mono' ?_
    intro x hx
    by_contra hn
    have heq : (χ : M → ℝ) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hn] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hd : mvfderiv (I := I) (χ : M → ℝ) x = 0 := by
      ext v
      rw [mvfderiv_real_eq_mfderiv (I := I),
        heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)), mfderiv_const]
      rfl
    have hdf : differential1FormFun (I := I) χ x = 0 := by
      ext v
      simp only [differential1FormFun, hd]
      rfl
    have hnzero := (normSq0S_eq_zero_iff (I := I) (g₁ t) x 1 0).2 rfl
    apply hx
    change η x ^ 2 * q x * d x = 0
    simp only [q, hdf, hnzero, mul_zero, zero_mul]
  have hi : (∫ x, normSq0S (I := I) (g₁ t) x 1
      (differential1FormFun (I := I) ψ x) * w x ∂μ) ≤
      2 * A * (∫ x, (η x * χ x) ^ 2 * d x ∂μ) +
        2 * (∫ x, η x ^ 2 * q x * d x ∂μ) := by
    have hm := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => mul_nonneg
        (normSq0S_nonneg (I := I) (g₁ t) x 1 _) (hw0 x))
      ((hEi.const_mul (2 * A)).add (hqi.const_mul 2))
      (Filter.Eventually.of_forall hbound)
    change (∫ x, normSq0S (I := I) (g₁ t) x 1
      (differential1FormFun (I := I) ψ x) * w x ∂μ) ≤
      ∫ x, 2 * A * ((η x * χ x) ^ 2 * d x) + 2 * (η x ^ 2 * q x * d x) ∂μ at hm
    rw [integral_add (hEi.const_mul (2 * A)) (hqi.const_mul 2), integral_const_mul,
      integral_const_mul] at hm
    exact hm
  change deriv (fun s => ∫ x, (η x * χ x) ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
    ∂riemannianMeasureFamily g₁ s) t ≤
    K * (∫ x, (η x * χ x) ^ 2 * d x ∂μ) -
    (∫ x, (η x * χ x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) ∂μ) +
    10 * (∫ x, normSq0S (I := I) (g₁ t) x 1
      (differential1FormFun (I := I) ψ x) * w x ∂μ) at he
  change deriv (fun s => ∫ x, (η x * χ x) ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
    ∂riemannianMeasureFamily g₁ s) t ≤
    (K + 20 * A) * (∫ x, (η x * χ x) ^ 2 * d x ∂μ) -
    (∫ x, (η x * χ x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (forwardUniquenessSfield (I := I) g₁ g₂ t) x) ∂μ) +
    20 * (∫ x, η x ^ 2 * q x * d x ∂μ)
  linarith only [he, hi]

end DifferentialGeometry.PDE.RicciFlow
