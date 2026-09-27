import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.UniformCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffContinuity
import DifferentialGeometry.Analysis.Integration.CompactExhaustionDerivative
import DifferentialGeometry.Analysis.ODE.Gronwall.DominatedSubsolutions
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.CovariantSlotNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.ODE
open scoped Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_energy_sub_le_integral_of_uniform_bounds
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ico a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ Ico a b,
      Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ Ico a b,
      IntervalIntegrable (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) volume a c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c ∈ Ico a b,
      forwardUniqueEnergy (I := I) (M := M) g₁ g₂ c -
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ a ≤
        K * ∫ t in a..c, forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK, henergy⟩ := forward_uniqueness_cutoff_energy_uniform_bound
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
  let S := fun t => forwardUniquenessSfield (I := I) g₁ g₂ t
  let w := fun t x => normSq0S (I := I) (g₁ t) x 4 (S t x)
  let q := fun n t x => normSq0S (I := I) (g₁ t) x 1
    (differential1FormFun (I := I) (χ n) x)
  let u := fun n t => ∫ x, χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂riemannianMeasureFamily g₁ t
  let r := fun n t => 10 * ∫ x, q n t x * w t x ∂riemannianMeasureFamily g₁ t
  have hw0 (t : ℝ) (x : M) : 0 ≤ w t x := normSq0S_nonneg (I := I) (g₁ t) x 4 _
  have hq0 (n : ℕ) (t : ℝ) (x : M) : 0 ≤ q n t x :=
    normSq0S_nonneg (I := I) (g₁ t) x 1 _
  have hwle (t : ℝ) (x : M) : w t x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x :=
    rmDiffSq_le_dens (I := I) g₁ g₂ t x
  have hwint (t : ℝ) (ht : t ∈ Ico a b) :
      Integrable (w t) (riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
    apply (hden t ht).mono' (normSq0S_cont (I := I) (g₁ t) (S t)).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 t x)]
    exact hwle t x
  have hqjoint (n : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q n p.1 p.2) (Ico a b ×ˢ (univ : Set M)) := by
    apply normSq0S_jointContMDiffOn (I := I) g₁
      (fun _ x => differential1FormFun (I := I) (χ n) x) hjoint₁
    intro α slots t ht
    have hf := tensor0SField_eval_cmdAt_slots (I := I)
      (duSec (I := I) (χ n) (χ n).contMDiff)
      (fun i y => chartBasisVecFiber (I := I) α (slots i) y)
      (fun i => (chartBasisVec_contMDiffOn (I := I) α (slots i)).contMDiffAt
        ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) α)))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2) (t, α) :=
      contMDiffAt_snd
    exact (hf.comp (t, α) hsnd).contMDiffWithinAt
  have hrcont (n : ℕ) : ContinuousOn (r n) (Ico a b) := by
    have hf : ContinuousOn (fun p : ℝ × M => q n p.1 p.2 * w p.1 p.2)
        (Ico a b ×ˢ (univ : Set M)) :=
      (hqjoint n).continuousOn.mul
        (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hjoint₁ hjoint₂).continuousOn
    have hc := continuousOn_integral_riemannianVolumeMeasure_of_compact_support
      (I := I) g₁ (fun α i j => (hjoint₁ α i j).continuousOn)
      (fun t x => q n t x * w t x) hf (hχsupport n) ?_
    · exact hc.const_mul 10
    · intro t ht x hx
      have heq : (χ n : M → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      have hd : mvfderiv (I := I) (χ n : M → ℝ) x = 0 := by
        ext v
        rw [mvfderiv_real_eq_mfderiv (I := I),
          heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)), mfderiv_const]
        rfl
      have hdf : differential1FormFun (I := I) (χ n) x = 0 := by
        ext v
        simp only [differential1FormFun, hd]
        rfl
      have hnzero := (normSq0S_eq_zero_iff (I := I) (g₁ t) x 1 0).2 rfl
      simp only [q, hdf, hnzero, zero_mul]
  have hu0 (n : ℕ) (t : ℝ) : 0 ≤ u n t := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg (χ n x)) (density_nonneg (I := I) g₁ g₂ t x)
  have hr0 (n : ℕ) (t : ℝ) : 0 ≤ r n t :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => mul_nonneg (hq0 n t x) (hw0 t x))
  have hule (n : ℕ) (t : ℝ) (ht : t ∈ Ico a b) :
      u n t ≤ forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x))
      (hden t ht)
    filter_upwards [] with x
    have hsq : χ n x ^ 2 ≤ 1 := by nlinarith [abs_nonneg (χ n x), sq_abs (χ n x), hχrange n x]
    exact mul_le_of_le_one_left (density_nonneg (I := I) g₁ g₂ t x) hsq
  have hrle (n : ℕ) (t : ℝ) (ht : t ∈ Ico a b) :
      r n t ≤ (10 * |L|) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t := by
    have hi : (∫ x, q n t x * w t x ∂riemannianMeasureFamily g₁ t) ≤
        ∫ x, |L| * forwardUniqueDensity (I := I) g₁ g₂ t x ∂riemannianMeasureFamily g₁ t := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg (hq0 n t x) (hw0 t x)) ((hden t ht).const_mul |L|)
      filter_upwards [] with x
      exact (mul_le_mul_of_nonneg_left (hwle t x) (hq0 n t x)).trans
        (mul_le_mul_of_nonneg_right ((hχgrad n t ht x).trans (le_abs_self L))
          (density_nonneg (I := I) g₁ g₂ t x))
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 10)).trans_eq (mul_assoc _ _ _).symm
  have hrto (t : ℝ) (ht : t ∈ Ico a b) : Tendsto (fun n => r n t) atTop (𝓝 0) := by
    have h := tendsto_integral_normSq0S_differential_mul_of_compactExhaustion
      (I := I) Kex (g₁ t) χ hχone
      (fun n => Eventually.of_forall fun x => hχgrad n t ht x) (hwint t ht)
    simpa only [mul_zero] using h.const_mul 10
  refine ⟨K, hK, fun c hc => ?_⟩
  have hsubinterval : Icc a c ⊆ Ico a b := fun t ht => ⟨ht.1, ht.2.trans_lt hc.2⟩
  have hcont (n : ℕ) : ContinuousOn (u n) (Icc a c) :=
    (forward_uniqueness_cutoff_energy_continuousOn (I := I) g₁ g₂
      (χ n) (χ n).contMDiff.continuous (hχsupport n) hjoint₁ hjoint₂).mono hsubinterval
  apply sub_le_integral_of_dominated_subsolutions hc.1 (u := u)
    (u' := fun n => deriv (u n)) (r := r)
    (G := forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
    (H := fun t => (10 * |L|) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t)
    hcont
  · intro n t ht
    exact (forward_uniqueness_cutoff_energy_hasDerivAt (I := I) g₁ g₂ (χ n)
      (hχsupport n) hjoint₁ hjoint₂ hpde₁ hpde₂
      ⟨ht.1, ht.2.trans hc.2⟩).differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro n t ht
    have he := henergy (χ n) (hχsupport n) t ⟨ht.1, ht.2.trans hc.2⟩
    dsimp only at he
    simp_rw [normSq0S_covGradBundleEquiv_smulRight, unitScalarRSLiftSection_apply_unit] at he
    have hd : 0 ≤ ∫ x, χ n x ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (normSq0S_nonneg (I := I) (g₁ t) x 5 _)
    change deriv (u n) t ≤ K * u n t -
      (∫ x, χ n x ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t) + r n t at he
    linarith only [he, hd]
  · intro n
    exact ((hrcont n).mono hsubinterval).integrableOn_Icc.aestronglyMeasurable
  · exact hEint c hc
  · exact (hEint c hc).const_mul (10 * |L|)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 n t)]
    exact hule n t (hsubinterval ht)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hr0 n t)]
    exact hrle n t (hsubinterval ht)
  · intro t ht
    exact tendsto_integral_sq_mul_of_compactExhaustion Kex
      (fun n => (χ n).contMDiff.continuous.aestronglyMeasurable)
      (fun n => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hχrange n x)
      hχone (hden t (hsubinterval ht))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hrto t (hsubinterval ht)

end DifferentialGeometry.PDE.RicciFlow
