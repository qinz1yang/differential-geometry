import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.WeightedCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffContinuity
import DifferentialGeometry.Analysis.Integration.CompactExhaustionDerivative
import DifferentialGeometry.Analysis.ODE.Gronwall.DominatedSubsolutions

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

theorem forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds
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
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) η x) ≤ A * η x ^ 2)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ Ioo a b,
      Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ Ioo a b,
      IntervalIntegrable (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ t) volume a c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Ioo a b, ∀ c ∈ Ico s b,
      (∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ c x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ c) -
      (∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ s) ≤
        K * ∫ t in s..c, ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
          ∂riemannianMeasureFamily (I := I) (M := M) g₁ t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK, henergy⟩ := forward_uniqueness_weighted_cutoff_energy_uniform_bound_on_Ioo
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂ η hA hηgrad
  let S := fun t => forwardUniquenessSfield (I := I) g₁ g₂ t
  let d := fun t x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
  let e := fun t => ∫ x, d t x ∂riemannianMeasureFamily g₁ t
  let q := fun n t x => normSq0S (I := I) (g₁ t) x 1
    (differential1FormFun (I := I) (χ n) x)
  let u := fun n t => ∫ x, χ n x ^ 2 * d t x ∂riemannianMeasureFamily g₁ t
  let r := fun n t => 20 * ∫ x, q n t x * d t x ∂riemannianMeasureFamily g₁ t
  let ψ : ℕ → C^∞⟮I, M; ℝ⟯ := fun n => η * χ n
  have hψ (n : ℕ) : HasCompactSupport (ψ n : M → ℝ) := by
    apply HasCompactSupport.mono (hχsupport n)
    intro x hx hzero
    apply hx
    simp [ψ, hzero]
  have hu (n : ℕ) : u n = fun t => ∫ x, (ψ n x) ^ 2 *
      forwardUniqueDensity (I := I) g₁ g₂ t x ∂riemannianMeasureFamily g₁ t := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ψ, ContMDiffMap.coe_mul, Pi.mul_apply, d]
    ring
  have hd0 (t : ℝ) (x : M) : 0 ≤ d t x :=
    mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x)
  have hq0 (n : ℕ) (t : ℝ) (x : M) : 0 ≤ q n t x :=
    normSq0S_nonneg (I := I) (g₁ t) x 1 _
  have hqjoint (n : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q n p.1 p.2) (Ioo a b ×ˢ (univ : Set M)) := by
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
  have hrcont (n : ℕ) : ContinuousOn (r n) (Ioo a b) := by
    have hf : ContinuousOn (fun p : ℝ × M => q n p.1 p.2 * d p.1 p.2)
        (Ioo a b ×ˢ (univ : Set M)) :=
      (hqjoint n).continuousOn.mul
        (((η.contMDiff.continuous.comp continuous_snd).pow 2).continuousOn.mul
          (dens_jointContMDiffOn (I := I) g₁ g₂ hjoint₁ hjoint₂).continuousOn)
    have hc := continuousOn_integral_riemannianVolumeMeasure_of_compact_support
      (I := I) g₁ (fun α i j => (hjoint₁ α i j).continuousOn)
      (fun t x => q n t x * d t x) hf (hχsupport n) ?_
    · exact hc.const_mul 20
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
    mul_nonneg (sq_nonneg (χ n x)) (hd0 t x)
  have hr0 (n : ℕ) (t : ℝ) : 0 ≤ r n t :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => mul_nonneg (hq0 n t x) (hd0 t x))
  have hule (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      u n t ≤ e t := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hd0 t x))
      (hden t ht)
    filter_upwards [] with x
    have hsq : χ n x ^ 2 ≤ 1 := by nlinarith [abs_nonneg (χ n x), sq_abs (χ n x), hχrange n x]
    exact mul_le_of_le_one_left (hd0 t x) hsq
  have hrle (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      r n t ≤ (20 * |L|) * e t := by
    have hi : (∫ x, q n t x * d t x ∂riemannianMeasureFamily g₁ t) ≤
        ∫ x, |L| * d t x ∂riemannianMeasureFamily g₁ t := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg (hq0 n t x) (hd0 t x)) ((hden t ht).const_mul |L|)
      filter_upwards [] with x
      exact mul_le_mul_of_nonneg_right ((hχgrad n t ht x).trans (le_abs_self L))
        (hd0 t x)
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 20)).trans_eq (mul_assoc _ _ _).symm
  have hrto (t : ℝ) (ht : t ∈ Ioo a b) : Tendsto (fun n => r n t) atTop (𝓝 0) := by
    have h := tendsto_integral_normSq0S_differential_mul_of_compactExhaustion
      (I := I) Kex (g₁ t) χ hχone
      (fun n => Eventually.of_forall fun x => hχgrad n t ht x) (hden t ht)
    simpa only [mul_zero] using h.const_mul 20
  refine ⟨K, hK, fun s hs c hc => ?_⟩
  have hca : c ∈ Ioo a b := ⟨hs.1.trans_le hc.1, hc.2⟩
  have hein : IntervalIntegrable e volume s c := (hEint s hs).symm.trans (hEint c hca)
  have hsubinterval : Icc s c ⊆ Ioo a b := fun t ht => ⟨hs.1.trans_le ht.1, ht.2.trans_lt hc.2⟩
  have hcont (n : ℕ) : ContinuousOn (u n) (Icc s c) := by
    rw [hu n]
    exact (forward_uniqueness_cutoff_energy_continuousOn (I := I) g₁ g₂
      (ψ n) (ψ n).contMDiff.continuous (hψ n) hjoint₁ hjoint₂).mono hsubinterval
  apply sub_le_integral_of_dominated_subsolutions hc.1 (u := u)
    (u' := fun n => deriv (u n)) (r := r)
    (G := e)
    (H := fun t => (20 * |L|) * e t)
    hcont
  · intro n t ht
    rw [hu n]
    exact (forward_uniqueness_cutoff_energy_hasDerivAt_on_Ioo (I := I) g₁ g₂ (ψ n)
      (hψ n) hjoint₁ hjoint₂ hpde₁ hpde₂
      ⟨hs.1.trans ht.1, ht.2.trans hc.2⟩).differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro n t ht
    have he := henergy (χ n) (hχsupport n) t ⟨hs.1.trans ht.1, ht.2.trans hc.2⟩
    have hd : 0 ≤ ∫ x, (η x * χ n x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (normSq0S_nonneg (I := I) (g₁ t) x 5 _)
    have he' : deriv (u n) t ≤ K * u n t -
      (∫ x, (η x * χ n x) ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t) + r n t := by
      convert he using 1 <;> simp only [hu n, ψ, ContMDiffMap.coe_mul, Pi.mul_apply, r, q, d, S]
      congr 2
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    linarith only [he', hd]
  · intro n
    exact ((hrcont n).mono hsubinterval).integrableOn_Icc.aestronglyMeasurable
  · exact hein
  · exact hein.const_mul (20 * |L|)
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
