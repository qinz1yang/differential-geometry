import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.UniformCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Noncompact
import DifferentialGeometry.Analysis.ODE.Gronwall.EnergyHierarchy
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.CovariantSlotNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle _root_.Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.ODE
open scoped Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_unique_of_cutoff_energy_growth
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
    (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχcover : ∀ x : M, ∃ n, χ n x ≠ 0)
    {L B R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hχgrad : ∀ n, ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤
        L * χ (n + 1) x ^ 2)
    (hbound : ∀ n, ∀ t ∈ Ico a b,
      (∫ x, χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily g₁ t) ≤ B * R ^ n)
    (hinitial : g₁ a = g₂ a) : ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, _, henergy⟩ := forward_uniqueness_cutoff_energy_uniform_bound
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
  let S := fun t => forwardUniquenessSfield (I := I) g₁ g₂ t
  let w := fun t x => normSq0S (I := I) (g₁ t) x 4 (S t x)
  let q := fun n t x => normSq0S (I := I) (g₁ t) x 1
    (differential1FormFun (I := I) (χ n) x)
  let u := fun n t => ∫ x, χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂riemannianMeasureFamily g₁ t
  have hw0 (t : ℝ) (x : M) : 0 ≤ w t x := normSq0S_nonneg (I := I) (g₁ t) x 4 _
  have hq0 (n : ℕ) (t : ℝ) (x : M) : 0 ≤ q n t x :=
    normSq0S_nonneg (I := I) (g₁ t) x 1 _
  have hwle (t : ℝ) (x : M) : w t x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x :=
    rmDiffSq_le_dens (I := I) g₁ g₂ t x
  have hcont (n : ℕ) (t : ℝ) :
      Continuous (fun x => χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) :=
    ((χ n).contMDiff.continuous.pow 2).mul (dens_continuous (I := I) g₁ g₂ t)
  have hint (n : ℕ) (t : ℝ) :
      Integrable (fun x => χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily g₁ t) := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (g₁ t) (hcont n t)
    apply HasCompactSupport.mono (hχsupport n)
    intro x hx hzero
    apply hx
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_mul]
  have hu0 (n : ℕ) (t : ℝ) : 0 ≤ u n t := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg (χ n x)) (density_nonneg (I := I) g₁ g₂ t x)
  have hsub (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (u n) t ≤ K * u n t + (10 * L) * u (n + 1) t := by
    have he := henergy (χ n) (hχsupport n) t ht
    dsimp only at he
    simp_rw [normSq0S_covGradBundleEquiv_smulRight, unitScalarRSLiftSection_apply_unit] at he
    have hd : 0 ≤ ∫ x, χ n x ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (normSq0S_nonneg (I := I) (g₁ t) x 5 _)
    have herr : (∫ x, q n t x * w t x ∂riemannianMeasureFamily g₁ t) ≤ L * u (n + 1) t := by
      calc _ ≤ ∫ x, L * (χ (n + 1) x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
              ∂riemannianMeasureFamily g₁ t := by
            apply integral_mono_of_nonneg
              (Eventually.of_forall fun x => mul_nonneg (hq0 n t x) (hw0 t x))
              ((hint (n + 1) t).const_mul L)
            filter_upwards [] with x
            calc q n t x * w t x ≤ q n t x * forwardUniqueDensity (I := I) g₁ g₂ t x :=
                  mul_le_mul_of_nonneg_left (hwle t x) (hq0 n t x)
              _ ≤ (L * χ (n + 1) x ^ 2) * forwardUniqueDensity (I := I) g₁ g₂ t x :=
                  mul_le_mul_of_nonneg_right (hχgrad n t (Ioo_subset_Ico_self ht) x)
                    (density_nonneg (I := I) g₁ g₂ t x)
              _ = _ := mul_assoc _ _ _
        _ = _ := integral_const_mul _ _
    change deriv (u n) t ≤ K * u n t -
      (∫ x, χ n x ^ 2 * normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (S t) x) ∂riemannianMeasureFamily g₁ t) +
      10 * (∫ x, q n t x * w t x ∂riemannianMeasureFamily g₁ t) at he
    linarith only [he, hd, herr]
  intro c hc
  have hsubinterval : Icc a c ⊆ Ico a b := fun t ht => ⟨ht.1, ht.2.trans_lt hc.2⟩
  have hu : ∀ n, ∀ t ∈ Icc a c, u n t = 0 := by
    apply energy_hierarchy_eq_zero_of_exponential_bound (C := 10 * L) (K := K)
      (B := B) (R := R) (u' := fun n => deriv (u n)) (by positivity) hR
    · exact fun n t _ => hu0 n t
    · intro n
      exact (forward_uniqueness_cutoff_energy_continuousOn (I := I) g₁ g₂
        (χ n) (χ n).contMDiff.continuous (hχsupport n) hjoint₁ hjoint₂).mono hsubinterval
    · intro n t ht
      exact (forward_uniqueness_cutoff_energy_hasDerivAt (I := I) g₁ g₂ (χ n)
        (hχsupport n) hjoint₁ hjoint₂ hpde₁ hpde₂
        ⟨ht.1, ht.2.trans hc.2⟩).differentiableAt.hasDerivAt
    · exact fun n t ht => hsub n t ⟨ht.1, ht.2.trans hc.2⟩
    · exact fun n t ht => hbound n t (hsubinterval ht)
    · intro n
      simp only [u, density_eq_zero_of_eq (I := I) g₁ g₂ hinitial, mul_zero, integral_zero]
  have hμpos : (riemannianMeasureFamily (I := I) (M := M) g₁ c).IsOpenPosMeasure := by
    rw [riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g₁ c)
  have hzero : (fun x => forwardUniqueDensity (I := I) g₁ g₂ c x) = 0 := by
    funext x
    obtain ⟨n, hn⟩ := hχcover x
    have hae : (fun x => χ n x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ c x)
        =ᵐ[riemannianMeasureFamily g₁ c] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x => mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ c x))
        (hint n c)).mp (hu n c ⟨hc.1, le_rfl⟩)
    have heq := (Continuous.ae_eq_iff_eq (riemannianMeasureFamily g₁ c)
      (hcont n c) continuous_const).mp hae
    exact (mul_eq_zero.mp (congrFun heq x)).resolve_left (pow_ne_zero 2 hn)
  apply metric_eq_of_energy_zero_noncompact (I := I) g₁ g₂ (dens_continuous (I := I) g₁ g₂ c)
  · rw [hzero]
    exact integrable_zero _ _ _
  · change (∫ x, forwardUniqueDensity (I := I) g₁ g₂ c x ∂riemannianMeasureFamily g₁ c) = 0
    simp only [hzero, Pi.zero_apply, integral_zero]

end DifferentialGeometry.PDE.RicciFlow
