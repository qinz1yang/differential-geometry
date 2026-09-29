import DifferentialGeometry.Geometry.Metric.ScalarCurveComparison
import DifferentialGeometry.Geometry.Metric.LipschitzCurves
import DifferentialGeometry.Topology.EMetricSpace.FiniteDistanceLipschitz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.MetricSpace.HausdorffDistance
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem norm_sub_sq_le_length_mul_integral_deriv_sq
    {ν : ℝ → ℝ} {C : ℝ≥0} (hν : LipschitzWith C ν) {a b : ℝ} (hab : a ≤ b) :
    ‖ν b - ν a‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv ν t‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hac := hν.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hnorm : ‖ν b - ν a‖ ≤ ∫ t, ‖deriv ν t‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub]
    calc
      _ ≤ ∫ t in uIoc a b, ‖deriv ν t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ t, ‖deriv ν t‖ ∂μ := by
        rw [uIoc_of_le hab]
        exact integral_Icc_eq_integral_Ioc.symm
  have hholder : (∫ t, ‖deriv ν t‖ ∂μ) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖deriv ν t‖)
      (by simpa using (memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hd.norm)
    simpa only [norm_one, norm_norm, one_mul, one_pow, integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one,
      Real.one_rpow, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hnonneg : 0 ≤ ∫ t, ‖deriv ν t‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    ‖ν b - ν a‖ ^ 2 ≤
        (Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt hnonneg]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_toReal_sq_le_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc a b)) :
    (riemannianEDistOf g (γ a) (γ b)).toReal ^ 2 ≤
      (b - a) * ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2 := by
  let : IsManifold 𝓘(ℝ, E) 1 M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := M) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hγLip : LipschitzWith C γ := hγ
  have hfin (t : ℝ) : edist (γ t) (γ a) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top t a)) (hγLip t a)
  let ν : ℝ → ℝ := fun t => (edist (γ t) (γ a)).toReal
  have hν : LipschitzWith C ν := EMetric.lipschitzWith_toReal_edist_comp hγLip (γ a) hfin
  have hνa : ν a = 0 := by simp only [ν, edist_self, ENNReal.toReal_zero]
  have hder : ∀ᵐ t ∂volume, ‖deriv ν t‖ ^ 2 ≤ (riemannianCurveSpeed g γ t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hν.ae_differentiableAt_real]
      with t ht hνt
    have hb := abs_deriv_le_of_riemannian_distance_bound g ht hνt (fun y => by
      change |(edist (γ y) (γ a)).toReal - (edist (γ t) (γ a)).toReal| ≤
        (edist (γ t) (γ y)).toReal
      simpa only [edist_comm (γ y) (γ t)] using
        EMetric.abs_toReal_edist_sub_le_of_edist_ne_top (hfin y) (hfin t))
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hb) 2
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hcompare : (∫ t in Icc a b, ‖deriv ν t‖ ^ 2) ≤
      ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2 :=
    integral_mono_ae hd.norm.integrable_sq henergy (ae_restrict_of_ae hder)
  have hscalar := norm_sub_sq_le_length_mul_integral_deriv_sq hν hab
  rw [hνa, sub_zero, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hscalar
  have hdist : ν b = (riemannianEDistOf g (γ a) (γ b)).toReal := by
    change (edist (γ b) (γ a)).toReal = (edist (γ a) (γ b)).toReal
    rw [edist_comm]
  change ν b ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv ν t‖ ^ 2 at hscalar
  rw [hdist] at hscalar
  exact hscalar.trans (mul_le_mul_of_nonneg_left hcompare (sub_nonneg.mpr hab))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_ofReal_sqrt_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc a b)) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal
      (Real.sqrt ((b - a) * ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2)) := by
  have hfin : riemannianEDistOf g (γ a) (γ b) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top a b)) (hγ a b)
  apply (ENNReal.le_ofReal_iff_toReal_le hfin (Real.sqrt_nonneg _)).mpr
  have hs := Real.sqrt_le_sqrt (riemannianEDistOf_toReal_sq_le_interval_energy g hγ hab henergy)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hs

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_energy_bound_curve_range_subset_of_isCompact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {K O : Set M}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (α : ℝ → M) (C : ℝ≥0),
      (∀ x y, riemannianEDistOf g (α x) (α y) ≤ (C : ℝ≥0∞) * edist x y) →
      α 0 ∈ K →
      IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (Icc (0 : ℝ) 1) →
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2) ≤ ε →
      MapsTo α (Icc (0 : ℝ) 1) O := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨ρ, hρ, hsep⟩ := Metric.exists_pos_forall_lt_edist hK hO.isClosed_compl
    hKO.disjoint_compl_right
  refine ⟨(ρ : ℝ) ^ 2, sq_pos_of_pos (by exact_mod_cast hρ), ?_⟩
  intro α C hα hα0 hint hsmall t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
  have hI : (∫ s in Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2) ≤
      ∫ s in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α s) ^ 2 :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hI0 : 0 ≤ ∫ s in Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hb : t * (∫ s in Icc (0 : ℝ) t, (riemannianCurveSpeed g α s) ^ 2) ≤ (ρ : ℝ) ^ 2 :=
    (mul_le_of_le_one_left hI0 ht.2).trans (hI.trans hsmall)
  have hd := riemannianEDistOf_le_ofReal_sqrt_interval_energy g hα ht.1 (hint.mono_set hsub)
  rw [sub_zero] at hd
  have hroot : Real.sqrt (t * ∫ s in Icc (0 : ℝ) t,
      (riemannianCurveSpeed g α s) ^ 2) ≤ ρ := by
    exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq ρ.coe_nonneg)
  have hdρ : riemannianEDistOf g (α 0) (α t) ≤ (ρ : ℝ≥0∞) := by
    exact hd.trans ((ENNReal.ofReal_le_ofReal hroot).trans_eq ENNReal.ofReal_coe_nnreal)
  by_contra hnot
  exact (hsep (α 0) hα0 (α t) hnot).not_ge hdρ

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_curve_energy_bound_of_hasCompactSupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e : M → F}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hes : HasCompactSupport e) :
    ∃ C : ℝ≥0, 0 < C ∧
      (∀ x y, edist (e x) (e y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y) ∧
      ∀ (α : ℝ → M) (L : ℝ≥0),
        (∀ s t, riemannianEDistOf g (α s) (α t) ≤ (L : ℝ≥0∞) * edist s t) →
        ∀ a b : ℝ,
          IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (Icc a b) →
          IntegrableOn (fun t => ‖deriv (e ∘ α) t‖ ^ 2) (Icc a b) ∧
          (∫ t in Icc a b, ‖deriv (e ∘ α) t‖ ^ 2) ≤
            (C : ℝ) ^ 2 * ∫ t in Icc a b, (riemannianCurveSpeed g α t) ^ 2 := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g he hes
  let C : ℝ≥0 := B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (p : M) (v : TangentSpace 𝓘(ℝ, E) p) :
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p v : F)‖ ≤ C * Real.sqrt (g.inner p v v) :=
    (hB p v).trans (mul_le_mul_of_nonneg_right (by simp [C]) (Real.sqrt_nonneg _))
  have hLip := edist_map_le_of_metric_mfderiv_bound g hC he hbound
  refine ⟨C, hC, hLip, ?_⟩
  intro α L hα a b hint
  have hcomp : LipschitzWith (C * L) (e ∘ α) := by
    intro s t
    apply (hLip (α s) (α t)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hα s t)
  let μ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv (e ∘ α)) 2 μ := MemLp.of_bound
    (aestronglyMeasurable_deriv (e ∘ α) μ) (C * L)
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hcomp)
  have hpoint : ∀ᵐ t ∂volume,
      ‖deriv (e ∘ α) t‖ ^ 2 ≤ (C : ℝ) ^ 2 * (riemannianCurveSpeed g α t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hα] with t ht
    have heq : deriv (e ∘ α) t = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e (α t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α t 1) := by
      have h := mfderiv_comp t (he.mdifferentiableAt one_ne_zero) ht
      rw [mfderiv_eq_fderiv] at h
      have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (e (α t))
        (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)))) h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv] using! hv
    rw [heq]
    have hb := pow_le_pow_left₀ (norm_nonneg _)
      (hbound (α t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α t 1)) 2
    rw [mul_pow] at hb
    exact hb
  refine ⟨hd.norm.integrable_sq, ?_⟩
  have h := integral_mono_ae hd.norm.integrable_sq (hint.const_mul ((C : ℝ) ^ 2))
    (ae_restrict_of_ae hpoint)
  simpa only [integral_const_mul] using h

end DifferentialGeometry.Geometry

end

end
