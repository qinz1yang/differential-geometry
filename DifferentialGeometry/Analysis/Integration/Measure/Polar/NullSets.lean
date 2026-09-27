import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem measure_sdiff_iUnion_compact_smul_eq_zero [Nontrivial E]
    (K : Set E) (hK : IsCompact K) :
    μ
        (K \ ⋃ n : ℕ, K ∩
          (fun z : ℝ × E => z.1 • z.2) ''
            (Icc (0 : ℝ) ((n : ℝ) / (n + 1)) ×ˢ K)) = 0 := by
  classical
  let C : ℕ → Set E := fun n => K ∩
    (fun z : ℝ × E => z.1 • z.2) ''
      (Icc (0 : ℝ) ((n : ℝ) / (n + 1)) ×ˢ K)
  let B : Set E := K \ ⋃ n : ℕ, C n
  let f : E → ℝ≥0∞ := B.indicator fun _ => 1
  have hCcompact : ∀ n : ℕ, IsCompact (C n) := by
    intro n
    apply hK.inter
    exact (isCompact_Icc.prod hK).image
      (continuous_fst.smul continuous_snd)
  have hCmeas : ∀ n : ℕ, MeasurableSet (C n) :=
    fun n => (hCcompact n).measurableSet
  have hB : MeasurableSet B :=
    hK.measurableSet.diff (MeasurableSet.iUnion hCmeas)
  have hf : Measurable f :=
    measurable_const.indicator hB
  change μ B = 0
  calc
    μ B = ∫⁻ z : E, f z ∂μ :=
      (lintegral_indicator_one hB).symm
    _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ), f (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂μ.toSphere :=
      lintegral_polar μ f hf.aemeasurable
    _ = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with u
      let A : Set (Ioi (0 : ℝ)) := {r | r.1 • u.1 ∈ B}
      have hA : MeasurableSet A := by
        exact hB.preimage (continuous_subtype_val.smul continuous_const).measurable
      have hAsub : A.Subsingleton := by
        rintro ⟨a, ha0⟩ ha ⟨b, hb0⟩ hb
        change a • u.1 ∈ B at ha
        change b • u.1 ∈ B at hb
        rcases ha with ⟨haK, haB⟩
        rcases hb with ⟨hbK, hbB⟩
        apply Subtype.ext
        rcases lt_trichotomy a b with hab | hab | hab
        · exfalso
          have ha_pos : 0 < a := ha0
          have hb_pos : 0 < b := hb0
          have hdiff : 0 < b - a := sub_pos.mpr hab
          obtain ⟨n, hn⟩ := exists_nat_gt (a / (b - a))
          have hn_pos : 0 < (n : ℝ) + 1 := by positivity
          have hfrac : a / b ≤ (n : ℝ) / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ hb_pos hn_pos]
            have hn' : a < (n : ℝ) * (b - a) :=
              (div_lt_iff₀ hdiff).mp hn
            nlinarith
          apply haB
          refine mem_iUnion.2 ⟨n, ?_⟩
          refine ⟨haK, ?_⟩
          refine ⟨(a / b, b • u.1), ⟨⟨?_, hbK⟩, ?_⟩⟩
          · exact ⟨div_nonneg ha_pos.le hb_pos.le, hfrac⟩
          · change (a / b) • (b • u.1) = a • u.1
            rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
        · exact hab
        · exfalso
          have ha_pos : 0 < a := ha0
          have hb_pos : 0 < b := hb0
          have hdiff : 0 < a - b := sub_pos.mpr hab
          obtain ⟨n, hn⟩ := exists_nat_gt (b / (a - b))
          have hn_pos : 0 < (n : ℝ) + 1 := by positivity
          have hfrac : b / a ≤ (n : ℝ) / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ ha_pos hn_pos]
            have hn' : b < (n : ℝ) * (a - b) :=
              (div_lt_iff₀ hdiff).mp hn
            nlinarith
          apply hbB
          refine mem_iUnion.2 ⟨n, ?_⟩
          refine ⟨hbK, ?_⟩
          refine ⟨(b / a, a • u.1), ⟨⟨?_, haK⟩, ?_⟩⟩
          · exact ⟨div_nonneg hb_pos.le ha_pos.le, hfrac⟩
          · change (b / a) • (a • u.1) = b • u.1
            rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
      have hbase :
          (Measure.comap ((↑) : Ioi (0 : ℝ) → ℝ) volume) A = 0 := by
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        exact (hAsub.image ((↑) : Ioi (0 : ℝ) → ℝ)).measure_zero volume
      have hAzero :
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A = 0 := by
        rw [Measure.volumeIoiPow]
        exact withDensity_absolutelyContinuous _ _ hbase
      calc
        ∫⁻ r : Ioi (0 : ℝ), f (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
            ∫⁻ r : Ioi (0 : ℝ), A.indicator (fun _ => 1) r
              ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
          apply lintegral_congr
          intro r
          by_cases hr : r.1 • u.1 ∈ B
          · have hrA : r ∈ A := hr
            simp only [f, Set.indicator_of_mem hr, Set.indicator_of_mem hrA]
          · have hrA : r ∉ A := hr
            simp only [f, Set.indicator_of_notMem hr, Set.indicator_of_notMem hrA]
        _ = (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A :=
          lintegral_indicator_one hA
        _ = 0 := hAzero

private theorem measure_setOf_forall_smul_notMem_of_isCompact
    {K : Set E} (hK : IsCompact K) :
    μ {x | x ∈ K ∧ ∀ t : ℝ, 1 < t → t • x ∉ K} = 0 := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have hempty : {x | x ∈ K ∧ ∀ t : ℝ, 1 < t → t • x ∉ K} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxt⟩
      apply hxt 2 one_lt_two
      simpa only [Subsingleton.elim ((2 : ℝ) • x) x] using hx
    rw [hempty, measure_empty]
  | inr h =>
    apply measure_mono_null ?_ (measure_sdiff_iUnion_compact_smul_eq_zero μ K hK)
    rintro x ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    intro hxC
    obtain ⟨n, _, z, ⟨hz, hzK⟩, hzx⟩ := mem_iUnion.mp hxC
    by_cases hz0 : z.1 = 0
    · have hx0 : x = 0 := by simpa only [hz0, zero_smul] using hzx.symm
      apply hxt 2 one_lt_two
      simpa only [hx0, smul_zero] using hx
    · have hzpos : 0 < z.1 := lt_of_le_of_ne hz.1 (Ne.symm hz0)
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have hnlt : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
        (div_lt_one₀ hnpos).2 (by linarith)
      apply hxt (1 / z.1) ((one_lt_div hzpos).2 (hz.2.trans_lt hnlt))
      rw [← hzx]
      change (1 / z.1) • (z.1 • z.2) ∈ K
      simpa only [smul_smul, div_mul_cancel₀ 1 hz0, one_smul] using hzK

theorem IsSigmaCompact.measure_setOf_forall_smul_notMem {S : Set E} (hS : IsSigmaCompact S) :
    μ {x | x ∈ S ∧ ∀ t : ℝ, 1 < t → t • x ∉ S} = 0 := by
  obtain ⟨K, hK, hKS⟩ := hS
  have hnull : μ (⋃ n : ℕ, {x | x ∈ K n ∧ ∀ t : ℝ, 1 < t → t • x ∉ K n}) = 0 :=
    measure_iUnion_null fun n => measure_setOf_forall_smul_notMem_of_isCompact μ (hK n)
  apply measure_mono_null ?_ hnull
  rintro x ⟨hx, hxt⟩
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (hKS.symm ▸ hx)
  refine mem_iUnion.mpr ⟨n, hxn, ?_⟩
  intro t ht htx
  exact hxt t ht (hKS ▸ mem_iUnion.mpr ⟨n, htx⟩)

theorem IsCompact.measure_setOf_forall_smul_notMem {K : Set E} (hK : IsCompact K) :
    μ {x | x ∈ K ∧ ∀ t : ℝ, 1 < t → t • x ∉ K} = 0 :=
  hK.isSigmaCompact.measure_setOf_forall_smul_notMem μ
