import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Homeomorph.Lemmas

open scoped Topology

namespace Homeomorph

private theorem ae_exists_measure_closedBall_le
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ] :
    ∀ᵐ y : ℝ ∂MeasureTheory.volume, ∃ N : ℝ, 0 < N ∧ ∀ r : ℝ, 0 < r →
      μ (Metric.closedBall y r) ≤ ENNReal.ofReal (2 * N * r) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ MeasureTheory.volume,
    MeasureTheory.Measure.rnDeriv_lt_top μ MeasureTheory.volume] with y hlim hfinite
  let M := (μ.rnDeriv MeasureTheory.volume y).toReal + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hlt : μ.rnDeriv MeasureTheory.volume y < ENNReal.ofReal M := by
    calc
      _ = ENNReal.ofReal (μ.rnDeriv MeasureTheory.volume y).toReal :=
        (ENNReal.ofReal_toReal hfinite.ne).symm
      _ < ENNReal.ofReal M := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        ENNReal.toReal_nonneg).mpr (by dsimp [M]; linarith)
  have hevent := Filter.Tendsto.eventually_lt_const hlt hlim
  obtain ⟨S, hS, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hevent
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hS
  let A := (μ _root_.Set.univ).toReal
  let N := max M (A / (2 * δ))
  have hN : 0 < N := hM.trans_le (le_max_left _ _)
  refine ⟨N, hN, ?_⟩
  intro r hr
  by_cases hsmall : r < δ
  · have hrball : r ∈ Metric.ball (0 : ℝ) δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hsmall
    have hquotlt : μ (Metric.closedBall y r) / MeasureTheory.volume (Metric.closedBall y r) <
        ENNReal.ofReal M := hsub ⟨hball hrball, hr⟩
    have hquot := hquotlt.le
    rw [Real.volume_closedBall] at hquot
    have hden : ENNReal.ofReal (2 * r) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hmass := (ENNReal.div_le_iff hden ENNReal.ofReal_ne_top).mp hquot
    calc
      μ (Metric.closedBall y r) ≤ ENNReal.ofReal M * ENNReal.ofReal (2 * r) := hmass
      _ = ENNReal.ofReal (2 * M * r) := by rw [← ENNReal.ofReal_mul hM.le]; congr 1; ring
      _ ≤ ENNReal.ofReal (2 * N * r) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
          (by norm_num)) hr.le)
  · have hδr : δ ≤ r := le_of_not_gt hsmall
    have hlarge : A ≤ 2 * N * δ := by
      have h := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp (le_max_right M (A / (2 * δ)))
      dsimp only [N]
      nlinarith only [h]
    have hmass : A ≤ 2 * N * r := hlarge.trans
      (mul_le_mul_of_nonneg_left hδr (mul_nonneg (by norm_num) hN.le))
    calc
      μ (Metric.closedBall y r) ≤ μ _root_.Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal A := (ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ _root_.Set.univ)).symm
      _ ≤ ENNReal.ofReal (2 * N * r) := ENNReal.ofReal_le_ofReal hmass

theorem ae_exists_volume_image_strip_le (h : ℂ ≃ₜ ℂ) (a b c d : ℝ) :
    ∀ᵐ y : ℝ ∂MeasureTheory.volume.restrict (Set.Ioo c d),
      ∃ N : ℝ, 0 < N ∧ ∀ ε : ℝ, 0 < ε → ε < min (y - c) (d - y) →
        MeasureTheory.volume
          (h '' {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (y - ε) (y + ε)}) ≤
            ENNReal.ofReal (2 * N * ε) := by
  let K : Set ℂ := {z | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d}
  have hK : IsCompact K :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).reProdIm (isCompact_Icc : IsCompact (Set.Icc c d))
  let ν : MeasureTheory.Measure ℂ := MeasureTheory.Measure.map h.symm MeasureTheory.volume
  have hν (S : Set ℂ) (hS : MeasurableSet S) : ν S = MeasureTheory.volume (h '' S) := by
    change (MeasureTheory.Measure.map h.symm MeasureTheory.volume) S = _
    rw [MeasureTheory.Measure.map_apply h.symm.continuous.measurable hS]
    congr 1
    ext z
    constructor
    · intro hz
      exact ⟨h.symm z, hz, h.apply_symm_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      change h.symm (h w) ∈ S
      rw [h.symm_apply_apply]
      exact hw
  have hνK : ν K ≠ ⊤ := by
    rw [hν K hK.measurableSet]
    exact (hK.image h.continuous).measure_ne_top
  let _ : MeasureTheory.IsFiniteMeasure (ν.restrict K) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hνK
  let σ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.map Complex.im (ν.restrict K)
  let _ : MeasureTheory.IsFiniteMeasure σ := by dsimp [σ]; infer_instance
  have hstiff := ae_exists_measure_closedBall_le σ
  filter_upwards [MeasureTheory.ae_restrict_of_ae hstiff] with y hy
  obtain ⟨N, hN, hbound⟩ := hy
  refine ⟨N, hN, ?_⟩
  intro ε hε hmargin
  have hinterval : Set.Icc (y - ε) (y + ε) ⊆ Set.Icc c d := by
    intro z hz
    have hl := hmargin.trans_le (min_le_left _ _)
    have hr := hmargin.trans_le (min_le_right _ _)
    constructor <;> linarith [hz.1, hz.2]
  have him : Measurable Complex.im := Complex.continuous_im.measurable
  have hstrip : σ (Metric.closedBall y ε) = MeasureTheory.volume
      (h '' {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (y - ε) (y + ε)}) := by
    rw [Real.closedBall_eq_Icc]
    change (MeasureTheory.Measure.map Complex.im (ν.restrict K)) (Set.Icc (y - ε) (y + ε)) = _
    rw [MeasureTheory.Measure.map_apply him measurableSet_Icc,
      MeasureTheory.Measure.restrict_apply (measurableSet_Icc.preimage him),
      hν _ ((measurableSet_Icc.preimage him).inter hK.measurableSet)]
    apply congrArg (fun S : Set ℂ => MeasureTheory.volume (h '' S))
    ext z
    constructor
    · rintro ⟨himz, hre, _⟩
      exact ⟨hre, himz⟩
    · rintro ⟨hre, himz⟩
      exact ⟨himz, hre, hinterval himz⟩
  rw [← hstrip]
  exact hbound ε hε

end Homeomorph
