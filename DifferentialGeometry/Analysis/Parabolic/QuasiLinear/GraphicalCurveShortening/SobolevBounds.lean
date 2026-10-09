import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Sobolev
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTameComposition
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.AffineMajorant

noncomputable section
open Set MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem exists_lp_graphDiffusionCoefficient_h2_bound
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure Ω) [IsFiniteMeasure μ]
      {p : ℝ≥0∞} (u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 2)),
      MemLp u p μ → ∀ a : Ω → TensorHs g 0 0 1, AEStronglyMeasurable a μ →
      (∀ᵐ t ∂μ, ‖P (u t)‖ ≤ R) →
      (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (a t) x =
        graphDiffusionCoefficient (WithLp.toLp 2 (scalarH1PiToContinuous g (P (u t)) x))) →
      ∃ v : Lp (TensorHs g 0 0 2) p μ, (fun t => J (v t)) =ᵐ[μ] a ∧
        ∀ᵐ t ∂μ, ‖v t‖ ≤ C * (1 + ‖u t‖) := by
  intro J P
  let A := scalarH1PiToContinuous (ι := ι) g
  let K : Set (ι → ℝ) := Metric.closedBall 0 (‖A‖ * R)
  let F : (ι → ℝ) → ℝ := fun q => graphDiffusionCoefficient (WithLp.toLp 2 q)
  have hF : ContDiff ℝ ∞ F := contDiff_graphDiffusionCoefficient.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff
  obtain ⟨C, hC, hc⟩ := AddCircle.exists_lp_scalarH2_composition_bound_of_h1_bound
    (Ω := Ω) g F hF.contDiffOn isOpen_univ (isCompact_closedBall _ _) (subset_univ K)
    ((Fintype.card ι : ℝ) * R)
  refine ⟨C * (1 + Fintype.card ι), mul_nonneg hC (by positivity), ?_⟩
  intro μ _ p u hu a ha hbound heval
  have hrange : ∀ᵐ t ∂μ, range (A (P (u t))) ⊆ K := by
    filter_upwards [hbound] with t ht
    rintro y ⟨x, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((A (P (u t))).norm_coe_le_norm x).trans
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg A)))
  have hsum : ∀ᵐ t ∂μ, (∑ i, ‖J (u t i)‖) ≤ (Fintype.card ι : ℝ) * R := by
    filter_upwards [hbound] with t ht
    calc
      _ ≤ ∑ _i : ι, ‖P (u t)‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = (Fintype.card ι : ℝ) * ‖P (u t)‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  obtain ⟨v, hv, hnorm⟩ := hc μ hu a ha hrange hsum heval
  refine ⟨v, hv, ?_⟩
  filter_upwards [hnorm] with t ht
  have hsum' : (∑ i, ‖u t i‖) ≤ (Fintype.card ι : ℝ) * ‖u t‖ := by
    calc
      _ ≤ ∑ _i : ι, ‖u t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
      _ = _ := by simp
  exact ht.trans (by nlinarith [mul_nonneg hC (norm_nonneg (u t))])



private theorem memLp_linear_shift
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (f : X) {T : ℝ} (u : timeL2 X T) :
    MemLp (fun t => L (f + u t)) 2 (timeMeasure T) :=
  L.comp_memLp' ((memLp_const f).add (Lp.memLp u))

private theorem graph_slope_h2_inclusion
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let D₁ := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1))).comp
        (AddCircle.parameterDerivativeHsPi (ι := ι) g 1)
    let D₂ := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsCongrL g 0 0 (by norm_num : ((2 : ℕ) : ℝ) = 2))).comp
        (AddCircle.parameterDerivativeHsPi (ι := ι) g 2)
    P (D₂ f) = D₁ (K f) := by
  intro K J P D₁ D₂
  apply PiLp.ext
  intro i
  change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2)
      (tensorHsCongrL g 0 0 (by norm_num : ((2 : ℕ) : ℝ) = 2)
        (AddCircle.parameterDerivativeHs g 2 (f i))) =
    tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
      (AddCircle.parameterDerivativeHs g 1
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1) (f i)))
  have hc := AddCircle.parameterDerivativeHs_tensorHsInclusion g
    (by decide : 1 ≤ 2) (f i)
  simp only [tensorHsCongrL_apply]
  rw [← tensorHsCongr_incl
    (by norm_num : ((1 : ℕ) : ℝ) = 1)
    (by norm_num : ((2 : ℕ) : ℝ) = 2)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    (by norm_num : (1 : ℝ) ≤ 2)]
  exact congrArg (tensorHsCongr g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)) hc.symm


private theorem exists_timeL2_graphDiffusionCoefficient_h2_of_bounded_state
    {ι X Y : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (K : X →L[ℝ] Y)
    (D₁ : Y →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (D₂ : X →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (f₀ : X) {R : ℝ}
    (alpha : Metric.closedBall (0 : Y) R → TensorHs g 0 0 1)
    (hAlpha : Continuous alpha)
    (hEval : ∀ v x, scalarH1ToContinuous g (alpha v) x =
      graphDiffusionCoefficient (WithLp.toLp 2
        (scalarH1PiToContinuous g (D₁ (K f₀ + v.val)) x))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ f, P (D₂ f) = D₁ (K f)) →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ T : ℝ, ∀ u : timeL2 X T,
      ∀ w : ℝ → Metric.closedBall (0 : Y) R,
      (fun t => (w t).val) =ᵐ[timeMeasure T] (fun t => K (u t)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => J (a₂ t)) =ᵐ[timeMeasure T] (fun t => alpha (w t)) ∧
        ‖a₂‖ ≤ C₂ * (Real.sqrt T + ‖u‖) := by
  intro J P hDP
  obtain ⟨C, hC, hc⟩ := exists_lp_graphDiffusionCoefficient_h2_bound (Ω := ℝ)
    (ι := ι) g (‖D₁‖ * (‖K f₀‖ + R))
  let A := C * ‖D₂‖
  let B := C * (1 + ‖D₂‖ * ‖f₀‖)
  refine ⟨A + B, by positivity, ?_⟩
  intro T u w hwu
  have hw : AEStronglyMeasurable w (timeMeasure T) := by
    apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
    exact (K.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).congr hwu.symm
  let slope := fun t => D₂ (f₀ + u t)
  have hslope : MemLp slope 2 (timeMeasure T) :=
    memLp_linear_shift D₂ f₀ u
  have ha : AEStronglyMeasurable (fun t => alpha (w t)) (timeMeasure T) :=
    hAlpha.comp_aestronglyMeasurable hw
  have hbound : ∀ᵐ t ∂timeMeasure T, ‖P (slope t)‖ ≤ ‖D₁‖ * (‖K f₀‖ + R) := by
    filter_upwards [hwu] with t ht
    change ‖P (D₂ (f₀ + u t))‖ ≤ _
    rw [hDP, map_add, ← ht]
    apply (D₁.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg D₁)
    exact (norm_add_le _ _).trans (add_le_add_right
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using (w t).property) _)
  have heval : ∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (alpha (w t)) x =
      graphDiffusionCoefficient (WithLp.toLp 2 (scalarH1PiToContinuous g (P (slope t)) x)) := by
    filter_upwards [hwu] with t ht
    intro x
    dsimp only [slope]
    rw [hDP, map_add, ← ht]
    exact hEval (w t) x
  obtain ⟨a₂, ha₂, hnorm⟩ := hc (timeMeasure T) slope hslope
    (fun t => alpha (w t)) ha hbound heval
  refine ⟨a₂, ha₂, ?_⟩
  have hn : ‖a₂‖ ≤ A * ‖u‖ + Real.sqrt T * B := by
    apply timeL2_norm_le_of_ae_affine_bound a₂ u (by positivity) (by positivity)
    filter_upwards [hnorm] with t ht
    have hs := (D₂.le_opNorm (f₀ + u t)).trans
      (mul_le_mul_of_nonneg_left (norm_add_le f₀ (u t)) (norm_nonneg D₂))
    exact ht.trans (by dsimp only [slope, A, B] at *; nlinarith)
  exact hn.trans (by
    dsimp only [A, B]
    nlinarith [mul_nonneg (mul_nonneg hC (norm_nonneg D₂)) (Real.sqrt_nonneg T),
      mul_nonneg (mul_nonneg hC (show 0 ≤ 1 + ‖D₂‖ * ‖f₀‖ by positivity)) (norm_nonneg u)])


theorem exists_graphDiffusionCoefficient_h1_on_closedBall_with_timeL2_h2_bound
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
    ∃ R : ℝ, 0 < R ∧ ∃ C₁ : ℝ≥0,
      ∃ alpha : Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
          TensorHs g 0 0 1,
        LipschitzWith C₁ alpha ∧
        (∀ v x, scalarH1ToContinuous g (alpha v) x =
          graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι =>
            scalarH1ToContinuous g
              (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
                (AddCircle.parameterDerivativeHsPi g 1 (K f₀ + v.val) i)) x))) ∧
        ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ T : ℝ,
          ∀ u : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T,
          ∀ w : ℝ → Metric.closedBall
            (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R,
          (fun t => (w t).val) =ᵐ[timeMeasure T] (fun t => K (u t)) →
          ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
            (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
                (fun t => alpha (w t)) ∧
            ‖a₂‖ ≤ C₂ * (Real.sqrt T + ‖u‖) := by
  intro K
  obtain ⟨R, hR, C₁, alpha, hAlpha, hEval⟩ :=
    exists_graphDiffusionCoefficient_h1_on_closedBall g (K f₀)
  refine ⟨R, hR, C₁, alpha, hAlpha, hEval, ?_⟩
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ 2)
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
  let D₁ := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1))).comp
      (AddCircle.parameterDerivativeHsPi (ι := ι) g 1)
  let D₂ := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsCongrL g 0 0 (by norm_num : ((2 : ℕ) : ℝ) = 2))).comp
      (AddCircle.parameterDerivativeHsPi (ι := ι) g 2)
  have hDP (f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) :
      P (D₂ f) = D₁ (K f) := graph_slope_h2_inclusion g f
  exact exists_timeL2_graphDiffusionCoefficient_h2_of_bounded_state
    g K D₁ D₂ f₀ alpha hAlpha.continuous hEval hDP

end DifferentialGeometry.Analysis.Parabolic
