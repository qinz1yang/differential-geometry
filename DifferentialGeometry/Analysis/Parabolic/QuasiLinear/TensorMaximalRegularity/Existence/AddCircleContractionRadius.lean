import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleDriftBounds

noncomputable section

open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_pos_contraction_radius_lt
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 ≤ T → T ≤ r → r ≤ δ →
      A * r * (1 + T) + Real.sqrt (1 + T) *
        (B * (Real.sqrt T + (1 + T) * r / 4) + C * Real.sqrt T) < η := by
  let f : ℝ → ℝ := fun r => A * r * (1 + r) + Real.sqrt (1 + r) *
    (B * (Real.sqrt r + (1 + r) * r / 4) + C * Real.sqrt r)
  have hf : ContinuousAt f 0 := by fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), f r < η :=
    hf.eventually_lt_const (by rw [hf0]; exact hη)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := min R (min 1 (ε / 2))
  have hδ : 0 < δ := lt_min hR (lt_min zero_lt_one (by positivity))
  refine ⟨δ, hδ, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro r T hT hTr hrδ
  have hr : 0 ≤ r := hT.trans hTr
  have hrε : r < ε := lt_of_le_of_lt
    (hrδ.trans ((min_le_right _ _).trans (min_le_right _ _))) (by linarith)
  have hfr : f r < η := he (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hr] using hrε)
  refine lt_of_le_of_lt ?_ hfr
  dsimp only [f]
  gcongr

private theorem exists_pos_contraction_radius
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 ≤ T → T ≤ r → r ≤ δ →
      A * r * (1 + T) + Real.sqrt (1 + T) *
        (B * (Real.sqrt T + (1 + T) * r / 4) + C * Real.sqrt T) < 1 := by
  exact exists_pos_contraction_radius_lt A B C hA hB hC hR zero_lt_one

private theorem eLpNorm_postcomp_toReal_le_of_norm_le_one
    {𝕜 Ω X Y W : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace Ω]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    {μ : Measure Ω} {p : ℝ≥0∞} (Z : Y →L[𝕜] W) (hZ : ‖Z‖ ≤ 1)
    {f : Ω → X →L[𝕜] Y} (hf : MemLp f p μ) :
    (eLpNorm (fun t => Z.comp (f t)) p μ).toReal ≤ (eLpNorm f p μ).toReal := by
  apply ENNReal.toReal_mono hf.eLpNorm_lt_top.ne
  apply eLpNorm_mono_enorm
    (((ContinuousLinearMap.compL 𝕜 X Y W) Z).continuous.comp_aestronglyMeasurable
      hf.aestronglyMeasurable)
  intro t
  apply enorm_le_iff_norm_le.mpr
  exact (ContinuousLinearMap.opNorm_comp_le Z (f t)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ (norm_nonneg (f t)))

private theorem postcomp_norm_and_eLpNorm_lt_of_norm_le_one
    {𝕜 Ω X₁ X₂ Y W : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace Ω]
    [SeminormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
    [SeminormedAddCommGroup X₂] [NormedSpace 𝕜 X₂]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    {μ : Measure Ω} {p : ℝ≥0∞} (Z : Y →L[𝕜] W) (hZ : ‖Z‖ ≤ 1)
    {f₁ : Ω → X₁ →L[𝕜] Y} (hf₁ : MemLp f₁ p μ)
    {f₂ : Ω → X₂ →L[𝕜] Y} {C b w q : ℝ} (hw : 0 ≤ w)
    (hC : ∀ᵐ t ∂μ, ‖f₂ t‖ ≤ C) (hsmall : b + w * (eLpNorm f₁ p μ).toReal < q) :
    (∀ᵐ t ∂μ, ‖Z.comp (f₂ t)‖ ≤ C) ∧
      b + w * (eLpNorm (fun t => Z.comp (f₁ t)) p μ).toReal < q := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hC] with t ht
    exact ((ContinuousLinearMap.opNorm_comp_le Z (f₂ t)).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hZ (norm_nonneg (f₂ t)))).trans ht
  · exact (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (eLpNorm_postcomp_toReal_le_of_norm_le_one Z hZ hf₁) hw)).trans_lt hsmall

private def scalarTensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) : TensorHs g 0 0 b →L[ℝ] TensorHs g 0 0 a :=
  tensorHsInclusion hab

variable {ι : Type*} [Fintype ι]

private local instance vectorTensorHsNormedSpace
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private def vectorTensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 b) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarTensorHsInclusion g hab)

private theorem vectorTensorHsInclusion_norm_le_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) : ‖vectorTensorHsInclusion (ι := ι) g hab‖ ≤ 1 :=
  ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
    (fun _ => tensorHsInclusion_opNorm_le_one hab)

private theorem drift_high_memLp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a t)) 2 (timeMeasure T) :=
  memLp_parameterDriftOperatorHsPi (ι := ι) g (Lp.memLp a)

private theorem drift_low_memLp
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    MemLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a t)) 2 (timeMeasure T) :=
  memLp_parameterDriftOperatorH0Pi (ι := ι) g (Lp.memLp a)

theorem exists_pos_parameterDerivativeHsPi_contraction_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (Cα C : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 < T → T ≤ r → r ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (a₂ t) - q‖ ≤ Cα * r) →
      ‖a₂‖ ≤ C * (Real.sqrt T + (1 + T) * r / 4) →
      let hh := drift_high_memLp (ι := ι) g a₂
      ∃ C2 : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2) ∧
        (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          ‖hh.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a₂ t))‖ < 1 := by
  intro J q
  let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
  let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := scalarHsMul g 1 (by norm_num)
  let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  let A : ℝ≥0 := ‖m‖₊ * ‖parameterSecondDerivativeHs g 1‖₊ * Cα
  let K := ‖m‖ * ‖D‖ ^ 2
  let B := ‖m‖ * ‖d‖ * ‖D‖
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    A (K * C) B A.coe_nonneg (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro r T hT hTr hrδ a₂ hclose hnorm hh
  have hr : 0 ≤ r := hT.le.trans hTr
  let C2 : ℝ≥0 := A * ⟨r, hr⟩
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g (J (a₂ t))‖ ≤ C2 := by
    filter_upwards [hclose] with t ht
    calc
      _ ≤ ‖m‖ * ‖J (a₂ t) - q‖ * ‖parameterSecondDerivativeHs g 1‖ :=
        norm_parameterPrincipalOperatorHsPi_le g (J (a₂ t))
      _ ≤ ‖m‖ * (Cα * r) * ‖parameterSecondDerivativeHs g 1‖ := by gcongr
      _ = C2 := by
        change ‖m‖ * (Cα * r) * ‖parameterSecondDerivativeHs g 1‖ =
          (‖m‖ * ‖parameterSecondDerivativeHs g 1‖ * Cα) * r
        ring
  refine ⟨C2, hbound, ?_⟩
  have hn : ‖hh.toLp (fun t => parameterDriftOperatorHsPi (ι := ι) g (a₂ t))‖ ≤
      K * ‖a₂‖ + Real.sqrt T * B := norm_toLp_parameterDriftOperatorHsPi_le g a₂
  apply lt_of_le_of_lt _ (hsmall hT.le hTr hrδ)
  change (A : ℝ) * r * (1 + T) + _ ≤ _
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ K * ‖a₂‖ + Real.sqrt T * B := hn
    _ ≤ K * (C * (Real.sqrt T + (1 + T) * r / 4)) + Real.sqrt T * B := by gcongr
    _ = _ := by ring

theorem exists_pos_parameterDerivativeH0Pi_contraction_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (Cα C : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {r T : ℝ},
      0 < T → T ≤ r → r ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (a₂ t) - q‖ ≤ Cα * r) →
      ‖a₂‖ ≤ C * (Real.sqrt T + (1 + T) * r / 4) →
      let hl := drift_low_memLp (ι := ι) g a₂
      ∃ C2 : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2) ∧
        (C2 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          ‖hl.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a₂ t))‖ < 1 := by
  intro J q
  let D : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 ((1 : ℕ) : ℝ) := parameterDerivativeHs g 1
  let d : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianDriftCoefficient g))
  let c : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] C(AddCircle (1 : ℝ), ℝ) := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z : TensorHs g 0 0 ((0 : ℕ) : ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let D₀ : TensorHs g 0 0 (((0 : ℕ) : ℝ) + 1) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := Z.comp (parameterDerivativeHs g 0)
  let M : C(AddCircle (1 : ℝ), ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) →L[ℝ] TensorHs g 0 0 (0 : ℝ) := scalarH0ContinuousMul g
  let A : ℝ≥0 := ‖M‖₊ * ‖c‖₊ * ‖Z.comp (parameterSecondDerivativeHs g 0)‖₊ * Cα
  let K := ‖M‖ * ‖c‖ * ‖D‖ * ‖D₀‖
  let B := ‖M‖ * ‖c‖ * ‖d‖ * ‖D₀‖
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    A (K * C) B A.coe_nonneg (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro r T hT hTr hrδ a₂ hclose hnorm hl
  have hr : 0 ≤ r := hT.le.trans hTr
  let C2 : ℝ≥0 := A * ⟨r, hr⟩
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g (J (a₂ t))‖ ≤ C2 := by
    filter_upwards [hclose] with t ht
    calc
      _ ≤ ‖M‖ * (‖c‖ * ‖J (a₂ t) - q‖) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ :=
        norm_parameterPrincipalOperatorH0Pi_le g (J (a₂ t))
      _ ≤ ‖M‖ * (‖c‖ * (Cα * r)) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ := by gcongr
      _ = C2 := by
        change ‖M‖ * (‖c‖ * (Cα * r)) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ =
          (‖M‖ * ‖c‖ * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ * Cα) * r
        ring
  refine ⟨C2, hbound, ?_⟩
  have hn : ‖hl.toLp (fun t => parameterDriftOperatorH0Pi (ι := ι) g (a₂ t))‖ ≤
      K * ‖a₂‖ + Real.sqrt T * B := norm_toLp_parameterDriftOperatorH0Pi_le g a₂
  apply lt_of_le_of_lt _ (hsmall hT.le hTr hrδ)
  change (A : ℝ) * r * (1 + T) + _ ≤ _
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ K * ‖a₂‖ + Real.sqrt T * B := hn
    _ ≤ K * (C * (Real.sqrt T + (1 + T) * r / 4)) + Real.sqrt T * B := by gcongr
    _ = _ := by ring

private theorem parameter_derivative_h0_postcomp_bounds
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C₂ : ℝ≥0) {q : ℝ} :
    have H := scalarTensorHsInclusion g₀
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    have Z :=
      vectorTensorHsInclusion (ι := ι) g₀
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    have A₂ := fun (t : ℝ) => AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g₀ (H (a₂ t))
    let A₁ := fun (t : ℝ) => AddCircle.parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t)
    (∀ᵐ t ∂timeMeasure T,
      ‖A₂ t‖ ≤ C₂) →
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm A₁ 2 (timeMeasure T)).toReal < q →
    (∀ᵐ t ∂timeMeasure T,
      ‖Z.comp (A₂ t)‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal < q := by
  intro H Z A₂ A₁ hC hsmall
  have hA₁ := drift_low_memLp (ι := ι) g₀ a₂
  have hZ : ‖Z‖ ≤ 1 := vectorTensorHsInclusion_norm_le_one g₀ _
  have hnormalized := postcomp_norm_and_eLpNorm_lt_of_norm_le_one Z hZ hA₁
    (Real.sqrt_nonneg (1 + T)) hC hsmall
  exact hnormalized

theorem parameter_derivative_h0_normalized_contraction
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C₂ : ℝ≥0) {q : ℝ} :
    have H := scalarTensorHsInclusion g₀
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    have Z :=
      vectorTensorHsInclusion (ι := ι) g₀
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    have A₂ := fun (t : ℝ) => AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g₀ (H (a₂ t))
    let A₁ := fun (t : ℝ) => AddCircle.parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t)
    have hA₁ := drift_low_memLp (ι := ι) g₀ a₂
    (∀ᵐ t ∂timeMeasure T,
      ‖A₂ t‖ ≤ C₂) →
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA₁.toLp A₁‖ < q →
    (∀ᵐ t ∂timeMeasure T,
      ‖Z.comp (A₂ t)‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal < q := by
  intro H Z A₂ A₁ hA₁ hC hsmall
  rw [Lp.norm_toLp] at hsmall
  exact parameter_derivative_h0_postcomp_bounds (ι := ι) g₀ a₂ C₂ hC hsmall

theorem exists_pos_parameter_principal_operator_norm_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (η : ℝ) (hη : 0 < η) :
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ), ‖a - q‖ ≤ ε →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g₀ a‖ ≤ η ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g₀ a‖ ≤ η := by
  intro q
  let m := scalarHsMul g₀ 1 (by norm_num)
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let M := scalarH0ContinuousMul g₀
  let Ch := ‖m‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖
  let Cl := ‖M‖ * ‖c‖ * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖
  have hCh : 0 ≤ Ch := by positivity
  have hCl : 0 ≤ Cl := by positivity
  let ε := η / (Ch + Cl + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεeq : ε * (Ch + Cl + 1) = η := by
    exact div_mul_cancel₀ _ (by positivity)
  have hChε : Ch * ε ≤ η := by
    nlinarith [mul_nonneg hCl hε.le]
  have hClε : Cl * ε ≤ η := by
    nlinarith [mul_nonneg hCh hε.le]
  refine ⟨ε, hε, ?_⟩
  intro a ht
  constructor
  · calc
      _ ≤ ‖m‖ * ‖a - q‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ :=
        AddCircle.norm_parameterPrincipalOperatorHsPi_le g₀ a
      _ ≤ ‖m‖ * ε * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ := by gcongr
      _ = Ch * ε := by dsimp only [Ch]; ring
      _ ≤ η := hChε
  · calc
      _ ≤ ‖M‖ * (‖c‖ * ‖a - q‖) *
          ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ :=
        AddCircle.norm_parameterPrincipalOperatorH0Pi_le g₀ a
      _ ≤ ‖M‖ * (‖c‖ * ε) * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ := by gcongr
      _ = Cl * ε := by dsimp only [Cl]; ring
      _ ≤ η := hClε

theorem exists_pos_parameter_drift_operator_norm_lt
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (A : ℝ≥0) (η : ℝ) (hη : 0 < η) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < η ∧
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < η := by
  let D := AddCircle.parameterDerivativeHs g₀ 1
  let m := scalarHsMul g₀ 1 (by norm_num)
  let d := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
    (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀))
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let D₀ := Z.comp (AddCircle.parameterDerivativeHs g₀ 0)
  let M := scalarH0ContinuousMul g₀
  let Kh := ‖m‖ * ‖D‖ ^ 2
  let Kl := ‖M‖ * ‖c‖ * ‖D‖ * ‖D₀‖
  let Bh := ‖m‖ * ‖d‖ * ‖D‖
  let Bl := ‖M‖ * ‖c‖ * ‖d‖ * ‖D₀‖
  let K := max Kh Kl
  let B := max Bh Bl
  have hKh : 0 ≤ Kh := by positivity
  have hKl : 0 ≤ Kl := by positivity
  have hBh : 0 ≤ Bh := by positivity
  have hK : 0 ≤ K := hKh.trans (le_max_left _ _)
  have hB : 0 ≤ B := hBh.trans (le_max_left _ _)
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius_lt
    0 (K * A) B le_rfl (mul_nonneg hK A.coe_nonneg) hB hR hη
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hnorm
  have hcommon : Real.sqrt (1 + T) *
      (K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B) < η := by
    simpa only [zero_mul, zero_add, mul_comm B (Real.sqrt T)] using
      hsmall hT.le hTρ hρδ
  let hh := AddCircle.memLp_parameterDriftOperatorHsPi (ι := ι) g₀ (Lp.memLp a₂)
  let hl := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := ι) g₀ (Lp.memLp a₂)
  have hnh : ‖hh.toLp (fun t => AddCircle.parameterDriftOperatorHsPi (ι := ι) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kh * ‖a₂‖ + Real.sqrt T * Bh := AddCircle.norm_toLp_parameterDriftOperatorHsPi_le g₀ a₂
      _ ≤ Kh * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bh :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKh) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) ((norm_nonneg a₂).trans hnorm))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hnl : ‖hl.toLp (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kl * ‖a₂‖ + Real.sqrt T * Bl := AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le g₀ a₂
      _ ≤ Kl * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bl :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKl) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right _ _) ((norm_nonneg a₂).trans hnorm))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hhbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnh (Real.sqrt_nonneg (1 + T))) hcommon
  have hlbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnl (Real.sqrt_nonneg (1 + T))) hcommon
  exact ⟨by simpa only [Lp.norm_toLp] using hhbound,
    by simpa only [Lp.norm_toLp] using hlbound⟩

theorem exists_pos_parameter_derivative_contraction_margin
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    have H := scalarTensorHsInclusion g₀
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    have b := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (laplacianPrincipalCoefficient g₀))
    have Z := vectorTensorHsInclusion (ι := ι) g₀
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : ℝ≥0, ∀ R : ℝ, 0 < R →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
        0 < T → T ≤ ρ → ρ ≤ δ →
        ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - b‖ ≤ ε) →
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
        ∃ C₂h C₂l : ℝ≥0,
          (∀ᵐ t ∂timeMeasure T,
            ‖parameterPrincipalOperatorHsPi (ι := ι) g₀ (H (a₂ t))‖ ≤ C₂h) ∧
          (∀ᵐ t ∂timeMeasure T,
            ‖Z.comp (parameterPrincipalOperatorH0Pi (ι := ι) g₀ (H (a₂ t)))‖ ≤ C₂l) ∧
          (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm
            (fun t => parameterDriftOperatorHsPi (ι := ι) g₀ (a₂ t))
            2 (timeMeasure T)).toReal ≤ q ∧
          (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm
            (fun t => Z.comp (parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t)))
            2 (timeMeasure T)).toReal < 1 := by
  intro H b Z
  have hη : 0 < q / 3 := by positivity
  obtain ⟨ε, hε, hp⟩ := exists_pos_parameter_principal_operator_norm_le (ι := ι) g₀
    (q / 3) hη
  refine ⟨ε, hε, ?_⟩
  intro A R hR
  apply Exists.elim (exists_pos_parameter_drift_operator_norm_lt (ι := ι)
    g₀ A (q / 3) hη hR)
  intro δ hδdata
  have hδ := hδdata.1
  have hδR := hδdata.2.1
  have hδ1 := hδdata.2.2.1
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  have hT1 : T ≤ 1 := hTρ.trans (hρδ.trans hδ1)
  obtain ⟨hdh, hdl⟩ := hδdata.2.2.2 hT hTρ hρδ a₂ hnorm
  let C₂ : ℝ≥0 := ⟨q / 3, hη.le⟩
  have hph : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorHsPi (ι := ι) g₀ (H (a₂ t))‖ ≤ C₂ := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).1
  have hpl : ∀ᵐ t ∂timeMeasure T,
      ‖parameterPrincipalOperatorH0Pi (ι := ι) g₀ (H (a₂ t))‖ ≤ C₂ := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).2
  have hprincipal : (C₂ : ℝ) * (1 + T) ≤ 2 * q / 3 := by
    calc
      (C₂ : ℝ) * (1 + T) ≤ (q / 3) * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hT1) hη.le
      _ = 2 * q / 3 := by ring
  have hmargin : (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm
      (fun t => parameterDriftOperatorHsPi (ι := ι) g₀ (a₂ t))
      2 (timeMeasure T)).toReal ≤ q := by
    apply le_of_lt
    calc
      _ < 2 * q / 3 + q / 3 := add_lt_add_of_le_of_lt hprincipal hdh
      _ = q := by ring
  have hsmalll : (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      ‖(memLp_parameterDriftOperatorH0Pi (ι := ι) g₀ (Lp.memLp a₂)).toLp
        (fun t => parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t))‖ < q := by
    rw [Lp.norm_toLp]
    calc
      _ < 2 * q / 3 + q / 3 := add_lt_add_of_le_of_lt hprincipal hdl
      _ = q := by ring
  obtain ⟨hpl', hsmalll'⟩ := parameter_derivative_h0_normalized_contraction (ι := ι)
    g₀ a₂ C₂ hpl hsmalll
  exact ⟨C₂, C₂, hph, hpl', hmargin, hsmalll'.trans hq1⟩

theorem exists_pos_parameter_derivative_translated_margin_radius
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (A Cα : ℝ≥0) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (Jn : ℝ) (hJn : 0 ≤ Jn) :
    have H := scalarTensorHsInclusion g₀
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    have b := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (laplacianPrincipalCoefficient g₀))
    have Z := vectorTensorHsInclusion (ι := ι) g₀
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R / 2 ∧ δ ≤ 1 ∧ 2 * Jn * δ ≤ r ∧
      ∀ {ρ T : ℝ}, 0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - b‖ ≤ (Cα : ℝ) * (2 * δ)) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂h C₂l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T,
          ‖parameterPrincipalOperatorHsPi (ι := ι) g₀ (H (a₂ t))‖ ≤ C₂h) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖Z.comp (parameterPrincipalOperatorH0Pi (ι := ι) g₀ (H (a₂ t)))‖ ≤ C₂l) ∧
        (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm
          (fun t => parameterDriftOperatorHsPi (ι := ι) g₀ (a₂ t))
          2 (timeMeasure T)).toReal ≤ q ∧
        (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) * (eLpNorm
          (fun t => Z.comp (parameterDriftOperatorH0Pi (ι := ι) g₀ (a₂ t)))
          2 (timeMeasure T)).toReal < 1 := by
  intro H b Z
  obtain ⟨ε, hε, hεcontract⟩ := exists_pos_parameter_derivative_contraction_margin (ι := ι)
    g₀ q hq hq1
  let r₀ := min (R / 2) (min (r / (2 * (1 + Jn))) (ε / (2 * (1 + (Cα : ℝ)))))
  have hr₀ : 0 < r₀ := by dsimp only [r₀]; positivity
  have hrR : r₀ ≤ R / 2 := min_le_left _ _
  have hrJ : 2 * Jn * r₀ ≤ r := by
    have hp : r₀ ≤ r / (2 * (1 + Jn)) := (min_le_right _ _).trans (min_le_left _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + Jn))).mp hp
    nlinarith
  have hrα : (Cα : ℝ) * (2 * r₀) ≤ ε := by
    have hp : r₀ ≤ ε / (2 * (1 + (Cα : ℝ))) := (min_le_right _ _).trans (min_le_right _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + (Cα : ℝ)))).mp hp
    nlinarith [Cα.coe_nonneg]
  obtain ⟨δ, hδ, hδr, hδ1, hcontract⟩ := hεcontract A r₀ hr₀
  refine ⟨δ, hδ, hδr.trans hrR, hδ1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hδr (by positivity)).trans hrJ
  · intro ρ T hT hTρ hρδ a₂ hclose hnorm
    apply hcontract hT hTρ hρδ a₂ ?_ hnorm
    filter_upwards [hclose] with t ht
    exact ht.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hδr (by norm_num : (0 : ℝ) ≤ 2)) Cα.coe_nonneg).trans hrα)

end AddCircle
