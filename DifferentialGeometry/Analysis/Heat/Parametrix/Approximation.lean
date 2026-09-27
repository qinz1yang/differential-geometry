import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import DifferentialGeometry.Analysis.Heat.Kernel.GaussianApproximation
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.PolarFramed
import DifferentialGeometry.Analysis.Heat.Parametrix.Cutoff
import DifferentialGeometry.Geometry.Exponential.NormalChartCompatibility
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I ∞ M] in
private theorem param_measurableEmbedding [T2Space M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB : MeasurableSet B) (hB_source : B ⊆ Ψ.source) :
    MeasurableEmbedding (fun w : B => Ψ (w : E)) where
  injective u v huv := Subtype.ext <|
    Ψ.toPartialEquiv.injOn (hB_source u.2) (hB_source v.2) huv
  measurable :=
    (continuousOn_iff_continuous_domRestrict.mp
      (Ψ.contMDiffOn_toFun.continuousOn.mono hB_source)).measurable
  measurableSet_image' := by
    intro C hC
    have hcoeC : MeasurableSet (((↑) : B → E) '' C) := hB.subtype_image hC
    have hsource : ((↑) : B → E) '' C ⊆ Ψ.source := by
      rintro _ ⟨w, _, rfl⟩
      exact hB_source w.2
    simpa only [Function.comp_apply, Set.image_image] using
      measurableSet_image_param_global (I := I) Ψ hcoeC hsource

private theorem map_paramDensity_eq_restrict
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB : MeasurableSet B) (hB_source : B ⊆ Ψ.source) :
    Measure.map (fun w : B => Ψ (w : E))
        (Measure.comap ((↑) : B → E)
          ((modelHaar (E := E)).withDensity
            (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w)))) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (Ψ '' B) := by
  let ν : Measure E := (modelHaar (E := E)).withDensity
    (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
  have hΨB := param_measurableEmbedding Ψ hB hB_source
  apply Measure.ext_of_lintegral
  intro F hF
  rw [hΨB.lintegral_map]
  rw [← (MeasurableEmbedding.subtype_coe hB).lintegral_map
    (μ := Measure.comap ((↑) : B → E) ν) (fun w : E => F (Ψ w))]
  rw [map_comap_subtype_coe hB]
  have hd : AEMeasurable (fun w => ENNReal.ofReal (paramDensity g Ψ w))
      ((modelHaar (E := E)).restrict B) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((paramDensity_contOn g Ψ).mono hB_source).aemeasurable hB)
  rw [riemVol_param_lint g Ψ F hB hB_source]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
    (modelHaar (E := E)) hd (fun w => F (Ψ w)) hB
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))

private theorem integral_image_param_eq
    [T2Space M] [SigmaCompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (f : M → V) {B : Set E} (hB : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    ∫ y in Ψ '' B, f y ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ w in B, paramDensity (I := I) g Ψ w • f (Ψ w)
        ∂modelHaar (E := E) := by
  let ν : Measure E := (modelHaar (E := E)).withDensity
    (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
  have hΨB := param_measurableEmbedding Ψ hB hB_source
  rw [← map_paramDensity_eq_restrict g Ψ hB hB_source, hΨB.integral_map]
  rw [← (MeasurableEmbedding.subtype_coe hB).integral_map
    (μ := Measure.comap ((↑) : B → E) ν) (fun w : E => f (Ψ w))]
  rw [map_comap_subtype_coe hB]
  have hd : AEMeasurable (fun w => ENNReal.ofReal (paramDensity g Ψ w))
      ((modelHaar (E := E)).restrict B) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((paramDensity_contOn g Ψ).mono hB_source).aemeasurable hB)
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hB]
  apply setIntegral_congr_fun hB
  intro w hw
  dsimp only
  rw [ENNReal.toReal_ofReal (paramDensity_pos g Ψ (hB_source hw)).le]

end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Analysis.HeatEquation

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem integral_image_framed_eq_volume
    (g : SmoothRiemannianMetric I M) (p : M) (f : M → ℝ)
    {B : Set E} (hB : MeasurableSet B)
    (hBs : B ⊆ (framedExpDiffeo g p).source) :
    ∫ y in framedExpDiffeo g p '' B, f y ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ z in B, (paramDensity g (framedExpDiffeo g p) z /
        paramDensity g (framedExpDiffeo g p) 0) * f (framedExpDiffeo g p z) := by
  have hd : 0 < paramDensity g (framedExpDiffeo g p) 0 :=
    paramDensity_pos g (framedExpDiffeo g p) (zero_mem_framedExp_source g p)
  rw [integral_image_param_eq g (framedExpDiffeo g p) f hB hBs]
  conv_rhs => rw [← framedDens_haar g p]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hd.le]
  change _ = paramDensity g (framedExpDiffeo g p) 0 * _
  rw [← integral_const_mul]
  apply setIntegral_congr_fun hB
  intro z hz
  simp only [smul_eq_mul]
  field_simp

omit [T2Space M] [SigmaCompactSpace M] in
private theorem framed_cutoff_pullback
    (g : SmoothRiemannianMetric I M) (p : M) (χ : M → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (framedExpDiffeo g p).target) :
    let Ψ := framedExpDiffeo g p
    let η := Ψ.source.indicator (fun z => χ (Ψ z))
    Continuous η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ψ.source ∧
      tsupport η ⊆ Ψ.symm '' tsupport χ ∧
      (∀ y ∈ Ψ.target, η (Ψ.symm y) = χ y) := by
  classical
  let Ψ := framedExpDiffeo g p
  let η := Ψ.source.indicator (fun z => χ (Ψ z))
  let K := Ψ.symm '' tsupport χ
  have hK : IsCompact K := hc.image_of_continuousOn
    (Ψ.contMDiffOn_invFun.continuousOn.mono hs)
  have hKs : K ⊆ Ψ.source := by
    rintro z ⟨y, hy, rfl⟩
    exact Ψ.map_target (hs hy)
  have hsη : Function.support η ⊆ K := by
    intro z hz
    have hzS : z ∈ Ψ.source := by
      by_contra h
      exact hz (by simp [η, h])
    have hχz : χ (Ψ z) ≠ 0 := by simpa only [Function.mem_support, η, indicator_of_mem hzS] using hz
    refine ⟨Ψ z, subset_closure hχz, ?_⟩
    exact Ψ.left_inv hzS
  have htη : tsupport η ⊆ K := hK.isClosed.closure_subset_iff.mpr hsη
  refine ⟨?_, IsCompact.of_isClosed_subset hK (isClosed_tsupport η) htη,
    htη.trans hKs, htη, ?_⟩
  · apply continuous_of_tsupport
    intro z hz
    have hzS := hKs (htη hz)
    have heq : η =ᶠ[𝓝 z] (fun z => χ (Ψ z)) := by
      filter_upwards [Ψ.open_source.mem_nhds hzS] with w hw
      exact indicator_of_mem hw _
    exact (hχ.continuousAt.comp (Ψ.contMDiffOn_toFun.continuousOn.continuousAt
      (Ψ.open_source.mem_nhds hzS))).congr_of_eventuallyEq heq
  · intro y hy
    have hyS := Ψ.map_target hy
    change Ψ.source.indicator (fun z => χ (Ψ z)) (Ψ.symm y) = χ y
    have hi : Ψ.source.indicator (fun z => χ (Ψ z)) (Ψ.symm.toPartialEquiv y) =
        χ (Ψ (Ψ.symm.toPartialEquiv y)) := indicator_of_mem hyS _
    exact hi.trans (congrArg χ (Ψ.right_inv hy))

private theorem tendsto_integral_framed_gaussian_polynomial
    (g : SmoothRiemannianMetric I M) (p : M) (N : ℕ)
    (χ : E → ℝ) (a : ℕ → M → ℝ) (f : M → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hχs : tsupport χ ⊆ (framedExpDiffeo g p).source)
    (ha : ∀ k ≤ N, ∀ z ∈ tsupport χ, ContinuousAt (a k) (framedExpDiffeo g p z))
    (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y in (framedExpDiffeo g p).target,
      χ ((framedExpDiffeo g p).symm y) *
        Parabolic.Euclidean.heatKernel t (-((framedExpDiffeo g p).symm y)) *
        (∑ k ∈ Finset.range (N + 1), t ^ k * a k y) * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (a 0 p * f p)) := by
  let Ψ := framedExpDiffeo g p
  let d := paramDensity g Ψ
  have hd : 0 < d 0 := paramDensity_pos g Ψ (zero_mem_framedExp_source g p)
  let A : ℕ → E → ℝ := fun k z => (d z / d 0) * a k (Ψ z) * f (Ψ z)
  have hA : ∀ k ≤ N, ∀ z ∈ tsupport χ, ContinuousAt (A k) z := by
    intro k hk z hz
    have hΨ := Ψ.contMDiffOn_toFun.continuousOn.continuousAt
      (Ψ.open_source.mem_nhds (hχs hz))
    have hdz := (paramDensity_contOn g Ψ).continuousAt
      (Ψ.open_source.mem_nhds (hχs hz))
    exact ((hdz.div_const (d 0)).mul ((ha k hk z hz).comp hΨ)).mul
      (hf.continuousAt.comp hΨ)
  have hlim := Parabolic.Euclidean.tendsto_integral_heatKernel_smul_cutoff_polynomial
    N χ A (0 : E) hχ hχc hχ0 hA
  have hA0 : A 0 0 = a 0 p * f p := by
    simp only [A, Ψ, framedExp_zero]
    rw [div_self hd.ne', one_mul]
  rw [hA0] at hlim
  apply hlim.congr'
  filter_upwards with t
  rw [show Ψ.target = Ψ '' Ψ.source from Ψ.toPartialEquiv.image_source_eq_target.symm]
  rw [integral_image_framed_eq_volume g p _ Ψ.open_source.measurableSet Subset.rfl]
  have heq : (∫ z in Ψ.source,
      (d z / d 0) * (χ (Ψ.symm (Ψ z)) *
        Parabolic.Euclidean.heatKernel t (-(Ψ.symm (Ψ z))) *
        (∑ k ∈ Finset.range (N + 1), t ^ k * a k (Ψ z)) * f (Ψ z))) =
      ∫ z in Ψ.source, Parabolic.Euclidean.heatKernel t (-z) *
        ∑ k ∈ Finset.range (N + 1), t ^ k * (χ z * A k z) := by
    apply setIntegral_congr_fun Ψ.open_source.measurableSet
    intro z hz
    dsimp only
    have hinv : Ψ.symm.toPartialEquiv (Ψ.toPartialEquiv z) = z := Ψ.left_inv hz
    rw [hinv]
    simp only [A, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change (∫ z, Parabolic.Euclidean.heatKernel t (0 - z) •
      ∑ k ∈ Finset.range (N + 1), t ^ k • (χ z • A k z)) = _
  rw [heq]
  simp only [zero_sub, smul_eq_mul]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hχz : χ z = 0 := by
    by_contra hn
    exact hz (hχs (subset_closure hn))
  simp only [hχz, zero_mul, mul_zero, Finset.sum_const_zero]

private theorem tendsto_integral_gaussian_polynomial_manifold_cutoff
    (g : SmoothRiemannianMetric I M) (p : M) (N : ℕ)
    (χ : M → ℝ) (a : ℕ → M → ℝ) (f : M → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ p = 1)
    (hχs : tsupport χ ⊆ (framedExpDiffeo g p).target)
    (ha : ∀ k ≤ N, ∀ y ∈ tsupport χ, ContinuousAt (a k) y)
    (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y,
      χ y * Parabolic.Euclidean.heatKernel t (-((framedExpDiffeo g p).symm y)) *
        (∑ k ∈ Finset.range (N + 1), t ^ k * a k y) * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (a 0 p * f p)) := by
  classical
  let Ψ := framedExpDiffeo g p
  let η := Ψ.source.indicator (fun z => χ (Ψ z))
  obtain ⟨hη, hηc, hηs, hηχ, hηeq⟩ := framed_cutoff_pullback g p χ hχ hχc hχs
  have hη0 : η 0 = 1 := by
    dsimp only [η, Ψ]
    rw [indicator_of_mem (zero_mem_framedExp_source g p), framedExp_zero, hχ0]
  have hA : ∀ k ≤ N, ∀ z ∈ tsupport η, ContinuousAt (a k) (Ψ z) := by
    intro k hk z hz
    obtain ⟨y, hy, hyz⟩ := hηχ hz
    have hyT := hχs hy
    have hΨz : Ψ z = y := by
      rw [← hyz]
      exact Ψ.right_inv hyT
    rw [hΨz]
    exact ha k hk y hy
  have hlim := tendsto_integral_framed_gaussian_polynomial g p N η a f hη hηc hη0 hηs hA hf
  apply hlim.congr'
  filter_upwards with t
  calc
    _ = ∫ y in Ψ.target, χ y *
        Parabolic.Euclidean.heatKernel t (-(Ψ.symm y)) *
          (∑ k ∈ Finset.range (N + 1), t ^ k * a k y) * f y
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      apply setIntegral_congr_fun Ψ.open_target.measurableSet
      intro y hy
      dsimp only
      have hηy : η ((framedExpDiffeo g p).symm.toPartialEquiv y) = χ y := hηeq y hy
      rw [hηy]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hyχ : χ y = 0 := by
        by_contra hn
        exact hy (hχs (subset_closure hn))
      simp only [hyχ, zero_mul]

end DifferentialGeometry.Analysis.HeatEquation

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem heatKernel_eq_rpow {t : ℝ} (ht : 0 < t) (z : E) :
    heatKernel t z = (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-‖z‖ ^ 2 / (4 * t)) := by
  have hsqrt : (Real.sqrt t) ^ Module.finrank ℝ E =
      t ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    rw [Real.rpow_div_two_eq_sqrt _ ht.le, Real.rpow_natCast]
  unfold heatKernel heatScale baseHeat baseHeatMass
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt ht.le, hsqrt]
  have he : -(4 : ℝ)⁻¹ * (t⁻¹ * ‖z‖ ^ 2) = -‖z‖ ^ 2 / (4 * t) := by ring
  rw [he]
  have hpi : Real.pi / (4 : ℝ)⁻¹ = 4 * Real.pi := by ring
  rw [hpi, ← mul_assoc]
  congr 1
  rw [neg_div, Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) ht.le,
    mul_inv_rev]

end DifferentialGeometry.Analysis.Parabolic.Euclidean

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius mem_expMapDiffeo_source_of_norm_lt_radius)
open Geometry.Riemannian.Exponential Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem branch_inv_eq_normalChart_of_norm_lt
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {q : M} (hq : q ∈ B.dom)
    (hsmall : ‖B.inv q‖ < expMapC2Radius g p) :
    B.inv q = normalChartAt g p q := by
  have hs := mem_expMapDiffeo_source_of_norm_lt_radius g p hsmall
  have hexp : expMapDiffeo g p (B.inv q) = q :=
    (expMapDiffeo_apply_eq g p hs).trans
      ((congrFun (expMap_eq_expMapIntrinsic g hEnorm p) _).trans (B.right_inv hq))
  have hinv : normalChartAt g p (expMapDiffeo g p (B.inv q)) = B.inv q :=
    (expMapDiffeo g p).left_inv hs
  rw [hexp] at hinv
  exact hinv.symm

private theorem branchEnergy_eq_framed_norm_sq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {q : M} (hq : q ∈ B.dom)
    (hsmall : ‖B.inv q‖ < expMapC2Radius g p) :
    branchEnergy g B q = ‖(framedExpDiffeo g p).symm q‖ ^ 2 / 2 := by
  rw [branchEnergy, branch_inv_eq_normalChart_of_norm_lt B hq hsmall]
  change (1 / 2 : ℝ) * g.inner p
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (normalChartAt g p q))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (normalChartAt g p q)) = _
  have hf := normalFrame_normSq g p ((framedExpDiffeo g p).symm q)
  change g.inner p
      ((normalFrame g p) ((normalFrame g p).symm
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (normalChartAt g p q))))
      ((normalFrame g p) ((normalFrame g p).symm
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (normalChartAt g p q)))) = _ at hf
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  rw [hf]
  ring

theorem heatParametrix_eq_framed_gaussian_polynomial
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) {q : M} (hq : q ∈ B.dom)
    (hsmall : ‖B.inv q‖ < expMapC2Radius g p) {t : ℝ} (ht : 0 < t) :
    heatParametrix g B N t q =
      Parabolic.Euclidean.heatKernel t (-((framedExpDiffeo g p).symm q)) *
        ∑ k ∈ Finset.range (N + 1), t ^ k * heatParametrixCoefficient g p k q := by
  rw [heatParametrix, Parabolic.Euclidean.heatKernel_eq_rpow ht, norm_neg,
    branchEnergy_eq_framed_norm_sq B hq hsmall]
  have he : -((‖(framedExpDiffeo g p).symm q‖ ^ 2 / 2)) / (2 * t) =
      -‖(framedExpDiffeo g p).symm q‖ ^ 2 / (4 * t) := by ring
  rw [he]

open MeasureTheory Filter
open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tendsto_integral_cutoffHeatParametrix_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) (χ f : M → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ p = 1)
    (hχs : tsupport χ ⊆ B.dom)
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y, cutoffHeatParametrix g B χ N t y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
      (𝓝[>] 0) (𝓝 (f p)) := by
  have hC (y : M) (hy : y ∈ tsupport χ) : y ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
    have hs := mem_expMapDiffeo_source_of_norm_lt_radius g p (hsmall y hy)
    have hexp : expMapDiffeo g p (B.inv y) = y :=
      (expMapDiffeo_apply_eq g p hs).trans
        ((congrFun (expMap_eq_expMapIntrinsic g hEnorm p) _).trans (B.right_inv (hχs hy)))
    refine ⟨?_, ?_⟩
    · rw [← hexp]
      exact (expMapDiffeo g p).map_source hs
    · change normalChartAt g p y ∈ Metric.ball (0 : E) (expMapC2Radius g p)
      rw [← branch_inv_eq_normalChart_of_norm_lt B (hχs hy) (hsmall y hy)]
      simpa only [Metric.mem_ball, dist_zero_right] using hsmall y hy
  have hV : IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hA : ∀ k ≤ N, ∀ y ∈ tsupport χ, ContinuousAt (heatParametrixCoefficient g p k) y := by
    intro k hk y hy
    exact ((contMDiffOn_heatParametrixCoefficient g p k y (hC y hy)).contMDiffAt
      (hV.mem_nhds (hC y hy))).continuousAt
  have hT : tsupport χ ⊆ (framedExpDiffeo g p).target := fun y hy => (hC y hy).1
  have hlim := tendsto_integral_gaussian_polynomial_manifold_cutoff g p N χ
    (heatParametrixCoefficient g p) f hχ hχc hχ0 hT hA hf
  rw [heatParametrixCoefficient_zero_centre, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply integral_congr_ae
  filter_upwards with y
  change _ = (χ y * heatParametrix g B N t y) * f y
  by_cases hy : y ∈ tsupport χ
  · rw [heatParametrix_eq_framed_gaussian_polynomial B N (hχs hy) (hsmall y hy) ht]
    ring
  · have hχy := image_eq_zero_of_notMem_tsupport hy
    simp only [hχy, zero_mul]

theorem eventually_integral_norm_cutoffHeatParametrix_le_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) (χ : M → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ p = 1)
    (hχs : tsupport χ ⊆ B.dom)
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ y, ‖cutoffHeatParametrix g B χ N t y‖
      ∂riemannianVolumeMeasure (I := I) (M := M) g ≤ 2 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let a := heatParametrixCoefficient g p
  let Ψ := framedExpDiffeo g p
  let G : ℝ → M → ℝ := fun t y => ‖χ y‖ *
    Parabolic.Euclidean.heatKernel t (-(Ψ.symm y)) *
      (∑ k ∈ Finset.range (N + 1), t ^ k * ‖a k y‖)
  have hC (y : M) (hy : y ∈ tsupport χ) : y ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
    have hs := mem_expMapDiffeo_source_of_norm_lt_radius g p (hsmall y hy)
    have hexp : expMapDiffeo g p (B.inv y) = y :=
      (expMapDiffeo_apply_eq g p hs).trans
        ((congrFun (expMap_eq_expMapIntrinsic g hEnorm p) _).trans (B.right_inv (hχs hy)))
    refine ⟨?_, ?_⟩
    · rw [← hexp]
      exact (expMapDiffeo g p).map_source hs
    · change normalChartAt g p y ∈ Metric.ball (0 : E) (expMapC2Radius g p)
      rw [← branch_inv_eq_normalChart_of_norm_lt B (hχs hy) (hsmall y hy)]
      simpa only [Metric.mem_ball, dist_zero_right] using hsmall y hy
  have hV : IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have ha : ∀ k, ∀ y ∈ tsupport χ, ContinuousAt (a k) y := by
    intro k y hy
    exact ((contMDiffOn_heatParametrixCoefficient g p k y (hC y hy)).contMDiffAt
      (hV.mem_nhds (hC y hy))).continuousAt
  have hsχ : tsupport (fun y => ‖χ y‖) = tsupport χ := by
    apply congrArg closure
    ext y
    change (‖χ y‖ ≠ 0) ↔ (χ y ≠ 0)
    exact not_congr norm_eq_zero
  have hlim := tendsto_integral_gaussian_polynomial_manifold_cutoff g p N
    (fun y => ‖χ y‖) (fun k y => ‖a k y‖) (fun _ => 1)
    hχ.norm hχc.norm (by simp [hχ0])
    (by
      rw [hsχ]
      exact fun y hy => (hC y hy).1)
    (by
      intro k hk y hy
      rw [hsχ] at hy
      exact (ha k y hy).norm)
    continuous_const
  have hlimG : Tendsto (fun t => ∫ y, G t y ∂μ) (𝓝[>] 0) (𝓝 1) := by
    simpa only [G, μ, a, mul_one, heatParametrixCoefficient_zero_centre, norm_one] using hlim
  have hb := hlimG.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hb, self_mem_nhdsWithin] with t ht htpos
  have hcont : Continuous (G t) := by
    apply continuous_of_tsupport
    intro y hy
    have hyχ : y ∈ tsupport χ := by
      have hh := tsupport_mul_subset_left (tsupport_mul_subset_left hy)
      rwa [hsχ] at hh
    have hcoord := Ψ.contMDiffOn_invFun.continuousOn.continuousAt
      (Ψ.open_target.mem_nhds (hC y hyχ).1)
    have hker : ContinuousAt
        (fun y => Parabolic.Euclidean.heatKernel t (-(Ψ.symm y))) y := by
      have heq : (fun y => Parabolic.Euclidean.heatKernel t (-(Ψ.symm y))) =
          (fun y => (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (-‖Ψ.symm y‖ ^ 2 / (4 * t))) := by
        funext z
        rw [Parabolic.Euclidean.heatKernel_eq_rpow htpos, norm_neg]
      rw [heq]
      exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
        ((hcoord.norm.pow 2).neg.div_const (4 * t)))
    exact (hχ.continuousAt.norm.mul hker).mul
      (tendsto_finsetSum _ (fun k hk => continuousAt_const.mul (ha k y hyχ).norm))
  have hcG : HasCompactSupport (G t) := (hχc.norm.mul_right).mul_right
  have hiG : Integrable (G t) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      g hcont hcG
  have hle (y : M) : ‖cutoffHeatParametrix g B χ N t y‖ ≤ G t y := by
    by_cases hy : y ∈ tsupport χ
    · have hk := Parabolic.Euclidean.heatKernel_nonneg htpos (-(Ψ.symm y))
      rw [cutoffHeatParametrix, heatParametrix_eq_framed_gaussian_polynomial B N
        (hχs hy) (hsmall y hy) htpos, norm_mul, norm_mul, Real.norm_of_nonneg hk]
      change ‖χ y‖ * (Parabolic.Euclidean.heatKernel t (-(Ψ.symm y)) *
        ‖∑ k ∈ Finset.range (N + 1), t ^ k * a k y‖) ≤ _
      have hsum : ‖∑ k ∈ Finset.range (N + 1), t ^ k * a k y‖ ≤
          ∑ k ∈ Finset.range (N + 1), t ^ k * ‖a k y‖ := by
        simpa only [norm_mul, Real.norm_of_nonneg (pow_nonneg htpos.le _)] using
          norm_sum_le (Finset.range (N + 1)) (fun k => t ^ k * a k y)
      simpa only [G, mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum hk) (norm_nonneg (χ y))
    · have hχy := image_eq_zero_of_notMem_tsupport hy
      simp only [cutoffHeatParametrix, G, hχy, zero_mul, norm_zero, le_refl]
  exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    hiG (Filter.Eventually.of_forall hle)).trans ht.le

end DifferentialGeometry.Analysis.HeatEquation
