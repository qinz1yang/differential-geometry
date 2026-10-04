import DifferentialGeometry.Geometry.Metric.ChartDistanceComparison
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import Mathlib.Analysis.Matrix.Order

/-!
# Normalized Hausdorff measure versus Riemannian volume

On a smooth Riemannian manifold whose extended distance is the length distance of `g`
(`IsRiemannianManifold` together with `IsMetricNorm g`), the normalized `n`-dimensional Hausdorff
measure (`n = finrank ℝ E`, Euclidean normalization of
`Analysis/Integration/Measure/NormalizedHausdorffMeasure.lean`) and the chart-density volume
`riemannianVolumeMeasure I M g` are comparable with constant `K ^ n * c` for every `K > 1` and
`c > 1`, on every measurable set. In dimension three the choice `K = 2`, `c = 8` gives the uniform
constant `64` in both directions. The constant is fixed before the manifold, the metric, the
point and any sequence index. Letting `K, c ↓ 1` gives the exact identity
`normalizedHausdorffMeasure n = riemannianVolumeMeasure I M g` of Borel measures.

Route. At a point `p` the chart coordinates are mapped to `EuclideanSpace` by a linear map `L`
with `‖L v‖ = g_p`-norm of `v`, built from a square root of the chart Gram matrix, so that the
image of a set has Lebesgue measure `chartDensity g p p` times its `modelHaar` measure. The
two-sided ambient distance comparison `exists_open_riemannianEDistOf_comparison` (which controls
shortcuts leaving the chart) makes `L ∘ extChartAt I p` and its inverse `K`-Lipschitz near `p`;
continuity of the chart density gives the factor `c`; a countable disjointed cover of the
σ-compact manifold globalizes the estimate.

## Main declarations

* `exists_linearMap_chartGram_isometry`: the Euclidean coordinates of the Gram matrix at `p`.
* `exists_isOpen_normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison`: local version.
* `normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison`: every `K, c > 1`.
* `normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure`,
  `riemannianVolumeMeasure_le_sixtyFour_normalizedHausdorffMeasure`: dimension three, constant
  `64`, measurable sets; the primed versions hold for all sets.
* `normalizedHausdorffMeasure_eq_riemannianVolumeMeasure` (general `n`),
  `normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure`,
  `lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure` (the length distance
  of `g` itself), and the set-level forms `…_apply_eq_…_apply`: the exact identity.
* `collapse_ballVolume_lower_of_normalizedHausdorffMeasure_lower`: a normalized Hausdorff lower
  bound `L` for a metric ball gives the Riemannian `ballVolume` lower bound `L / 64`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix Filter
open scoped Manifold ContDiff Topology ENNReal NNReal MatrixOrder

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Coordinates

/-! ### Countable disjointed covers -/

/-- A comparison of two measures on the measurable subsets of each member of a countable cover
holds on every measurable set. -/
theorem measure_le_mul_of_iUnion_eq_univ {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    (C : ℝ≥0∞) (V : ℕ → Set X) (hV : ∀ k, MeasurableSet (V k)) (hcov : ⋃ k, V k = univ)
    (hloc : ∀ k, ∀ A, MeasurableSet A → A ⊆ V k → μ A ≤ C * ν A)
    {s : Set X} (hs : MeasurableSet s) : μ s ≤ C * ν s := by
  have hD (k : ℕ) : MeasurableSet (s ∩ disjointed V k) :=
    hs.inter (MeasurableSet.disjointed hV k)
  have hdisj : Pairwise (Function.onFun Disjoint fun k => s ∩ disjointed V k) :=
    fun i j hij => ((disjoint_disjointed V) hij).mono inter_subset_right inter_subset_right
  have hs_eq : ⋃ k, s ∩ disjointed V k = s := by
    rw [← inter_iUnion, iUnion_disjointed, hcov, inter_univ]
  rw [← hs_eq, measure_iUnion hdisj hD, measure_iUnion hdisj hD, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun k =>
    hloc k _ (hD k) (inter_subset_right.trans (disjointed_subset V k))

/-- A bound by `ofReal (r ^ n * r) * b` for every `r > 1` gives the bound by `b`. -/
theorem le_of_forall_one_lt_le_ofReal_pow_mul {a b : ℝ≥0∞} (n : ℕ)
    (h : ∀ r : ℝ, 1 < r → a ≤ ENNReal.ofReal (r ^ n * r) * b) : a ≤ b := by
  have hcont : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ n * r)) (𝓝[>] 1) (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ n * r)) (𝓝 1)
        (𝓝 (ENNReal.ofReal (1 ^ n * 1))) :=
      (ENNReal.continuous_ofReal.comp ((continuous_pow n).mul continuous_id)).tendsto 1
    rw [one_pow, one_mul, ENNReal.ofReal_one] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hlim := ENNReal.Tendsto.mul_const hcont (Or.inl one_ne_zero) (b := b)
  rw [one_mul] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun r hr => h r hr)

/-! ### Euclidean coordinates for the Gram matrix at a point -/

section Gram

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
theorem sum_toEuclidean_smul_chartModelBasis [FiniteDimensional ℝ E] (v : E) :
    ∑ i, (WithLp.ofLp (toEuclidean (E := E) v)) i • chartModelBasis E i = v := by
  simp only [chartModelBasis_apply, ← map_smul, ← map_sum]
  conv_rhs => rw [← (toEuclidean (E := E)).symm_apply_apply v]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_transpose_mul_self_eq_chartGramMatrix (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ R : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ,
      Rᵀ * R = chartGramMatrix g p p := by
  have hG : (chartGramMatrix g p p).PosDef :=
    chartGramMatrix_posDef (I := I) g p (mem_baseSet_trivializationAt E (TangentSpace I) p)
  refine ⟨CFC.sqrt (chartGramMatrix g p p), ?_⟩
  have h1 := CFC.sqrt_mul_sqrt_self (chartGramMatrix g p p) hG.posSemidef.nonneg
  have h2 : (CFC.sqrt (chartGramMatrix g p p))ᴴ = CFC.sqrt (chartGramMatrix g p p) :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian
  rw [conjTranspose_eq_transpose_of_trivial] at h2
  rw [h2, h1]

theorem inner_symmL_self_eq_dotProduct_chartGramMatrix (g : SmoothRiemannianMetric I M) (p : M)
    (v : E) :
    let S := (trivializationAt E (TangentSpace I) p).symmL ℝ p
    g.inner p (S v) (S v) =
      WithLp.ofLp (toEuclidean (E := E) v) ⬝ᵥ
        chartGramMatrix g p p *ᵥ WithLp.ofLp (toEuclidean (E := E) v) := by
  intro S
  have h := chartGramMatrix_dotProduct_mulVec (I := I) g p p
    (WithLp.ofLp (toEuclidean (E := E) v))
  simp only [star_trivial] at h
  rw [h]
  have hv : S v = ∑ i, (WithLp.ofLp (toEuclidean (E := E) v)) i •
      chartBasisVecFiber (I := I) p i p := by
    conv_lhs => rw [← sum_toEuclidean_smul_chartModelBasis v]
    simp only [map_sum, map_smul]
    rfl
  rw [hv]

/-- Euclidean coordinates at `p`: a linear map `L` from the model space to `EuclideanSpace`
whose norm is the `g_p`-norm of the chart vector, and which multiplies `modelHaar` by the chart
density at `p`. -/
theorem exists_linearMap_chartGram_isometry (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ v : E, ‖L v‖ = Real.sqrt (g.inner p
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p v)
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p v))) ∧
      ∀ X : Set E, volume (L '' X) =
        ENNReal.ofReal (chartDensity g p p) * modelHaar (E := E) X := by
  obtain ⟨R, hR⟩ := exists_transpose_mul_self_eq_chartGramMatrix (I := I) g p
  let T : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := Matrix.toEuclideanLin R
  refine ⟨T.comp (toEuclidean (E := E) : E →L[ℝ] _).toLinearMap, ?_, ?_⟩
  · intro v
    rw [inner_symmL_self_eq_dotProduct_chartGramMatrix (I := I) g p v, ← hR,
      norm_eq_sqrt_real_inner]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have key (x : Fin (Module.finrank ℝ E) → ℝ) :
        (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ (Rᵀ * R) *ᵥ x := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
    simp only [LinearMap.comp_apply, T, Matrix.toLpLin_apply, star_trivial]
    exact key _
  · intro X
    have hdet : LinearMap.det T = R.det := by
      simp only [T]
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    have hdens : chartDensity g p p = |R.det| := by
      rw [chartDensity, ← hR, Matrix.det_mul, Matrix.det_transpose, ← sq,
        Real.sqrt_sq_eq_abs]
    have hX : volume ((toEuclidean (E := E)) '' X) = modelHaar (E := E) X := by
      rw [← map_toEuclidean_modelHaar_eq_volume (E := E)]
      exact ((toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.map_apply
        (μ := modelHaar (E := E)) _).trans
        (congrArg _ ((toEuclidean (E := E)).injective.preimage_image X))
    rw [LinearMap.coe_comp, Set.image_comp, Measure.addHaar_image_linearMap, hdet, hdens]
    exact congrArg _ hX

end Gram

/-! ### Chart density bounds for the chart-local measure -/

section ChartLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartLocalMeasure_apply_eq_setLIntegral (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA : MeasurableSet A) :
    chartLocalMeasure (I := I) g p A =
      ∫⁻ y in (extChartAt I p).symm ⁻¹' A,
        ENNReal.ofReal (chartDensity g p ((extChartAt I p).symm y))
        ∂((modelHaar (E := E)).restrict (extChartAt I p).target) := by
  have haem : AEMeasurable (extChartAt I p).symm
      (((modelHaar (E := E)).restrict (extChartAt I p).target).withDensity
        (fun y : E => ENNReal.ofReal (chartDensity g p ((extChartAt I p).symm y)))) :=
    (aemeasurable_extChartAt_symm_restrict_target (I := I) p).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [chartLocalMeasure_def, Measure.map_apply_of_aemeasurable haem hA, withDensity_apply']

theorem chartLocalMeasure_le_ofReal_mul_modelHaar (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ (extChartAt I p).source) {b : ℝ}
    (hb : ∀ x ∈ A, chartDensity g p x ≤ b) :
    chartLocalMeasure (I := I) g p A ≤
      ENNReal.ofReal b * modelHaar (E := E) ((extChartAt I p) '' A) := by
  have ht := measurableSet_extChartAt_target (I := I) p
  rw [chartLocalMeasure_apply_eq_setLIntegral g p hA]
  calc
    _ ≤ ∫⁻ _ in (extChartAt I p).symm ⁻¹' A, ENNReal.ofReal b
          ∂((modelHaar (E := E)).restrict (extChartAt I p).target) := by
      apply setLIntegral_mono_ae measurable_const.aemeasurable
      filter_upwards [ae_restrict_mem ht] with y _ hyA
      exact ENNReal.ofReal_le_ofReal (hb _ hyA)
    _ = ENNReal.ofReal b * modelHaar (E := E) ((extChartAt I p) '' A) := by
      rw [setLIntegral_const, Measure.restrict_apply' ht,
        (extChartAt I p).image_eq_target_inter_inv_preimage hAs, inter_comm]

theorem ofReal_mul_modelHaar_le_chartLocalMeasure (g : SmoothRiemannianMetric I M) (p : M)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ (extChartAt I p).source) {a c : ℝ}
    (hc : 0 ≤ c) (ha : ∀ x ∈ A, a ≤ c * chartDensity g p x) :
    ENNReal.ofReal a * modelHaar (E := E) ((extChartAt I p) '' A) ≤
      ENNReal.ofReal c * chartLocalMeasure (I := I) g p A := by
  have ht := measurableSet_extChartAt_target (I := I) p
  rw [chartLocalMeasure_apply_eq_setLIntegral g p hA,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    ENNReal.ofReal a * modelHaar (E := E) ((extChartAt I p) '' A) =
        ∫⁻ _ in (extChartAt I p).symm ⁻¹' A, ENNReal.ofReal a
          ∂((modelHaar (E := E)).restrict (extChartAt I p).target) := by
      rw [setLIntegral_const, Measure.restrict_apply' ht,
        (extChartAt I p).image_eq_target_inter_inv_preimage hAs, inter_comm]
    _ ≤ _ := by
      apply setLIntegral_mono_ae
      · exact ((aemeasurable_chartDensity_symm_pullback (I := I) g p).mono_measure
          Measure.restrict_le_self).const_mul _
      filter_upwards [ae_restrict_mem ht] with y _ hyA
      rw [← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (ha _ hyA)

end ChartLevel

/-! ### The local and global comparison -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Geometry.Riemannian

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
theorem edist_eq_riemannianEDistOf_of_isMetricNorm (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x y : M) :
    edist x y = riemannianEDistOf (I := I) g x y := by
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, IsRiemannianManifold.out (I := I)]

/-- Local two-sided comparison: around every point, on every measurable subset of a
neighborhood, the normalized Hausdorff measure and the Riemannian volume agree up to the factor
`K ^ n * c`. -/
theorem exists_isOpen_normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {K c : ℝ} (hK : 1 < K) (hc : 1 < c) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ A : Set M, MeasurableSet A → A ⊆ U →
      normalizedHausdorffMeasure (Module.finrank ℝ E) A ≤
          ENNReal.ofReal (K ^ Module.finrank ℝ E * c) * riemannianVolumeMeasure I M g A ∧
      riemannianVolumeMeasure I M g A ≤
          ENNReal.ofReal (K ^ Module.finrank ℝ E * c) *
            normalizedHausdorffMeasure (Module.finrank ℝ E) A := by
  classical
  obtain ⟨U₁, hpU₁, hU₁src, hcmp⟩ := exists_open_riemannianEDistOf_comparison g p hK
  obtain ⟨L, hLnorm, hLvol⟩ := exists_linearMap_chartGram_isometry (I := I) g p
  let φ := extChartAt I p
  let F : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun x => L (φ x)
  have hFedist (x y : M) : edist (F x) (F y) =
      ENNReal.ofReal (Real.sqrt (g.inner p
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p (φ y - φ x))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p (φ y - φ x)))) := by
    rw [edist_comm, edist_dist, dist_eq_norm, ← map_sub, hLnorm]
  have hd (x y : M) := edist_eq_riemannianEDistOf_of_isMetricNorm g hEnorm x y
  have hFlip : LipschitzOnWith K.toNNReal F U₁ := by
    intro x hx y hy
    rw [hFedist, hd]
    exact (hcmp x hx y hy).1
  have hinj : InjOn F U₁ := by
    intro x hx y hy hxy
    have h2 := (hcmp x hx y hy).2
    rw [← hFedist, hxy, edist_self, mul_zero, ← hd] at h2
    exact edist_le_zero.mp h2
  have : Nonempty M := ⟨p⟩
  let G := Function.invFunOn F U₁
  have hGmem {y} (hy : y ∈ F '' U₁) : G y ∈ U₁ := Function.invFunOn_mem hy
  have hGeq {y} (hy : y ∈ F '' U₁) : F (G y) = y := Function.invFunOn_eq hy
  have hGlip : LipschitzOnWith K.toNNReal G (F '' U₁) := by
    intro y₁ hy₁ y₂ hy₂
    have h2 := (hcmp (G y₁) (hGmem hy₁) (G y₂) (hGmem hy₂)).2
    rw [← hFedist, hGeq hy₁, hGeq hy₂, ← hd] at h2
    exact h2
  let ρ := chartDensity g p
  have hpbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) p
  have hρp : 0 < ρ p := chartDensity_pos (I := I) g p hpbase
  have hρcont : ContinuousAt ρ p := (chartDensity_continuousOn (I := I) g p).continuousAt
    ((trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds hpbase)
  have hD₁ : ∀ᶠ x in 𝓝 p, ρ x < c * ρ p :=
    hρcont.eventually_lt continuousAt_const (by nlinarith)
  have hD₂ : ∀ᶠ x in 𝓝 p, ρ p < c * ρ x :=
    continuousAt_const.eventually_lt (hρcont.const_mul c) (by nlinarith)
  have hN : (U₁ : Set M) ∩ (chartAt H p).source ∩ {x | ρ x < c * ρ p} ∩
      {x | ρ p < c * ρ x} ∈ 𝓝 p :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (U₁.isOpen.mem_nhds hpU₁)
      ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))) hD₁) hD₂
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨Kc, hKc, hKcsub, hKcc⟩ := local_compact_nhds hN
  refine ⟨interior Kc, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKc, ?_⟩
  intro A hA hAU
  have hAK : A ⊆ Kc := hAU.trans interior_subset
  have hAN (x) (hx : x ∈ A) := hKcsub (hAK hx)
  have hAU₁ : A ⊆ U₁ := fun x hx => (hAN x hx).1.1.1
  have hAsrc : A ⊆ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact fun x hx => (hAN x hx).1.1.2
  have hKsrc : Kc ⊆ (chartAt H p).source := fun x hx => (hKcsub hx).1.1.2
  have hvol : riemannianVolumeMeasure I M g A = chartLocalMeasure (I := I) g p A := by
    have h := congrArg (fun μ : Measure M => μ A)
      (riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict g p hKcc hKsrc)
    simpa only [Measure.restrict_apply hA, inter_eq_left.mpr hAK] using h
  have hFA : F '' A = L '' (φ '' A) := (image_image _ _ _).symm
  have hvolE : volume (F '' A) = ENNReal.ofReal (ρ p) * modelHaar (E := E) (φ '' A) := by
    rw [hFA, hLvol]
  have hHF : normalizedHausdorffMeasure (Module.finrank ℝ E) (F '' A) = volume (F '' A) := by
    rw [normalizedHausdorffMeasure_euclidean]
  have hup : volume (F '' A) ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      normalizedHausdorffMeasure (Module.finrank ℝ E) A := by
    rw [← hHF]
    exact normalizedHausdorffMeasure_image_le (hFlip.mono hAU₁) _
  have hlo : normalizedHausdorffMeasure (Module.finrank ℝ E) A ≤
      ENNReal.ofReal K ^ Module.finrank ℝ E * volume (F '' A) := by
    rw [← hHF]
    have h := normalizedHausdorffMeasure_image_le (hGlip.mono (image_mono hAU₁))
      (Module.finrank ℝ E)
    rwa [((hinj.leftInvOn_invFunOn).mono hAU₁).image_image] at h
  have hcu : chartLocalMeasure (I := I) g p A ≤
      ENNReal.ofReal (c * ρ p) * modelHaar (E := E) (φ '' A) :=
    chartLocalMeasure_le_ofReal_mul_modelHaar g p hA hAsrc
      (fun x hx => (hAN x hx).1.2.le)
  have hcl : ENNReal.ofReal (ρ p) * modelHaar (E := E) (φ '' A) ≤
      ENNReal.ofReal c * chartLocalMeasure (I := I) g p A :=
    ofReal_mul_modelHaar_le_chartLocalMeasure g p hA hAsrc (by linarith)
      (fun x hx => (hAN x hx).2.le)
  have hconst : ENNReal.ofReal (K ^ Module.finrank ℝ E * c) =
      ENNReal.ofReal K ^ Module.finrank ℝ E * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (pow_nonneg (by linarith) _), ENNReal.ofReal_pow (by linarith)]
  rw [hvol, hconst]
  constructor
  · calc
      _ ≤ ENNReal.ofReal K ^ Module.finrank ℝ E * volume (F '' A) := hlo
      _ ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
          (ENNReal.ofReal c * chartLocalMeasure (I := I) g p A) := by
        rw [hvolE]
        gcongr
      _ = _ := by ring
  · calc
      _ ≤ ENNReal.ofReal (c * ρ p) * modelHaar (E := E) (φ '' A) := hcu
      _ = ENNReal.ofReal c * volume (F '' A) := by
        rw [hvolE, ENNReal.ofReal_mul (by linarith), mul_assoc]
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal K ^ Module.finrank ℝ E *
          normalizedHausdorffMeasure (Module.finrank ℝ E) A) := by gcongr
      _ = _ := by ring

private theorem normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison_borel
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {K c : ℝ} (hK : 1 < K) (hc : 1 < c) {s : Set M} (hs : MeasurableSet s) :
    normalizedHausdorffMeasure (Module.finrank ℝ E) s ≤
        ENNReal.ofReal (K ^ Module.finrank ℝ E * c) * riemannianVolumeMeasure I M g s ∧
      riemannianVolumeMeasure I M g s ≤
        ENNReal.ofReal (K ^ Module.finrank ℝ E * c) *
          normalizedHausdorffMeasure (Module.finrank ℝ E) s := by
  choose U hUo hpU hU using fun p : M =>
    exists_isOpen_normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison
      g hEnorm p hK hc
  obtain ⟨t, htc, htU⟩ := countable_cover_nhds_of_sigmaCompact
    (fun p => (hUo p).mem_nhds (hpU p))
  rcases isEmpty_or_nonempty M with hM | ⟨⟨p₀⟩⟩
  · simp [Subsingleton.elim s ∅]
  have htne : t.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have h := htU ▸ mem_univ p₀
    simp [hne] at h
  obtain ⟨f, rfl⟩ := htc.exists_eq_range htne
  have hcov : ⋃ k, U (f k) = univ := by rw [← htU, biUnion_range]
  exact ⟨measure_le_mul_of_iUnion_eq_univ _ _ _ (fun k => U (f k))
      (fun k => (hUo (f k)).measurableSet) hcov (fun k A hA hAU => (hU (f k) A hA hAU).1) hs,
    measure_le_mul_of_iUnion_eq_univ _ _ _ (fun k => U (f k))
      (fun k => (hUo (f k)).measurableSet) hcov (fun k A hA hAU => (hU (f k) A hA hAU).2) hs⟩

end Local

/-! ### Public statements for an arbitrary Borel structure -/

section Public

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

open DifferentialGeometry.Geometry.Riemannian

/-- Two-sided comparison with constant `K ^ n * c` for every `K > 1`, `c > 1`, on every
measurable set. -/
theorem normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {K c : ℝ} (hK : 1 < K) (hc : 1 < c) {s : Set M} (hs : MeasurableSet s) :
    MeasureTheory.normalizedHausdorffMeasure (Module.finrank ℝ E) s ≤
        ENNReal.ofReal (K ^ Module.finrank ℝ E * c) *
          DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ∧
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ≤
        ENNReal.ofReal (K ^ Module.finrank ℝ E * c) *
          MeasureTheory.normalizedHausdorffMeasure (Module.finrank ℝ E) s := by
  obtain rfl := BorelSpace.measurable_eq (α := M)
  exact normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison_borel g hEnorm hK hc hs

/-- Dimension three: normalized `ℋ³ ≤ 64 · vol_g` on measurable sets. -/
theorem normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) {s : Set M} (hs : MeasurableSet s) :
    MeasureTheory.normalizedHausdorffMeasure 3 s ≤
      64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s := by
  have h := (normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison g hEnorm
    (K := 2) (c := 8) (by norm_num) (by norm_num) hs).1
  rw [hdim] at h
  norm_num at h
  exact h

/-- Dimension three: `vol_g ≤ 64 ·` normalized `ℋ³` on measurable sets. -/
theorem riemannianVolumeMeasure_le_sixtyFour_normalizedHausdorffMeasure
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) {s : Set M} (hs : MeasurableSet s) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ≤
      64 * MeasureTheory.normalizedHausdorffMeasure 3 s := by
  have h := (normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison g hEnorm
    (K := 2) (c := 8) (by norm_num) (by norm_num) hs).2
  rw [hdim] at h
  norm_num at h
  exact h

/-- Dimension three, every set: normalized `ℋ³ ≤ 64 · vol_g`. -/
theorem normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure'
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) (s : Set M) :
    MeasureTheory.normalizedHausdorffMeasure 3 s ≤
      64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s := by
  obtain rfl := BorelSpace.measurable_eq (α := M)
  let : MeasurableSpace M := borel M
  let t := toMeasurable (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) s
  calc
    MeasureTheory.normalizedHausdorffMeasure 3 s ≤
        MeasureTheory.normalizedHausdorffMeasure 3 t := measure_mono (subset_toMeasurable _ _)
    _ ≤ 64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g t :=
      normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure g hEnorm hdim
        (measurableSet_toMeasurable _ _)
    _ = 64 * DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s := by
      rw [measure_toMeasurable]

/-- Dimension three, every set: `vol_g ≤ 64 ·` normalized `ℋ³`. -/
theorem riemannianVolumeMeasure_le_sixtyFour_normalizedHausdorffMeasure'
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) (s : Set M) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ≤
      64 * MeasureTheory.normalizedHausdorffMeasure 3 s := by
  obtain rfl := BorelSpace.measurable_eq (α := M)
  let : MeasurableSpace M := borel M
  let t := toMeasurable (MeasureTheory.normalizedHausdorffMeasure 3 : Measure M) s
  calc
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s ≤
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g t :=
      measure_mono (subset_toMeasurable _ _)
    _ ≤ 64 * MeasureTheory.normalizedHausdorffMeasure 3 t :=
      riemannianVolumeMeasure_le_sixtyFour_normalizedHausdorffMeasure g hEnorm hdim
        (measurableSet_toMeasurable _ _)
    _ = 64 * MeasureTheory.normalizedHausdorffMeasure 3 s := by
      rw [measure_toMeasurable]

/-- The exact identity on every set: the normalized `n`-dimensional Hausdorff measure of the
length distance is the Riemannian volume, `n = finrank ℝ E`. -/
theorem normalizedHausdorffMeasure_apply_eq_riemannianVolumeMeasure_apply
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (s : Set M) :
    MeasureTheory.normalizedHausdorffMeasure (Module.finrank ℝ E) s =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s := by
  obtain rfl := BorelSpace.measurable_eq (α := M)
  let _ : MeasurableSpace M := borel M
  have hμ : (MeasureTheory.normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g := by
    ext t ht
    exact le_antisymm
      (le_of_forall_one_lt_le_ofReal_pow_mul _ fun r hr =>
        (normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison g hEnorm hr hr ht).1)
      (le_of_forall_one_lt_le_ofReal_pow_mul _ fun r hr =>
        (normalizedHausdorffMeasure_riemannianVolumeMeasure_comparison g hEnorm hr hr ht).2)
  rw [hμ]

/-- Dimension three, every set: normalized `ℋ³ = vol_g`. -/
theorem normalizedHausdorffMeasure_three_apply_eq_riemannianVolumeMeasure_apply
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) (s : Set M) :
    MeasureTheory.normalizedHausdorffMeasure 3 s =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g s := by
  have h := normalizedHausdorffMeasure_apply_eq_riemannianVolumeMeasure_apply g hEnorm s
  rw [hdim] at h
  exact h

end Public

/-! ### The exact identity as an equality of Borel measures -/

section Identity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Geometry.Riemannian

/-- The exact identity of Borel measures, `n = finrank ℝ E`. -/
theorem normalizedHausdorffMeasure_eq_riemannianVolumeMeasure
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) :
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    (MeasureTheory.normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g := by
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  ext s _
  exact normalizedHausdorffMeasure_apply_eq_riemannianVolumeMeasure_apply g hEnorm s

/-- Dimension three: `normalizedHausdorffMeasure 3 = riemannianVolumeMeasure I M g` as Borel
measures. -/
theorem normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) :
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    (MeasureTheory.normalizedHausdorffMeasure 3 : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g := by
  have h := normalizedHausdorffMeasure_eq_riemannianVolumeMeasure g hEnorm
  rw [hdim] at h
  exact h

/-- The form recorded as missing by X67/X68: the same `g` installs the Riemannian bundle, the
length extended distance (`EMetricSpace.ofRiemannianMetric`) and the Borel structure; then the
normalized three-dimensional Hausdorff measure is the Riemannian volume of `g`. -/
theorem lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    (MeasureTheory.normalizedHausdorffMeasure 3 : Measure M) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  exact normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure g
    (isMetricNorm_of_riemannianBundle (I := I) g) hdim

end Identity

/-! ### Riemannian ball volumes from normalized Hausdorff lower bounds -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

open DifferentialGeometry.Geometry.Riemannian

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
theorem riemannianBallOf_eq_ball_of_isMetricNorm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (r : ℝ) : riemannianBallOf g p r = Metric.ball p r := by
  ext y
  change riemannianEDistOf (I := I) g p y < ENNReal.ofReal r ↔ _
  rw [← edist_eq_riemannianEDistOf_of_isMetricNorm g hEnorm, edist_lt_ofReal, Metric.mem_ball,
    dist_comm]

/-- The LC14 binding: a normalized Hausdorff lower bound `L` for the metric ball gives the
Riemannian ball-volume lower bound `L / 64`. -/
theorem collapse_ballVolume_lower_of_normalizedHausdorffMeasure_lower
    [MeasurableSpace M] [BorelSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 3) (p : M) {r L : ℝ}
    (hlower : ENNReal.ofReal L ≤
      MeasureTheory.normalizedHausdorffMeasure 3 (Metric.ball p r)) :
    ENNReal.ofReal (L / 64) ≤ DifferentialGeometry.Geometry.Collapse.ballVolume g p r := by
  have h := hlower.trans (normalizedHausdorffMeasure_le_sixtyFour_riemannianVolumeMeasure
    g hEnorm hdim measurableSet_ball)
  rw [DifferentialGeometry.Geometry.Collapse.ballVolume,
    riemannianBallOf_eq_ball_of_isMetricNorm g hEnorm p r,
    ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  exact ENNReal.div_le_of_le_mul' h

end Ball

end DifferentialGeometry.Geometry.Metric
