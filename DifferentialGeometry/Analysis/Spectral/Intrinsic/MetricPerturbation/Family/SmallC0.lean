import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Family.Difference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.UnitSelfBound
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Curvature.QuadraticFormBound
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem metricDifference_smallC0
    (g : Real → SmoothRiemannianMetric I M)
    (q : SmoothRiemannianMetric I M) {a b δ : Real}
    (hab : a < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hga : g a = q) (hδ : 0 < δ) :
    ∃ T : Real, 0 < T ∧ a + T < b ∧
      ∀ t ∈ Set.Icc a (a + T),
        metricCauchySchwarzBound (I := I) (M := M) q
          (ccTensorBilinSymm (I := I) q
            (metricDifferenceCcTensor (I := I) (M := M) q (g t))) δ := by
  let K : Set Real := Set.Ico a b
  have hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x) := by
    apply metricTensorCont_of_chartGram (K := K) g
    intro x₀ i j
    have hincl : Continuous
        (fun p : {t : Real // t ∈ K} × M => ((p.1 : Real), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hc : ContinuousOn
        ((fun p : Real × M =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j) ∘
          (fun p : {t : Real // t ∈ K} × M => ((p.1 : Real), p.2)))
        {p : {t : Real // t ∈ K} × M |
          p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      (hcont x₀ i j).comp hincl.continuousOn
        (fun p hp => ⟨p.1.2, hp⟩)
    exact hc.congr fun _ _ => rfl
  let X := MetricUnitTangent (I := I) (M := M) q
  have hXcompact : IsCompact (Set.univ : Set X) :=
    metricUnit_compact (I := I) (M := M) q
  let : CompactSpace X := ⟨hXcompact⟩
  let bfun : ({t : Real // t ∈ K} × X) → M :=
    fun p => MetricUnitTangent.base (I := I) (M := M) p.2
  let vfun : Fin 2 → (p : {t : Real // t ∈ K} × X) →
      TangentSpace I (bfun p) :=
    fun _ p => MetricUnitTangent.vec (I := I) (M := M) p.2
  have hbfun : Continuous bfun := by
    dsimp [bfun, MetricUnitTangent.base]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp
      (continuous_subtype_val.comp continuous_snd)
  have hvfun : ∀ i : Fin 2, Continuous
      (fun p : {t : Real // t ∈ K} × X =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
          (bfun p) (vfun i p)) := by
    intro i
    exact (continuous_subtype_val.comp continuous_snd :
      Continuous (fun p : {t : Real // t ∈ K} × X =>
        (p.2.1 : TangentBundle I M))).congr fun _ => rfl
  have hEval : Continuous
      (fun p : {t : Real // t ∈ K} × X =>
        (g p.1.1).inner (bfun p) (vfun 0 p) (vfun 1 p)) := by
    have he := hG.eval_continuous
      (P := {t : Real // t ∈ K} × X)
      (τ := fun p => p.1.1) (b := bfun)
      (continuous_subtype_val.comp continuous_fst)
      (fun p => p.1.2) hbfun hvfun
    simpa [metricTensorField_apply, bfun, vfun] using he
  let f : {t : Real // t ∈ K} → X → Real :=
    fun t p =>
      |(g t.1).inner
          (MetricUnitTangent.base (I := I) (M := M) p)
          (MetricUnitTangent.vec (I := I) (M := M) p)
          (MetricUnitTangent.vec (I := I) (M := M) p) -
        q.inner
          (MetricUnitTangent.base (I := I) (M := M) p)
          (MetricUnitTangent.vec (I := I) (M := M) p)
          (MetricUnitTangent.vec (I := I) (M := M) p)|
  have hf : Continuous
      (fun p : {t : Real // t ∈ K} × X => f p.1 p.2) := by
    have hc : Continuous
        (fun p : {t : Real // t ∈ K} × X =>
          |(g p.1.1).inner (bfun p) (vfun 0 p) (vfun 1 p) - (1 : Real)|) :=
      (hEval.sub continuous_const).abs
    simpa [f, bfun, vfun, MetricUnitTangent.unit] using hc
  let ta : {t : Real // t ∈ K} := ⟨a, ⟨le_rfl, hab⟩⟩
  have hfzero : ∀ p : X, f ta p = 0 := by
    intro p
    simp [f, ta, hga]
  have hsmall : ∀ᶠ t in 𝓝 ta, ∀ p : X, f t p < δ := by
    have hsmall' : ∀ᶠ t in 𝓝 ta, ∀ p ∈ (Set.univ : Set X), f t p < δ := by
      apply (isCompact_univ : IsCompact (Set.univ : Set X)).eventually_forall_of_forall_eventually
      intro p _
      exact hf.continuousAt.eventually_lt_const (by simpa only [hfzero p] using hδ)
    simpa only [Set.mem_univ, forall_const] using hsmall'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  let T : Real := min (b - a) r / 2
  have hmin : 0 < min (b - a) r := lt_min (sub_pos.mpr hab) hr
  have hT : 0 < T := by simp only [T]; positivity
  have hTb : a + T < b := by
    have hle := min_le_left (b - a) r
    dsimp [T]
    nlinarith
  have hTr : T < r := by
    have hle := min_le_right (b - a) r
    dsimp [T]
    nlinarith
  refine ⟨T, hT, hTb, ?_⟩
  intro t ht
  have htK : t ∈ K := ⟨ht.1, lt_of_le_of_lt ht.2 hTb⟩
  let ts : {s : Real // s ∈ K} := ⟨t, htK⟩
  have htsBall : ts ∈ Metric.ball ta r := by
    rw [Metric.mem_ball]
    change dist t a < r
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2, hTr]
  have hunit : ∀ (x : M) (u : TangentSpace I x),
      q.inner x u u = 1 →
        |ccTensorBilinSymm (I := I) q
          (metricDifferenceCcTensor (I := I) (M := M) q (g t)) x u u| ≤ δ := by
    intro x u hu
    let p : X := ⟨(⟨x, u⟩ : TangentBundle I M), hu⟩
    have hs := (hball htsBall) p
    rw [metricDifference_symVal]
    dsimp only [f, ts, p, MetricUnitTangent.base, MetricUnitTangent.vec] at hs
    exact @le_of_lt ℝ Real.partialOrder.toPreorder _ _ hs
  apply metricCauchySchwarzBound_of_unit_self_bound q
    (ccTensorBilinSymm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    (ccTensorBilinSymm_symm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    hunit

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem metricCauchySchwarzBound_between_of_reference_bounds
    (q g₀ g₁ : SmoothRiemannianMetric I M) {ε : Real}
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (h₀ : metricCauchySchwarzBound (I := I) (M := M) q
      (ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q g₀)) ε)
    (h₁ : metricCauchySchwarzBound (I := I) (M := M) q
      (ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q g₁)) ε) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
      (2 * ε / (1 - ε)) := by
  have hden : 0 < 1 - ε := sub_pos.mpr hε₁
  apply metricCauchySchwarzBound_of_unit_self_bound g₀
    (ccTensorBilinSymm (I := I) g₀
      (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
    (ccTensorBilinSymm_symm (I := I) g₀
      (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))
  intro x u hu
  let qu : Real := q.inner x u u
  have hqu : 0 ≤ qu := by
    dsimp only [qu]
    exact DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) q x u
  have hsqrt : Real.sqrt qu * Real.sqrt qu = qu := by
    rw [← Real.sqrt_mul hqu, Real.sqrt_mul_self hqu]
  have h₀u := h₀ x u u
  have h₁u := h₁ x u u
  rw [metricDifference_symVal (I := I) (M := M)] at h₀u h₁u
  have h₀u' : |g₀.inner x u u - q.inner x u u| ≤ ε * qu := by
    calc
      |g₀.inner x u u - q.inner x u u| ≤
          ε * Real.sqrt qu * Real.sqrt qu := by simpa only [qu] using h₀u
      _ = ε * qu := by nlinarith [hsqrt]
  have h₁u' : |g₁.inner x u u - q.inner x u u| ≤ ε * qu := by
    calc
      |g₁.inner x u u - q.inner x u u| ≤
          ε * Real.sqrt qu * Real.sqrt qu := by simpa only [qu] using h₁u
      _ = ε * qu := by nlinarith [hsqrt]
  have hqcarrier : (1 - ε) * qu ≤ g₀.inner x u u := by
    have hneg := neg_le_of_abs_le h₀u'
    dsimp only [qu] at hneg ⊢
    linarith
  have hqone : qu ≤ 1 / (1 - ε) := by
    apply (le_div_iff₀ hden).2
    simpa only [hu, mul_comm] using hqcarrier
  have htri :
      |g₁.inner x u u - g₀.inner x u u| ≤
        |g₁.inner x u u - q.inner x u u| +
          |g₀.inner x u u - q.inner x u u| := by
    rw [show g₁.inner x u u - g₀.inner x u u =
      (g₁.inner x u u - q.inner x u u) -
        (g₀.inner x u u - q.inner x u u) by ring]
    exact abs_sub _ _
  rw [metricDifference_symVal (I := I) (M := M)]
  calc
    |g₁.inner x u u - g₀.inner x u u| ≤ 2 * ε * qu := by
      calc
        _ ≤ |g₁.inner x u u - q.inner x u u| +
            |g₀.inner x u u - q.inner x u u| := htri
        _ ≤ ε * qu + ε * qu := add_le_add h₁u' h₀u'
        _ = 2 * ε * qu := by ring
    _ ≤ 2 * ε * (1 / (1 - ε)) :=
      mul_le_mul_of_nonneg_left hqone (mul_nonneg (by norm_num) hε₀)
    _ = 2 * ε / (1 - ε) := by ring
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem metricDifference_pair_smallC0
    (g₀ g₁ : Real → SmoothRiemannianMetric I M)
    (q : SmoothRiemannianMetric I M) {a b δ : Real}
    (hab : a < b)
    (hcont₀ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₀ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hg₀ : g₀ a = q) (hg₁ : g₁ a = q) (hδ : 0 < δ) :
    ∃ T : Real, 0 < T ∧ a + T < b ∧
      ∀ t ∈ Set.Icc a (a + T),
        metricCauchySchwarzBound (I := I) (M := M) (g₀ t)
          (ccTensorBilinSymm (I := I) (g₀ t)
            (metricDifferenceCcTensor (I := I) (M := M) (g₀ t) (g₁ t))) δ := by
  let ε : Real := δ / (2 + δ)
  have hden : 0 < 2 + δ := by linarith
  have hε : 0 < ε := div_pos hδ hden
  have hεlt : ε < 1 := by
    dsimp only [ε]
    exact (div_lt_one hden).2 (by linarith)
  obtain ⟨T₀, hT₀, hT₀b, hsmall₀⟩ :=
    metricDifference_smallC0 (I := I) (M := M) g₀ q hab hcont₀ hg₀ hε
  obtain ⟨T₁, hT₁, hT₁b, hsmall₁⟩ :=
    metricDifference_smallC0 (I := I) (M := M) g₁ q hab hcont₁ hg₁ hε
  let T : Real := min T₀ T₁
  have hT : 0 < T := by
    dsimp only [T]
    exact lt_min hT₀ hT₁
  have hTb : a + T < b := by
    have hTle : T ≤ T₀ := by exact min_le_left T₀ T₁
    nlinarith
  refine ⟨T, hT, hTb, ?_⟩
  intro t ht
  have ht₀ : t ∈ Set.Icc a (a + T₀) :=
    ⟨ht.1, by
      have hTle : T ≤ T₀ := by exact min_le_left T₀ T₁
      linarith [ht.2, hTle]⟩
  have ht₁ : t ∈ Set.Icc a (a + T₁) :=
    ⟨ht.1, by
      have hTle : T ≤ T₁ := by exact min_le_right T₀ T₁
      linarith [ht.2, hTle]⟩
  have hp := metricCauchySchwarzBound_between_of_reference_bounds (I := I) (M := M) q (g₀ t) (g₁ t)
    hε.le hεlt (hsmall₀ t ht₀) (hsmall₁ t ht₁)
  have hratio : 2 * ε / (1 - ε) = δ := by
    dsimp only [ε]
    field_simp
    ring
  simpa only [hratio] using hp

end DifferentialGeometry.Analysis.Spectral
