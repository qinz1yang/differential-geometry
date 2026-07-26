import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffJoint
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Curvature.QuadraticFormBound
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Endpoint smallness of a metric difference

Joint `C^0` chart-Gram control up to a closed initial edge, together with
equality to a fixed metric at that edge, makes the metric difference uniformly
small in the fixed metric's fibre operator norm on one common positive window.

The compactness step is carried out on the fixed metric's unit tangent bundle.
Only repeated-vector evaluations are needed there.  A separate polarization
lemma then promotes the uniform quadratic bound to the bilinear
`gFibreOpBound` consumed by metric realization and weak parabolic coercivity.
-/

noncomputable section

open Bundle Filter Set Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- A jointly continuous scalar family which vanishes on one compact slice is
uniformly small on that compact factor for all parameters sufficiently close
to the distinguished parameter. -/
theorem jointSmall_compact
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X]
    (f : P → X → Real) (p₀ : P)
    (hf : Continuous (fun p : P × X => f p.1 p.2))
    (hzero : ∀ x : X, f p₀ x = 0)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ p in 𝒩 p₀, ∀ x : X, f p x < ε := by
  classical
  have hpatch (x : X) :
      ∃ V : Set P, V ∈ 𝒩 p₀ ∧
        ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
          ∀ p ∈ V, ∀ y ∈ W, f p y < ε := by
    have hsmall : {q : P × X | f q.1 q.2 < ε} ∈ 𝒩 (p₀, x) := by
      exact hf.continuousAt.eventually_lt_const (by simpa [hzero x] using hε)
    obtain ⟨V, W, hVopen, hp₀V, hWopen, hxW, hVW⟩ :=
      mem_nhds_prod_iff'.mp hsmall
    refine ⟨V, hVopen.mem_nhds hp₀V, W, hWopen, hxW, ?_⟩
    intro p hp y hy
    exact hVW ⟨hp, hy⟩
  choose V hV W hWopen hxW hloc using hpatch
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).elim_nhds_subcover W
      (fun x _ => (hWopen x).mem_nhds (hxW x))
  have htime : ∀ᶠ p in 𝒩 p₀, ∀ x ∈ F, p ∈ V x :=
    (Finset.eventually_all
      (I := F) (l := 𝒩 p₀) (p := fun x p => p ∈ V x)).2
      (fun x _ => hV x)
  filter_upwards [htime] with p hp
  intro y
  obtain ⟨x, hxF, hyW⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x p (hp x hxF) y hyW

/-- A uniform bound on the quadratic form of a symmetric bilinear field over
the fixed metric's unit tangent bundle implies the intrinsic bilinear
operator bound with the same constant. -/
theorem gOpBound_unitQuad
    (q : SmoothRiemannianMetric I M)
    (A : ∀ x : M, TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] Real)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x),
      A x v w = A x w v)
    {δ : Real} (hδ : 0 ≤ δ)
    (hunit : ∀ (x : M) (u : TangentSpace I x),
      q.inner x u u = 1 → |A x u u| ≤ δ) :
    gFibreOpBound (I := I) (M := M) q A δ := by
  intro x v w
  let Q : Tensor02At (I := I) (M := M) x :=
    Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (A x))
  have hQeval (z₁ z₂ : TangentSpace I x) :
      Q (vec2 (I := I) z₁ z₂) = A x z₁ z₂ := by
    change Tensor0SSpace.toModel Q (vec2 (I := I) z₁ z₂) = A x z₁ z₂
    rw [Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
    simp [vec2]
  have hdiag (z : TangentSpace I x) :
      |A x z z| ≤ δ * q.inner x z z := by
    rw [← hQeval z z]
    apply tensor02_quadForm_abs_le_of_unit_bound q Q
    intro u hu
    rw [hQeval u u]
    exact hunit x u hu
  have hpair (u z : TangentSpace I x)
      (hu : q.inner x u u = 1) (hz : q.inner x z z = 1) :
      |A x u z| ≤ δ := by
    have hpolar :
        (4 : Real) * A x u z =
          A x (u + z) (u + z) - A x (u - z) (u - z) := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      rw [hsymm x z u]
      ring
    have habs :
        |(4 : Real) * A x u z| ≤
          |A x (u + z) (u + z)| + |A x (u - z) (u - z)| := by
      rw [hpolar]
      exact abs_sub_le _ _
    have hsum := add_le_add (hdiag (u + z)) (hdiag (u - z))
    have hmetric :
        q.inner x (u + z) (u + z) + q.inner x (u - z) (u - z) = 4 := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      rw [q.symm x z u, hu, hz]
      ring
    calc
      |A x u z| = (1 / 4 : Real) * |(4 : Real) * A x u z| := by
        rw [abs_mul]
        norm_num
      _ ≤ (1 / 4 : Real) *
          (|A x (u + z) (u + z)| + |A x (u - z) (u - z)|) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
      _ ≤ (1 / 4 : Real) *
          (δ * q.inner x (u + z) (u + z) +
            δ * q.inner x (u - z) (u - z)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = δ := by rw [← mul_add, hmetric]; ring
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hvpos : 0 < q.inner x v v := q.pos x v hv
  have hwpos : 0 < q.inner x w w := q.pos x w hw
  let rv : Real := Real.sqrt (q.inner x v v)
  let sw : Real := Real.sqrt (q.inner x w w)
  have hrvpos : 0 < rv := by simpa [rv] using Real.sqrt_pos.mpr hvpos
  have hswpos : 0 < sw := by simpa [sw] using Real.sqrt_pos.mpr hwpos
  have hrv_sq : rv * rv = q.inner x v v := by
    simpa [rv, pow_two] using Real.sq_sqrt hvpos.le
  have hsw_sq : sw * sw = q.inner x w w := by
    simpa [sw, pow_two] using Real.sq_sqrt hwpos.le
  let u : TangentSpace I x := rv⁻¹ • v
  let z : TangentSpace I x := sw⁻¹ • w
  have hu : q.inner x u u = 1 := by
    rw [show u = rv⁻¹ • v from rfl, metric_smul2, ← hrv_sq]
    field_simp [hrvpos.ne']
  have hz : q.inner x z z = 1 := by
    rw [show z = sw⁻¹ • w from rfl, metric_smul2, ← hsw_sq]
    field_simp [hswpos.ne']
  have hvscale : rv • u = v := by simp [u, hrvpos.ne']
  have hwscale : sw • z = w := by simp [z, hswpos.ne']
  have hval : A x v w = rv * sw * A x u z := by
    rw [← hvscale, ← hwscale]
    simp [smul_eq_mul]
    ring
  have habsval : |A x v w| = rv * sw * |A x u z| := by
    rw [hval, abs_mul, abs_mul, abs_of_pos hrvpos, abs_of_pos hswpos]
    ring
  rw [habsval]
  calc
    rv * sw * |A x u z| ≤ rv * sw * δ :=
      mul_le_mul_of_nonneg_left (hpair u z hu hz)
        (mul_nonneg hrvpos.le hswpos.le)
    _ = δ * Real.sqrt (q.inner x v v) * Real.sqrt (q.inner x w w) := by
      simp only [rv, sw]
      ring

/-- Joint chart-Gram continuity at a closed initial edge and equality to the
background metric at that edge produce one positive window on which the
fixed-background metric difference is uniformly small in `gFibreOpBound`.

The selected `T` is common to all base points and tangent vectors. -/
theorem metricDiff_smallC0
    (g : Real → SmoothRiemannianMetric I M)
    (q : SmoothRiemannianMetric I M) {a b δ : Real}
    (hab : a < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hga : g a = q) (hδ : 0 < δ) :
    ∃ T : Real, 0 < T ∧ a + T < b ∧
      ∀ t ∈ Set.Icc a (a + T),
        gFibreOpBound (I := I) (M := M) q
          (ccTensorBilinSymm (I := I) q
            (metricDifferenceCcTensor (I := I) (M := M) q (g t))) δ := by
  let K : Set Real := Set.Ico a b
  have hG : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x) := by
    apply metricTensorCont_of_chartGram (K := K) g
    intro x₀ i j
    have hincl : Continuous
        (fun p : {t : Real // t ∈ K} × M => ((p.1 : Real), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hc : ContinuousOn
        ((fun p : Real × M =>
            chartGramMatrix (I := I) (g p.1) x₀ p.2 i j) ∘
          (fun p : {t : Real // t ∈ K} × M => ((p.1 : Real), p.2)))
        {p : {t : Real // t ∈ K} × M |
          p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      (hcont x₀ i j).comp hincl.continuousOn
        (fun p hp => ⟨p.1.2, hp⟩)
    simpa only [Function.comp_apply, K] using hc
  let X := MetricUnitTangent (I := I) (M := M) q
  have hXcompact : IsCompact (Set.univ : Set X) :=
    metricUnit_compact (I := I) (M := M) q
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hXcompact
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
    simpa [bfun, vfun, MetricUnitTangent.base, MetricUnitTangent.vec] using
      (continuous_subtype_val.comp continuous_snd :
        Continuous (fun p : {t : Real // t ∈ K} × X =>
          (p.2.1 : TangentBundle I M)))
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
  have hsmall : ∀ᶠ t in 𝒩 ta, ∀ p : X, f t p < δ :=
    jointSmall_compact f ta hf hfzero hδ
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
    rw [metricDiff_symVal]
    simpa [f, ts, p] using hs.le
  apply gOpBound_unitQuad q
    (ccTensorBilinSymm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    (ccTensorBilinSymm_symm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    hδ.le hunit

/-! ## Transfer from a fixed initial metric to a moving carrier -/

/-- If two metrics are both `Îµ`-close to `q`, then their difference is
`2Îµ / (1 - Îµ)`-small relative to the first metric.

The proof uses only quadratic forms.  A `gâ‚€`-unit vector has `q`-length at
most `(1 - Îµ)â»Â¹`; polarization then recovers the full bilinear operator
bound. -/
theorem pairOpBound
    (q gâ‚€ gâ‚ : SmoothRiemannianMetric I M) {Îµ : Real}
    (hÎµâ‚€ : 0 â‰¤ Îµ) (hÎµâ‚ : Îµ < 1)
    (hâ‚€ : gFibreOpBound (I := I) (M := M) q
      (ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q gâ‚€)) Îµ)
    (hâ‚ : gFibreOpBound (I := I) (M := M) q
      (ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q gâ‚)) Îµ) :
    gFibreOpBound (I := I) (M := M) gâ‚€
      (ccTensorBilinSymm (I := I) gâ‚€
        (metricDifferenceCcTensor (I := I) (M := M) gâ‚€ gâ‚))
      (2 * Îµ / (1 - Îµ)) := by
  have hden : 0 < 1 - Îµ := sub_pos.mpr hÎµâ‚
  apply gOpBound_unitQuad gâ‚€
    (ccTensorBilinSymm (I := I) gâ‚€
      (metricDifferenceCcTensor (I := I) (M := M) gâ‚€ gâ‚))
    (ccTensorBilinSymm_symm (I := I) gâ‚€
      (metricDifferenceCcTensor (I := I) (M := M) gâ‚€ gâ‚))
    (div_nonneg (mul_nonneg (by norm_num) hÎµâ‚€) hden.le)
  intro x u hu
  let qu : Real := q.inner x u u
  have hqu : 0 â‰¤ qu := by
    dsimp only [qu]
    exact metric_inner_self_nonneg (I := I) (M := M) q x u
  have hsqrt : Real.sqrt qu * Real.sqrt qu = qu := by
    rw [â† Real.sqrt_mul hqu, Real.sqrt_mul_self hqu]
  have hâ‚€u := hâ‚€ x u u
  have hâ‚u := hâ‚ x u u
  rw [metricDiff_symVal (I := I) (M := M)] at hâ‚€u hâ‚u
  have hâ‚€u' : |gâ‚€.inner x u u - q.inner x u u| â‰¤ Îµ * qu := by
    calc
      |gâ‚€.inner x u u - q.inner x u u| â‰¤
          Îµ * Real.sqrt qu * Real.sqrt qu := by simpa only [qu] using hâ‚€u
      _ = Îµ * qu := by rw [hsqrt]
  have hâ‚u' : |gâ‚.inner x u u - q.inner x u u| â‰¤ Îµ * qu := by
    calc
      |gâ‚.inner x u u - q.inner x u u| â‰¤
          Îµ * Real.sqrt qu * Real.sqrt qu := by simpa only [qu] using hâ‚u
      _ = Îµ * qu := by rw [hsqrt]
  have hqcarrier : (1 - Îµ) * qu â‰¤ gâ‚€.inner x u u := by
    have hneg := neg_le_of_abs_le hâ‚€u'
    dsimp only [qu] at hneg âŠ¢
    linarith
  have hqone : qu â‰¤ 1 / (1 - Îµ) := by
    apply (le_div_iffâ‚€ hden).2
    simpa only [hu, mul_comm] using hqcarrier
  have htri :
      |gâ‚.inner x u u - gâ‚€.inner x u u| â‰¤
        |gâ‚.inner x u u - q.inner x u u| +
          |gâ‚€.inner x u u - q.inner x u u| := by
    rw [show gâ‚.inner x u u - gâ‚€.inner x u u =
      (gâ‚.inner x u u - q.inner x u u) -
        (gâ‚€.inner x u u - q.inner x u u) by ring]
    exact abs_sub _ _
  rw [metricDiff_symVal (I := I) (M := M)]
  calc
    |gâ‚.inner x u u - gâ‚€.inner x u u| â‰¤ 2 * Îµ * qu := by
      calc
        _ â‰¤ |gâ‚.inner x u u - q.inner x u u| +
            |gâ‚€.inner x u u - q.inner x u u| := htri
        _ â‰¤ Îµ * qu + Îµ * qu := add_le_add hâ‚u' hâ‚€u'
        _ = 2 * Îµ * qu := by ring
    _ â‰¤ 2 * Îµ * (1 / (1 - Îµ)) :=
      mul_le_mul_of_nonneg_left hqone (mul_nonneg (by norm_num) hÎµâ‚€)
    _ = 2 * Îµ / (1 - Îµ) := by ring

/-- Two jointly continuous metric paths with the same initial metric become
uniformly close relative to the first, moving path on one common positive
window.  The time and the operator bound are common to all base points and
tangent vectors. -/
theorem metricPair_smallC0
    (gâ‚€ gâ‚ : Real â†’ SmoothRiemannianMetric I M)
    (q : SmoothRiemannianMetric I M) {a b Î´ : Real}
    (hab : a < b)
    (hcontâ‚€ : âˆ€ (xâ‚€ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real Ã— M â†¦
          chartGramMatrix (I := I) (gâ‚€ p.1) xâ‚€ p.2 i j)
        (Set.Ico a b Ã—Ë¢
          (trivializationAt E (TangentSpace I) xâ‚€).baseSet))
    (hcontâ‚ : âˆ€ (xâ‚€ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real Ã— M â†¦
          chartGramMatrix (I := I) (gâ‚ p.1) xâ‚€ p.2 i j)
        (Set.Ico a b Ã—Ë¢
          (trivializationAt E (TangentSpace I) xâ‚€).baseSet))
    (hgâ‚€ : gâ‚€ a = q) (hgâ‚ : gâ‚ a = q) (hÎ´ : 0 < Î´) :
    âˆƒ T : Real, 0 < T âˆ§ a + T < b âˆ§
      âˆ€ t âˆˆ Set.Icc a (a + T),
        gFibreOpBound (I := I) (M := M) (gâ‚€ t)
          (ccTensorBilinSymm (I := I) (gâ‚€ t)
            (metricDifferenceCcTensor (I := I) (M := M) (gâ‚€ t) (gâ‚ t))) Î´ := by
  let Îµ : Real := Î´ / (2 + Î´)
  have hden : 0 < 2 + Î´ := by linarith
  have hÎµ : 0 < Îµ := div_pos hÎ´ hden
  have hÎµlt : Îµ < 1 := by
    dsimp only [Îµ]
    exact (div_lt_one hden).2 (by linarith)
  obtain âŸ¨Tâ‚€, hTâ‚€, hTâ‚€b, hsmallâ‚€âŸ© :=
    metricDiff_smallC0 (I := I) (M := M) gâ‚€ q hab hcontâ‚€ hgâ‚€ hÎµ
  obtain âŸ¨Tâ‚, hTâ‚, hTâ‚b, hsmallâ‚âŸ© :=
    metricDiff_smallC0 (I := I) (M := M) gâ‚ q hab hcontâ‚ hgâ‚ hÎµ
  let T : Real := min Tâ‚€ Tâ‚
  have hT : 0 < T := by
    dsimp only [T]
    exact lt_min hTâ‚€ hTâ‚
  have hTb : a + T < b := by
    exact lt_of_le_of_lt (add_le_add_left (min_le_left Tâ‚€ Tâ‚) a) hTâ‚€b
  refine âŸ¨T, hT, hTb, ?_âŸ©
  intro t ht
  have htâ‚€ : t âˆˆ Set.Icc a (a + Tâ‚€) :=
    âŸ¨ht.1, le_trans ht.2 (add_le_add_left (min_le_left Tâ‚€ Tâ‚) a)âŸ©
  have htâ‚ : t âˆˆ Set.Icc a (a + Tâ‚) :=
    âŸ¨ht.1, le_trans ht.2 (add_le_add_left (min_le_right Tâ‚€ Tâ‚) a)âŸ©
  have hp := pairOpBound (I := I) (M := M) q (gâ‚€ t) (gâ‚ t)
    hÎµ.le hÎµlt (hsmallâ‚€ t htâ‚€) (hsmallâ‚ t htâ‚)
  have hratio : 2 * Îµ / (1 - Îµ) = Î´ := by
    dsimp only [Îµ]
    field_simp
    ring
  simpa only [hratio] using hp

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
