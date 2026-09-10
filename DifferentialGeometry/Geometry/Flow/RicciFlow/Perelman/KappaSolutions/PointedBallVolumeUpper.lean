import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAsymptoticVolumeRatio

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

section LocalVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance ballUpperLocalMMeasurable : MeasurableSpace M := borel M
private local instance ballUpperLocalMBorel : BorelSpace M := ⟨rfl⟩
private local instance ballUpperLocalNMeasurable : MeasurableSpace N := borel N
private local instance ballUpperLocalNBorel : BorelSpace N := ⟨rfl⟩

private theorem pointedBallUpper_volume_le_image
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (F : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {A : Set M} (hA : MeasurableSet A) (hsource : A ⊆ F.source)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ x ∈ A, ∀ v : TangentSpace I x,
      g.inner x v v ≤ Q * h.inner (F x) (mfderiv I I (F : M → N) x v)
        (mfderiv I I (F : M → N) x v)) :
    riemannianVolumeMeasure (I := I) (M := M) g A ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) := by
  let U : Opens M := ⟨F.source, F.open_source⟩
  have hU : (U : Set M) ⊆ F.source := subset_rfl
  let V : Opens N := ⟨(F : M → N) '' (U : Set M), image_opens_isOpen F hU⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace V := borel V
  let _ : BorelSpace V := ⟨rfl⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo F hU
  let B : Set U := (Subtype.val : U → M) ⁻¹' A
  let gU := g.restrictOpen U
  let hV := h.restrictOpen V
  let gP := Diffeomorph.pullbackMetric hV e
  have hB : MeasurableSet B := hA.preimage continuous_subtype_val.measurable
  have hvalB : (Subtype.val : U → M) '' B = A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hsource hx⟩, hx, rfl⟩
  have himage : (Subtype.val : V → N) '' ((e : U → V) '' B) =
      (F : M → N) '' A := by
    rw [Set.image_image]
    change (fun x : U => F (x : M)) '' B = (F : M → N) '' A
    rw [← Set.image_image, hvalB]
  have he : MeasurableEmbedding (e : U → V) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres := (volumeMeasurePreserving_pullbackMetric hV e).measure_preimage_emb he
    ((e : U → V) '' B)
  rw [he.injective.preimage_image] at hpres
  have hcomp : ∀ x ∈ B, ∀ v : TangentSpace I x,
      gU.inner x v v ≤ Q * gP.inner x v v := by
    intro x hx v
    dsimp only [gP, gU, hV]
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    dsimp only [e]
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact hmetric (x : M) hx v
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A =
        riemannianVolumeMeasure (I := I) (M := U) gU B := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, hvalB]
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := U) gP B :=
      riemannianVolumeMeasure_le_on gP gU hB hQ hcomp
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := V) hV ((e : U → V) '' B) := by
      rw [hpres]
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, himage]

end LocalVolume

private theorem pointedBallUpper_quadratic_comparison
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hepsilon : 0 < epsilon)
    (herror : |b - a| ≤ epsilon / (1 + epsilon) * a) :
    b ≤ (1 + epsilon) ^ 2 * a ∧ a ≤ (1 + epsilon) * b := by
  have hL : 0 < 1 + epsilon := by linarith
  have hcoef : epsilon / (1 + epsilon) ≤ epsilon :=
    div_le_self hepsilon.le (by linarith)
  have hsq : 1 + epsilon ≤ (1 + epsilon) ^ 2 := by nlinarith
  have hupper : b ≤ (1 + epsilon) * a := by
    have hmul := mul_le_mul_of_nonneg_right hcoef ha
    have habs := (abs_le.mp herror).2
    nlinarith
  have hdivision : a / (1 + epsilon) = a - epsilon / (1 + epsilon) * a := by
    field_simp [ne_of_gt hL]
    ring
  have hlower : a ≤ (1 + epsilon) * b := by
    have hdiv : a / (1 + epsilon) ≤ b := by
      rw [hdivision]
      have habs := (abs_le.mp herror).1
      linarith
    simpa only [mul_comm] using (div_le_iff₀ hL).1 hdiv
  exact ⟨hupper.trans (mul_le_mul_of_nonneg_right hsq ha), hlower⟩

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance pointedBallUpperTopology : TopologicalSpace L.M := L.topology
private local instance pointedBallUpperCharted : ChartedSpace H L.M := L.charted
private local instance pointedBallUpperSmooth : IsManifold I ∞ L.M := L.smooth
private local instance pointedBallUpperT2 : T2Space L.M := L.t2
private local instance pointedBallUpperSigma : SigmaCompactSpace L.M := L.sigmaCompact
private local instance pointedBallUpperTangentT2 : T2Space (TangentBundle I L.M) :=
  L.t2TangentBundle
private local instance pointedBallUpperMeasurable : MeasurableSpace L.M := borel L.M
private local instance pointedBallUpperBorel : BorelSpace L.M := ⟨rfl⟩

private local instance pointedBallUpperSourceTopology (i : ℕ) :
    TopologicalSpace (X.obj i).M := (X.obj i).topology
private local instance pointedBallUpperSourceCharted (i : ℕ) :
    ChartedSpace H (X.obj i).M := (X.obj i).charted
private local instance pointedBallUpperSourceSmooth (i : ℕ) :
    IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
private local instance pointedBallUpperSourceT2 (i : ℕ) : T2Space (X.obj i).M :=
  (X.obj i).t2
private local instance pointedBallUpperSourceSigma (i : ℕ) :
    SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
private local instance pointedBallUpperSourceMeasurable (i : ℕ) :
    MeasurableSpace (X.obj i).M := borel (X.obj i).M
private local instance pointedBallUpperSourceBorel (i : ℕ) :
    BorelSpace (X.obj i).M := ⟨rfl⟩

theorem exists_pointed_limit_ball_volume_le_source
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L)
    {s r epsilon : ℝ} (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hbuffer : (1 + epsilon) * s < r) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric L.basepoint s) ≤
        ENNReal.ofReal (Real.sqrt ((1 + epsilon) ^ Module.finrank ℝ E)) *
          riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
            (X.obj (subseq k)).metric
            (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r) := by
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric :=
    ⟨MetricComplete.complete (I := I) L hcomplete⟩
  let K := riemannianClosedBallOf L.metric L.basepoint (s + 1)
  have hK : IsCompact K :=
    RiemannianMetricComplete.closedEBall_isCompact hmetricComplete L.basepoint (s + 1)
  have hL : 0 < 1 + epsilon := by linarith
  have hr : 0 < r := (mul_pos hL hs).trans hbuffer
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C hreference K hK (epsilon / (1 + epsilon)) (div_pos hepsilon hL)
  refine ⟨k0, fun k hk => ?_⟩
  let F := Phi.partialDiffeomorph k
  let A := riemannianBallOf L.metric L.basepoint s
  have hA : MeasurableSet A :=
    (isOpen_lt (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
      (I := I) L.metric L.basepoint) continuous_const).measurableSet
  have hAK : A ⊆ K := by
    intro x hx
    change riemannianEDistOf (I := I) L.metric L.basepoint x < ENNReal.ofReal s at hx
    exact hx.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hsource : K ⊆ F.source := (hk0 k hk).1
  have hquadratic : ∀ x ∈ K, ∀ v : TangentSpace I x,
      (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) ≤
        (1 + epsilon) ^ 2 * L.metric.inner x v v ∧
      L.metric.inner x v v ≤ (1 + epsilon) *
        (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) := by
    intro x hx v
    have ha : 0 ≤ L.metric.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (L.metric.pos x v hv).le
    exact pointedBallUpper_quadratic_comparison ha hepsilon ((hk0 k hk).2 x hx v)
  have himage : (F : L.M → (X.obj (subseq k)).M) '' A ⊆
      riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r := by
    rintro y ⟨x, hx, rfl⟩
    change riemannianEDistOf (I := I) L.metric L.basepoint x < ENNReal.ofReal s at hx
    have hxR : riemannianEDistOf (I := I) L.metric L.basepoint x <
        ENNReal.ofReal (s + 1) :=
      hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    have hdist := edistOf_map_le_of_metric_upper_on_ball L.metric
      (X.obj (subseq k)).metric F L.basepoint x (by linarith : 0 < s + 1)
      hL hsource (fun z hz v => (hquadratic z hz v).1) hxR
    have hbase : F L.basepoint = (X.obj (subseq k)).basepoint := Phi.basepoint_map k
    rw [hbase] at hdist
    change riemannianEDistOf (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint (F x) < ENNReal.ofReal r
    calc
      _ ≤ ENNReal.ofReal (1 + epsilon) *
          riemannianEDistOf (I := I) L.metric L.basepoint x := hdist
      _ ≤ ENNReal.ofReal (1 + epsilon) * ENNReal.ofReal s := mul_le_mul_right hx.le _
      _ = ENNReal.ofReal ((1 + epsilon) * s) := (ENNReal.ofReal_mul hL.le).symm
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 hbuffer
  have hv := pointedBallUpper_volume_le_image L.metric (X.obj (subseq k)).metric F
    hA (hAK.trans hsource) hL (fun x hx v => (hquadratic x (hAK hx) v).2)
  exact hv.trans (mul_le_mul_right (measure_mono himage) _)

theorem pointed_ball_volume_upper_of_eventually
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L) {r : ℝ} (hr : 0 < r) (V : ℝ≥0∞)
    (hsource : ∀ᶠ k : ℕ in atTop,
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
        (X.obj (subseq k)).metric
        (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r) ≤ V) :
    riemannianVolumeMeasure (I := I) (M := L.M) L.metric
      (riemannianBallOf L.metric L.basepoint r) ≤ V := by
  let mu := riemannianVolumeMeasure (I := I) (M := L.M) L.metric
  have hsmall : ∀ s : ℝ, 0 < s → s < r → mu (riemannianBallOf L.metric L.basepoint s) ≤ V := by
    intro s hs hsr
    let epsilon : ℕ → ℝ := fun j => ((r - s) / (2 * s)) * (1 / ((j : ℝ) + 1))
    have hepsilon : Tendsto epsilon atTop (𝓝 (0 : ℝ)) := by
      simpa only [epsilon, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((r - s) / (2 * s))
    have hone : Tendsto (fun j => 1 + epsilon j) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hepsilon
    have hsqrt : Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ E))
        atTop (𝓝 (1 : ℝ)) := by
      simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
        Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow (Module.finrank ℝ E))
    have hcoef : Tendsto
        (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ E)))
        atTop (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [ENNReal.ofReal_one, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
    have hright : Tendsto (fun j =>
        ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ E)) * V)
        atTop (𝓝 V) := by
      simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hright
    intro j
    have hc : 0 < (r - s) / (2 * s) := div_pos (sub_pos.mpr hsr) (by positivity)
    have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
    have he_le : epsilon j ≤ (r - s) / (2 * s) := by
      dsimp only [epsilon]
      apply mul_le_of_le_one_right hc.le
      exact (div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1)).2
        (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))])
    have hdivision : ((r - s) / (2 * s)) * s = (r - s) / 2 := by
      field_simp [ne_of_gt hs]
    have hbuffer : (1 + epsilon j) * s < r := by
      have hmul := mul_le_mul_of_nonneg_right he_le hs.le
      rw [hdivision] at hmul
      nlinarith
    obtain ⟨k0, hk0⟩ := exists_pointed_limit_ball_volume_le_source
      C hcanonical hcomplete hs he hbuffer
    obtain ⟨k1, hk1⟩ := eventually_atTop.mp hsource
    exact (hk0 (max k0 k1) (Nat.le_max_left _ _)).trans
      (mul_le_mul_right (hk1 (max k0 k1) (Nat.le_max_right _ _)) _)
  let s : ℕ → ℝ := fun j => r - r * (1 / ((j : ℝ) + 1))
  have hs : Tendsto s atTop (𝓝 r) := by
    simpa only [s, mul_zero, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r)
  have hsmono : Monotone s := by
    intro i j hij
    dsimp only [s]
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have hinv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) < (i : ℝ) + 1) hcast
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hinv hr.le) r
  have hballmono : Monotone (fun j => riemannianBallOf L.metric L.basepoint (s j)) := by
    intro i j hij x hx
    change riemannianEDistOf (I := I) L.metric L.basepoint x < ENNReal.ofReal (s i) at hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (hsmono hij))
  have hunion : (⋃ j : ℕ, riemannianBallOf L.metric L.basepoint (s j)) =
      riemannianBallOf L.metric L.basepoint r := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      change riemannianEDistOf (I := I) L.metric L.basepoint x < ENNReal.ofReal (s j) at hj
      exact hj.trans_le (ENNReal.ofReal_le_ofReal
        (sub_le_self r (mul_nonneg hr.le (by positivity))))
    · intro hx
      change riemannianEDistOf (I := I) L.metric L.basepoint x < ENNReal.ofReal r at hx
      have hlim : Tendsto (fun j => ENNReal.ofReal (s j)) atTop (𝓝 (ENNReal.ofReal r)) :=
        ENNReal.tendsto_ofReal hs
      obtain ⟨j, hj⟩ := (hlim.eventually (Ioi_mem_nhds hx)).exists
      exact mem_iUnion.mpr ⟨j, hj⟩
  rw [← hunion, hballmono.measure_iUnion]
  refine iSup_le fun j => ?_
  by_cases hsj : 0 < s j
  · apply hsmall (s j) hsj
    dsimp only [s]
    have hj : 0 < r * ((1 : ℝ) / ((j : ℝ) + 1)) := mul_pos hr (by positivity)
    linarith
  · have hempty : riemannianBallOf L.metric L.basepoint (s j) = ∅ := by
      ext x
      simp only [riemannianBallOf, mem_ofPred_eq, ENNReal.ofReal_of_nonpos (le_of_not_gt hsj),
        ENNReal.not_lt_zero, mem_empty_iff_false]
    rw [hempty, measure_empty]
    exact bot_le

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
