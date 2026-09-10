import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.EuclideanUpper
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal Topology

def euclideanUnitBallVolume (n : ℕ) : ℝ≥0∞ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)

theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n :=
  Metric.measure_ball_pos volume 0 (by norm_num)

theorem euclideanUnitBallVolume_ne_top (n : ℕ) : euclideanUnitBallVolume n ≠ ⊤ :=
  measure_ball_lt_top.ne

private theorem avr_denominator_ne_zero (n : ℕ) {r : ℝ} (hr : 0 < r) :
    euclideanUnitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 :=
  mul_ne_zero (euclideanUnitBallVolume_pos n).ne'
    (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'

private theorem avr_denominator_ne_top (n : ℕ) (r : ℝ) :
    euclideanUnitBallVolume n * ENNReal.ofReal (r ^ n) ≠ ⊤ :=
  ENNReal.mul_ne_top (euclideanUnitBallVolume_ne_top n) ENNReal.ofReal_ne_top

private theorem avr_div_le_div {a b c d : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : a * d ≤ b * c) : a / c ≤ b / d := by
  apply (ENNReal.div_le_iff hc0 hct).mpr
  rw [← ENNReal.mul_div_right_comm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdt)).mpr h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance avrMeasurable : MeasurableSpace M := borel M
private local instance avrBorel : BorelSpace M := ⟨rfl⟩
private local instance avrIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


def normalizedBallVolumeRatio (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) : ℝ≥0∞ :=
  riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) /
    (euclideanUnitBallVolume (Module.finrank ℝ E) *
      ENNReal.ofReal (r ^ Module.finrank ℝ E))

def asymptoticVolumeRatio (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r), normalizedBallVolumeRatio g p r

theorem asymptoticVolumeRatio_le_ratio (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ} (hr : 0 < r) :
    asymptoticVolumeRatio g p ≤ normalizedBallVolumeRatio g p r :=
  iInf_le_of_le r (iInf_le _ hr)

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    riemannianBallOf (scaleMetric c hc g) p (Real.sqrt c * r) =
      riemannianBallOf g p r := by
  have hs0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  ext x
  change riemannianEDistOf (scaleMetric c hc g) p x <
      ENNReal.ofReal (Real.sqrt c * r) ↔ riemannianEDistOf g p x < ENNReal.ofReal r
  rw [edistOf_scale, ENNReal.ofReal_mul (Real.sqrt_nonneg c),
    ENNReal.mul_lt_mul_iff_right hs0 ENNReal.ofReal_ne_top]

theorem normalizedBallVolumeRatio_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    normalizedBallVolumeRatio (scaleMetric c hc g) p (Real.sqrt c * r) =
      normalizedBallVolumeRatio g p r := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c) ^ Module.finrank ℝ E
  have ha0 : a ≠ 0 := pow_ne_zero _
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  have hat : a ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  unfold normalizedBallVolumeRatio
  rw [riemannianBallOf_scaleMetric, volume_scale_apply, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg c) _),
    ENNReal.ofReal_pow (Real.sqrt_nonneg c)]
  have hden : euclideanUnitBallVolume (Module.finrank ℝ E) *
      (a * ENNReal.ofReal (r ^ Module.finrank ℝ E)) =
      a * (euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E)) := by ac_rfl
  change a * _ / (euclideanUnitBallVolume (Module.finrank ℝ E) *
    (a * ENNReal.ofReal (r ^ Module.finrank ℝ E))) = _
  rw [hden]
  exact ENNReal.mul_div_mul_left _ _ ha0 hat

theorem asymptoticVolumeRatio_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (p : M) :
    asymptoticVolumeRatio (scaleMetric c hc g) p = asymptoticVolumeRatio g p := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  apply le_antisymm
  · refine le_iInf fun r => le_iInf fun hr => ?_
    calc
      asymptoticVolumeRatio (scaleMetric c hc g) p ≤
          normalizedBallVolumeRatio (scaleMetric c hc g) p (Real.sqrt c * r) :=
        asymptoticVolumeRatio_le_ratio _ _ (mul_pos hs hr)
      _ = normalizedBallVolumeRatio g p r := normalizedBallVolumeRatio_scaleMetric g c hc p r
  · refine le_iInf fun r => le_iInf fun hr => ?_
    calc
      asymptoticVolumeRatio g p ≤ normalizedBallVolumeRatio g p (r / Real.sqrt c) :=
        asymptoticVolumeRatio_le_ratio _ _ (div_pos hr hs)
      _ = normalizedBallVolumeRatio (scaleMetric c hc g) p
          (Real.sqrt c * (r / Real.sqrt c)) :=
        (normalizedBallVolumeRatio_scaleMetric g c hc p _).symm
      _ = normalizedBallVolumeRatio (scaleMetric c hc g) p r := by
        rw [mul_div_cancel₀ r hs.ne']

section Bishop

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianBallOf_volume_bishop_nonnegative
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M) :
    (∀ s R : ℝ, 0 < s → s ≤ R →
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p R) *
          ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p s)) ∧
    (∀ R : ℝ, 0 < R →
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p R) ≤
        euclideanUnitBallVolume (Module.finrank ℝ E) *
          ENNReal.ofReal (R ^ Module.finrank ℝ E)) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  constructor
  · intro s R hs hsR
    exact segmentBall_vol_pow g hEnorm p hs hsR hRic
  · intro R hR
    have hupper := segmentBall_vol_le_euclidean g hEnorm p (q := 0)
      (by norm_num) hR (by simpa using hRic)
    let n : ℕ := Module.finrank ℝ E
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub hn]
      norm_num
    have hmodel :
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
          ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) R) =
        euclideanUnitBallVolume n * ENNReal.ofReal (R ^ n) := by
      rw [Measure.toSphere_apply_univ, finrank_euclideanSpace, Fintype.card_fin,
        hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn, hncast,
        ENNReal.ofReal_div_of_pos hnreal, ENNReal.ofReal_natCast]
      change ((n : ℝ≥0∞) * euclideanUnitBallVolume n) *
        (ENNReal.ofReal (R ^ n) / n) = _
      calc
        _ = euclideanUnitBallVolume n *
            ((n : ℝ≥0∞) * (ENNReal.ofReal (R ^ n) / n)) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_div_cancel hn0 (by simp)]
    exact hupper.trans_eq hmodel

theorem normalizedBallVolumeRatio_antitoneOn
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M) :
    AntitoneOn (normalizedBallVolumeRatio g p) (Ioi 0) := by
  intro s hs R _hR hsR
  have h := (riemannianBallOf_volume_bishop_nonnegative g hcomplete hRic p).1 s R hs hsR
  apply avr_div_le_div (avr_denominator_ne_zero _ (hs.trans_le hsR))
    (avr_denominator_ne_top _ _) (avr_denominator_ne_zero _ hs) (avr_denominator_ne_top _ _)
  calc
    _ = euclideanUnitBallVolume (Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p R) *
          ENNReal.ofReal (s ^ Module.finrank ℝ E)) := by ac_rfl
    _ ≤ euclideanUnitBallVolume (Module.finrank ℝ E) *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p s)) :=
      mul_le_mul_right h _
    _ = _ := by ac_rfl

theorem normalizedBallVolumeRatio_le_one
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M) {r : ℝ} (hr : 0 < r) :
    normalizedBallVolumeRatio g p r ≤ 1 := by
  apply (ENNReal.div_le_iff (avr_denominator_ne_zero _ hr)
    (avr_denominator_ne_top _ _)).mpr
  rw [one_mul]
  exact (riemannianBallOf_volume_bishop_nonnegative g hcomplete hRic p).2 r hr


theorem asymptoticVolumeRatio_le_one
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M) :
    asymptoticVolumeRatio g p ≤ 1 :=
  (asymptoticVolumeRatio_le_ratio g p (r := 1) one_pos).trans
    (normalizedBallVolumeRatio_le_one g hcomplete hRic p one_pos)

theorem tendsto_normalizedBallVolumeRatio_atTop
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M) :
    Tendsto (normalizedBallVolumeRatio g p) atTop (𝓝 (asymptoticVolumeRatio g p)) := by
  have hanti := normalizedBallVolumeRatio_antitoneOn g hcomplete hRic p
  let f : ℝ → ℝ≥0∞ := fun r => normalizedBallVolumeRatio g p (max 1 r)
  have hpositive (r : ℝ) : max 1 r ∈ Ioi (0 : ℝ) := by
    change (0 : ℝ) < max 1 r
    exact lt_of_lt_of_le one_pos (le_max_left 1 r)
  have hf : Antitone f := by
    intro s R hsR
    exact hanti (hpositive s) (hpositive R) (max_le_max_left 1 hsR)
  have hinf : (⨅ r : ℝ, f r) = asymptoticVolumeRatio g p := by
    apply le_antisymm
    · refine le_iInf fun r => le_iInf fun hr => ?_
      exact (iInf_le f r).trans
        (hanti (Set.mem_Ioi.mpr hr) (hpositive r) (le_max_right 1 r))
    · refine le_iInf fun r => ?_
      exact asymptoticVolumeRatio_le_ratio g p
        (lt_of_lt_of_le one_pos (le_max_left _ _))
  have hlim : Tendsto f atTop (𝓝 (asymptoticVolumeRatio g p)) := by
    rw [← hinf]
    exact tendsto_atTop_iInf hf
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact congrArg (normalizedBallVolumeRatio g p) (max_eq_right hr)

end Bishop

section IntrinsicBalls

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem avr_mem_ball_iff (g : SmoothRiemannianMetric I M) (p x : M) (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ (riemannianEDistOf g p x).toReal < r := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  change riemannianEDist I p x < ENNReal.ofReal r ↔ (riemannianEDist I p x).toReal < r
  constructor
  · exact ENNReal.toReal_lt_of_lt_ofReal
  · intro h
    rw [← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) p x)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem avr_real_distance_triangle (g : SmoothRiemannianMetric I M) (p q x : M) :
    (riemannianEDistOf g p x).toReal ≤
      (riemannianEDistOf g p q).toReal + (riemannianEDistOf g q x).toReal := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  change (riemannianEDist I p x).toReal ≤
    (riemannianEDist I p q).toReal + (riemannianEDist I q x).toReal
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) p q,
      riemannianEDist_ne_top (I := I) q x⟩)
    (riemannianEDist_triangle (I := I) (x := p) (y := q) (z := x))
  simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) p q)
    (riemannianEDist_ne_top (I := I) q x)] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem avr_real_distance_comm (g : SmoothRiemannianMetric I M) (p q : M) :
    (riemannianEDistOf g p q).toReal = (riemannianEDistOf g q p).toReal := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  exact congrArg ENNReal.toReal (Manifold.riemannianEDist_comm (I := I) (x := p) (y := q))

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_subset_add_distance (g : SmoothRiemannianMetric I M)
    (p q : M) (r : ℝ) :
    riemannianBallOf g q r ⊆
      riemannianBallOf g p (r + (riemannianEDistOf g p q).toReal) := by
  intro x hx
  apply (avr_mem_ball_iff g p x _).mpr
  have hxreal := (avr_mem_ball_iff g q x r).mp hx
  have htriangle := avr_real_distance_triangle g p q x
  linarith

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianBallOf_basepoint_sandwich (g : SmoothRiemannianMetric I M)
    (p q : M) (r : ℝ) :
    riemannianBallOf g p (r - (riemannianEDistOf g p q).toReal) ⊆
        riemannianBallOf g q r ∧
      riemannianBallOf g q r ⊆
        riemannianBallOf g p (r + (riemannianEDistOf g p q).toReal) := by
  constructor
  · have h := riemannianBallOf_subset_add_distance g q p
      (r - (riemannianEDistOf g p q).toReal)
    simpa only [avr_real_distance_comm g q p, sub_add_cancel] using h
  · exact riemannianBallOf_subset_add_distance g p q r

end IntrinsicBalls

private theorem avr_radius_denominator_change (g : SmoothRiemannianMetric I M)
    (p : M) (r a : ℝ) (ha : 0 < a) :
    riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (a * r)) /
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          ENNReal.ofReal (r ^ Module.finrank ℝ E)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        normalizedBallVolumeRatio g p (a * r) := by
  let k : ℝ≥0∞ := ENNReal.ofReal (a ^ Module.finrank ℝ E)
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos ha _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold normalizedBallVolumeRatio
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg ha.le _)]
  have hden : euclideanUnitBallVolume (Module.finrank ℝ E) *
      (k * ENNReal.ofReal (r ^ Module.finrank ℝ E)) =
      k * (euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E)) := by ac_rfl
  change _ = k * (_ / (euclideanUnitBallVolume (Module.finrank ℝ E) *
    (k * ENNReal.ofReal (r ^ Module.finrank ℝ E))))
  rw [hden]
  let V := riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (a * r))
  let b := euclideanUnitBallVolume (Module.finrank ℝ E) *
    ENNReal.ofReal (r ^ Module.finrank ℝ E)
  change V / b = k * (V / (k * b))
  symm
  calc
    k * (V / (k * b)) = (k * V) / (k * b) := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ = _ := ENNReal.mul_div_mul_left _ _ hk0 hkt

section Basepoint

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

theorem asymptoticVolumeRatio_basepoint_le_mul
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p q : M)
    (delta : ℝ) (hdelta : 0 < delta) :
    asymptoticVolumeRatio g q ≤ ENNReal.ofReal ((1 + delta) ^ Module.finrank ℝ E) *
      asymptoticVolumeRatio g p := by
  let k : ℝ≥0∞ := ENNReal.ofReal ((1 + delta) ^ Module.finrank ℝ E)
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  let d : ℝ := (riemannianEDistOf g p q).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hddelta : 0 ≤ d / delta := div_nonneg hd hdelta.le
  have hanti := normalizedBallVolumeRatio_antitoneOn g hcomplete hRic p
  calc
    asymptoticVolumeRatio g q ≤
        ⨅ (rho : ℝ) (_ : 0 < rho), k * normalizedBallVolumeRatio g p rho := by
      refine le_iInf fun rho => le_iInf fun hrho => ?_
      let R : ℝ := rho + d / delta + 1
      have hR : 0 < R := by dsimp only [R]; linarith
      have hrhoR : rho ≤ R := by dsimp only [R]; linarith
      have hdR : d ≤ delta * R := by
        have hdiv : d / delta ≤ R := by dsimp only [R]; linarith
        simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hdiv
      have hRlarge : R + d ≤ (1 + delta) * R := by nlinarith
      have hscale : R ≤ (1 + delta) * R := by nlinarith
      have hball : riemannianBallOf g q R ⊆ riemannianBallOf g p ((1 + delta) * R) :=
        (riemannianBallOf_subset_add_distance g p q R).trans
          (riemannianBallOf_mono g p hRlarge)
      have hvolume := measure_mono (μ := riemannianVolumeMeasure (I := I) (M := M) g) hball
      calc
        asymptoticVolumeRatio g q ≤ normalizedBallVolumeRatio g q R :=
          asymptoticVolumeRatio_le_ratio g q hR
        _ ≤ riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p ((1 + delta) * R)) /
            (euclideanUnitBallVolume (Module.finrank ℝ E) *
              ENNReal.ofReal (R ^ Module.finrank ℝ E)) :=
          mul_le_mul_left hvolume _
        _ = k * normalizedBallVolumeRatio g p ((1 + delta) * R) :=
          avr_radius_denominator_change g p R (1 + delta) (by linarith)
        _ ≤ k * normalizedBallVolumeRatio g p rho :=
          mul_le_mul_right (hanti (Set.mem_Ioi.mpr hrho)
            (Set.mem_Ioi.mpr (hR.trans_le hscale)) (hrhoR.trans hscale)) k
    _ = k * asymptoticVolumeRatio g p := by
      simp only [asymptoticVolumeRatio, ENNReal.mul_iInf_of_ne hk0 hkt]

private theorem avr_basepoint_le
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p q : M) :
    asymptoticVolumeRatio g q ≤ asymptoticVolumeRatio g p := by
  have hp : asymptoticVolumeRatio g p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (asymptoticVolumeRatio_le_one g hcomplete hRic p)
  let b : ℝ := (asymptoticVolumeRatio g p).toReal
  have hcontinuous : Continuous (fun delta : ℝ =>
      ENNReal.ofReal ((1 + delta) ^ Module.finrank ℝ E * b)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun delta : ℝ =>
      ENNReal.ofReal ((1 + delta) ^ Module.finrank ℝ E * b))
      (𝓝[>] (0 : ℝ)) (𝓝 (asymptoticVolumeRatio g p)) := by
    simpa only [add_zero, one_pow, one_mul, b, ENNReal.ofReal_toReal hp] using
      (hcontinuous.tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with delta (hdelta : 0 < delta)
  have h := asymptoticVolumeRatio_basepoint_le_mul g hcomplete hRic p q delta hdelta
  rw [ENNReal.ofReal_mul (pow_nonneg (by linarith) _), ENNReal.ofReal_toReal hp]
  exact h

theorem asymptoticVolumeRatio_basepoint_eq
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p q : M) :
    asymptoticVolumeRatio g p = asymptoticVolumeRatio g q :=
  le_antisymm (avr_basepoint_le g hcomplete hRic q p)
    (avr_basepoint_le g hcomplete hRic p q)

end Basepoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
