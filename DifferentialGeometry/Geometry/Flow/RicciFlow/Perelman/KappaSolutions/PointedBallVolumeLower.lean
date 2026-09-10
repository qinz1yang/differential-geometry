import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAsymptoticVolumeRatio
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

section Static

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ballLowerMeasurable : MeasurableSpace M := borel M
private local instance ballLowerBorel : BorelSpace M := ⟨rfl⟩

theorem asymptoticVolumeRatio_lower_of_ball_volume_lower
    (g : SmoothRiemannianMetric I M) (p : M) (v : ℝ≥0∞)
    (hvolume : ∀ r : ℝ, 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)) :
    v / euclideanUnitBallVolume (Module.finrank ℝ E) ≤
      asymptoticVolumeRatio (I := I) g p := by
  let n := Module.finrank ℝ E
  let omega := euclideanUnitBallVolume n
  have homega0 : omega ≠ 0 := (euclideanUnitBallVolume_pos n).ne'
  have homegat : omega ≠ ⊤ := euclideanUnitBallVolume_ne_top n
  change v / omega ≤ ⨅ (r : ℝ) (_ : 0 < r), normalizedBallVolumeRatio g p r
  refine le_iInf fun r => le_iInf fun hr => ?_
  have hp0 : ENNReal.ofReal (r ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
  change v / omega ≤ riemannianVolumeMeasure (I := I) (M := M) g
    (riemannianBallOf g p r) / (omega * ENNReal.ofReal (r ^ n))
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero homega0 hp0))
    (Or.inl (ENNReal.mul_ne_top homegat ENNReal.ofReal_ne_top))).2
  calc
    v / omega * (omega * ENNReal.ofReal (r ^ n)) =
        (v / omega * omega) * ENNReal.ofReal (r ^ n) := (mul_assoc _ _ _).symm
    _ = v * ENNReal.ofReal (r ^ n) := by rw [ENNReal.div_mul_cancel homega0 homegat]
    _ ≤ _ := hvolume r hr

theorem noncompact_of_positive_ball_volume_lower [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : ℝ≥0∞) (hv : v ≠ 0)
    (hvolume : ∀ r : ℝ, 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)) :
    NoncompactSpace M := by
  constructor
  intro hcompact
  let _ : CompactSpace M := ⟨hcompact⟩
  let mu := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasure mu :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let n := Module.finrank ℝ E
  have hpow : Tendsto (fun r : ℝ => r ^ n) atTop atTop :=
    tendsto_pow_atTop (NeZero.ne n)
  have hlim : Tendsto (fun r : ℝ => v * ENNReal.ofReal (r ^ n)) atTop (𝓝 ⊤) := by
    simpa only [ENNReal.mul_top hv, Function.comp_def] using
      ENNReal.Tendsto.const_mul (a := v) (ENNReal.tendsto_ofReal_atTop.comp hpow)
        (Or.inl ENNReal.top_ne_zero)
  have htop : (⊤ : ℝ≥0∞) ≤ mu univ := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hvolume r hr).trans (measure_mono (subset_univ _))
  exact (measure_lt_top mu univ).not_ge htop

end Static

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance pointedBallLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedBallLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedBallLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance pointedBallLimitT2 : T2Space L.M := L.t2
private local instance pointedBallLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact
private local instance pointedBallLimitMeasurable : MeasurableSpace L.M := borel L.M
private local instance pointedBallLimitBorel : BorelSpace L.M := ⟨rfl⟩

private local instance pointedBallSourceTopology (i : ℕ) : TopologicalSpace (X.obj i).M :=
  (X.obj i).topology
private local instance pointedBallSourceCharted (i : ℕ) : ChartedSpace H (X.obj i).M :=
  (X.obj i).charted
private local instance pointedBallSourceSmooth (i : ℕ) : IsManifold I ∞ (X.obj i).M :=
  (X.obj i).smooth
private local instance pointedBallSourceOne (i : ℕ) : IsManifold I 1 (X.obj i).M :=
  IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
private local instance pointedBallSourceT2 (i : ℕ) : T2Space (X.obj i).M := (X.obj i).t2
private local instance pointedBallSourceSigma (i : ℕ) : SigmaCompactSpace (X.obj i).M :=
  (X.obj i).sigmaCompact
private local instance pointedBallSourceTangentT2 (i : ℕ) :
    T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
private local instance pointedBallSourceMeasurable (i : ℕ) : MeasurableSpace (X.obj i).M :=
  borel (X.obj i).M
private local instance pointedBallSourceBorel (i : ℕ) : BorelSpace (X.obj i).M := ⟨rfl⟩

theorem pointed_ball_volume_lower_of_eventually
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L) (v : ℝ≥0∞)
    (hsource : ∀ s : ℝ, 0 < s → ∀ᶠ k : ℕ in atTop,
      v * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
          (X.obj (subseq k)).metric
          (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint s)) :
    ∀ r : ℝ, 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric L.basepoint r) := by
  intro r hr
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  let n := Module.finrank ℝ E
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : Tendsto epsilon atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Tendsto (fun j => 1 + epsilon j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hepsilon
  have hs : Tendsto s atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hpow : Tendsto (fun j => ENNReal.ofReal ((s j) ^ n)) atTop
      (𝓝 (ENNReal.ofReal (r ^ n))) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.pow n)
  have hleft := ENNReal.Tendsto.const_mul (a := v) hpow
    (Or.inl (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne')
  have hsqrt : Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ n)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow n)
  have hcoef : Tendsto (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hright : Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric L.basepoint r))
      atTop (𝓝 (riemannianVolumeMeasure (I := I) (M := L.M) L.metric
        (riemannianBallOf L.metric L.basepoint r))) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro j
  have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
  have h1 : 0 < 1 + epsilon j := by linarith
  have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
  have hbuffer : (1 + epsilon j) * s j < r := by
    calc
      (1 + epsilon j) * s j = r / (1 + epsilon j) := by
        dsimp only [s]
        field_simp [ne_of_gt h1]
      _ < r := (div_lt_iff₀ h1).2 (by nlinarith)
  obtain ⟨k0, hk0⟩ := exists_pointed_buffered_ball_volume_le C hreference hcomplete
    hsj he hbuffer he
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp (hsource (s j) hsj)
  exact (hk1 (max k0 k1) (Nat.le_max_right _ _)).trans
    (hk0 (max k0 k1) (Nat.le_max_left _ _))

theorem pointed_ball_volume_lower_of_expanding_radii
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L)
    (hsourceComplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) (X.obj i).metric 0)
    (hsubseq : StrictMono subseq) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (v : ℝ≥0∞)
    (hsource : ∀ i : ℕ,
      v * ENNReal.ofReal ((R i) ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
          (riemannianBallOf (X.obj i).metric (X.obj i).basepoint (R i))) :
    (∀ r : ℝ, 0 < r →
      v * ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric
          (riemannianBallOf L.metric L.basepoint r)) ∧
    v / euclideanUnitBallVolume (Module.finrank ℝ E) ≤
      asymptoticVolumeRatio (I := I) L.metric L.basepoint ∧
    (v ≠ 0 → NoncompactSpace L.M) := by
  have hfixed : ∀ s : ℝ, 0 < s → ∀ᶠ k : ℕ in atTop,
      v * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
          (X.obj (subseq k)).metric
          (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint s) := by
    intro s hs
    have hexpand : Tendsto (fun k => R (subseq k)) atTop atTop :=
      hR.comp hsubseq.tendsto_atTop
    filter_upwards [hexpand.eventually_ge_atTop s] with k hk
    let _ : ConnectedSpace (X.obj (subseq k)).M := hconnected (subseq k)
    have hg : RiemannianMetricComplete (I := I) (X.obj (subseq k)).metric :=
      ⟨MetricComplete.complete (I := I) (X.obj (subseq k))
        (hsourceComplete.complete (subseq k))⟩
    have hbig : 0 < R (subseq k) := hs.trans_le hk
    have hbishop := (riemannianBallOf_volume_bishop_nonnegative
      (I := I) (M := (X.obj (subseq k)).M)
      (X.obj (subseq k)).metric hg (hRic (subseq k))
      (X.obj (subseq k)).basepoint).1 s (R (subseq k)) hs hk
    have hraw := (mul_le_mul_left (hsource (subseq k))
      (ENNReal.ofReal (s ^ Module.finrank ℝ E))).trans hbishop
    have hp0 : ENNReal.ofReal ((R (subseq k)) ^ Module.finrank ℝ E) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (pow_pos hbig _)).ne'
    apply (ENNReal.mul_le_mul_iff_right hp0 ENNReal.ofReal_ne_top).1
    calc
      ENNReal.ofReal ((R (subseq k)) ^ Module.finrank ℝ E) *
          (v * ENNReal.ofReal (s ^ Module.finrank ℝ E)) =
        (v * ENNReal.ofReal ((R (subseq k)) ^ Module.finrank ℝ E)) *
          ENNReal.ofReal (s ^ Module.finrank ℝ E) := by ac_rfl
      _ ≤ _ := hraw
  have hlimit := pointed_ball_volume_lower_of_eventually C hcanonical hcomplete v hfixed
  exact ⟨hlimit, asymptoticVolumeRatio_lower_of_ball_volume_lower
    (I := I) (M := L.M) L.metric L.basepoint v hlimit,
    fun hv => noncompact_of_positive_ball_volume_lower
      (I := I) (M := L.M) L.metric L.basepoint v hv hlimit⟩

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
