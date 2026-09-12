import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SmallBallEuclideanRatio
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

section Static

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

private local instance halfScaleMeasurable : MeasurableSpace M := borel M
private local instance halfScaleBorel : BorelSpace M := ⟨rfl⟩

theorem exists_halfEuclideanScale
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M)
    (hunit : riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p 1) <
      euclideanUnitBallVolume (Module.finrank ℝ E) / 2) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta) =
        (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
          ENNReal.ofReal (delta ^ Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  let omega := euclideanUnitBallVolume n
  let theta : ℝ → ℝ := fun r =>
    (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)).toReal / r ^ n
  have homega : 0 < omega.toReal :=
    ENNReal.toReal_pos (euclideanUnitBallVolume_pos n).ne' (euclideanUnitBallVolume_ne_top n)
  have hhalftop : omega / 2 ≠ ⊤ :=
    ENNReal.div_ne_top (euclideanUnitBallVolume_ne_top n) (by norm_num)
  have hunitfinite :
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hhalftop hunit.le
  have htheta_one : theta 1 < omega.toReal / 2 := by
    have hreal := (ENNReal.toReal_lt_toReal hunitfinite hhalftop).2 hunit
    simpa only [theta, one_pow, div_one, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hreal
  have hlimit : Tendsto theta (𝓝[>] (0 : ℝ)) (𝓝 omega.toReal) :=
    tendsto_riemannianBallOf_realVolume_div_pow_nhdsGT_zero g hcomplete p
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), omega.toReal / 2 < theta r :=
    hlimit.eventually (Ioi_mem_nhds (half_lt_self homega))
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  obtain ⟨a, ha, htheta_a⟩ := (hsmall.and hnear).exists
  have hcontinuous : ContinuousOn theta (Set.Icc a 1) := by
    intro r hr
    exact (continuousAt_riemannianBallOf_realVolume_div_pow g hcomplete p
      (ha.1.trans_le hr.1)).continuousWithinAt
  obtain ⟨delta, hdelta, hequal⟩ :=
    intermediate_value_Icc' ha.2.le hcontinuous ⟨htheta_one.le, htheta_a.le⟩
  have hdelta_pos : 0 < delta := ha.1.trans_le hdelta.1
  have hdelta_lt : delta < 1 := by
    by_contra hn
    have hdelta_one : delta = 1 := le_antisymm hdelta.2 (le_of_not_gt hn)
    rw [hdelta_one] at hequal
    exact htheta_one.ne hequal
  have hdeltafinite :
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta) ≠ ⊤ :=
    ne_top_of_le_ne_top hunitfinite
      (measure_mono (riemannianBallOf_mono (I := I) g p hdelta.2))
  have hrealEqual :
      (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta)).toReal =
        (omega.toReal / 2) * delta ^ n :=
    (div_eq_iff (pow_ne_zero _ hdelta_pos.ne')).1 hequal
  refine ⟨delta, hdelta_pos, hdelta_lt, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' hdeltafinite
    (ENNReal.mul_ne_top hhalftop ENNReal.ofReal_ne_top)).1
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (pow_nonneg hdelta_pos.le _)] using hrealEqual

end Static

section VaryingPointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (X : PointedRiemannianSeq.{u, uE, uH} (I := I))

private local instance halfScaleSourceTopology (i : ℕ) : TopologicalSpace (X.obj i).M :=
  (X.obj i).topology
private local instance halfScaleSourceCharted (i : ℕ) : ChartedSpace H (X.obj i).M :=
  (X.obj i).charted
private local instance halfScaleSourceSmooth (i : ℕ) : IsManifold I ∞ (X.obj i).M :=
  (X.obj i).smooth
private local instance halfScaleSourceT2 (i : ℕ) : T2Space (X.obj i).M := (X.obj i).t2
private local instance halfScaleSourceSigma (i : ℕ) : SigmaCompactSpace (X.obj i).M :=
  (X.obj i).sigmaCompact
private local instance halfScaleSourceTangentT2 (i : ℕ) : T2Space (TangentBundle I (X.obj i).M) :=
  (X.obj i).t2TangentBundle
private local instance halfScaleSourceMeasurable (i : ℕ) : MeasurableSpace (X.obj i).M :=
  borel (X.obj i).M
private local instance halfScaleSourceBorel (i : ℕ) : BorelSpace (X.obj i).M := ⟨rfl⟩

theorem exists_halfEuclideanScales_tendsto_zero
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hunit : ∀ i : ℕ,
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1) <
          euclideanUnitBallVolume (Module.finrank ℝ E) / 2)
    (hcollapse : Tendsto (fun i : ℕ =>
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1))
      atTop (𝓝 0)) :
    ∃ delta : ℕ → ℝ,
      (∀ i : ℕ, 0 < delta i ∧ delta i < 1 ∧
        riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
          (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint (delta i)) =
            (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
              ENNReal.ofReal ((delta i) ^ Module.finrank ℝ E)) ∧
      Tendsto delta atTop (𝓝 0) := by
  classical
  have hscales : ∀ i : ℕ, ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint delta) =
          (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
            ENNReal.ofReal (delta ^ Module.finrank ℝ E) := by
    intro i
    let _ : ConnectedSpace (X.obj i).M := hconnected i
    have hg : RiemannianMetricComplete (I := I) (X.obj i).metric :=
      ⟨hcomplete.complete i⟩
    exact exists_halfEuclideanScale (I := I) (X.obj i).metric hg
      (X.obj i).basepoint (hunit i)
  choose delta hpositive hsmall hequal using hscales
  refine ⟨delta, fun i => ⟨hpositive i, hsmall i, hequal i⟩, ?_⟩
  let n := Module.finrank ℝ E
  let a : ℝ≥0∞ := euclideanUnitBallVolume n / 2
  have ha : 0 < a :=
    ENNReal.div_pos (euclideanUnitBallVolume_pos n).ne' (by norm_num)
  have hbound : ∀ i : ℕ, a * ENNReal.ofReal ((delta i) ^ n) ≤
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1) := by
    intro i
    exact (hequal i).symm.le.trans
      (measure_mono (riemannianBallOf_mono (I := I) (X.obj i).metric
        (X.obj i).basepoint (hsmall i).le))
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthreshold : 0 < a * ENNReal.ofReal (epsilon ^ n) :=
    ENNReal.mul_pos ha.ne' (ENNReal.ofReal_pos.mpr (pow_pos hepsilon n)).ne'
  filter_upwards [hcollapse.eventually (Iio_mem_nhds hthreshold)] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpositive i).le]
  by_contra hn
  have hle : epsilon ≤ delta i := le_of_not_gt hn
  have hpower : ENNReal.ofReal (epsilon ^ n) ≤ ENNReal.ofReal ((delta i) ^ n) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hepsilon.le hle n)
  exact hi.not_ge ((mul_le_mul_right hpower a).trans (hbound i))

end VaryingPointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
