import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickRadiusTransfer_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCompact_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferRadius_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ImageVolumeLower_S100
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture

set_option autoImplicit false

/-! # CH12-S114 G1a: auxiliary lemmas for the HLOW producer.

* `exists_curvatureRadius_real_S114`: lower sectional bound `-(c²)⁻¹` on `B(x, c)` and a plane violating `-1/8`
  at `x` give a real `r ∈ [c, √8]` with `curvatureRadius g x = ofReal r`.
* `exists_uniform_ball_volume_S114`: for a finite-volume hyperbolic model `H`, `R, ρ`, there is `v > 0` with
  `ofReal v ≤ vol_H(B(y, ρ))` for all `y ∈ B(base, R)` (compact closed ball + finite cover). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section CurvRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem curvatureRadius_le_sqrt8_S114 (g : SmoothRiemannianMetric I M) (x : M)
    (hup : ¬ SectionalBoundedBelowAt g x (-(1 / 8 : ℝ))) :
    curvatureRadius g x ≤ ENNReal.ofReal (Real.sqrt 8) := by
  unfold curvatureRadius
  refine iSup_le fun r' => iSup_le fun hr' => iSup_le fun hP => ENNReal.ofReal_le_ofReal ?_
  by_contra hcon
  have hlt : Real.sqrt 8 < r' := not_le.mp hcon
  have h8 : (8 : ℝ) < r' ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
    nlinarith [Real.sqrt_nonneg 8]
  have hx : x ∈ riemannianBallOf g x r' := by
    change riemannianEDistOf g x x < ENNReal.ofReal r'
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr'
  refine hup ((hP x hx).mono ?_)
  have : ((r' ^ 2)⁻¹ : ℝ) ≤ 1 / 8 := by
    rw [← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem exists_curvatureRadius_real_S114 (g : SmoothRiemannianMetric I M) (x : M) {c : ℝ}
    (hc : 0 < c)
    (hlow : ∀ q ∈ riemannianBallOf g x c, SectionalBoundedBelowAt g q (-(c ^ 2)⁻¹))
    (hup : ¬ SectionalBoundedBelowAt g x (-(1 / 8 : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ curvatureRadius g x = ENNReal.ofReal r ∧ c ≤ r ∧ r ^ 2 ≤ 8 := by
  have h1 : ENNReal.ofReal c ≤ curvatureRadius g x :=
    le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le hlow le_rfl))
  have h2 := curvatureRadius_le_sqrt8_S114 g x hup
  have hne : curvatureRadius g x ≠ ⊤ := (h2.trans_lt ENNReal.ofReal_lt_top).ne
  set r : ℝ := (curvatureRadius g x).toReal with hr
  have hcr : curvatureRadius g x = ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_toReal hne]
  have hcpos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hrpos : 0 < r := by
    have : 0 < curvatureRadius g x := hcpos.trans_le h1
    rw [hr]; exact ENNReal.toReal_pos this.ne' hne
  obtain ⟨hr1, hr8⟩ := curvatureRadius_bounds_S35 g x hc hlow hup hrpos hcr
  exact ⟨r, hrpos, hcr, hr1, hr8⟩

end CurvRadius

theorem exists_real_pos_ofReal_le_S114 {p : ℝ≥0∞} (hp : 0 < p) : ∃ u : ℝ, 0 < u ∧ ENNReal.ofReal u ≤ p := by
  obtain ⟨u, hu0, hu1, hu2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp
  exact ⟨u, ENNReal.ofReal_pos.mp hu1, hu2.le⟩

theorem exists_finset_lower_S114 {X : Type*} (f : X → ℝ≥0∞) (hf : ∀ x, 0 < f x) (s : Finset X) :
    ∃ v : ℝ, 0 < v ∧ ∀ x ∈ s, ENNReal.ofReal v ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert a s ha ih =>
    obtain ⟨v, hv, hvs⟩ := ih
    obtain ⟨u, hu, hua⟩ := exists_real_pos_ofReal_le_S114 (hf a)
    refine ⟨min v u, lt_min hv hu, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hua
    · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hvs x hx)

theorem exists_uniform_ball_volume_S114 (H : FiniteVolumeHyperbolicModel.{u}) (R : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ v : ℝ, 0 < v ∧ ∀ y ∈ riemannianBallOf H.metric H.basepoint R,
      ENNReal.ofReal v ≤ DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
        H.Carrier H.metric (riemannianBallOf H.metric y ρ) := by
  classical
  have hopen : ∀ x : H.Carrier, IsOpen (riemannianBallOf H.metric x (ρ / 2)) := fun x =>
    isOpen_riemannianBallOf H.metric x (ρ / 2)
  have hself : ∀ x : H.Carrier, x ∈ riemannianBallOf H.metric x (ρ / 2) := fun x => by
    change riemannianEDistOf H.metric x x < ENNReal.ofReal (ρ / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hK := isCompact_closedBall_S98 H R
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : H.Carrier => riemannianBallOf H.metric x (ρ / 2))
    hopen (fun x _ => mem_iUnion.mpr ⟨x, hself x⟩)
  have : (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier
      H.metric).IsOpenPosMeasure :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure H.metric
  obtain ⟨v, hv, hvt⟩ := exists_finset_lower_S114
    (fun x : H.Carrier => DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
      H.Carrier H.metric (riemannianBallOf H.metric x (ρ / 2)))
    (fun x => (hopen x).measure_pos _ ⟨x, hself x⟩) t
  refine ⟨v, hv, fun y hy => ?_⟩
  have hyK : y ∈ {x : H.Carrier | riemannianEDistOf H.metric H.basepoint x ≤ ENNReal.ofReal R} :=
    (show riemannianEDistOf H.metric H.basepoint y ≤ ENNReal.ofReal R from (hy : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal R).le)
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hyK)
  refine (hvt x hxt).trans (MeasureTheory.measure_mono fun z hz => ?_)
  change riemannianEDistOf H.metric x y < ENNReal.ofReal (ρ / 2) at hyx
  change riemannianEDistOf H.metric x z < ENNReal.ofReal (ρ / 2) at hz
  change riemannianEDistOf H.metric y z < ENNReal.ofReal ρ
  calc riemannianEDistOf H.metric y z
      ≤ riemannianEDistOf H.metric y x + riemannianEDistOf H.metric x z :=
        riemannianEDistOf_triangle H.metric y x z
    _ < ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) := by
        rw [riemannianEDistOf_comm H.metric y x]
        exact ENNReal.add_lt_add hyx hz
    _ = ENNReal.ofReal ρ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end GC.LongTime.Ch12
