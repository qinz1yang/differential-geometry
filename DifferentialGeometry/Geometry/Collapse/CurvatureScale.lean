import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Distance.Neighborhood
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open Filter Set
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Collapse
universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def curvatureRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r)
    (_ : ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)),
    ENNReal.ofReal r

def ballVolume (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) : ℝ≥0∞ :=
  (Integral.Measure.riemannianVolumeMeasure I M g) (riemannianBallOf g p r)

def euclideanThreeUnitBallVolume : ℝ := 4 * Real.pi / 3

def volumeCollapsedAtCurvatureScale (g : SmoothRiemannianMetric I M)
    (w : ℝ) (p : M) : Prop :=
  ∀ r : ℝ, 0 < r → curvatureRadius g p = ENNReal.ofReal r →
    ballVolume g p r ≤ ENNReal.ofReal (w * r ^ 3)

def curvatureDerivativesControlled (g : SmoothRiemannianMetric I M)
    (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) : Prop :=
  ∀ (p : M) (w r : ℝ), w₀ ≤ w → w < euclideanThreeUnitBallVolume →
    0 < r → ENNReal.ofReal r < curvatureRadius g p →
    ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
    ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf g p r,
      curvatureDerivativeNorm g k q ≤ A w * (r ^ (k + 2))⁻¹

omit [SigmaCompactSpace M] in
theorem curvatureRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < curvatureRadius g p := by
  have hcont : Continuous (fun y : M =>
      normSq0S (I := I) g y 4 (metricRm04 (I := I) (M := M) g y)) :=
    Tensor0SBundle.normSq0S_cont (I := I) g (metricRm04 (I := I) (M := M) g)
  have hU : {y : M | normSq0S (I := I) g y 4 (metricRm04 (I := I) (M := M) g y) <
      normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1} ∈ 𝓝 p :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  obtain ⟨r₀, hr₀, hsub⟩ := exists_riemannianBallOf_subset_of_mem_nhds g p hU
  have hK0 : 0 ≤ Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) :=
    Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) + 1 := by
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min r₀
      (1 / (Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) + 1)) :=
    ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min hr₀ (by positivity)
  have hrr₀ : r ≤ r₀ := by
    rw [hr]
    exact min_le_left _ _
  have hrK : r ≤ 1 / (Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) + 1) := by
    rw [hr]
    exact min_le_right _ _
  have hr1 : r ≤ 1 := by
    refine hrK.trans ?_
    rw [div_le_one hden]
    linarith
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hmul : r * (Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) + 1) ≤ 1 := by
    rwa [le_div_iff₀ hden] at hrK
  have hKr2 : Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) * r ^ 2 ≤ 1 := by
    nlinarith
  have hKr : Real.sqrt (normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1) ≤ (r ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (pow_pos hrpos 2)]
    exact hKr2
  have hP : ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
    intro q hq
    have hqU := hsub (riemannianBallOf_mono g p hrr₀ hq)
    have hqC : normSq0S (I := I) g q 4 (metricRm04At (I := I) (M := M) g q) ≤
        normSq0S (I := I) g p 4 (metricRm04 (I := I) (M := M) g p) + 1 := by
      simp only [Set.mem_ofPred_eq, metricRm04_apply] at hqU
      exact hqU.le
    have hsec := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
      (I := I) g q hqC
    exact hsec.mono (by linarith)
  calc (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hrpos
    _ ≤ curvatureRadius g p := by
      unfold curvatureRadius
      exact le_iSup_of_le r (le_iSup_of_le hrpos (le_iSup_of_le hP le_rfl))

private theorem nonneg_of_large_radius (G Rm : ℝ)
    (h : ∀ R : ℝ, ∃ r : ℝ, R < r ∧ 0 < r ∧ -(r ^ 2)⁻¹ * G ≤ Rm) : 0 ≤ Rm := by
  by_contra hneg
  rw [not_le] at hneg
  have hε : 0 < -Rm := by linarith
  obtain ⟨r, hRr, hrpos, hsec⟩ := h (max 1 (|G| / (-Rm) + 1))
  have hR1 : 1 ≤ max 1 (|G| / (-Rm) + 1) := le_max_left _ _
  have hRG : |G| / (-Rm) + 1 ≤ max 1 (|G| / (-Rm) + 1) := le_max_right _ _
  have hr2 : 0 < r ^ 2 := by positivity
  have h1 : (-Rm) * r ^ 2 ≤ G := by
    have h2 : -(G / r ^ 2) ≤ Rm := by rwa [neg_mul, inv_mul_eq_div] at hsec
    have h3 : -Rm ≤ G / r ^ 2 := by linarith
    exact (le_div_iff₀ hr2).mp h3
  have hGabs : G ≤ |G| := le_abs_self G
  have h4 : |G| ≤ (max 1 (|G| / (-Rm) + 1) - 1) * (-Rm) := by
    exact (div_le_iff₀ hε).mp (show |G| / (-Rm) ≤ max 1 (|G| / (-Rm) + 1) - 1 by linarith)
  have hr1 : 1 < r := by linarith
  have hrr : r ≤ r ^ 2 := by nlinarith
  have h5 : (-Rm) * (max 1 (|G| / (-Rm) + 1)) < (-Rm) * r :=
    mul_lt_mul_of_pos_left hRr hε
  have h6 : (-Rm) * r ≤ (-Rm) * r ^ 2 := mul_le_mul_of_nonneg_left hrr hε.le
  nlinarith

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem curvatureRadius_eq_top_iff [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} (p : M) :
    curvatureRadius g p = ⊤ ↔ SectionalBoundedBelow g 0 := by
  constructor
  · intro htop x v w
    rw [zero_mul]
    apply nonneg_of_large_radius
      (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2)
    intro R
    have hfin : riemannianEDistOf (I := I) g p x ≠ ⊤ := riemannianEDistOf_ne_top g p x
    have hlt : ENNReal.ofReal (max R ((riemannianEDistOf (I := I) g p x).toReal + 1)) <
        curvatureRadius g p := by
      rw [htop]
      exact ENNReal.ofReal_lt_top
    unfold curvatureRadius at hlt
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hrpos, hr⟩ := lt_iSup_iff.mp hr
    obtain ⟨hP, hr⟩ := lt_iSup_iff.mp hr
    have hRr : max R ((riemannianEDistOf (I := I) g p x).toReal + 1) < r :=
      (ENNReal.ofReal_lt_ofReal_iff hrpos).mp hr
    refine ⟨r, (le_max_left _ _).trans_lt hRr, hrpos, ?_⟩
    have hx : x ∈ riemannianBallOf g p r := by
      change riemannianEDistOf (I := I) g p x < ENNReal.ofReal r
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr
        (by linarith [le_max_right R ((riemannianEDistOf (I := I) g p x).toReal + 1)])
    exact hP x hx v w
  · intro hsec
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro n
    unfold curvatureRadius
    have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine le_iSup_of_le ((n : ℝ) + 1) (le_iSup_of_le hs (le_iSup_of_le ?_ ?_))
    · intro q _
      exact (hsec q).mono
        (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
    · rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by linarith)

theorem curvatureDerivativesControlled_mono_threshold
    (g : SmoothRiemannianMetric I M) (K : ℕ) (A : ℝ → ℝ)
    {w₁ w₂ : ℝ} (hw : w₁ ≤ w₂)
    (h : curvatureDerivativesControlled g K A w₁) :
    curvatureDerivativesControlled g K A w₂ := by
  intro p w r hw₂ hwc hr hrR hv k hk q hq
  exact h p w r (hw.trans hw₂) hwc hr hrR hv k hk q hq

theorem volumeCollapsedAtCurvatureScale_of_curvatureRadius_eq_top {W : GC.Endpoint.CompactCarrier.{u}} (g : SmoothRiemannianMetric W.model W.Carrier)
    (w : ℝ) (p : W.Carrier) (h : curvatureRadius g p = ⊤) :
    volumeCollapsedAtCurvatureScale g w p := by
  intro r _ hr
  exact False.elim (ENNReal.ofReal_ne_top (h.symm.trans hr).symm)

theorem curvatureDerivativesControlled_mono_control {W : GC.Endpoint.CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {A A' : ℝ → ℝ} {w₀ : ℝ}
    (hAA' : ∀ w, A w ≤ A' w) (h : curvatureDerivativesControlled g K A w₀) :
    curvatureDerivativesControlled g K A' w₀ := by
  intro p w r hw hwupper hr hR hvol k hk q hq
  exact (h p w r hw hwupper hr hR hvol k hk q hq).trans
    (mul_le_mul_of_nonneg_right (hAA' w) (inv_nonneg.mpr (pow_nonneg hr.le _)))

theorem curvatureDerivativesControlled_anti_order {W : GC.Endpoint.CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K K' : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (hKK' : K' ≤ K) (h : curvatureDerivativesControlled g K A w₀) :
    curvatureDerivativesControlled g K' A w₀ := by
  intro p w r hw hwupper hr hR hvol k hk q hq
  exact h p w r hw hwupper hr hR hvol k (hk.trans hKK') q hq

theorem volumeCollapsedAtCurvatureScale_iff_toReal {W : GC.Endpoint.CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {w : ℝ} {p : W.Carrier} (hfinite : curvatureRadius g p ≠ ⊤) :
    volumeCollapsedAtCurvatureScale g w p ↔
      ballVolume g p (curvatureRadius g p).toReal ≤
        ENNReal.ofReal (w * (curvatureRadius g p).toReal ^ 3) := by
  constructor
  · intro h
    exact h _ (ENNReal.toReal_pos (ne_of_gt (curvatureRadius_pos g p)) hfinite)
      (ENNReal.ofReal_toReal hfinite).symm
  · intro h r _ hr
    have hreal : (curvatureRadius g p).toReal = r := by
      rw [hr, ENNReal.toReal_ofReal]
      positivity
    rwa [hreal] at h

end DifferentialGeometry.Geometry.Collapse
