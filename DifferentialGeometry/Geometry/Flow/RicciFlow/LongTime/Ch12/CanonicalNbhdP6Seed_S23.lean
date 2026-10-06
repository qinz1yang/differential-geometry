import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerSeed_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# CH12-S23 / K2a, group S: seed conversions

* `physSeed_S23`: a normalised seed `(a, v)` of a regular slice is a physical seed of radius `a√t`
  (`sec ≥ -(a√t)⁻²`, `vol ≥ v (a√t)³`) for `s.metric`.
* `hasSmall_of_traced_S23`: a traced region `(ρ, τ, K)` gives `hasSmallParabolicCurvature r`
  (KL84.1 (1)(2)) for `r ≤ ρ`, `r² ≤ τ`, `K ≤ 1/(3r²)`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

/-- Normalised seed `(a, v)` ⇒ physical seed of radius `a √t`. -/
theorem physSeed_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (s : RegularSlice F.observation) (p : s.stage.Carrier)
    {a v : ℝ} (ha : 0 < a) (h : HasNormalizedSeed_S13 s p a v) :
    (∀ q ∈ riemannianBallOf s.metric p (a * Real.sqrt s.time),
        SectionalBoundedBelowAt s.metric q (-((a * Real.sqrt s.time) ^ 2)⁻¹)) ∧
      ENNReal.ofReal (v * (a * Real.sqrt s.time) ^ 3) ≤
        ballVolume s.metric p (a * Real.sqrt s.time) := by
  have ht := s.positive
  have hst : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
  have hc : 0 < s.time⁻¹ := inv_pos.mpr ht
  have hs : Real.sqrt s.time⁻¹ * (a * Real.sqrt s.time) = a := by
    rw [Real.sqrt_inv]; field_simp
  have hb := riemannianBallOf_scaleMetric (I := ThreeModel) s.time⁻¹ hc s.metric p
    (a * Real.sqrt s.time)
  rw [hs] at hb
  refine ⟨fun q hq => ?_, ?_⟩
  · have hq' : q ∈ riemannianBallOf s.normalizedMetric p a := by
      rw [show s.normalizedMetric = scaleMetric s.time⁻¹ hc s.metric from rfl, hb]; exact hq
    have h1 := (sectionalBoundedBelowAt_scaleMetric_iff hc).mp (h.1 q hq')
    have hK : -(a ^ 2)⁻¹ * s.time⁻¹ = -((a * Real.sqrt s.time) ^ 2)⁻¹ := by
      rw [mul_pow, Real.sq_sqrt ht.le]; field_simp
    rwa [hK] at h1
  · have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
    have h2 := h.2
    rw [← hs] at h2
    exact (le_ballVolume_scaleMetric_iff hdim s.time⁻¹ hc).mp h2

/-- Traced region ⇒ `hasSmallParabolicCurvature` (KL84.1 (1)(2)). -/
theorem hasSmall_of_traced_S23 {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {ρ τ K r : ℝ} (h : H.isTracedRegion t p ρ τ K)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hrτ : r ^ 2 ≤ τ) (hK0 : 0 ≤ K)
    (hK : K ≤ ((Real.sqrt 3 * r) ^ 2)⁻¹) :
    hasSmallParabolicCurvature H t p r := by
  have h' := h.mono hr hrρ (by positivity) hrτ hK0 hK
  obtain ⟨-, -, a, hat, ha, htr⟩ := h'
  have hr3 : 0 < Real.sqrt 3 * r := by positivity
  refine ⟨hr, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨A, hA⟩ := htr x hx
  exact ⟨A, (A.isRmControlled_iff_isRmBoundedBy hr3).2 hA⟩

/-- Normalised ball = physical ball of radius `b √t`. -/
theorem ball_norm_eq_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (s : RegularSlice F.observation) (p : s.stage.Carrier)
    (b : ℝ) :
    riemannianBallOf s.normalizedMetric p b =
      riemannianBallOf s.metric p (b * Real.sqrt s.time) := by
  have ht := s.positive
  have hst : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
  have hc : 0 < s.time⁻¹ := inv_pos.mpr ht
  have hs : Real.sqrt s.time⁻¹ * (b * Real.sqrt s.time) = b := by
    rw [Real.sqrt_inv]; field_simp
  have hb := riemannianBallOf_scaleMetric (I := ThreeModel) s.time⁻¹ hc s.metric p
    (b * Real.sqrt s.time)
  rw [hs] at hb
  exact hb

/-- Physical seed of radius `b √t` ⇒ normalised seed `(b, w)`. -/
theorem normSeed_of_phys_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (s : RegularSlice F.observation) (p : s.stage.Carrier)
    {b w : ℝ}
    (hsec : ∀ q ∈ riemannianBallOf s.metric p (b * Real.sqrt s.time),
        SectionalBoundedBelowAt s.metric q (-((b * Real.sqrt s.time) ^ 2)⁻¹))
    (hvol : ENNReal.ofReal (w * (b * Real.sqrt s.time) ^ 3) ≤
        ballVolume s.metric p (b * Real.sqrt s.time)) :
    HasNormalizedSeed_S13 s p b w := by
  have ht := s.positive
  have hc : 0 < s.time⁻¹ := inv_pos.mpr ht
  have hs : Real.sqrt s.time⁻¹ * (b * Real.sqrt s.time) = b := by
    have hst : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
    rw [Real.sqrt_inv]; field_simp
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [show s.normalizedMetric = scaleMetric s.time⁻¹ hc s.metric from rfl,
      sectionalBoundedBelowAt_scaleMetric_iff hc]
    have hq' : q ∈ riemannianBallOf s.metric p (b * Real.sqrt s.time) := by
      rw [← ball_norm_eq_S23]; exact hq
    have h1 := hsec q hq'
    have hK : -(b ^ 2)⁻¹ * s.time⁻¹ = -((b * Real.sqrt s.time) ^ 2)⁻¹ := by
      rw [mul_pow, Real.sq_sqrt ht.le]; field_simp
    rwa [hK]
  · have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
    rw [show s.normalizedMetric = scaleMetric s.time⁻¹ hc s.metric from rfl]
    have := (le_ballVolume_scaleMetric_iff hdim s.time⁻¹ hc (g := s.metric) (p := p) (w := w)
      (t := b * Real.sqrt s.time)).mpr hvol
    rwa [hs] at this

end GC.LongTime.Ch12
