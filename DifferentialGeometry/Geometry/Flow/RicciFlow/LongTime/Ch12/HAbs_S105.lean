import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapWindowTransfer_S105
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses

/-!
# CH12-S105, group 2 (history level): `hAbs` (S95 binder form), constants, birth shift; RFC-b reduction

* `hAbs_S105`: the absorption clause `hAbs` of `located_barrier_of_noCAP_S95`, for an arbitrary
  predicate `CAPat`, from the event-level `cap_of_lowscalar_S105` and the glue clause `hglue`
  (window point + age clause for the centre `c i hW` of event `i` ⇒ `CAPat i`; for the S64 CAP clause
  it is the trace-point glue, which only has to produce a trace `B` with `B.point = c i hW`).
* `hscale_of_record_S105`: `hscale` (cap scalar lower bound at every window point) from the record fields.
* `shift_le_of_birth_S105`: `40 r √q ≤ 1` from the birth bound `q ≤ 16 C₀/ρ²`, `r = a ρ`.
* `rfcB_of_collar_dist_S105`: RFC-b from the (still to be proved) collar-distance clause `hdist`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- `hAbs` of `located_barrier_of_noCAP_S95` (window point of a low-scalar set in the 20 r-ball ⇒ `CAPat i`). -/
theorem hAbs_S105 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    (T₀ θ Dc r K Tc τ c₀ : ℝ) (W : Fin H.eventCount → Prop)
    (records : ∀ i : Fin H.eventCount, T₀ - θ ≤ H.time i.succ → GeometricCutoffRecord H i pp)
    (c : ∀ i : Fin H.eventCount, W i → (H.stage i.succ).Carrier)
    (CAPat : Fin H.eventCount → Prop)
    (hr : 0 < r) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hτK : 9 * K * τ ≤ c₀ * θ)
    (hD : Dc + 2 ≤ pp.modelRadius) (hacc : pp.modelAccuracy ≤ 3 / 4)
    (hscale : ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 1 → c₀ * ((records i hi).static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric (((records i hi).static b).window x))
    (hshift : ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ) (_ : W i)
      (b : (H.event i).RetainedBoundaryIndex),
      40 * r * Real.sqrt ((records i hi).static b).neck.scale ≤ 1)
    (hage : ∀ (i : Fin H.eventCount) (_ : W i), Tc - H.time i.succ < τ * r ^ 2)
    (hglue : ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ) (hW : W i),
      (∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        ‖x.val‖ < Dc + 2 ∧ ((records i hi).static b).window x = c i hW ∧
          Tc - H.time i.succ ≤ θ * ((records i hi).static b).neck.scale⁻¹) → CAPat i) :
    ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ)
      (hW : W i) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      (∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        ‖x.val‖ < Dc + 1 ∧ ((records i hi).static b).window x ∈ U) → CAPat i := by
  intro i hi hW U hUb hs ⟨b, x, hx, hxU⟩
  obtain ⟨w', hw', he, hag⟩ := cap_of_lowscalar_S105 ((records i hi).static b) hacc hr hτ hc₀ hD
    (hscale i hi b) (hshift i hi hW b) (hage i hW) hτK hUb hs hx hxU
  exact hglue i hi hW ⟨b, w', hw', he, hag⟩

/-- `hscale` from the record fields: constants `ε₀ c₀` (absolute) such that accuracy `≤ ε₀` and order `≥ 4`
give `c₀ q ≤ scalar_out (window x)` for every `‖x‖ < modelRadius`. -/
theorem hscale_of_record_S105 : ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
    ∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀ → 4 ≤ pp.modelOrder → ∀ (R : GeometricCutoffRecord H i pp)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < pp.modelRadius → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric ((R.static b).window x) := by
  obtain ⟨ε₀, c₀, hε₀, hc₀, h⟩ := window_scalar_lower_S105.{u}
  exact ⟨ε₀, c₀, hε₀, hc₀, fun hε hm R b x hx => h (R.static b) hε hm x hx⟩

/-- The birth shift: `q ≤ 16 C₀ / ρ²`, `r = a ρ`, `160 a √C₀ ≤ 1` give `40 r √q ≤ 1`. -/
theorem shift_le_of_birth_S105 {q ρ r a C₀ : ℝ} (hρ : 0 < ρ) (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a)
    (hq : q ≤ 16 * C₀ / ρ ^ 2) (hr : r = a * ρ) (ha' : a * (160 * Real.sqrt C₀) ≤ 1) :
    40 * r * Real.sqrt q ≤ 1 := by
  have hsC : 0 ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
  have hsq : Real.sqrt q ≤ 4 * Real.sqrt C₀ / ρ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow, Real.sq_sqrt hC₀]
    norm_num
    exact hq
  have h1 : 40 * r * Real.sqrt q ≤ 40 * r * (4 * Real.sqrt C₀ / ρ) :=
    mul_le_mul_of_nonneg_left hsq (by rw [hr]; positivity)
  refine h1.trans ?_
  rw [hr]
  have : 40 * (a * ρ) * (4 * Real.sqrt C₀ / ρ) = a * (160 * Real.sqrt C₀) := by
    field_simp
    ring
  rw [this]
  exact ha'

/-- RFC-b from the collar-distance clause `hdist` (every retained collar point with `z' ≤ 1` is within
`3/(2√q)` of the image of a cap point) and the linked canonical window (`‖x₀‖ ≤ transitionEnd` for cap points). -/
theorem rfcB_of_collar_dist_S105 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H i pp)
    (b : (H.event i).RetainedBoundaryIndex) {Dc : ℝ}
    (hlink : linkedCanonicalWindow_O2 (R.static b)) (hacc : pp.modelAccuracy ≤ 3 / 4)
    (hDc : StandardCap.transitionEnd + 2 ≤ Dc)
    (hD : StandardCap.transitionEnd + 3 < pp.modelRadius)
    (hdist : ∀ c : neckRetainedCollar (R.static b).delta, c.1.2 ≤ 1 →
      ∃ z : ThreeBall, riemannianEDistOf (H.event i).outputMetric
        ((R.static b).inclusion ((R.static b).witness.cap z))
        ((R.static b).inclusion ((R.static b).witness.retained c)) <
          ENNReal.ofReal (3 / (2 * Real.sqrt (R.static b).neck.scale))) :
    ∀ c : neckRetainedCollar (R.static b).delta, c.1.2 ≤ 1 →
      ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dc + 1 ∧
        (R.static b).window x = (R.static b).inclusion ((R.static b).witness.retained c) := by
  intro c hc
  obtain ⟨z, hz⟩ := hdist c hc
  obtain ⟨-, -, -, -, -, -, -, h3, -, -⟩ := hlink
  obtain ⟨x₀, hx₀, hx₀e⟩ := h3 z
  have hq := (R.static b).neck.scale_pos
  have hsq : 0 < Real.sqrt (R.static b).neck.scale := Real.sqrt_pos.mpr hq
  have hρ : 0 < 3 / (2 * Real.sqrt (R.static b).neck.scale) := by positivity
  have hmul : 2 * (Real.sqrt (R.static b).neck.scale * (3 / (2 * Real.sqrt (R.static b).neck.scale))) = 3 := by
    field_simp
  have hroom : ‖x₀.val‖ + 2 * (Real.sqrt (R.static b).neck.scale *
      (3 / (2 * Real.sqrt (R.static b).neck.scale))) < pp.modelRadius := by
    rw [hmul]; linarith only [hx₀, hD]
  have hball : (R.static b).inclusion ((R.static b).witness.retained c) ∈
      riemannianBallOf (H.event i).outputMetric ((R.static b).window x₀)
        (3 / (2 * Real.sqrt (R.static b).neck.scale)) := by
    change riemannianEDistOf (H.event i).outputMetric ((R.static b).window x₀) _ < _
    rw [hx₀e]
    exact hz
  obtain ⟨w, hw, hwe⟩ := ball_subset_window_S105 (R.static b) hacc x₀ hρ hroom hball
  refine ⟨w, ?_, hwe⟩
  have hw' : ‖w.val‖ < ‖x₀.val‖ + 2 * (Real.sqrt (R.static b).neck.scale *
      (3 / (2 * Real.sqrt (R.static b).neck.scale))) := hw
  rw [hmul] at hw'
  linarith only [hw', hx₀, hDc]

end GC.LongTime.Ch12
