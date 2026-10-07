import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower

/-!
# CH12-S74 G2 (b1'), cap exclusion for a single output point

An output point `q` of event `j` is either a regular-crossing image or a static-cap point
(`exists_regularCrossing_or_exists_cap`).  Cap points have output scalar
`≥ (R.static b).neck.scale / 2 ≥ (nominalRadius²)⁻¹ / 4` (record `scale_eq`, recentering comparison
`recenter_scale_comparison` with `recenterConstant * delta ≤ 1/2`).  Hence a point with scalar
`< C₁² / (4 r0²)` and `C₁ * nominalRadius ≤ r0` has a regular-crossing preimage.  The input
`hscale` (cap scalar `≥ neck.scale / 2`) is the shape used in all `*_O3L` lemmas
(MicroGlueLateRecords.lean:421); it is NOT a field of the record.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature

namespace GC.LongTime.Ch12

universe u

theorem cap_scalar_ge_of_nominal_S74 {H : ObservedHistory.{u}} {j : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H j p) {C₁ r0 : ℝ} (hC₁ : 0 < C₁)
    (hr0 : 0 < r0)
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (H.time j.succ) ≤ 1 / 2)
    (hnom : ∀ h, C₁ * R.nominalRadius h ≤ r0) :
    ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      C₁ ^ 2 / (4 * r0 ^ 2) ≤
        metricScalarAt (H.event j).outputMetric ((R.static b).inclusion ((R.static b).witness.cap z)) := by
  intro b z
  rw [← (R.static b).scalar_eq]
  have hb := R.recenter_scale_comparison b
  have hdel : R.delta b.1.1 ≤ p.delta (H.time j.succ) := R.delta_le _
  have hκ := p.recenterConstant_ge_four
  have h1 : p.recenterConstant * R.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hdel (by linarith)).trans hrc
  have hsrec : 0 < (R.neck b.1.1).scale := (R.neck _).scale_pos
  have hratio : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.1.1).scale := by
    have := abs_le.mp (hb.trans h1)
    linarith [this.1]
  have hst : (R.neck b.1.1).scale / 2 ≤ (R.static b).neck.scale := by
    rw [le_div_iff₀ hsrec] at hratio
    linarith
  have hnom' := hnom ⟨b.1.1⟩
  have hnompos := R.nominal_pos ⟨b.1.1⟩
  have hse := R.scale_eq b.1.1
  set nom := R.nominalRadius ⟨b.1.1⟩ with hnomdef
  have hsq : (C₁ * nom) ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ (by positivity) hnom' 2
  have key : C₁ ^ 2 / r0 ^ 2 ≤ (nom ^ 2)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    calc C₁ ^ 2 = (nom ^ 2)⁻¹ * (C₁ * nom) ^ 2 := by field_simp
      _ ≤ (nom ^ 2)⁻¹ * r0 ^ 2 := by gcongr
  have h2 := hscale b z
  have h3 : C₁ ^ 2 / (4 * r0 ^ 2) = (C₁ ^ 2 / r0 ^ 2) / 4 := by field_simp
  rw [h3]
  rw [hse] at hst
  linarith

theorem exists_regularCrossing_of_scalar_lt_S74 {H : ObservedHistory.{u}} {j : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H j p) {C₁ r0 : ℝ} (hC₁ : 0 < C₁)
    (hr0 : 0 < r0)
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (H.time j.succ) ≤ 1 / 2)
    (hnom : ∀ h, C₁ * R.nominalRadius h ≤ r0)
    (q : (H.stage j.succ).Carrier)
    (hq : metricScalarAt (H.event j).outputMetric q < C₁ ^ 2 / (4 * r0 ^ 2)) :
    ∃ p' : (H.stage j.castSucc).Carrier, (H.event j).RegularCrossing p' q := by
  rcases R.exists_regularCrossing_or_exists_cap q with h | ⟨b, z, rfl⟩
  · exact h
  · exact absurd (cap_scalar_ge_of_nominal_S74 R hC₁ hr0 hscale hrc hnom b z) (not_le.mpr hq)

end GC.LongTime.Ch12
