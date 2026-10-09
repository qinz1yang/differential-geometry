import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113

/-!
# CH12-S133, group 3a (partial): cap exclusion of a point by `hnc` + the cap-window clause `hCapWin`

`exists_regularCrossing_of_nc_S133` = step 2 of the F-S130 first-exit plan (obstacle F-S130-1, lead ruling A): a point `q` of the
output stage of event `j` with output scalar `≤ S`, which is not a young cap-window point (the `hnc` clause of `hcore`: no
`x` with `‖x‖ < Dc+1`, `window x = q`, `age ≤ θ / neck.scale`), has a regular-crossing preimage.  Uses the record clause
`hCapWin` (every cap point is a window point `‖x‖ < Dc+1`, `[FROZEN] CH12-S133 hCapWin`) and the cap-scale clause of
`hscale_of_record_S105` (`c₀ · neck.scale ≤ scalar (window x)`), so `neck.scale ≤ S / c₀` and `age · S ≤ c₀ θ` gives
`age ≤ θ / neck.scale`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem exists_regularCrossing_of_nc_S133 {H : ObservedHistory.{u}} {j : Fin H.eventCount}
    {pp : CutoffParameters} (R : GeometricCutoffRecord H j pp) {Dc c₀ S age θ : ℝ}
    (hc₀ : 0 < c₀) (hage0 : 0 ≤ age)
    (hcap : ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dc + 1 ∧
        (R.static b).window x = (R.static b).inclusion ((R.static b).witness.cap z))
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 1 →
        c₀ * (R.static b).neck.scale ≤ metricScalarAt (H.event j).outputMetric ((R.static b).window x))
    (q : (H.stage j.succ).Carrier) (hq : metricScalarAt (H.event j).outputMetric q ≤ S)
    (hage : age * S ≤ c₀ * θ)
    (hno : ¬ ∃ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      (R.static b).window x = q ∧ ‖x.val‖ < Dc + 1 ∧ age ≤ θ * ((R.static b).neck.scale)⁻¹) :
    ∃ p' : (H.stage j.castSucc).Carrier, (H.event j).RegularCrossing p' q := by
  rcases R.exists_regularCrossing_or_exists_cap q with h | ⟨b, z, hz⟩
  · exact h
  · exfalso
    obtain ⟨x, hx, hwx⟩ := hcap b z
    apply hno
    refine ⟨b, x, hwx.trans hz.symm, hx, ?_⟩
    have hsc := hscale b x hx
    have hqs : metricScalarAt (H.event j).outputMetric ((R.static b).window x) ≤ S := by
      rw [hwx, ← hz]; exact hq
    have hpos := (R.static b).neck.scale_pos
    have h1 : c₀ * (R.static b).neck.scale ≤ S := hsc.trans hqs
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    have h2 : c₀ * (age * (R.static b).neck.scale) ≤ c₀ * θ := by
      nlinarith only [mul_le_mul_of_nonneg_left h1 hage0, hage]
    exact le_of_mul_le_mul_left h2 hc₀

end GC.LongTime.Ch12
