import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreRecentre_O31

/-!
# CH12-O31, group 3: non-round strong witnesses with uniform centre volume (`[FROZEN v2] CH12-O31 G3`)

`strong_witness_nonround_volume_O31`: at a late point `x` strictly above the canonical threshold
that sees, in its own component, a point `z` with `R(z) > C2 R(x)`, the `hStrong` witness is not a
whole-component alternative (`SpatialCanonicalWitness.scalar_bounds_of_isWholeComponent` would give
`R(z) ≤ C2 R(x)`), hence `requiresVolume` holds and `centre_volume_of_witness_O14` gives the
normalized centre volume `vol B(x, b) ≥ κ b³` (`b ≤ C2^{-1/2}`, metric scaled by `R(x)`) with
`κ = κ(ε, C1, C2)`.  This removes the round/whole-component exception (review R3 Q3(c), gap 1) and
supplies the centre volume at second blow-up centres (gap 3) in the KL70.2 route.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **Non-round strong witness with uniform centre volume** (`[FROZEN v2] CH12-O31 G3`).
The neck clause of `hStrong` is a free predicate `NK` (instances: `[FROZEN] CH12-O23 hStrong` and
`[FROZEN v2] CH12-O31 hStrong`); it is passed through unchanged. -/
theorem strong_witness_nonround_volume_O31 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (NK : ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
      (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x → Prop)
    (hStrong : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧ NK s x hR W) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∀ z : s.stage.Carrier, riemannianEDistOf s.metric x z < ⊤ →
        Hp.C2 * metricScalarAt s.metric x < metricScalarAt s.metric z →
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧ ¬ W.alternative.isWholeComponent ∧
        (∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
          ENNReal.ofReal (κ * b ^ 3) ≤
            riemannianVolumeMeasure ThreeModel s.stage.Carrier
              (scaleMetric (metricScalarAt s.metric x) W.Q_pos s.metric)
              (riemannianBallOf (scaleMetric (metricScalarAt s.metric x) W.Q_pos s.metric) x b)) ∧
        NK s x hR W := by
  obtain ⟨κ, hκ, hvol⟩ := centre_volume_of_witness_O14.{u} Hp.epsilon Hp.C1 Hp.C2
    (lt_of_lt_of_le one_pos Hp.C2_ge_one)
  obtain ⟨T, hT⟩ := hStrong
  refine ⟨κ, hκ, T, ?_⟩
  intro s hs x hR z hz hzx
  obtain ⟨W, hchart, hstrong⟩ := hT s hs x hR
  have hnw : ¬ W.alternative.isWholeComponent := fun hw =>
    absurd (W.scalar_bounds_of_isWholeComponent hw hz).2 (not_le.mpr hzx)
  have hreq : W.alternative.requiresVolume := by
    cases hA : W.alternative with
    | round whole data =>
      exact (hnw (by rw [hA]; exact True.intro)).elim
    | neck data => exact True.intro
    | cap cap deep => exact True.intro
    | positive whole data sec =>
      exact (hnw (by rw [hA]; exact True.intro)).elim
  exact ⟨W, hchart, hnw, hvol W hchart hreq, hstrong⟩

end GC.LongTime.Ch12
