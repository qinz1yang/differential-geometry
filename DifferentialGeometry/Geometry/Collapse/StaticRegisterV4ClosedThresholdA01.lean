import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGateUniverseFinalJN74
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive

/-!
# The closed endpoint input from the final FCW gate, at universe 0

Lane S-A01MAP, G1 (suffix `_A01`). The CLOSED direct admission of the endpoint
`GC.Endpoint.geometrization` is `exists_closed_graph_threshold_of_finite_scales_disj`
(`Geometry/Collapse/GraphManifold.lean:103`; listed as A02 in the X132 admission ledger, the brief
of this lane calls it A01). At `CompactCarrier.{0}` it is a combinatorial consequence of
`pbr03_threshold_final_FCW` (`StaticRegisterV4ChainGateUniverseFinalJN74`):

* the order `staticDerivativeOrder ≤ K` is `10 ≤ K` (`staticDerivativeOrder := 10`);
* the positivity hypothesis of the admitted statement (`0 < A w` only on `(0, ω₃)`) is NOT used:
  the FCW theorem is applied to `A' w := max (A w) 1` (positive everywhere, `A ≤ A'`), and the
  collapse hypotheses at `(A, w₀)` imply those at `(A', w₀)`
  (`curvatureDerivativesControlled_mono_control`); the threshold `w₀` is the one of `A'`;
* the conclusion `Raw ∨ (boundary = ∅ ∧ ∃ g', sec ≥ 0)` becomes `Raw ∨ ∃ G, spherical ∨
  sphericalProduct ∨ euclidean` by `finite_scales_disj_of_raw_or_aux_nonneg`.

`a01_of_closed_final_A01` is the admitted statement at universe 0, with `hA` dropped
(strengthening); the verbatim form with `hA` is the `example` below. The universe-`u` statement
(`u > 0`) is NOT claimed: it needs the cross-universe lift of `RawGraphPresentation`
(see `build-logs/resume/state-S-A01MAP.md`, section 4).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The collapse hypotheses at `(A, w₀)` imply those at any `A' ≥ A` (same `w₀`). -/
theorem closedCollapseHypotheses_mono_control_A01 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A A' : ℝ → ℝ} {w₀ : ℝ}
    (hAA' : ∀ w, A w ≤ A' w) (h : closedCollapseHypotheses W g K A w₀) :
    closedCollapseHypotheses W g K A' w₀ :=
  ⟨h.1, h.2.1, curvatureDerivativesControlled_mono_control hAA' h.2.2⟩

/-- **The closed endpoint input at universe 0**: the statement of the admitted
`exists_closed_graph_threshold_of_finite_scales_disj` at `CompactCarrier.{0}`, without its
positivity hypothesis on `A`, from `pbr03_threshold_final_FCW`. -/
theorem a01_of_closed_final_A01 (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨w₀, hw₀, hwu, hDI⟩ := pbr03_threshold_final_FCW K hK (fun w => max (A w) 1)
    (fun _ _ => lt_max_of_lt_right one_pos)
  exact ⟨w₀, hw₀, hwu, fun W _ g hfin hcol => finite_scales_disj_of_raw_or_aux_nonneg hDI W g hfin
    (closedCollapseHypotheses_mono_control_A01 (fun w => le_max_left (A w) 1) hcol)⟩

/-- **The admitted statement verbatim at universe 0**, with the positivity hypothesis `hA` of the
admitted form (unused by `a01_of_closed_final_A01`). -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  have _ := hA
  exact a01_of_closed_final_A01 K hK A

end DifferentialGeometry.Geometry.Collapse
