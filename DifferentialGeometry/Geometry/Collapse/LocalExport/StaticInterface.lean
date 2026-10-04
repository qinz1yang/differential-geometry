import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Geometry.Collapse.UniformDerivativeBounds

/-!
# LC90, static side, closed branch: parameter order and componentwise composition

Blueprint row LC90 (`prop:collapse-static-flow-interface`, master207A) is a conditional
composition; this module proves its static side for the CLOSED branch, in interface form.  The
static theorem enters as an explicit `∀`-hypothesis spelling out the tree's closed statement
(the shape of `exists_closed_graph_threshold`, `Geometry/Collapse/GraphManifold.lean`), exactly as
the tree's `geometrizes_of_hyperbolicOrCollapsed` takes its `collapse` argument; no sorry-carrying
theorem is used.

* `exists_common_control_closedCollapseHypotheses_iff` (S1, closed): for finite families of compact
  carriers `W j i` satisfying the eventual whole-ball derivative tests (the row's input 3), LC89
  gives ONE positive `A`, chosen before any `w₀`, for which the closed hypotheses at `(K, A, w₀)`
  reduce to "empty boundary and volume collapse at the curvature scale", for every `w₀ > 0`.
* `exists_threshold_closed_components_rawGraph` (S2, closed): in the required order `K` → `A`
  (LC89) → `w₀` (static theorem at `(K, A)`), every closed volume-collapsed component of the family
  receives a raw graph presentation, with its label `(j, i)` retained.

The boundary branch of S1/S2 is stated against `staticCollapseHypotheses`, whose boundary part uses
`NearlyCuspidalBoundary`; it waits for the repair of `CuspEmbedding.boundary_preimage` (audit lane
CUSP-FIX) and is recorded in the lane sheet, not here.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC90 S1, closed branch: one common positive `A` from LC89, fixed before `w₀`, for which the
closed collapse hypotheses at `(K, A, w₀)` of every carrier of the family reduce to empty boundary
and volume collapse at the curvature scale. -/
theorem exists_common_control_closedCollapseHypotheses_iff (K : ℕ)
    (ι : ℕ → Type*) [∀ j, Finite (ι j)]
    (W : (j : ℕ) → ι j → CompactCarrier.{u})
    (g : (j : ℕ) → (i : ι j) → SmoothRiemannianMetric (W j i).model (W j i).Carrier)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (i : ι j) (p : (W j i).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j i) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j i) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j i) p r,
            curvatureDerivativeNorm (g j i) k q ≤ C * (r ^ (k + 2))⁻¹) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < w → 0 < A w) ∧
      ∀ j (i : ι j) (w₀ : ℝ), 0 < w₀ →
        (closedCollapseHypotheses (W j i) (g j i) K A w₀ ↔
          (W j i).model.boundary (W j i).Carrier = ∅ ∧
            ∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p) := by
  obtain ⟨A, hA, hcontrol⟩ :=
    exists_common_curvature_derivative_bound_of_eventual K ι W g eventual_bound
  refine ⟨A, hA, fun j i w₀ hw₀ => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩⟩
  exact hcontrol j i w₀ hw₀

/-- LC90 S2, closed branch, interface form: given the closed static theorem at the derivative
order `K` (for every admissible `A`, a threshold `w₀` below which closed collapse gives a raw
graph presentation), the parameters are chosen in the required order — `A` by LC89 from the
family's eventual derivative tests, then `w₀` by the static theorem — and every closed component
`W j i` of the family that is volume collapsed at the curvature scale below `w₀` receives a raw
graph presentation; the component labels `(j, i)` are retained. -/
theorem exists_threshold_closed_components_rawGraph (K : ℕ)
    (ι : ℕ → Type*) [∀ j, Finite (ι j)]
    (W : (j : ℕ) → ι j → CompactCarrier.{u}) [∀ j i, ConnectedSpace (W j i).Carrier]
    (g : (j : ℕ) → (i : ι j) → SmoothRiemannianMetric (W j i).model (W j i).Carrier)
    (eventual_bound : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ j, N ≤ j → ∀ (i : ι j) (p : (W j i).Carrier) (r : ℝ), 0 < r →
          ENNReal.ofReal r < curvatureRadius (g j i) p →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (g j i) p r →
          ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (g j i) p r,
            curvatureDerivativeNorm (g j i) k q ≤ C * (r ^ (k + 2))⁻¹)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          closedCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ j (i : ι j), (W j i).model.boundary (W j i).Carrier = ∅ →
        (∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p) →
        Nonempty (RawGraphPresentation (W j i)) := by
  obtain ⟨A, hA, hiff⟩ := exists_common_control_closedCollapseHypotheses_iff K ι W g eventual_bound
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A fun w hw _ => hA w hw
  exact ⟨w₀, hw₀, hwc, fun j i hb hv =>
    hstatic (W j i) (g j i) ((hiff j i w₀ hw₀).mpr ⟨hb, hv⟩)⟩

end DifferentialGeometry.Geometry.Collapse
