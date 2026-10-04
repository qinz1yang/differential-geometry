import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterface
import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry

/-!
# LC90, static side, boundary branch: parameter order and componentwise composition

Blueprint row LC90 (`prop:collapse-static-flow-interface`, master207A) is a conditional
composition. `LocalExport/StaticInterface.lean` proves its static side for the closed branch; this
module adds the boundary branch, in the same interface form (lead's answer Q2): the static theorem
enters as an explicit `∀`-hypothesis in the shape of the tree's `exists_graph_threshold`
(`Geometry/Collapse/GraphManifold.lean`), the convention of `geometrizes_of_hyperbolicOrCollapsed`;
no sorry-carrying theorem is used. The boundary premises are the tree's `NearlyCuspidalBoundary`
(with the repaired field `CuspEmbedding.boundary_preimage`), `boundaryVolumeCollapsed` and
`curvatureDerivativesControlled`.

* `exists_common_control_staticCollapseHypotheses_iff` (S1): one positive `A` from LC89, fixed
  before any `w₀`, for which the boundary hypotheses at `(K, A, w₀)` reduce to the cusp collar
  data and the interior volume collapse, and the static hypotheses reduce to the closed premise or
  the boundary premise, for every `w₀ > 0` and every carrier of the family.
* `exists_threshold_components_rawGraph` (S2): in the order `K` → `A` (LC89) → `w₀` (static
  theorem at `(K, A)`), every closed collapsed component receives a raw graph presentation, and
  every boundary-collapsed component receives one whose external tori are matched with the
  labelled boundary components of the collar data (labels `(j, i)` and boundary labels kept).
* `HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph`: the componentwise step of the chapter exit,
  with the static theorem and the nonnegative branch as explicit inputs (LC90's inputs 1 and 4).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC90 S1, both branches: one common positive `A` from LC89, fixed before `w₀`, for which, for
every `w₀ > 0` and every carrier of the family, the boundary collapse hypotheses at `(K, A, w₀)`
reduce to the nearly cuspidal collar data and the interior volume collapse, and the static
hypotheses reduce to "closed premise or boundary premise". -/
theorem exists_common_control_staticCollapseHypotheses_iff (K : ℕ)
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
        (boundaryCollapseHypotheses (W j i) (g j i) K A w₀ ↔
          Nonempty (NearlyCuspidalBoundary (W j i) (g j i) K w₀) ∧
            boundaryVolumeCollapsed (W j i) (g j i) w₀) ∧
        (staticCollapseHypotheses (W j i) (g j i) K A w₀ ↔
          ((W j i).model.boundary (W j i).Carrier = ∅ ∧
              ∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p) ∨
            (Nonempty (NearlyCuspidalBoundary (W j i) (g j i) K w₀) ∧
              boundaryVolumeCollapsed (W j i) (g j i) w₀)) := by
  obtain ⟨A, hA, hcontrol⟩ :=
    exists_common_curvature_derivative_bound_of_eventual K ι W g eventual_bound
  refine ⟨A, hA, fun j i w₀ hw₀ => ?_⟩
  have hb : boundaryCollapseHypotheses (W j i) (g j i) K A w₀ ↔
      Nonempty (NearlyCuspidalBoundary (W j i) (g j i) K w₀) ∧
        boundaryVolumeCollapsed (W j i) (g j i) w₀ :=
    ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hcontrol j i w₀ hw₀⟩⟩
  have hc : closedCollapseHypotheses (W j i) (g j i) K A w₀ ↔
      (W j i).model.boundary (W j i).Carrier = ∅ ∧
        ∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p :=
    ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hcontrol j i w₀ hw₀⟩⟩
  exact ⟨hb, or_congr hc hb⟩

/-- LC90 S2, both branches, interface form: given the static theorem at the derivative order `K`
(for every admissible `A`, a threshold `w₀` below which the static hypotheses give a raw graph
presentation), the parameters are chosen in the required order — `A` by LC89 from the family's
eventual derivative tests, then `w₀` by the static theorem. Then every closed component `W j i`
volume collapsed below `w₀` has a raw graph presentation, and every component carrying nearly
cuspidal collar data `B` at `w₀` and interior volume collapse has a raw graph presentation whose
external tori are matched, label by label, with the boundary components of `B`. -/
theorem exists_threshold_components_rawGraph (K : ℕ)
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
          staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      (∀ j (i : ι j), (W j i).model.boundary (W j i).Carrier = ∅ →
        (∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p) →
        Nonempty (RawGraphPresentation (W j i))) ∧
      (∀ j (i : ι j) (B : NearlyCuspidalBoundary (W j i) (g j i) K w₀),
        boundaryVolumeCollapsed (W j i) (g j i) w₀ →
        ∃ G : RawGraphPresentation (W j i), ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ k, Set.range (G.external.torusMap (e k)) = B.component k) := by
  obtain ⟨A, hA, hiff⟩ := exists_common_control_staticCollapseHypotheses_iff K ι W g eventual_bound
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A fun w hw _ => hA w hw
  refine ⟨w₀, hw₀, hwc, fun j i hb hv => ?_, fun j i B hv => ?_⟩
  · exact hstatic (W j i) (g j i) (((hiff j i w₀ hw₀).2).mpr (Or.inl ⟨hb, hv⟩))
  · obtain ⟨G⟩ := hstatic (W j i) (g j i) (((hiff j i w₀ hw₀).2).mpr (Or.inr ⟨⟨B⟩, hv⟩))
    exact ⟨G, G.external_matching B⟩

/-- The componentwise step of LC90's chapter exit, interface form: a piece of a torus
decomposition which is hyperbolic, collapsed (static hypotheses at `(K, A, w₀)`) or closed and
nonnegatively curved is hyperbolic or carries a raw graph presentation, given the static theorem
at `(K, A, w₀)` and the separately supplied nonnegative branch as explicit inputs. -/
theorem HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph
    {M : ConnectedClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    {D : TorusDecomposition M} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} {i : Fin D.components.count}
    (piece : HyperbolicOrCollapsed g D K A w₀ i)
    (collapse : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V))
    (nonneg : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      V.model.boundary V.Carrier = ∅ →
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow h 0 →
      Nonempty (RawGraphPresentation V)) :
    Nonempty (HyperbolicOrGraph D.carrier D.components i) := by
  have : ConnectedSpace (D.component i).Carrier := D.components.connected i
  cases piece with
  | hyperbolic geometry model_eq => exact ⟨.hyperbolic geometry model_eq⟩
  | collapsed h _ hh =>
    obtain ⟨G⟩ := collapse (D.component i) h hh
    exact ⟨.graph G⟩
  | nonnegative h _ hclosed hcurvature =>
    obtain ⟨G⟩ := nonneg (D.component i) h hclosed hcurvature
    exact ⟨.graph G⟩

end DifferentialGeometry.Geometry.Collapse
