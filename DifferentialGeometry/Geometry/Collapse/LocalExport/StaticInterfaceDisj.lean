import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterfaceBoundary
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# LC90, raw-graph form, restated with the V3 disjunctive static theorem

The raw-graph form of LC90 (`LocalExport/StaticInterfaceBoundary.lean`:
`exists_threshold_components_rawGraph`, `HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph`) takes
the static theorem with conclusion `Nonempty (RawGraphPresentation V)` and, for closed
nonnegatively curved pieces, a raw-graph nonnegative input; the only supplier of the latter is the
admitted recognitions `rawGraphPresentation_of_{sphericalSpaceForm, sphericalProduct, flat}`.
Interface V3 (user decision 2026-10-04,
`docs/geometrization/chapter14/decision-nonnegative-branch-20261004.md`) replaces both by the
disjunction "raw graph presentation, or closed with a spherical, `S² × ℝ` or Euclidean geometric
structure". The static theorem enters as an explicit `∀`-hypothesis (lead's interface form Q2), now
in V3 form; no admitted declaration and no nonnegative input is used.

* `exists_threshold_components_rawGraph_or_closedGeometric` (S2, V3): in the order `K` → `A`
  (LC89) → `w₀` (static theorem at `(K, A)`), every closed collapsed component is Raw or closed
  geometric, and every boundary-collapsed component is Raw with external tori matched label by
  label with the boundary components of its collar data (the geometric disjunct is excluded there
  because the boundary is nonempty).
* `GC.LongTime.LateCutFamily.exists_late_hyperbolicOrGraph_or_closedGeometric_disj` and
  `…_of_boundary_nonempty_disj`: LC90 for the tree's late cut families with the V3 static theorem
  as the only explicit input (same conclusions as the F9-C interface forms).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **LC90 S2, V3.** Given the static theorem at the derivative order `K` in V3 form, the parameters
are chosen in the order `A` (LC89, from the family's eventual derivative tests) → `w₀` (static
theorem). Every closed component volume collapsed below `w₀` has a raw graph presentation or a
spherical, `S² × ℝ` or Euclidean geometric structure; every component carrying nearly cuspidal
collar data `B` at `w₀` with interior volume collapse has a raw graph presentation whose external
tori are matched, label by label, with the boundary components of `B`. -/
theorem exists_threshold_components_rawGraph_or_closedGeometric (K : ℕ)
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
          staticCollapseHypotheses V h K A w₀ →
            Nonempty (RawGraphPresentation V) ∨
              (V.model.boundary V.Carrier = ∅ ∧
                ∃ G : GC.Geometry.GeometricStructure V.model V.Carrier,
                  G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      (∀ j (i : ι j), (W j i).model.boundary (W j i).Carrier = ∅ →
        (∀ p, volumeCollapsedAtCurvatureScale (g j i) w₀ p) →
        Nonempty (RawGraphPresentation (W j i)) ∨
          ∃ G : GC.Geometry.GeometricStructure (W j i).model (W j i).Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) ∧
      (∀ j (i : ι j) (B : NearlyCuspidalBoundary (W j i) (g j i) K w₀),
        boundaryVolumeCollapsed (W j i) (g j i) w₀ →
        ∃ G : RawGraphPresentation (W j i), ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ k, Set.range (G.external.torusMap (e k)) = B.component k) := by
  obtain ⟨A, hA, hiff⟩ := exists_common_control_staticCollapseHypotheses_iff K ι W g eventual_bound
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A fun w hw _ => hA w hw
  refine ⟨w₀, hw₀, hwc, fun j i hb hv => ?_, fun j i B hv => ?_⟩
  · exact (hstatic (W j i) (g j i) (((hiff j i w₀ hw₀).2).mpr (Or.inl ⟨hb, hv⟩))).imp id
      fun h => h.2
  · have hbd : boundaryCollapseHypotheses (W j i) (g j i) K A w₀ :=
      ((hiff j i w₀ hw₀).1).mpr ⟨⟨B⟩, hv⟩
    rcases hstatic (W j i) (g j i) (Or.inr hbd) with hG | ⟨hclosed, -⟩
    · obtain ⟨G⟩ := hG
      exact ⟨G, G.external_matching B⟩
    · exact (not_boundaryCollapseHypotheses_of_boundary_empty (W j i) (g j i) K A w₀ hclosed
        hbd).elim

end DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime

open DifferentialGeometry.Geometry.Collapse

universe u

/-- **LC90 for a late cut family, V3.** With only the static theorem at order `K` in V3 form as
explicit input, in the order `A` (LC89) → `w₀` (static theorem) → late index `N`, every late piece is
hyperbolic or carries a raw graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean
geometric structure. -/
theorem LateCutFamily.exists_late_hyperbolicOrGraph_or_closedGeometric_disj
    {P : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ →
            Nonempty (RawGraphPresentation V) ∨
              (V.model.boundary V.Carrier = ∅ ∧
                ∃ G : GC.Geometry.GeometricStructure V.model V.Carrier,
                  G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ (C : ConnectedComponents (slices j).stage.Carrier)
        (i : Fin (L.decomposition j C).components.count),
        Nonempty (HyperbolicOrGraph (L.decomposition j C).carrier
          (L.decomposition j C).components i) ∨
        (((L.decomposition j C).component i).model.boundary
            ((L.decomposition j C).component i).Carrier = ∅ ∧
          ∃ G : GC.Geometry.GeometricStructure ((L.decomposition j C).component i).model
              ((L.decomposition j C).component i).Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds h
  obtain ⟨w₀, hw₀, hwc, hstatic⟩ := static A hA
  obtain ⟨N, hN⟩ := htests w₀ hw₀ hwc
  refine ⟨w₀, hw₀, hwc, N, fun j hj C i => ?_⟩
  obtain ⟨pieces⟩ := hN j hj C
  exact (pieces i).hyperbolicOrGraph_or_closedGeometric_disj hstatic

/-- On the same late tail, every late piece with nonempty boundary is hyperbolic or carries a raw
graph presentation, with only the V3 static theorem as explicit input. -/
theorem LateCutFamily.exists_late_hyperbolicOrGraph_of_boundary_nonempty_disj
    {P : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ →
            Nonempty (RawGraphPresentation V) ∨
              (V.model.boundary V.Carrier = ∅ ∧
                ∃ G : GC.Geometry.GeometricStructure V.model V.Carrier,
                  G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ (C : ConnectedComponents (slices j).stage.Carrier)
        (i : Fin (L.decomposition j C).components.count),
        (((L.decomposition j C).component i).model.boundary
            ((L.decomposition j C).component i).Carrier).Nonempty →
        Nonempty (HyperbolicOrGraph (L.decomposition j C).carrier
          (L.decomposition j C).components i) := by
  obtain ⟨w₀, hw₀, hwc, N, hN⟩ := L.exists_late_hyperbolicOrGraph_or_closedGeometric_disj h static
  exact ⟨w₀, hw₀, hwc, N, fun j hj C i hbd =>
    (hN j hj C i).resolve_right fun hc => hbd.ne_empty hc.1⟩

end GC.LongTime
