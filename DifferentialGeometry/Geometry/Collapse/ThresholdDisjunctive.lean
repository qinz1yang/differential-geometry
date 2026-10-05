import DifferentialGeometry.Geometry.Collapse.ClosedCutComponent
import DifferentialGeometry.Geometry.Thurston.NonnegativeClassificationUnconditional
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Geometry.Thurston.SphericalStructureStandard
import DifferentialGeometry.Geometry.Thurston.FlatPrime
import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedral
import DifferentialGeometry.Geometry.Thurston.SphericalProductUniversalCover

/-!
# Chapter 14 thresholds, interface V3: the disjunctive nonnegative branch

User decision 2026-10-04 (`docs/geometrization/chapter14/decision-nonnegative-branch-20261004.md`):
the closed threshold theorems conclude

  `Nonempty (RawGraphPresentation W) ∨ ∃ G : GeometricStructure W.model W.Carrier,
     G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean`,

and the geometrization endpoint takes the second disjunct directly (one closed piece carrying a
spherical, `S² × ℝ` or Euclidean structure), never through the admitted recognitions
`rawGraphPresentation_of_{sphericalSpaceForm, sphericalProduct, flat}`
(`Geometry/Thurston/GraphPresentation.lean`). This is an OPEN statement change (change log
`docs/geometrization/chapter14/design-fc39-fc42-assembly-v3-changes-20261004.md`).

The admitted threshold theorems are not used here: every threshold enters as an explicit
hypothesis, in the convention of `geometrizes_of_hyperbolicOrCollapsed`. The chapter-7 input is the
unconditional classification `GC.Geometry.closed_nonnegative_sectional_classification_unconditional`.

* `raw_or_closedGeometric_of_raw_or_aux_nonneg`: the V2 DI disjunct (closed, auxiliary smooth
  `sec ≥ 0` metric) gives the V3 disjunct.
* `closed_threshold_disj_of_finite_scales_disj`, `exists_closed_graph_threshold_disj_of_finite_scales_disj`:
  the finite-scale closed threshold in V3 form gives the full closed threshold in V3 form (the
  `sec ≥ 0` case by the classification; this replaces `exists_rawGraphPresentation_of_nonnegative`).
* `finite_scales_disj_of_raw_or_aux_nonneg`: V2 PBR03-DI ⇒ V3 finite-scale threshold, same `w₀`.
* `exists_graph_threshold_disj_of_closed_disj`: the static threshold (closed or nearly cuspidal
  boundary) with conclusion `Raw ∨ (closed ∧ geometric)`, from the V3 closed threshold and A2.
* `HyperbolicOrCollapsed.hyperbolicOrGraph_or_closedGeometric_disj`: LC90 componentwise step with
  the static theorem in V3 form.
* `geometrizes_of_closedGeometric_cut_piece`, `geometrizes_of_hyperbolicOrGraph_or_closedGeometric`,
  `geometrizes_of_hyperbolicOrCollapsed_disj`: the endpoint. A closed cut piece is `M` itself
  (`exists_diffeomorph_of_closed_cut_component`); its structure is pulled back to `M`
  (`GeometricStructure.pullback`) and `M` geometrizes by the spherical, `S² × ℝ`
  (`sphericalProductStandardConnectedSum_of_universalCover_only sphericalProductUniversalCover`) or
  flat (`flatStructurePrime`) certificate.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ## The V2 → V3 disjunct -/

/-- The V2 DI right disjunct (closed carrier with an auxiliary smooth `sec ≥ 0` metric) gives the
V3 right disjunct (closed carrier with a spherical, `S² × ℝ` or Euclidean geometric structure), by
chapter 7's unconditional classification. -/
theorem raw_or_closedGeometric_of_raw_or_aux_nonneg (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier]
    (h : Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        Riemannian.SectionalBoundedBelow g' 0)) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  rcases h with h | ⟨hclosed, g', hsec⟩
  · exact Or.inl h
  · exact Or.inr ⟨hclosed,
      GC.Geometry.closed_nonnegative_sectional_classification_unconditional W g' hclosed hsec⟩

/-- V2 PBR03-DI at one `w₀` gives the V3 finite-scale closed threshold at the same `w₀`. -/
theorem finite_scales_disj_of_raw_or_aux_nonneg {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (hDI : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier),
      (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hfin : ∀ p, curvatureRadius g p ≠ ⊤) (hcol : closedCollapseHypotheses W g K A w₀) :
    Nonempty (RawGraphPresentation W) ∨
      ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
        G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  (raw_or_closedGeometric_of_raw_or_aux_nonneg W (hDI W g hfin hcol)).imp id fun h => h.2

/-! ## The closed threshold, V3 -/

/-- **Closed threshold, V3, at one `w₀`.** The finite-scale closed threshold in V3 form gives the
closed threshold in V3 form for every closed collapsed carrier: if `sec ≥ 0` everywhere, chapter 7's
classification gives the geometric disjunct (this replaces `exists_rawGraphPresentation_of_nonnegative`
and the three admitted recognitions); otherwise every curvature scale is finite. -/
theorem closed_threshold_disj_of_finite_scales_disj {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (hfinite : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier),
      (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (hcol : closedCollapseHypotheses W g K A w₀) :
    Nonempty (RawGraphPresentation W) ∨
      ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
        G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  by_cases hsec : Riemannian.SectionalBoundedBelow g 0
  · exact Or.inr
      (GC.Geometry.closed_nonnegative_sectional_classification_unconditional W g hcol.1 hsec)
  · exact hfinite W g (fun p hp => hsec ((curvatureRadius_eq_top_iff p).mp hp)) hcol

/-- **Closed threshold, V3** (the replacement of `exists_closed_graph_threshold`): one uniform `w₀`
before all `(W, g)`, as in the finite-scale form it comes from. -/
theorem exists_closed_graph_threshold_disj_of_finite_scales_disj {K : ℕ} {A : ℝ → ℝ}
    (hfinite : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨w₀, hw₀, hwupper, hfin⟩ := hfinite
  exact ⟨w₀, hw₀, hwupper, fun W _ g hcol => closed_threshold_disj_of_finite_scales_disj hfin W g hcol⟩

/-! ## The static threshold, V3 -/

/-- **Static threshold, V3** (the replacement of `exists_graph_threshold`): from the V3 closed
threshold and the boundary threshold A2 (unchanged), one `w₀ = min w_c w_b` before all `(W, g)`; a
closed collapsed carrier is Raw or closed with a geometric structure, a boundary-collapsed one is
Raw. -/
theorem exists_graph_threshold_disj_of_closed_disj {K : ℕ} {A : ℝ → ℝ}
    (hclosed : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)
    (hboundary : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  obtain ⟨wc, hwc, hcupper, hc⟩ := hclosed
  obtain ⟨wb, hwb, -, hb⟩ := hboundary
  refine ⟨min wc wb, lt_min hwc hwb, (min_le_left wc wb).trans_lt hcupper, ?_⟩
  intro W _ g h
  rcases h with h | h
  · have h' := closedCollapseHypotheses_mono g K A (min_le_left wc wb) h
    exact (hc W g h').imp id fun hG => ⟨h'.1, hG⟩
  · obtain ⟨⟨B⟩, hvol, hder⟩ := boundaryCollapseHypotheses_mono g K A (min_le_right wc wb) h
    obtain ⟨G, -, -⟩ := hb W g B hvol hder
    exact Or.inl ⟨G⟩

/-! ## LC90, componentwise step, V3 -/

/-- **LC90 componentwise step with the static theorem in V3 form.** Every piece of a torus
decomposition that is hyperbolic, collapsed or closed and nonnegatively curved is hyperbolic or
carries a raw graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean geometric
structure. No recognition and no nonnegative input is used. -/
theorem HyperbolicOrCollapsed.hyperbolicOrGraph_or_closedGeometric_disj
    {M : ConnectedClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    {D : TorusDecomposition M} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} {i : Fin D.components.count}
    (piece : HyperbolicOrCollapsed g D K A w₀ i)
    (collapse : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      staticCollapseHypotheses V h K A w₀ →
        Nonempty (RawGraphPresentation V) ∨
          (V.model.boundary V.Carrier = ∅ ∧
            ∃ G : GC.Geometry.GeometricStructure V.model V.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) :
    Nonempty (HyperbolicOrGraph D.carrier D.components i) ∨
      ((D.component i).model.boundary (D.component i).Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure (D.component i).model (D.component i).Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  have : ConnectedSpace (D.component i).Carrier := D.components.connected i
  cases piece with
  | hyperbolic geometry model_eq => exact Or.inl ⟨.hyperbolic geometry model_eq⟩
  | collapsed h _ hh =>
    exact (collapse (D.component i) h hh).imp (fun ⟨G⟩ => ⟨.graph G⟩) id
  | nonnegative h _ hclosed hcurvature =>
    exact Or.inr ⟨hclosed, GC.Geometry.closed_nonnegative_sectional_classification_unconditional
      (D.component i) h hclosed hcurvature⟩

/-! ## The endpoint, V3 -/

/-- A closed cut piece carrying a spherical, `S² × ℝ` or Euclidean geometric structure: the piece is
`M` (by the cut-piece diffeomorphism), the structure pulls back to `M`, and `M` geometrizes by the
corresponding standard certificate. -/
theorem geometrizes_of_closedGeometric_cut_piece (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (hclosed : (D.component i).model.boundary (D.component i).Carrier = ∅)
    (G : GC.Geometry.GeometricStructure (D.component i).model (D.component i).Carrier)
    (hG : G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :
    Geometrizes M := by
  obtain ⟨e, -⟩ := exists_diffeomorph_of_closed_cut_component M D i hclosed
  have hmodel : (G.pullback e.symm).model = G.model := rfl
  rcases hG with hG | hG | hG
  · exact geometrizes_of_sphericalStructure M (G.pullback e.symm) (hmodel.trans hG)
  · exact geometrizes_of_sphericalProductStructure
      (GC.Geometry.SphericalProduct.sphericalProductStandardConnectedSum_of_universalCover_only
        GC.Geometry.SphericalProduct.sphericalProductUniversalCover)
      M (G.pullback e.symm) (hmodel.trans hG)
  · exact geometrizes_of_euclideanStructure flatStructurePrime M (G.pullback e.symm)
      (hmodel.trans hG)

/-- **Endpoint, piece form.** If every piece of an incompressible torus decomposition is hyperbolic,
carries a raw graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean structure,
then `M` geometrizes. -/
theorem geometrizes_of_hyperbolicOrGraph_or_closedGeometric
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : ∀ i : Fin D.components.count,
      Nonempty (HyperbolicOrGraph D.carrier D.components i) ∨
        ((D.component i).model.boundary (D.component i).Carrier = ∅ ∧
          ∃ G : GC.Geometry.GeometricStructure (D.component i).model (D.component i).Carrier,
            G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean)) :
    Geometrizes M := by
  by_cases hgeom : ∃ i : Fin D.components.count,
      (D.component i).model.boundary (D.component i).Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure (D.component i).model (D.component i).Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean
  · obtain ⟨i, hclosed, G, hG⟩ := hgeom
    exact geometrizes_of_closedGeometric_cut_piece M D i hclosed G hG
  · have hraw : ∀ i : Fin D.components.count,
        Nonempty (HyperbolicOrGraph D.carrier D.components i) := fun i =>
      (pieces i).resolve_right fun h => hgeom ⟨i, h⟩
    exact geometrizes_of_hyperbolicOrGraph M D incompressible fun i => Classical.choice (hraw i)

/-- **Endpoint, V3** (the replacement of `geometrizes_of_hyperbolicOrCollapsed`): the static
threshold enters in V3 form (`Raw ∨ closed geometric`); the `nonnegative` constructor goes through
chapter 7's classification. No admitted recognition is on this path. -/
theorem geometrizes_of_hyperbolicOrCollapsed_disj
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ)
    (collapse : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (h : SmoothRiemannianMetric W.model W.Carrier),
      staticCollapseHypotheses W h K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean))
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → HyperbolicOrCollapsed g D K A w₀ i) :
    Geometrizes M :=
  geometrizes_of_hyperbolicOrGraph_or_closedGeometric M D incompressible fun i =>
    (pieces i).hyperbolicOrGraph_or_closedGeometric_disj collapse

end DifferentialGeometry.Geometry.Collapse
