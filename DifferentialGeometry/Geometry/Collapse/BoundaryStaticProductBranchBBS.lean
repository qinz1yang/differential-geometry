import DifferentialGeometry.Geometry.Collapse.BoundaryRestrictedPacketsRowBBS
import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models

/-!
# BBR02's graph clause in the product branch, and BBR02 / BBR03 reduced to the separated branch
(lane B-BBR-BSA)

Blueprint 207B, BBR02 (B:10567–10590): "The whole-product case is already a graph piece. Otherwise
BCG gives the actual augmented clouds …". This file proves the product case and states what is left
of BBR02 / BBR03 exactly as the separated case of BCP03 / BCP05.

* `exists_labelledRawGraphPresentation_of_torusProduct_BBS`: a carrier with nearly cuspidal boundary
  data `B` that is diffeomorphic to `T² × [0, 1]` has a raw graph presentation whose external tori
  are the components of `B` (A2's labelled conclusion; transport of the annulus presentation,
  `exists_rawGraphPresentation_of_torusProduct_diffeomorph`, and `external_matching`).
* `bbr02_graph_or_separated_BBS` (BBR02 sharpened): for every early choice and every standing
  sequence, ONE zero scale, ONE register and ONE tail on which every member EITHER has the labelled
  raw graph presentation (the product branch, proved) OR is in the separated branch with the full
  BCP04 family and BCP05's separations (collars `B_i⁺ = e_i{z < 92}` pairwise disjoint, selected
  zero balls pairwise disjoint and disjoint from every `B_i⁺`).
* `bbr03_reduction_separated_BBS` (BBR03 sharpened): EITHER BBR03's threshold exists, OR there is a
  standing sequence of nongraph counterexamples (at `δ₀ = δStar`) whose late members are, for every
  early choice, in the separated branch with the full BCP04 / BCP05 data.

What remains for the rows is the separated branch only: the augmented chain BCG03–BCF04 (draft 61
§7.5) giving a decomposition certificate with the rim-product clause, then FC42 (form (b),
`exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic
open GC.GraphManifold GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The product branch is a graph piece** (BBR02, B:10577): a carrier with nearly cuspidal
boundary data `B` and a diffeomorphism from `T² × [0, 1]` has a raw graph presentation whose
external tori are exactly the components of `B` (with a bijection of labels). -/
theorem exists_labelledRawGraphPresentation_of_torusProduct_BBS {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞) :
    ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  obtain ⟨G, -⟩ := exists_rawGraphPresentation_of_torusProduct_diffeomorph
    (annulusCircleCarrierDiffeomorphTorusInterval.{u}.trans D)
  exact ⟨G, G.external_matching B⟩

/-- **BBR02 reduced to the separated branch**: for every early choice `E` and every standing
sequence `S`, ONE zero scale `V`, ONE register `R` over `(E, V)` and ONE tail such that every member
EITHER has a raw graph presentation labelled by its boundary components (product branch) OR has its
labelled packet, BCP04.a, the completed interior and, for every orientation, ONE family
`F : LocalPacketsOnBFRZ` on `{d > 10}`, `{d ≥ 20}` (ranks on `{d > 5}`, actual `g`-ball domains and
zero balls) with BCP05's separations: all `B_i⁺ = e_i{z < 92}` and all selected zero balls are
pairwise disjoint. -/
theorem bbr02_graph_or_separated_BBS {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (∃ G : RawGraphPresentation (S.W n), ∃ e : Fin (S.B n).count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (e i)) = (S.B n).component i) ∨
    ∃ P : BoundaryExportPacket (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
      (cuspTolerance_BCUSP1 (E.β 1) R.βd R.εN),
    P.cusp = S.B n ∧
    ∃ ρ : (S.W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
      (∀ p, 0 < distanceToBoundary (S.W n) (S.g n) p →
        ((n + 1 : ℕ) : ℝ) * (distanceToBoundary (S.W n) (S.g n) p).toReal /
            ((distanceToBoundary (S.W n) (S.g n) p).toReal + 3) <
          (distanceToBoundary (S.W n) (S.g n) p).toReal / ρ p) ∧
      letI := interiorChartedT_BDRY1 (S.W n)
      haveI := interiorManifoldT_BDRY1 (S.W n)
      ∃ _ : ConnectedSpace ((S.W n).pieceInterior ⊤),
      ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤),
      ∃ O : Set ((S.W n).pieceInterior ⊤), IsOpen O ∧
        {x : (S.W n).pieceInterior ⊤ |
          ENNReal.ofReal 4 ≤ distanceToBoundary (S.W n) (S.g n) x} ⊆ O ∧
        (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x) ∧
        (∀ (x : (S.W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
          (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
        letI := inducedMetricSpace ĝ
        ∃ _ : CompleteSpace ((S.W n).pieceInterior ⊤),
        ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤) 3,
        ∃ F : LocalPacketsOnBFRZ ((S.W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
            (fun x => ρ x) (fun x => hρpos x) E.Λ E.β E.Δ E.σs K E.σc E.μ E.b E.s E.b' E.s' E.ε
            E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz
            {x | ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 20 < distanceToBoundary (S.W n) (S.g n) x}
            {x | ENNReal.ofReal 35 ≤ distanceToBoundary (S.W n) (S.g n) x} oM,
          (∀ x : (S.W n).pieceInterior ⊤,
            ENNReal.ofReal 5 < distanceToBoundary (S.W n) (S.g n) x →
            scaledSplittingRank.{0, 0} (fun y : (S.W n).pieceInterior ⊤ => ρ y)
                (fun y => hρpos y) E.β x =
              @scaledSplittingRank.{0, 0} (S.W n).Carrier (inducedMetricSpace (S.g n)) ρ hρpos
                E.β x) ∧
          (∀ j : (S.W n).pieceInterior ⊤,
            ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) j →
            Subtype.val '' Metric.ball j
                (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) =
              riemannianBallOf (S.g n) j.val
                (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) ∧
            ∀ y ∈ Metric.ball j ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
              ∀ z ∈ Metric.ball j
                  ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
                riemannianEDistOf (S.g n) y.val z.val = edist y z) ∧
          (letI := F.instMetricN
          letI := F.instChartedN
          letI := F.instMetricC
          (∀ z (hz : z ∈ F.zero.centres),
            Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
              riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius) ∧
          (∀ i j : Fin P.cusp.count, i ≠ j →
            Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
              ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
          (∀ z (hz : z ∈ F.zero.centres) z' (hz' : z' ∈ F.zero.centres), z ≠ z' →
            Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
              (riemannianBallOf (S.g n) z'.val (F.zero.zero z' hz').radius)) ∧
          ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
            Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
              ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) := by
  obtain ⟨V, R, n₀, hR⟩ := bcp04_bcp05_row_BBS E S
  refine ⟨V, R, n₀, fun n hn => ?_⟩
  by_cases hprod : Nonempty (Diffeomorph (torusModel.prod (𝓡∂ 1)) (S.W n).model
      (Torus × Icc (0 : ℝ) 1) (S.W n).Carrier ∞)
  · obtain ⟨D⟩ := hprod
    exact Or.inl (exists_labelledRawGraphPresentation_of_torusProduct_BBS (S.B n) D)
  · right
    obtain ⟨P, hPB, ρ, hρpos, ha, hconn, ĝ, O, hO, hOsub, hOeq, hle, hcomp, hF⟩ := hR n hn
    refine ⟨P, hPB, ρ, hρpos, ha, hconn, ĝ, O, hO, hOsub, hOeq, hle, hcomp, fun oM => ?_⟩
    obtain ⟨F, hrank, hdom, hzb, hsep⟩ := hF oM
    refine ⟨F, hrank, hdom, hzb, ?_⟩
    rcases hsep with ⟨i, j, -, D, -, -⟩ | hsep
    · exact (hprod ⟨D⟩).elim
    · exact hsep

/-- **BBR03 reduced to the separated branch**: EITHER BBR03's threshold exists (every member at
`w₀` has a raw graph presentation labelled by its boundary components), OR there is a standing
sequence below `δStar` (at `δ₀ = δStar`) of nongraph counterexamples whose late members are, for
every early choice, in the separated branch of `bbr02_graph_or_separated_BBS` with the full
BCP04 / BCP05 data. No hypothesis. -/
theorem bbr03_reduction_separated_BBS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) ∨
    ∃ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
      S.δ₀ = (bdryThresholds_BSTD1 K hK A hA).δStar ∧
      (∀ n, ¬ ∃ G : RawGraphPresentation (S.W n), ∃ e : Fin (S.B n).count ≃ Fin G.externalCount,
        ∀ i, Set.range (G.external.torusMap (e i)) = (S.B n).component i) ∧
      ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
      ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      IsEmpty (Diffeomorph (torusModel.prod (𝓡∂ 1)) (S.W n).model (Torus × Icc (0 : ℝ) 1)
        (S.W n).Carrier ∞) ∧
      ∃ P : BoundaryExportPacket (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
        (cuspTolerance_BCUSP1 (E.β 1) R.βd R.εN),
      P.cusp = S.B n ∧
      ∃ ρ : (S.W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, 0 < distanceToBoundary (S.W n) (S.g n) p →
          ((n + 1 : ℕ) : ℝ) * (distanceToBoundary (S.W n) (S.g n) p).toReal /
              ((distanceToBoundary (S.W n) (S.g n) p).toReal + 3) <
            (distanceToBoundary (S.W n) (S.g n) p).toReal / ρ p) ∧
        letI := interiorChartedT_BDRY1 (S.W n)
        haveI := interiorManifoldT_BDRY1 (S.W n)
        ∃ _ : ConnectedSpace ((S.W n).pieceInterior ⊤),
        ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤),
        ∃ O : Set ((S.W n).pieceInterior ⊤), IsOpen O ∧
          {x : (S.W n).pieceInterior ⊤ |
            ENNReal.ofReal 4 ≤ distanceToBoundary (S.W n) (S.g n) x} ⊆ O ∧
          (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x) ∧
          (∀ (x : (S.W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
            (pieceInteriorMetric (S.W n) (S.g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
          letI := inducedMetricSpace ĝ
          ∃ _ : CompleteSpace ((S.W n).pieceInterior ⊤),
          ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤) 3,
          ∃ F : LocalPacketsOnBFRZ ((S.W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
              (fun x => ρ x) (fun x => hρpos x) E.Λ E.β E.Δ E.σs K E.σc E.μ E.b E.s E.b' E.s'
              E.ε E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz
              {x | ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) x}
              {x | ENNReal.ofReal 20 ≤ distanceToBoundary (S.W n) (S.g n) x}
              {x | ENNReal.ofReal 20 < distanceToBoundary (S.W n) (S.g n) x}
              {x | ENNReal.ofReal 35 ≤ distanceToBoundary (S.W n) (S.g n) x} oM,
            (∀ x : (S.W n).pieceInterior ⊤,
              ENNReal.ofReal 5 < distanceToBoundary (S.W n) (S.g n) x →
              scaledSplittingRank.{0, 0} (fun y : (S.W n).pieceInterior ⊤ => ρ y)
                  (fun y => hρpos y) E.β x =
                @scaledSplittingRank.{0, 0} (S.W n).Carrier (inducedMetricSpace (S.g n)) ρ hρpos
                  E.β x) ∧
            (∀ j : (S.W n).pieceInterior ⊤,
              ENNReal.ofReal 10 < distanceToBoundary (S.W n) (S.g n) j →
              Subtype.val '' Metric.ball j
                  (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) =
                riemannianBallOf (S.g n) j.val
                  (4 * (2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j) ∧
              ∀ y ∈ Metric.ball j
                  ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
                ∀ z ∈ Metric.ball j
                    ((2010000 + 2000000 * E.Δ + 400 * V + (E.β 1)⁻¹ + E.b⁻¹) * ρ j),
                  riemannianEDistOf (S.g n) y.val z.val = edist y z) ∧
            (letI := F.instMetricN
            letI := F.instChartedN
            letI := F.instMetricC
            (∀ z (hz : z ∈ F.zero.centres),
              Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius) ∧
            (∀ i j : Fin P.cusp.count, i ≠ j →
              Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
                ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
            (∀ z (hz : z ∈ F.zero.centres) z' (hz' : z' ∈ F.zero.centres), z ≠ z' →
              Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
                (riemannianBallOf (S.g n) z'.val (F.zero.zero z' hz').radius)) ∧
            ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
              Disjoint (riemannianBallOf (S.g n) z.val (F.zero.zero z hz).radius)
                ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) := by
  by_cases hthr : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
          ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i
  · exact Or.inl hthr
  · right
    have hδ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
    obtain ⟨W, hW, g, B, hseq⟩ := exists_boundary_counterexample_sequence_of_no_threshold.{0} K A
      hδ (fun W _ _ B => ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
        ∀ i, Set.range (G.external.torusMap (e i)) = B.component i) hthr
    let S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar :=
      ⟨_, hδ, le_rfl, W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1⟩
    refine ⟨S, rfl, fun n => (hseq n).2.2, fun E => ?_⟩
    obtain ⟨V, R, n₀, hR⟩ := bbr02_graph_or_separated_BBS E S
    refine ⟨V, R, n₀, fun n hn => ?_⟩
    have hng := (hseq n).2.2
    have hempty : IsEmpty (Diffeomorph (torusModel.prod (𝓡∂ 1)) (S.W n).model
        (Torus × Icc (0 : ℝ) 1) (S.W n).Carrier ∞) :=
      ⟨fun D => hng (exists_labelledRawGraphPresentation_of_torusProduct_BBS (S.B n) D)⟩
    rcases hR n hn with hG | hsep
    · exact (hng hG).elim
    · exact ⟨hempty, hsep⟩

end DifferentialGeometry.Geometry.Collapse
