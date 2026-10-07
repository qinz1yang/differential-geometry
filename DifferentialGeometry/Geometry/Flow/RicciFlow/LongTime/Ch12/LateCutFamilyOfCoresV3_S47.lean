import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AmbientSliceThin_O17
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringG2_S16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinAlternativesFinite_S27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferFinal_S40

set_option autoImplicit false

/-!
# CH12-S47 (G2): A09 from cores, v3 -- `hG2`, `hNP`, `hTrans` discharged

`exists_late_cut_family_of_cores_v2_O17` (O17 G3) left the inline binders `hG2`, `hNP` (proved as
`collarNegativePlane_S16` and `exists_negative_plane_of_nearlyCuspidal_S27`, but unimportable
together with the S29/S35 chain: duplicate `CuspEmbedding.isOpen_image`, fixed by CH12-S47 FIX) and
`hTrans` (proved as `hTrans_S40`).  Here they are supplied by the proved theorems; the remaining
inputs are the buffered cores `B`, the truncation `base`, `hNCB` (S51) and `hNC`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- **A09 from cores, v3 (CH12-S47 G2).**  Conclusion verbatim `exists_late_cut_family`.  As
`exists_late_cut_family_of_cores_v2_O17` with `hG2 := collarNegativePlane_S16 K`,
`hNP := exists_negative_plane_of_nearlyCuspidal_S27` and `hTrans := hTrans_S40 B`; only `hNCB` and
the point sub-leaf `hNC` remain besides `B` and `base`. -/

theorem exists_late_cut_family_of_cores_v3_S47 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (hNCB : ∀ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j)
      (hball : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            (2 * ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹))
      (_hcore : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion ⊆
          riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹)
      ,
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) →
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        riemannianClosedBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (((B.restart_S30 T hT).accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion)) →
      ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈(B.restart_S30 T hT).start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin (B.restart_S30 T hT).count,
          Disjoint
            ((fun x => (((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                ((B.restart_S30 T hT).toCores.map c (slices j).time (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj)
                  ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion x))) ''
              ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).core.interior : Set _))) →
        ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).model.boundary
            ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).Carrier ≠ ∅ →
        Nonempty (NearlyCuspidalBoundary
          ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i)
          (cutMetric_S25 ((slices j).componentMetric C)
            (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) (K + 4) w))
    (hNC : ∀ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j)
      (hball : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
        p.2.val 0 ≤ level j + 200 →
          (base i).cuspMap q p ∈ riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            (2 * ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹))
      (_hcore : ∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion ⊆
          riemannianBallOf ((B.restart_S30 T hT).model i).metric ((B.restart_S30 T hT).model i).basepoint
            ((B.restart_S30 T hT).accuracy (slices j).time)⁻¹)
      ,
      (∀ j, (B.accuracy (slices j).time)⁻¹ / 2 ≤ level j) →
      (∀ j, ⌈(B.restart_S30 T hT).start⌉₊ ≤ j → ∀ i : Fin (B.restart_S30 T hT).count,
        riemannianClosedBallOf ((B.restart_S30 T hT).model i).metric
            ((B.restart_S30 T hT).model i).basepoint
            (((B.restart_S30 T hT).accuracy (slices j).time)⁻¹ / 2) ⊆
          interior (Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j i).inclusion)) →
      ∀ j (hj : ⌈(B.restart_S30 T hT).start⌉₊ ≤ j)
      (C : ConnectedComponents (slices j).stage.Carrier)
      (i : Fin (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin (B.restart_S30 T hT).count,
          Disjoint
            ((fun x => (((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                ((B.restart_S30 T hT).toCores.map c (slices j).time (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj)
                  ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion x))) ''
              ((trunc_S24 (B.restart_S30 T hT) base level two_le j c).core.interior : Set _))) →
        ∀ p : ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) p →
          ((cutPieceMap (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i p).val :
              (slices j).stage.Carrier) ∉
            sliceCast_CX4 (slices j) '' ⋃ c : Fin (B.restart_S30 T hT).count,
              (B.restart_S30 T hT).map c (slices j).time (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj) ''
                Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion) :
    Nonempty (LateCutFamily F K slices) :=
  exists_late_cut_family_of_cores_v2_O17 F K hK δ hadm hdec slices htimes hnonempty B base
    (collarNegativePlane_S16 K) (fun _ _ N => exists_negative_plane_of_nearlyCuspidal_S27 N)
    hNCB (hTrans_S40 B) hNC

end GC.LongTime.Ch12
