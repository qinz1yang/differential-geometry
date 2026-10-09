import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NoncorePointBase_S59
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedRestart_S30

set_option autoImplicit false

/-!
# CH12-S59 (G1): the point sub-leaf `hNC` of A09 (O17 G3 / S47 G2)

`hNC_S59` is, binder for binder, the `hNC` binder of `exists_late_cut_family_of_cores_v3_S47`
(copied by script): on the restart `B.restart_S30 T hT`, a point of a block `i` of the real cut of
a component of the slice, at boundary distance `> 10`, whose block interior image is disjoint from
all core interior images, is not in any core image.  Proof: `noncore_point_stage_S59` (block point
in the cut interior, `reconstruction ∘ quotientMap` open there, cores' interiors dense) at the
stage `Q = (slices j).stage`, `h = postStage_eq_sliceStage_CX4`.
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

/-- **`hNC` (S59).**  The point sub-leaf of A09: a non-core block point at boundary distance
`> 10` is not in any core image of the truncations (statement = the `hNC` binder of
`exists_late_cut_family_of_cores_v3_S47`). -/
theorem hNC_S59 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) :
    ∀ (T : ℝ) (hT : B.start ≤ T) (level : ℕ → ℝ) (two_le : ∀ j, 2 ≤ level j)
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
                Set.range (trunc_S24 (B.restart_S30 T hT) base level two_le j c).inclusion
 := by
  intro T hT level two_le hball hcore _ _ j hj C i hnc p hp
  exact noncore_point_stage_S59
    (TruncatedCutData_IF4.ofBuffered_S19 (B.restart_S30 T hT)
      (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj) base (level j) (two_le j)
      (hball j hj))
    (ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj)
    (hdom_ofBuffered_S31 (B.restart_S30 T hT) base level two_le slices htimes hball hcore j hj)
    (postStage_eq_sliceStage_CX4 (slices j)) C
    (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i hnc
    (cutMetric_S25 ((slices j).componentMetric C)
      (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) p hp

end GC.LongTime.Ch12
