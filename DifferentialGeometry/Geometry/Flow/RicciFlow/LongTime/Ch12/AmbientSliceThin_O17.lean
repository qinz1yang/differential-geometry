import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutFamilyOfCores_O17
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinAmbientV2_S35

set_option autoImplicit false

/-!
# CH12-O17 (G3): the slice form of S35's outer thinness (`hAmbS` of O17 G1)

`outerThin_ambient_v2_S35` is stated on `postStage F.observation t` with the rescaled post metric;
the leaf `hAmbS` of `exists_late_cut_family_thin_O17` is stated on the component metric of the
slice.  Transport: `postStage_eq_sliceStage_CX4` + `postMetric_regularSlice` (`subst`), then the
open-closed component restriction (`curvatureRadius_restrictOpen_of_isClosed`,
`riemannianVolumeMeasure_ball_restrictOpen_of_isClosed`).  The point condition
(`x ∉ ⋃ cores images of the truncations`) is the inline sub-leaf `hNC`.
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- Stage transport of ambient collapse (generic `Q`, then `subst`). -/
theorem volumeCollapsed_of_post_O17 {Q : OrientedThreeStage.{u}} (t : ℝ)
    (h : postStage F.observation t = Q) (m : Q.Metric)
    (hm : HEq (postMetric F.observation t) m) (hp : 0 < t⁻¹) (w : ℝ)
    (S : Set (postStage F.observation t).Carrier)
    (hS : ∀ x, x ∉ S → volumeCollapsedAtCurvatureScale
      (scaleMetric t⁻¹ hp (postMetric F.observation t)) w x)
    (y : Q.Carrier) (hy : y ∉ cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h) '' S) :
    volumeCollapsedAtCurvatureScale (scaleMetric t⁻¹ hp m) w y := by
  subst h
  obtain rfl := eq_of_heq hm
  exact hS y (fun hyS => hy ⟨y, hyS, rfl⟩)

/-- Ambient collapse of the normalized slice metric at `x.val` gives collapse of the component
metric at `x`. -/
theorem volumeCollapsed_component_O17 (s : RegularSlice F.observation)
    (C : ConnectedComponents s.stage.Carrier) (w : ℝ)
    (x : (s.stage.toClosedOrientedManifold.component C).Carrier)
    (hx : volumeCollapsedAtCurvatureScale s.normalizedMetric w x.val) :
    volumeCollapsedAtCurvatureScale (s.componentMetric C) w x := by
  set U := s.stage.toClosedOrientedManifold.componentOpen C with hUdef
  have hU : IsClosed (U : Set s.stage.toClosedOrientedManifold.Carrier) :=
    ClosedOrientedManifold.isClosed_componentSet s.stage.toClosedOrientedManifold C
  intro r hr hcr
  have hRc : curvatureRadius (s.componentMetric C) x = curvatureRadius s.normalizedMetric x.val :=
    curvatureRadius_restrictOpen_of_isClosed s.normalizedMetric U hU x
  have hvol : ballVolume (s.componentMetric C) x r = ballVolume s.normalizedMetric x.val r :=
    Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed s.normalizedMetric U hU x r
  rw [hvol]
  exact hx r hr (hRc ▸ hcr)

/-- **`hAmbS` from S35 (O17 G3).**  The slice-form leaf of `exists_late_cut_family_thin_O17`
from `outerThin_ambient_v2_S35` (inline `hTrans`, S40 / S41), the inner containment of the
restart data, and the point sub-leaf `hNC` (a non-core piece point at boundary distance `> 10`
is not in any core image of the truncations). -/
theorem hAmbS_of_outerThin_O17 {K : ℕ} (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹))
    (hTrans : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t →
      ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4)
    (hinner : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
      riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
          ((B.accuracy (slices j).time)⁻¹ / 2) ⊆
        interior (Set.range (trunc_S24 B base level two_le j i).inclusion))
    (hNC : ∀ j (hj : ⌈B.start⌉₊ ≤ j)
      (C : ConnectedComponents (slices j).stage.Carrier)
      (i : Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin B.count,
          Disjoint
            ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                  ((trunc_S24 B base level two_le j c).inclusion x))) ''
              ((trunc_S24 B base level two_le j c).core.interior : Set _))) →
        ∀ p : ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((realDec_S31 B base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 B base level two_le slices htimes hball j C) i) p →
          ((cutPieceMap (realDec_S31 B base level two_le slices htimes hball j C) i p).val :
              (slices j).stage.Carrier) ∉
            sliceCast_CX4 (slices j) '' ⋃ c : Fin B.count,
              B.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj) ''
                Set.range (trunc_S24 B base level two_le j c).inclusion) :
    ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈B.start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin B.count,
          Disjoint
            ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                  ((trunc_S24 B base level two_le j c).inclusion x))) ''
              ((trunc_S24 B base level two_le j c).core.interior : Set _))) →
        ∀ p : ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((realDec_S31 B base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 B base level two_le slices htimes hball j C) i) p →
          volumeCollapsedAtCurvatureScale ((slices j).componentMetric C) w
            (cutPieceMap (realDec_S31 B base level two_le slices htimes hball j C) i p) := by
  intro w hw
  obtain ⟨T, hT⟩ := outerThin_ambient_v2_S35 B base hTrans w hw
  refine ⟨⌈T⌉₊, fun j hj hN C i hnc p hD => ?_⟩
  have hTt : T ≤ (slices j).time :=
    ((Nat.le_ceil T).trans (by exact_mod_cast hN)).trans (htimes j).le
  have hpost := hT (slices j).time (ceil_le_time_S31 B slices htimes j hj) hTt
    (fun c => trunc_S24 B base level two_le j c) (fun c => (hinner j hj c).trans interior_subset)
  refine volumeCollapsed_component_O17 (slices j) C w _ ?_
  exact volumeCollapsed_of_post_O17 (slices j).time (postStage_eq_sliceStage_CX4 (slices j))
    (slices j).metric (postMetric_regularSlice F.observation (slices j)) _ w _ hpost _
    (hNC j hj C i hnc p hD)

/-- **A09 from cores, v2 (O17 G3).**  As `exists_late_cut_family_of_cores_O17`, with the leaf
`hAmbS` replaced by S35's `hTrans` (for `B`; transferred to the restart by `restart_map_S30`, rfl)
and the point sub-leaf `hNC` (G-form). -/
theorem exists_late_cut_family_of_cores_v2_O17 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    -- proved as `collarNegativePlane_S16` / `exists_negative_plane_of_nearlyCuspidal_S27`; inline only
    -- because BoundaryWiringG2_S16 cannot be imported together with S29 (duplicate
    -- `CuspEmbedding.isOpen_image`)
    (hG2 : CollarNegativePlane.{u} K)
    (hNP : ∀ (W : CompactCarrier.{u}) (h : SmoothRiemannianMetric W.model W.Carrier),
      NearlyCuspidalBoundary W h (K + 4) (1 / 10000) → ∃ q, ¬ SectionalBoundedBelowAt h q (-(1 / 81 : ℝ)))
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
    (hTrans : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t →
      ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4)
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
    Nonempty (LateCutFamily F K slices) := by
  obtain ⟨T, hT, level, two_le, hlev, hball, hcore, hinner⟩ :=
    exists_restart_ball_inputs_O17 B base slices htimes
  obtain ⟨c₀, hc₀, T₁, hT₁⟩ := hTrans
  exact exists_late_cut_family_thin_O17 F K hK δ hadm hdec slices htimes hnonempty
    (B.restart_S30 T hT) base level two_le hball hcore hG2 hNP
    (hNCB T hT level two_le hball hcore hlev hinner)
    (hAmbS_of_outerThin_O17 slices htimes (B.restart_S30 T hT) base level two_le hball
      ⟨c₀, hc₀, T₁, fun t ht hT1 i y hy => hT₁ t (hT.trans ht) hT1 i y hy⟩ hinner
      (hNC T hT level two_le hball hcore hlev hinner))

end GC.LongTime.Ch12
