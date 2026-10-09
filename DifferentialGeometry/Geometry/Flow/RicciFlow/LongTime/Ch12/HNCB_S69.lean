import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryTransport_S69
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundarySmall_S62
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutFamilyOfCoresV4_S59

set_option autoImplicit false

/-!
# CH12-S69 G1: `hNCB_S69` -- the `hNCB` leaf of `exists_late_cut_family_of_cores_v4_S59`

Statement = the `hNCB` binder of `exists_late_cut_family_of_cores_v4_S59`, verbatim.  Proof: the stage
theorem `ncb_stage_S69` (S39 + S51/S62 producer facts), transported to the slice by `ncb_slice_S69`
along `realDec_eq_S31`; size `max δ (√(1+δ) e^{-level/2} D_m) ≤ w` by `small_size_S62` for late `j`
(`B.accuracy_decay` and `htimes`), then `NearlyCuspidalBoundary.weaken`.
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

/-- **`hNCB` of the late-cut family (CH12-S69 G1).**  Statement verbatim the `hNCB` binder of
`exists_late_cut_family_of_cores_v4_S59`. -/
theorem hNCB_S69 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
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
            (realDec_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j C) i) (K + 4) w) := by
  intro T hT level two_le hball hcore hlev _hint w hw
  obtain ⟨Dm, hDm, hdiamDm⟩ := truncCusp_diam_S62 (B.restart_S30 T hT).toCores base
  obtain ⟨ε, hε, hsmall⟩ := small_size_S62 hDm hw
  obtain ⟨T₀, hT₀⟩ := B.accuracy_decay ε hε
  refine ⟨⌈T₀⌉₊, fun j hj hN C i hdisj hne => ?_⟩
  have ht := ceil_le_time_S31 (B.restart_S30 T hT) slices htimes j hj
  have hdecEq := congrFun
    (realDec_eq_S31 (B.restart_S30 T hT) base level two_le slices htimes hball j hj) C
  have hacc : B.accuracy (slices j).time < ε :=
    hT₀ _ ((Nat.le_ceil T₀).trans (by exact_mod_cast hN) |>.trans (htimes j).le)
  have hpos : 0 < B.accuracy (slices j).time := B.accuracy_pos _ (hT.trans ht)
  have hsm := hsmall _ (level j) hpos hacc (hlev j)
  obtain ⟨N⟩ := ncb_slice_S69 (B.restart_S30 T hT) ht
    (TruncatedCutData_IF4.ofBuffered_S19 (B.restart_S30 T hT) ht base (level j) (two_le j) (hball j hj))
    (hball j hj)
    (hdom_ofBuffered_S31 (B.restart_S30 T hT) base level two_le slices htimes hball hcore j hj)
    hDm (hdiamDm _ _ rfl)
    (postStage_eq_sliceStage_CX4 (slices j)) (slices j).metric
    (postMetric_regularSlice F.observation (slices j)) C _ hdecEq i hdisj hne
  exact ⟨N.weaken hsm⟩

end GC.LongTime.Ch12
