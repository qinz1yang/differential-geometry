import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryStage_S69

set_option autoImplicit false

/-!
# CH12-S69 G1b: transport of the stage-level `NearlyCuspidalBoundary` to the slice

`ncb_stage_S69` is on `postStage F.observation t` with `sliceDec_S28`; here a generic transport over
`h : postStage F.observation t = Q`, `HEq (postMetric ..) m` and `dec = transportDec_S31 h (sliceDec_S28 ..) C`
(`subst` pattern of `realBlock_dichotomy_S31` / `volumeCollapsed_of_post_O17`).  The hypothesis
`hdisj` (the block's interior image is disjoint from every core image) is turned into the
non-core-block condition `hj` of `noleft_of_noncore_S51` via `core_interior_nonempty_S31`.
-/

noncomputable section

open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
  DifferentialGeometry.Geometry.Collapse GC.Topology GC.GraphManifold
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- **G1b (transport).**  See the module docstring. -/
theorem ncb_slice_S69 {K : ℕ} (B : BufferedPersistentCores F K) {t : ℝ} (ht : B.start ≤ t)
    (D : TruncatedCutData_IF4 B.toCores t)
    (hball : ∀ i (q : Fin (D.base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ D.level + 200 →
      (D.base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
        (2 * (B.accuracy t)⁻¹))
    (hdom : ∀ i, range (D.truncation i).inclusion ⊆
      (B.toCores.domain i t : Set (B.toCores.model i).Carrier))
    {Dm : ℝ} (hDm : 0 ≤ Dm)
    (hdiam : ∀ (c : Fin B.toCores.count) (q : Fin (D.base c).count) (x y : Torus),
      riemannianEDistOf ((D.truncation c).cusp q).torusMetric x y ≤
        ENNReal.ofReal (Real.exp (-D.level / 2) * Dm))
    {Q : OrientedThreeStage.{u}} (h : postStage F.observation t = Q) (m : Q.Metric)
    (hm : HEq (postMetric F.observation t) m)
    (C : ConnectedComponents Q.Carrier)
    (dec : TorusDecomposition (Q.toClosedOrientedManifold.component C))
    (hdec : dec = transportDec_S31 h (sliceDec_S28 D ht) C) (i : Fin dec.components.count)
    (hdisj : ∀ c : Fin B.toCores.count,
      Disjoint
        ((fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val : Q.Carrier)) ''
          (dec.carrier.pieceInterior (dec.components.piece i) : Set _))
        ((fun x => cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h)
            (B.toCores.map c t ht ((D.truncation c).inclusion x))) ''
          ((D.truncation c).core.interior : Set _)))
    (hne : (dec.component i).model.boundary (dec.component i).Carrier ≠ ∅) :
    Nonempty (NearlyCuspidalBoundary (dec.component i)
      (cutMetric_S25
        ((scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) m).restrictOpen
          (Q.toClosedOrientedManifold.componentOpen C)) dec i)
      K (max (B.accuracy t) (Real.sqrt (1 + B.accuracy t) * (Real.exp (-D.level / 2) * Dm)))) := by
  subst hdec
  subst h
  obtain rfl := eq_of_heq hm
  refine ncb_stage_S69 B ht D hball hdom hDm hdiam C i ?_ hne
  intro c _ heq
  have hd : Disjoint (blockImage_S28 D ht C i)
      (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) := hdisj c
  rw [heq] at hd
  obtain ⟨y, hy⟩ := core_interior_nonempty_S31 D c
  exact Set.disjoint_left.mp hd ⟨y, hy, rfl⟩ ⟨y, hy, rfl⟩

end GC.LongTime.Ch12
