import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryOut_S62
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryErrDiam_S62
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryAssembleReal_S39
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutAssemblyReal_S31

set_option autoImplicit false

/-!
# CH12-S69 G1a: the stage-level `NearlyCuspidalBoundary` of a non-core block

On the stage `postStage F.observation t` (no transport): from the S51/S62 producer facts
(`exists_phi_S51`, `phi_col_S51`, `phi_out_S62`, `phi_emb_S51`, `phi_imm_S51`, `phi_err_S62`,
the torus diameter bound) and `noleft_of_noncore_S51`, `nearlyCuspidal_of_collars_S39` gives a
`NearlyCuspidalBoundary` of size `max δ (√(1+δ) · D₀)` of the block `j` of the real cut of `C`
(`δ = B.accuracy t`, `D₀ = e^{-level/2} D_m`).
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

/-- **G1a (stage).**  See the module docstring. -/
theorem ncb_stage_S69 {K : ℕ} (B : BufferedPersistentCores F K) {t : ℝ} (ht : B.start ≤ t)
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
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (j : Fin (sliceDec_S28 D ht C).components.count)
    (hj : ∀ c : Fin B.toCores.count, coreComp_S28 D ht c = C →
      blockImage_S28 D ht C j ≠ corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _))
    (hne : ((sliceDec_S28 D ht C).component j).model.boundary
      ((sliceDec_S28 D ht C).component j).Carrier ≠ ∅) :
    Nonempty (NearlyCuspidalBoundary ((sliceDec_S28 D ht C).component j)
      (cutMetric_S25
        ((scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).restrictOpen
          ((postStage F.observation t).toClosedOrientedManifold.componentOpen C))
        (sliceDec_S28 D ht C) j)
      K (max (B.accuracy t) (Real.sqrt (1 + B.accuracy t) * (Real.exp (-D.level / 2) * Dm)))) := by
  classical
  choose φ hφ hsm using fun x : CIdx_S19 D ht C => exists_phi_S51 D ht C x
  exact nearlyCuspidal_of_collars_S39 (componentFamily_S19 D ht C) j
    ((scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).restrictOpen
      ((postStage F.observation t).toClosedOrientedManifold.componentOpen C))
    K (B.accuracy t) (Real.exp (-D.level / 2) * Dm) (by positivity)
    (noleft_of_noncore_S51 D ht hdom C j hj) hne
    (fun i => (D.truncation ((cidxEquiv_S19 D ht C).symm i).1.1).cusp ((cidxEquiv_S19 D ht C).symm i).1.2)
    (fun i => φ ((cidxEquiv_S19 D ht C).symm i))
    (fun i => phi_col_S51 D ht C i _ (hφ _))
    (fun i => phi_out_S62 D ht C _ _ (hφ _))
    (fun i => hsm _)
    (fun i => phi_emb_S51 D ht C _ _ (hφ _) (hsm _))
    (fun i => phi_imm_S51 D ht C _ _ (hφ _) (hsm _))
    (fun i => phi_err_S62 B ht D hball C _ _ (hφ _) (hsm _))
    (fun i x y => hdiam _ _ x y)

end GC.LongTime.Ch12
