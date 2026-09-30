import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import DifferentialGeometry.Topology.FundamentalGroup.SigmaFundamentalGroup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapReconstruction
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open scoped Manifold ContDiff
universe u
namespace GC.Surgery

theorem finiteConnectedSum_factor
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) (i : Fin L.length)
    (x : (L.get i).Carrier) (y : (finiteConnectedSum L).Carrier) :
    GC.Group.IsFreeFactor (FundamentalGroup (L.get i).Carrier x)
      (FundamentalGroup (finiteConnectedSum L).Carrier y) := by
  let xs := fun j : Fin L.length => chosenPoint (L.get j)
  obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L xs y
  exact (GC.Group.isFreeFactor_coprodI
    (fun j : Fin L.length => FundamentalGroup (L.get j).Carrier (xs j)) i).congr
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (xs i) x) e.symm

theorem CutCapSumData.capComponent_freeFactor
    {M Q : ClosedOrientedManifold.{u} 3} {E : SphericalCutCapTransition M Q}
    (R : CutCapSumData E) (K : ConnectedComponents E.capped.Carrier)
    (x : (E.capped.component K).Carrier) :
    ∃ p : M.Carrier,
      GC.Group.IsFreeFactor (FundamentalGroup (E.capped.component K).Carrier x)
        (FundamentalGroup M.Carrier p) := by
  let L := fun w => (R.factors w).map E.capped.component ++
    List.replicate (R.sphereProducts w) (sphereTwoTimesCircleLift.ulift.{0, u})
  let V := fun w => (finiteConnectedSum (L w)).Carrier
  let w := R.assign K
  have hmem : E.capped.component K ∈ L w :=
    List.mem_append_left _ (List.mem_map.mpr
      ⟨K, (R.mem_factors w K).mpr rfl, rfl⟩)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  let y : V w := chosenPoint (finiteConnectedSum (L w))
  have hf : GC.Group.IsFreeFactor
      (FundamentalGroup (E.capped.component K).Carrier x)
      (FundamentalGroup (V w) y) := by
    have h := finiteConnectedSum_factor (L w) i
    rw [hi] at h
    exact h x y
  let a := GC.Topology.fundamentalGroupSigmaEquiv V w y
  let D : (Σ v, V v) ≃ₜ M.Carrier := R.reconstruct.toHomeomorph.symm
  let b := fundamentalGroupMulEquivOfHomotopyEquiv D.toHomotopyEquiv
    (⟨w, y⟩ : Σ v, V v) (D ⟨w, y⟩) rfl
  exact ⟨D ⟨w, y⟩, hf.congr (MulEquiv.refl _) (a.trans b)⟩

theorem actual_capComponent_freeFactor
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (K : ConnectedComponents E.capped.Carrier) (x : (E.capped.component K).Carrier) :
    ∃ p : M.Carrier,
      GC.Group.IsFreeFactor (FundamentalGroup (E.capped.component K).Carrier x)
        (FundamentalGroup M.Carrier p) := by
  obtain ⟨R⟩ := actual_cutCapSumData E
  exact R.capComponent_freeFactor K x

def componentFundamentalGroupEquiv (M : ClosedOrientedManifold.{u} 3)
    (K : ConnectedComponents M.Carrier) (x : (M.component K).Carrier) :
    FundamentalGroup (M.component K).Carrier x ≃* FundamentalGroup M.Carrier x.val :=
  (GC.Topology.fundamentalGroupSigmaEquiv (fun K => (M.component K).Carrier) K x).trans
    (fundamentalGroupMulEquivOfHomotopyEquiv M.componentUnionHomeomorph.toHomotopyEquiv
      (⟨K, x⟩ : Σ K, (M.component K).Carrier) x.val rfl)

theorem actual_retained_freeFactor
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (q : Q.Carrier) : ∃ p : M.Carrier,
      GC.Group.IsFreeFactor (FundamentalGroup Q.Carrier q) (FundamentalGroup M.Carrier p) := by
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, E.presentation_preservesOrientation⟩
  let z := E.presentation.symm (Sum.inl q)
  have hc : e.1.continuous.connectedComponentsMap (ConnectedComponents.mk z) =
      ConnectedComponents.mk (Sum.inl q) := by
    rw [Continuous.connectedComponentsMap_mk]
    exact congrArg ConnectedComponents.mk (E.presentation.apply_symm_apply (Sum.inl q))
  have hd : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (E.capped.component (ConnectedComponents.mk z)).toClosedOrientedManifold
      (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold) := by
    refine ⟨(e.component (ConnectedComponents.mk z)).trans ?_⟩
    rw [hc]
    exact ClosedOrientedManifold.sumComponentInlOrientedDiffeomorph q
  obtain ⟨D⟩ := hd
  let y : (Q.component (ConnectedComponents.mk q)).Carrier := ⟨q, rfl⟩
  let x := D.val.symm y
  obtain ⟨p, hp⟩ := actual_capComponent_freeFactor E (ConnectedComponents.mk z) x
  let a := fundamentalGroupMulEquivOfHomotopyEquiv D.val.toHomeomorph.toHomotopyEquiv
    x y (D.val.apply_symm_apply y)
  exact ⟨p, hp.congr (a.trans (componentFundamentalGroupEquiv Q _ y)) (MulEquiv.refl _)⟩

theorem finiteCutCapTrace_freeFactor (T : FiniteCutCapTrace.{u})
    (j : Fin (T.eventCount + 1)) (q : (T.stage j).Carrier) :
    ∃ p : (T.stage 0).Carrier,
      GC.Group.IsFreeFactor (FundamentalGroup (T.stage j).Carrier q)
        (FundamentalGroup (T.stage 0).Carrier p) := by
  induction j using Fin.induction with
  | zero => exact ⟨q, GC.Group.IsFreeFactor.refl _⟩
  | succ i ih =>
      obtain ⟨p, hp⟩ := actual_retained_freeFactor (T.transition i) q
      obtain ⟨p₀, h₀⟩ := ih p
      exact ⟨p₀, hp.trans h₀⟩

end GC.Surgery
