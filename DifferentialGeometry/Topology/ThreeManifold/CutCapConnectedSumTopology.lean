import DifferentialGeometry.Topology.ThreeManifold.CapComponentQuotient
import DifferentialGeometry.Topology.ThreeManifold.PairedBallFinite
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSumSimplyConnected
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleSimplyConnected
import DifferentialGeometry.Topology.FundamentalGroup.Sigma
import DifferentialGeometry.Topology.FundamentalGroup.ConnectedComponent

set_option autoImplicit false
noncomputable section
open Set Metric

section

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem nonempty_pairedBall_homeomorph :
    Nonempty (Quot (fun x y => ∃ a, PairedBallGluing.seamRel E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) E.pairwise_disjoint_capComponentBallChart_image
      a boundaryAttachment x y) ≃ₜ M.Carrier) := by
  obtain ⟨Ψ, ρ, hρ, hzero, hone, hpos, hgerm, hp, hlo, hhi, F, hsurj, hcore, hann, hin, H, hH⟩ :=
    E.capping.exists_uncapping_homeomorph
  exact ⟨E.pairedBallUncappingHomeomorph.trans H⟩

theorem exists_connectedSum_capComponents [ConnectedSpace M.Carrier] :
    ∃ (L : List (ConnectedComponents E.capped.Carrier)) (k : ℕ),
      L.Nodup ∧ (∀ K, K ∈ L) ∧
      Nonempty (M.Carrier ≃ₜ
        (finiteConnectedSum (L.map E.capped.component ++
          List.replicate k (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) := by
  obtain ⟨H⟩ := nonempty_pairedBall_homeomorph E
  let P := Quot (fun x y => ∃ a, PairedBallGluing.seamRel E.capped.component E.cutCapVertex
    (fun a t => E.capComponentBallChart (a, t)) E.pairwise_disjoint_capComponentBallChart_image
    a boundaryAttachment x y)
  let : ConnectedSpace P := (H.connectedSpace_iff).mpr inferInstance
  let := E.capped.finite_components
  have hcapped : Nonempty E.capped.Carrier := by
    obtain ⟨z⟩ := (inferInstance : Nonempty P)
    obtain ⟨x, hx⟩ := Quot.exists_rep z
    exact ⟨x.snd.val.val⟩
  let := hcapped
  let : Nonempty (ConnectedComponents E.capped.Carrier) :=
    ⟨ConnectedComponents.mk (Classical.choice hcapped)⟩
  obtain ⟨L, k, hn, hcov, ⟨J⟩⟩ :=
    PairedBallGluing.exists_connectedSum_quotient_of_preconnected E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) E.pairwise_disjoint_capComponentBallChart_image
  exact ⟨L, k, hn, hcov, ⟨H.symm.trans J⟩⟩

theorem simplyConnectedSpace_capComponent [SimplyConnectedSpace M.Carrier]
    (K : ConnectedComponents E.capped.Carrier) :
    SimplyConnectedSpace (E.capped.component K).Carrier := by
  obtain ⟨L, k, hn, hcov, ⟨H⟩⟩ := E.exists_connectedSum_capComponents
  have hsc := H.toHomotopyEquiv.simplyConnectedSpace_iff.mp
    (inferInstance : SimplyConnectedSpace M.Carrier)
  have h := (simplyConnectedSpace_finiteConnectedSum_append_replicate_iff
    (L.map E.capped.component) (sphereTwoTimesCircleLift.ulift.{0, u}) k
    not_simplyConnectedSpace_sphereTwoTimesCircleLift_ulift).mp hsc
  exact h.2 _ (List.mem_map.mpr ⟨K, hcov K, rfl⟩)


theorem exists_connectedSum_capComponents_of_simplyConnected [SimplyConnectedSpace M.Carrier] :
    ∃ L : List (ConnectedComponents E.capped.Carrier), L.Nodup ∧ (∀ K, K ∈ L) ∧
      Nonempty (M.Carrier ≃ₜ (finiteConnectedSum (L.map E.capped.component)).Carrier) := by
  obtain ⟨L, k, hn, hcov, ⟨H⟩⟩ := E.exists_connectedSum_capComponents
  exact ⟨L, hn, hcov, nonempty_homeomorph_finiteConnectedSum_of_simplyConnected
    (L.map E.capped.component) (sphereTwoTimesCircleLift.ulift.{0, u}) k
    not_simplyConnectedSpace_sphereTwoTimesCircleLift_ulift H⟩

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem fundamentalGroup_subsingleton_of_components
    (hM : ∀ K : ConnectedComponents M.Carrier, SimplyConnectedSpace (M.component K).Carrier)
    (x : M.Carrier) : Subsingleton (FundamentalGroup M.Carrier x) := by
  have h := hM (ConnectedComponents.mk x)
  change SimplyConnectedSpace (M.componentSet (ConnectedComponents.mk x)) at h
  rw [M.componentSet_mk] at h
  let := h
  exact subsingleton_fundamentalGroup_of_simplyConnected_connectedComponent x

theorem simplyConnectedSpace_capComponent_of_componentwise
    (hM : ∀ K : ConnectedComponents M.Carrier, SimplyConnectedSpace (M.component K).Carrier)
    (K : ConnectedComponents E.capped.Carrier) :
    SimplyConnectedSpace (E.capped.component K).Carrier := by
  obtain ⟨H⟩ := E.nonempty_pairedBall_homeomorph
  let := E.capped.finite_components
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, ⟨J⟩⟩ :=
    PairedBallGluing.exists_finite_connectedSum_quotient E.capped.component E.cutCapVertex
      (fun a t => E.capComponentBallChart (a, t)) E.pairwise_disjoint_capComponentBallChart_image
  let N := fun w => finiteConnectedSum ((L w).map E.capped.component ++
    List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))
  let G : (Σ w, (N w).Carrier) ≃ₜ M.Carrier := J.symm.trans H
  have hpi (x : Σ w, (N w).Carrier) : Subsingleton (FundamentalGroup (Σ w, (N w).Carrier) x) := by
    let := fundamentalGroup_subsingleton_of_components hM (G x)
    exact (fundamentalGroupMulEquivOfHomotopyEquiv G.toHomotopyEquiv x (G x)
        rfl).injective.subsingleton
  let x₀ : (N (assign K)).Carrier := Classical.choice inferInstance
  have hsc : SimplyConnectedSpace (N (assign K)).Carrier :=
    simplyConnectedSpace_sigma_fiber_of_subsingleton_fundamentalGroup
      (fun w => (N w).Carrier) (assign K) x₀ (hpi ⟨assign K, x₀⟩)
  have hfac := (simplyConnectedSpace_finiteConnectedSum_append_replicate_iff
    ((L (assign K)).map E.capped.component) (sphereTwoTimesCircleLift.ulift.{0, u})
    (k (assign K)) not_simplyConnectedSpace_sphereTwoTimesCircleLift_ulift).mp hsc
  exact hfac.2 _ (List.mem_map.mpr ⟨K, (hm (assign K) K).mpr rfl, rfl⟩)

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem simplyConnectedSpace_presentedComponent_of_componentwise (hM : ∀ C :
    ConnectedComponents M.Carrier, SimplyConnectedSpace (M.component C).Carrier)
    (y : Q.Carrier ⊕ E.discarded.Carrier) :
    SimplyConnectedSpace ((ClosedOrientedManifold.sum Q E.discarded).component
      (ConnectedComponents.mk y)).Carrier := by
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, E.presentation_preservesOrientation⟩
  let x := E.presentation.symm y
  have hC : e.val.continuous.connectedComponentsMap (ConnectedComponents.mk x) =
      ConnectedComponents.mk y := by
    rw [Continuous.connectedComponentsMap_mk]
    exact congrArg ConnectedComponents.mk (E.presentation.apply_symm_apply y)
  have hsc := E.simplyConnectedSpace_capComponent_of_componentwise hM (ConnectedComponents.mk x)
  let H := (e.component (ConnectedComponents.mk x)).val.toHomeomorph.toHomotopyEquiv
  have h := H.simplyConnectedSpace_iff.mp hsc
  rw [hC] at h
  exact h

include E in
theorem simplyConnectedSpace_retainedComponent_of_componentwise (hM : ∀ C :
    ConnectedComponents M.Carrier, SimplyConnectedSpace (M.component C).Carrier)
    (K : ConnectedComponents Q.Carrier) : SimplyConnectedSpace (Q.component K).Carrier := by
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe K
  have hsc := E.simplyConnectedSpace_presentedComponent_of_componentwise hM (Sum.inl q)
  exact (ClosedOrientedManifold.sumComponentInlOrientedDiffeomorph
    (X := Q) (Y := E.discarded) q).val.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mp hsc

theorem simplyConnectedSpace_discardedComponent_of_componentwise (hM : ∀ C :
    ConnectedComponents M.Carrier, SimplyConnectedSpace (M.component C).Carrier)
    (K : ConnectedComponents E.discarded.Carrier) :
    SimplyConnectedSpace (E.discarded.component K).Carrier := by
  obtain ⟨d, rfl⟩ := ConnectedComponents.surjective_coe K
  have hsc := E.simplyConnectedSpace_presentedComponent_of_componentwise hM (Sum.inr d)
  exact (ClosedOrientedManifold.sumComponentInrOrientedDiffeomorph
    (X := Q) (Y := E.discarded) d).val.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mp hsc

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section

namespace DifferentialGeometry.Topology.FiniteCutCapTrace

universe u

theorem componentwise_simplyConnectedSpace
    (T : FiniteCutCapTrace.{u})
    (h0 : ∀ C : ConnectedComponents (T.stage 0).Carrier,
      SimplyConnectedSpace ((T.stage 0).component C).Carrier) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      SimplyConnectedSpace ((T.stage i).component C).Carrier := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    exact (T.transition i).simplyConnectedSpace_retainedComponent_of_componentwise ih

theorem discarded_simplyConnectedSpace
    (T : FiniteCutCapTrace.{u})
    (h0 : ∀ C : ConnectedComponents (T.stage 0).Carrier,
      SimplyConnectedSpace ((T.stage 0).component C).Carrier)
    (i : Fin T.eventCount) (C : ConnectedComponents (T.transition i).discarded.Carrier) :
    SimplyConnectedSpace ((T.transition i).discarded.component C).Carrier :=
  (T.transition i).simplyConnectedSpace_discardedComponent_of_componentwise
    (T.componentwise_simplyConnectedSpace h0 i.castSucc) C

end DifferentialGeometry.Topology.FiniteCutCapTrace

end
