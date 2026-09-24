import DifferentialGeometry.Topology.ThreeManifold.CapComponentDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.PairedBallFinite

noncomputable section
open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_diffeomorph_finiteConnectedSum_capComponents :
    ∃ (W : Type u) (_ : Finite W)
      (assign : ConnectedComponents E.capped.Carrier → W)
      (L : W → List (ConnectedComponents E.capped.Carrier)) (k : W → ℕ),
      (∀ w K, K ∈ L w ↔ assign K = w) ∧ (∀ w, (L w).Nodup) ∧ (∀ w, L w ≠ []) ∧
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M.Carrier
        (Σ w, (finiteConnectedSum ((L w).map E.capped.component ++
          List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).Carrier) ∞) := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a,t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  let := E.capped.finite_components
  choose C _ using fun K => PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K
  obtain ⟨W,hW,assign,L,k,hm,hn,hne,Qcharts,hman,hcore,hseam,⟨D⟩⟩ :=
    PairedBallGluing.exists_finite_connectedSum_diffeomorph N ep ch hd C
  let _ := Qcharts
  obtain ⟨U⟩ := E.exists_pairedBallQuotient_diffeomorph C Qcharts hcore
    (fun a z => hseam a ⟨(z,0),Set.mem_univ _,by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  exact ⟨W,hW,assign,L,k,hm,hn,hne,⟨U.symm.trans D⟩⟩

end DifferentialGeometry.Topology.SphericalCutCapTransition
