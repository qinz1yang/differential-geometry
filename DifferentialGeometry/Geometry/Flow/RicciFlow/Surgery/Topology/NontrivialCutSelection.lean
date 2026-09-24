import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureBound
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

noncomputable section
open Set
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem nonempty_cut_or_discardedCore_of_singularEndpoint
    (G : P.IncomingSlab a s) (hG : G.SingularEndpoint)
    {ι : Type*} {δ : ι → ℝ} (f : ∀ i, bufferedCylinder (δ i) → P.Carrier)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R) G.terminalRegularRegion) :
    Nonempty ι ∨ Nonempty (discardedCore f R) := by
  classical
  by_cases hi : Nonempty ι
  · exact Or.inl hi
  · right
    let : IsEmpty ι := not_nonempty_iff.mp hi
    have hnot := G.terminalRegularRegion_ne_univ_of_singularEndpoint hG
    obtain ⟨x, hx⟩ : ∃ x : P.Carrier, x ∉ G.terminalRegularRegion := by
      by_contra h
      apply hnot
      ext x
      simp only [mem_univ, iff_true]
      exact not_exists_not.mp h x
    have hcore : x ∈ cutCore f := by
      simp only [cutCore, iUnion_of_empty, compl_empty, mem_univ]
    let p : cutCore f := ⟨x, hcore⟩
    have hn : p ∉ retainedCore f R := fun hp => hx (hRet hp)
    exact ⟨⟨p, hn⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
