import DifferentialGeometry.Topology.Homotopy.BasepointTransport
import DifferentialGeometry.Topology.Homotopy.CubeConcatenation



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



theorem genLoopTransport_transAt_homotopic (n : ℕ) (i : Fin (n + 1)) (p : Path x y)
    (Γ Δ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (GenLoop.transAt i (genLoopTransport n p Γ) (genLoopTransport n p Δ))
      (genLoopTransport n p (GenLoop.transAt i Γ Δ)) := by
  let F := (cubePathHomotopy n p Γ).toContinuousMap
  let G := (cubePathHomotopy n p Δ).toContinuousMap
  have hF : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t :=
    cubePathHomotopy_boundary n p Γ
  have hG : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → G (t, v) = p t :=
    cubePathHomotopy_boundary n p Δ
  let H : C(unitInterval × (Fin (n + 1) → unitInterval), X) :=
    ⟨cubeConcatValue n i F G, continuous_cubeConcatValue n i p F G hF hG⟩
  apply genLoopTransport_extension_unique n p (GenLoop.transAt i Γ Δ) _ H
  · intro v
    exact cubeConcatValue_eq_transAt n i F G 0 x Γ Δ
      (cubePathExtension_zero n p Γ) (cubePathExtension_zero n p Δ) v
  · intro v
    exact cubeConcatValue_eq_transAt n i F G 1 y (genLoopTransport n p Γ) (genLoopTransport n p Δ)
      (fun _ => rfl) (fun _ => rfl) v
  · exact cubeConcatValue_boundary n i p F G hF hG


theorem homotopyGroupTransport_mul (n : ℕ) (p : Path x y)
    (a b : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p (a * b) = homotopyGroupTransport n p a * homotopyGroupTransport n p b := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    induction b using Quotient.inductionOn with
    | h Δ =>
      have hmul := congrArg (homotopyGroupTransport n p)
        (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))) (p := Γ) (q := Δ))
      refine hmul.trans ?_
      have hc :
          (⟦genLoopTransport n p (GenLoop.transAt 0 Δ Γ)⟧ :
            HomotopyGroup (Fin (n + 1)) X y) =
          ⟦GenLoop.transAt 0 (genLoopTransport n p Δ) (genLoopTransport n p Γ)⟧ :=
        Quotient.sound (genLoopTransport_transAt_homotopic n 0 p Δ Γ).symm
      exact hc.trans (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))
        (p := genLoopTransport n p Γ) (q := genLoopTransport n p Δ)).symm



def homotopyGroupBasepointMulEquiv (n : ℕ) (p : Path x y) :
    HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) X y where
  toEquiv := homotopyGroupBasepointEquiv n p
  map_mul' := homotopyGroupTransport_mul n p

end DifferentialGeometry.Topology
