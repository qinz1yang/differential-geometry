import DifferentialGeometry.Topology.Homotopy.CubePathExtension
import DifferentialGeometry.Topology.Homotopy.CubePrismDeformation



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



theorem cubePathExtension_retract_eq (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x)
    (F : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (h0 : ∀ v, F (0, v) = Γ v)
    (hb : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    F (cubePrismRetract n z) = cubePathExtension n p Γ z := by
  unfold cubePathExtension
  split_ifs with h
  · have ht := cubePrismRetract_time_zero n z h
    have heq : cubePrismRetract n z = (0, (cubePrismRetract n z).2) := Prod.ext ht rfl
    rw [heq]
    exact h0 _
  · exact hb _ _ (cubePrismRetract_position_boundary n z (le_of_not_ge h))



theorem genLoopTransport_extension_unique (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (Δ : GenLoop (Fin (n + 1)) X y)
    (F : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (h0 : ∀ v, F (0, v) = Γ v) (h1 : ∀ v, F (1, v) = Δ v)
    (hb : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t) :
    GenLoop.Homotopic Δ (genLoopTransport n p Γ) := by
  refine ⟨{
    toFun := fun z => F (cubePrismDeformation n (z.1, (1, z.2)))
    continuous_toFun := F.continuous.comp ((cubePrismDeformation n).continuous.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro v
    rw [(cubePrismDeformation n).apply_zero]
    exact h1 v
  · intro v
    rw [(cubePrismDeformation n).apply_one]
    exact cubePathExtension_retract_eq n p Γ F h0 hb (1, v)
  · intro s v hv
    change F (cubePrismDeformation n (s, (1, v))) = Δ v
    rw [(cubePrismDeformation n).eq_fst s (show (1, v) ∈
      {z : unitInterval × (Fin (n + 1) → unitInterval) |
        z.1 = 0 ∨ z.2 ∈ Cube.boundary (Fin (n + 1))} from Or.inr hv)]
    exact h1 v



theorem genLoopTransport_refl_homotopic (n : ℕ) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n (Path.refl x) Γ) Γ := by
  exact (genLoopTransport_extension_unique n (Path.refl x) Γ Γ
    (Γ.val.comp ContinuousMap.snd) (fun _ => rfl) (fun _ => rfl)
      (fun _ v hv => GenLoop.boundary Γ v hv)).symm

end DifferentialGeometry.Topology
