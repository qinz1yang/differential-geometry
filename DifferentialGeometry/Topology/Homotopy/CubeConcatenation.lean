import DifferentialGeometry.Topology.Homotopy.TransportComposition
import Mathlib.Topology.Piecewise



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



def cubeConcatValue (n : ℕ) (i : Fin (n + 1))
    (F G : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (z : unitInterval × (Fin (n + 1) → unitInterval)) : X :=
  if (z.2 i).val ≤ 1 / 2 then
    F (z.1, Function.update z.2 i (Set.projIcc 0 1 zero_le_one (2 * (z.2 i).val)))
  else G (z.1, Function.update z.2 i (Set.projIcc 0 1 zero_le_one (2 * (z.2 i).val - 1)))



theorem continuous_cubeConcatValue (n : ℕ) (i : Fin (n + 1)) (p : Path x y)
    (F G : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (hF : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t)
    (hG : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → G (t, v) = p t) :
    Continuous (cubeConcatValue n i F G) := by
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
      (continuous_const (y := (1 / 2 : ℝ))) hz
    change (z.2 i).val = (1 / 2 : ℝ) at heq
    have hbF : Function.update z.2 i (Set.projIcc 0 1 zero_le_one (2 * (z.2 i).val)) ∈
        Cube.boundary (Fin (n + 1)) := by
      refine ⟨i, Or.inr ?_⟩
      simp only [Function.update_self]
      norm_num [heq, Set.projIcc]
    have hbG : Function.update z.2 i (Set.projIcc 0 1 zero_le_one (2 * (z.2 i).val - 1)) ∈
        Cube.boundary (Fin (n + 1)) := by
      refine ⟨i, Or.inl ?_⟩
      simp only [Function.update_self]
      norm_num [heq, Set.projIcc]
    exact (hF _ _ hbF).trans (hG _ _ hbG).symm
  · exact F.continuous.comp (continuous_fst.prodMk
      (continuous_snd.update i (continuous_projIcc.comp
        (continuous_const.mul (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))))))
  · exact G.continuous.comp (continuous_fst.prodMk
      (continuous_snd.update i (continuous_projIcc.comp
        ((continuous_const.mul (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).sub
          continuous_const))))


theorem cubeConcatValue_eq_transAt (n : ℕ) (i : Fin (n + 1))
    (F G : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (t : unitInterval) (a : X) (Γ Δ : GenLoop (Fin (n + 1)) X a)
    (hF : ∀ v, F (t, v) = Γ v) (hG : ∀ v, G (t, v) = Δ v)
    (v : Fin (n + 1) → unitInterval) :
    cubeConcatValue n i F G (t, v) = GenLoop.transAt i Γ Δ v := by
  simp only [cubeConcatValue, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs
  · exact hF _
  · exact hG _



theorem cubeConcatValue_boundary (n : ℕ) (i : Fin (n + 1)) (p : Path x y)
    (F G : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (hF : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t)
    (hG : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → G (t, v) = p t)
    (t : unitInterval) (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubeConcatValue n i F G (t, v) = p t := by
  let Γ : GenLoop (Fin (n + 1)) X (p t) :=
    ⟨⟨fun w => F (t, w), F.continuous.comp (continuous_const.prodMk continuous_id)⟩, hF t⟩
  let Δ : GenLoop (Fin (n + 1)) X (p t) :=
    ⟨⟨fun w => G (t, w), G.continuous.comp (continuous_const.prodMk continuous_id)⟩, hG t⟩
  rw [cubeConcatValue_eq_transAt n i F G t (p t) Γ Δ (fun _ => rfl) (fun _ => rfl)]
  exact GenLoop.boundary _ v hv

end DifferentialGeometry.Topology
