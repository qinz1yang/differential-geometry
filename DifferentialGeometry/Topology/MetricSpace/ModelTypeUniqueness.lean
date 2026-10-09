import DifferentialGeometry.Topology.MetricSpace.ModelSeparation
import Mathlib.Data.List.Pairwise

set_option autoImplicit false

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem one_dimensional_model_types_pairwise :
    List.Pairwise (fun A B : Prop => ¬ (A ∧ B))
      [Nonempty (X ≃ᵢ EuclideanSpace ℝ (Fin 0)),
       Nonempty (X ≃ᵢ ℝ),
       Nonempty (X ≃ᵢ Ici (0 : ℝ)),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ Icc (0 : ℝ) L),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ AddCircle L)] := by
  have ht {A B : Type} [MetricSpace A] [MetricSpace B]
      (h : ¬ Nonempty (A ≃ᵢ B)) : ¬ (Nonempty (X ≃ᵢ A) ∧ Nonempty (X ≃ᵢ B)) := by
    rintro ⟨⟨e⟩, ⟨f⟩⟩
    exact h ⟨e.symm.trans f⟩
  have hs := not_nonempty_subsingleton_models (X := EuclideanSpace ℝ (Fin 0))
  simp only [List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, List.Pairwise.nil, and_true]
  refine ⟨⟨ht hs.1, ht hs.2.1, ?_, ?_⟩,
    ⟨ht not_nonempty_real_Ici, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ha, L, hL, hb⟩
    exact ht (hs.2.2.1 L hL) ⟨ha, hb⟩
  · rintro ⟨ha, L, hL, hb⟩
    exact ht (hs.2.2.2 L hL) ⟨ha, hb⟩
  · rintro ⟨ha, L, hL, hb⟩
    exact ht (not_nonempty_real_Icc hL) ⟨ha, hb⟩
  · rintro ⟨ha, L, hL, hb⟩
    exact ht (not_nonempty_real_addCircle hL) ⟨ha, hb⟩
  · rintro ⟨ha, L, _, hb⟩
    exact ht not_nonempty_Ici_Icc ⟨ha, hb⟩
  · rintro ⟨ha, L, hL, hb⟩
    exact ht (not_nonempty_Ici_addCircle hL) ⟨ha, hb⟩
  · rintro ⟨⟨L, hL, ha⟩, M, hM, hb⟩
    exact ht (not_nonempty_Icc_addCircle hL hM) ⟨ha, hb⟩

end Metric
