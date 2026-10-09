import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelNormalForm

/-!
Every positive cycle length has actual balls, handles and necks on the fixed standard solid torus.
The empty index type cannot model that nonempty target, even though the bare normal-form structure
allows an empty union. The three-vertex consumer retains all six disjoint necks.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.Assembly

universe u

theorem exists_nonempty_modelCycleNormalForm (len : ℕ) (hlen : 0 < len) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ N : ModelCycleNormalForm.{u} len ε,
      (∀ k, (range (N.ball k)).Nonempty ∧ (range (N.handle k)).Nonempty) ∧
      ∀ k b, (N.neck k b).target.Nonempty := by
  let N := modelCycleNormalForm.{u} hlen hε hε1
  refine ⟨N, ?_, ?_⟩
  · intro k
    exact ⟨⟨N.ball k (⟨0, by simp⟩ : ClosedCell 3), mem_range_self _⟩,
      ⟨N.handle k ((⟨0, by simp⟩ : ClosedCell 2),
        (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)), mem_range_self _⟩⟩
  · intro k b
    have hzero : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ (N.neck k b).source := by
      rw [N.neck_source]
      change ‖(0 : EuclideanSpace ℝ (Fin 2))‖ < 1 + 2 * ε ∧ |(0 : ℝ)| < 2 * ε
      simp only [norm_zero, abs_zero]
      constructor <;> linarith
    exact ⟨N.neck k b 0, (N.neck k b).map_source hzero⟩

theorem isEmpty_modelCycleNormalForm_zero (ε : ℝ) :
    IsEmpty (ModelCycleNormalForm.{u} 0 ε) := by
  refine ⟨fun N => ?_⟩
  have hempty : solidTorusSet.{u} = ∅ := by
    simpa only [iUnion_of_empty, empty_union] using N.union_eq
  have hp := (solidTorusCollar.{u} ((1, 1), halfZero)).property
  exact (Set.mem_empty_iff_false _).mp ((Set.ext_iff.mp hempty _).mp hp)

theorem modelCycleNormalForm_length_pos {len : ℕ} {ε : ℝ}
    (N : ModelCycleNormalForm.{u} len ε) : 0 < len := by
  cases len with
  | zero => exact False.elim ((isEmpty_modelCycleNormalForm_zero ε).false N)
  | succ n => exact Nat.zero_lt_succ n

theorem threeCycle_six_nonempty_necks :
    ∃ N : ModelCycleNormalForm.{u} 3 (1 / 8),
      (∀ k b, (N.neck k b).target.Nonempty) ∧
      ∀ a b : Fin 3 × Bool, a ≠ b → Disjoint (N.neck a.1 a.2).target (N.neck b.1 b.2).target := by
  obtain ⟨N, hpieces, hnecks⟩ := exists_nonempty_modelCycleNormalForm.{u}
    3 (by decide) (1 / 8) (by norm_num) (by norm_num)
  exact ⟨N, hnecks, fun a b hab => N.neck_disjoint a.1 a.2 b.1 b.2 hab⟩

end GC.GraphManifold.Assembly
