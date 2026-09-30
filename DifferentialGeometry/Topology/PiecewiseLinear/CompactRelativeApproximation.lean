import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Chain

variable {n : ℕ} {M₁ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] {U : Set M₁}

theorem LocallyFinitePieceTower.eqOn_coreSpace_of_le {Y : Type*}
    (T : LocallyFinitePieceTower n M₁ U) {f : ℕ → M₁ → Y}
    (hf : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) {i j : ℕ} (hij : i ≤ j) :
    EqOn (f j) (f i) (T.coreSpace i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ k hik ih => exact fun x hx => (hf k (T.core_space_monotone hik hx)).trans (ih hx)

end Chain

section NonVacuity

theorem LocallyFinitePieceTower.coreSpace_ofPiece {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X} (P : PLPiece n X Y) (i : ℕ) :
    (LocallyFinitePieceTower.ofPiece P).coreSpace i = Y :=
  P.piece.bijOn.image_eq

theorem LocallyFinitePieceTower.exists_isPLOn_injOn_eqOn_dist_lt_of_coreSpace_succ_subset
    {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] {K : Set M₁}
    (T : LocallyFinitePieceTower n M₁ K) {i : ℕ}
    (hsub : T.coreSpace (i + 1) ⊆ T.coreSpace i) {g h : M₁ → M₂} {φ : M₁ → ℝ}
    (hg : IsPLHomeomorphInto n g (T.coreSpace i))
    (hd : ∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧ InjOn f (T.coreSpace (i + 1)) ∧
      EqOn f g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x := by
  have heq : T.coreSpace (i + 1) = T.coreSpace i :=
    Subset.antisymm hsub (T.core_space_monotone (Nat.le_succ i))
  refine ⟨g, ?_, ?_, fun _ _ => rfl, fun x hx => hd x (hsub hx)⟩
  · rw [heq]
    exact hg.isPLOn
  · rw [heq]
    exact hg.injOn

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
