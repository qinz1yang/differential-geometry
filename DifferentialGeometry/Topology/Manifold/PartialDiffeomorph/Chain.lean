import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)] [∀ j, ChartedSpace H (M j)]

theorem chainComp_mapsTo
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (U : ∀ j, Set (M j))
    (hstep : ∀ j, Set.MapsTo (Ψ j) (U j) (U (j + 1))) (j k : ℕ) :
    Set.MapsTo (chainComp Ψ j k) (U j) (U (j + k)) := by
  intro x hx
  induction k with
  | zero => exact hx
  | succ k ih =>
      rw [chainComp_apply_succ]
      exact hstep (j + k) ih

theorem subset_chainComp_source
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (U : ∀ j, Set (M j))
    (hsource : ∀ j, U j ⊆ (Ψ j).source)
    (hstep : ∀ j, Set.MapsTo (Ψ j) (U j) (U (j + 1))) (j k : ℕ) :
    U j ⊆ (chainComp Ψ j k).source := by
  intro x hx
  induction k with
  | zero => exact Set.mem_univ x
  | succ k ih =>
      change x ∈ (chainComp Ψ j k).source ∧ chainComp Ψ j k x ∈ (Ψ (j + k)).source
      exact ⟨ih, hsource (j + k) (chainComp_mapsTo Ψ U hstep j k hx)⟩

theorem chainComp_shift_eq
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (N j k : ℕ) :
    chainComp (Mf := fun n => M (N + n)) (fun n => Ψ (N + n)) j k =
      (Nat.add_assoc N j k) ▸ chainComp Ψ (N + j) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hcast : ∀ {a b : ℕ} (h : a = b)
          (F : PartialDiffeomorph I I (M (N + j)) (M a) (∞ : WithTop ℕ∞)),
          _root_.PartialDiffeomorph.trans (h ▸ F) (Ψ b) =
            (congrArg (fun n => n + 1) h) ▸ _root_.PartialDiffeomorph.trans F (Ψ a) := by
        intro a b h F
        cases h
        rfl
      change _root_.PartialDiffeomorph.trans
        (chainComp (Mf := fun n => M (N + n)) (fun n => Ψ (N + n)) j k)
        (Ψ (N + (j + k))) = _
      rw [ih]
      exact hcast (Nat.add_assoc N j k) (chainComp Ψ (N + j) k)

end DifferentialGeometry.CheegerGromovCompactness

section

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]

theorem chainComp_one_eq
    (Ψ : ∀ n, PartialDiffeomorph I I (M n) (M (n + 1)) ∞) (n : ℕ) :
    chainComp Ψ n 1 = Ψ n := by
  have hpe : (chainComp Ψ n 1).toPartialEquiv = (Ψ n).toPartialEquiv :=
    PartialEquiv.refl_trans _
  cases hF : chainComp Ψ n 1
  cases hG : Ψ n
  simp only [hF, hG] at hpe
  cases hpe
  rfl

end DifferentialGeometry.CheegerGromovCompactness

end
