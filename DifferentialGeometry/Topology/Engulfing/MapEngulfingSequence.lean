import DifferentialGeometry.Topology.Engulfing.EngulfingSequence
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology
open scoped ContinuousMap

variable {X M : Type*} [TopologicalSpace X] [MetricSpace M]

theorem exists_map_engulfing_of_finite_steps
    (f : C(X, M)) (L : Set X) (A : Set M) (S : ℕ → C(X, M) → Set M)
    (Inv : ℕ → C(X, M) → Prop) {U : Set M} (hU : IsOpen U)
    (hInv : Inv 0 f) (hstart : S 0 f ⊆ U) (N : ℕ)
    (hstep : ∀ i < N, ∀ (g : C(X, M)) (V : Set M), IsOpen V → Inv i g → S i g ⊆ V →
      ∀ δ : ℝ, 0 < δ → ∃ (g' : C(X, M)) (G : M ≃ₜ M),
        Inv (i + 1) g' ∧ (∀ x ∈ L, g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < δ) ∧ S (i + 1) g' ⊆ G '' V ∧
        (∀ x ∈ A, G x = x) ∧ IsCompact (closure {x | G x ≠ x}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(X, M)) (H : M ≃ₜ M), Inv N g ∧ (∀ x ∈ L, g x = f x) ∧
      (∀ x, dist (g x) (f x) < ε) ∧ S N g ⊆ H '' U ∧
      (∀ x ∈ A, H x = x) ∧ IsCompact (closure {x | H x ≠ x}) := by
  let δ : ℝ := ε / ((N : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbound : (N : ℝ) * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < N + 1)]
    nlinarith
  have hfinite (i : ℕ) (hi : i ≤ N) :
      ∃ (g : C(X, M)) (H : M ≃ₜ M), Inv i g ∧ (∀ x ∈ L, g x = f x) ∧
        (∀ x, dist (g x) (f x) ≤ (i : ℝ) * δ) ∧ S i g ⊆ H '' U ∧
        (∀ x ∈ A, H x = x) ∧ IsCompact (closure {x | H x ≠ x}) := by
    induction i with
    | zero =>
        refine ⟨f, Homeomorph.refl M, hInv, fun _ _ => rfl, ?_, ?_, fun _ _ => rfl, ?_⟩
        · intro x; simp
        · exact fun x hx => ⟨x, hstart hx, rfl⟩
        · simp
    | succ i ih =>
        obtain ⟨g, H, hgInv, hgfix, hgnear, hginc, hHfix, hHcompact⟩ := ih (by omega)
        obtain ⟨g', G, hg'Inv, hg'fix, hg'near, hg'inc, hGfix, hGcompact⟩ :=
          hstep i (by omega) g (H '' U) (H.isOpenMap _ hU) hgInv hginc δ hδ
        refine ⟨g', H.trans G, hg'Inv, fun x hx => (hg'fix x hx).trans (hgfix x hx),
          ?_, ?_, ?_, isCompact_closure_moved_trans H G hHcompact hGcompact⟩
        · intro x
          calc
            dist (g' x) (f x) ≤ dist (g' x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
            _ ≤ δ + (i : ℝ) * δ := add_le_add (hg'near x).le (hgnear x)
            _ = (i.succ : ℝ) * δ := by push_cast; ring
        · intro x hx
          obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hg'inc hx
          exact ⟨z, hz, hy⟩
        · intro x hx
          rw [Homeomorph.trans_apply, hHfix x hx, hGfix x hx]
  obtain ⟨g, H, hgInv, hgfix, hgnear, hginc, hHfix, hHcompact⟩ := hfinite N le_rfl
  exact ⟨g, H, hgInv, hgfix, fun x => (hgnear x).trans_lt hbound, hginc, hHfix, hHcompact⟩

end DifferentialGeometry.Topology.Engulfing
