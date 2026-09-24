import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_partial_tree_succ_of_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} {Ω : Set E} (K : ℕ)
    (f : Lp ℝ p (μ.prod (volume.restrict Ω)))
    (g : Fin d → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (V : Fin d → ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (hroot : ∀ i, V i 0 (fun j : Fin 0 => Fin.elim0 j) = g i)
    (hfirst : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => g i (t, x)) (fun x => f (t, x)) Ω)
    (hweak : ∀ i m, m < K → ∀ α j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => V i (m + 1) (Fin.cons j α) (t, x)) (fun x => V i m α (t, x)) Ω) :
    ∃ W : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)),
      W 0 (fun j : Fin 0 => Fin.elim0 j) = f ∧
      (∀ i, W 1 (Fin.cons i (fun j : Fin 0 => Fin.elim0 j)) = g i) ∧
      ∀ m, m < K + 1 → ∀ α j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => W (m + 1) (Fin.cons j α) (t, x)) (fun x => W m α (t, x)) Ω := by
  let W : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω))
    | 0, _ => f
    | m + 1, α => V (α (Fin.last m)) m (Fin.init α)
  have hrootV (i : Fin d) (α : Fin 0 → Fin d) : V i 0 α = g i := by
    have he : α = (fun j : Fin 0 => Fin.elim0 j) := Subsingleton.elim _ _
    rw [he]
    exact hroot i
  have hWone (i : Fin d) (α : Fin 0 → Fin d) : W 1 (Fin.cons i α) = g i := by
    change V i 0 (Fin.init (Fin.cons i α : Fin 1 → Fin d)) = g i
    exact hrootV i _
  have hinit (m : ℕ) (j : Fin d) (α : Fin (m + 1) → Fin d) :
      Fin.init (Fin.cons j α : Fin (m + 2) → Fin d) =
        (Fin.cons j (Fin.init α) : Fin (m + 1) → Fin d) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · rfl
  refine ⟨W, rfl, (fun i => hWone i _), ?_⟩
  intro m hm α j
  cases m with
  | zero =>
      change ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => W 1 (Fin.cons j α) (t, x)) (fun x => f (t, x)) Ω
      rw [hWone]
      exact hfirst j
  | succ m =>
      have hmK : m < K := Nat.lt_of_succ_lt_succ hm
      simpa only [W, Fin.cons_last, hinit] using hweak (α (Fin.last m)) m hmK (Fin.init α) j

end DifferentialGeometry.Analysis.Sobolev.Euclidean
