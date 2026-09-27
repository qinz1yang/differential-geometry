import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Weighted
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

theorem iterate_ds_eq_weightedDeriv (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (f : ℝ → ℝ → ℝ) (k : ℕ) (t : ℝ) :
    (fun x => (c.ds g)^[k] f x t) =
      (DifferentialGeometry.Analysis.weightedDeriv (fun x => (c.speed g x t)⁻¹))^[k]
        (fun x => f x t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    funext x
    simp only [Function.iterate_succ_apply', ds, DifferentialGeometry.Analysis.weightedDeriv]
    rw [ih]

theorem exists_iteratedDeriv_bound_of_iterate_ds (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (q : ℝ → ℝ → ℝ) (S : Set (ℝ × ℝ)) (n : ℕ)
    (hv : ∀ p ∈ S, ContDiffAt ℝ ((n - 1 : ℕ) : ℕ∞ω) (fun y => c.speed g y p.2) p.1)
    (hq : ∀ p ∈ S, ContDiffAt ℝ n (fun y => q y p.2) p.1)
    (hvn : ∀ p ∈ S, c.speed g p.1 p.2 ≠ 0)
    (hvb : ∀ i < n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      ‖iteratedDeriv i (fun y => c.speed g y p.2) p.1‖ ≤ C)
    (hqb : ∀ k ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ‖(c.ds g)^[k] q p.1 p.2‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ‖iteratedDeriv n (fun y => q y p.2) p.1‖ ≤ C := by
  have hb := DifferentialGeometry.Analysis.exists_iteratedDeriv_bound_of_weightedDeriv n
    (fun p : S => p.val.1) (fun p : S => fun y => c.speed g y p.val.2)
    (fun p : S => fun y => q y p.val.2) (fun p => hv p.val p.property)
    (fun p => hq p.val p.property) (fun p => hvn p.val p.property)
    (fun i hi => by
      obtain ⟨C, hC, hb⟩ := hvb i hi
      exact ⟨C, hC, fun p => hb p.val p.property⟩)
    (fun k hk => by
      obtain ⟨C, hC, hb⟩ := hqb k hk
      refine ⟨C, hC, fun p => ?_⟩
      rw [← c.iterate_ds_eq_weightedDeriv g q k p.val.2]
      exact hb p.val p.property)
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, fun p hp => hb ⟨p, hp⟩⟩

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
