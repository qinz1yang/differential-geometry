import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_of_weak_partial_tree
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (volume.restrict Ω))
    (hweak : ∀ n α i,
      DeGiorgi.HasWeakPartialDeriv i (u (n + 1) (Fin.cons i α)) (u n α) Ω) :
    ∀ k, MemWkp k p (u 0 (fun i : Fin 0 => Fin.elim0 i)) Ω := by
  have hnode : ∀ k n α, MemWkp k p (u n α) Ω := by
    intro k
    induction k with
    | zero =>
        intro n α
        exact hLp n α
    | succ k ih =>
        intro n α
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ (hLp n α)
        · intro i
          exact ih (n + 1) (Fin.cons i α)
        · intro i
          exact hweak n α i
  intro k
  exact hnode k 0 (fun i : Fin 0 => Fin.elim0 i)

theorem ae_memWkp_of_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    ∀ k, ∀ᵐ t ∂μ,
      MemWkp k p (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω := by
  have hslices {f : Z × E → ℝ}
      (hf : MemLp f p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) p (volume.restrict Ω) := by
    by_cases hptop : p = ⊤
    · subst p
      exact hf.prodMk_left_top
    · exact hf.prodMk_left hptop
  have hnode : ∀ k n α, ∀ᵐ t ∂μ,
      MemWkp k p (fun x => u n α (t, x)) Ω := by
    intro k
    induction k with
    | zero =>
        intro n α
        exact hslices (hLp n α)
    | succ k ih =>
        intro n α
        have hchild : ∀ i : Fin d, ∀ᵐ t ∂μ,
            MemWkp k p
              (fun x => u (n + 1) (Fin.cons i α) (t, x)) Ω := by
          intro i
          exact ih (n + 1) (Fin.cons i α)
        have hchild' := ae_all_iff.mpr hchild
        have hderiv : ∀ i : Fin d, ∀ᵐ t ∂μ,
            DeGiorgi.HasWeakPartialDeriv i
              (fun x => u (n + 1) (Fin.cons i α) (t, x))
              (fun x => u n α (t, x)) Ω :=
          fun i => hweak n α i
        have hderiv' := ae_all_iff.mpr hderiv
        have hbase := hslices (hLp n α)
        filter_upwards [hbase, hchild', hderiv'] with t ht htc htd
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ ht
          (g := fun i x => u (n + 1) (Fin.cons i α) (t, x))
        · exact htc
        · exact htd
  intro k
  exact hnode k 0 (fun i : Fin 0 => Fin.elim0 i)

theorem ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n ≤ K, ∀ α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n < K, ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    (∀ᵐ t ∂μ,
      MemWkp K p
        (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω) ∧
      MemLp
        (fun t =>
          (iteratedWeakSobolevNorm K p
            (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω).toReal) p μ := by
  have hnode : ∀ k n α, n + k ≤ K → (∀ᵐ t ∂μ,
      MemWkp k p (fun x => u n α (t, x)) Ω) ∧
      MemLp
        (fun t => (iteratedWeakSobolevNorm k p
          (fun x => u n α (t, x)) Ω).toReal) p μ := by
    intro k
    induction k with
    | zero =>
        intro n α hn
        have hslice := (hLp n (by omega) α).prodMk_left hpt
        refine ⟨hslice, ?_⟩
        simpa only [wkpNorm_zero] using (hLp n (by omega) α).eLpNorm_toReal hpt
    | succ k ih =>
        intro n α hn
        let V : Z × E → ℝ := u n α
        let W : Fin d → Z × E → ℝ := fun i => u (n + 1) (Fin.cons i α)
        have hW : ∀ i, ∀ᵐ t ∂μ,
            MemWkp k p (fun x => W i (t, x)) Ω := by
          intro i
          exact (ih (n + 1) (Fin.cons i α) (by omega)).1
        have hWnorm : ∀ i, MemLp
            (fun t => (iteratedWeakSobolevNorm k p
              (fun x => W i (t, x)) Ω).toReal) p μ := by
          intro i
          exact (ih (n + 1) (Fin.cons i α) (by omega)).2
        have hstep := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
          hΩ hp hpt (V := V) (W := W) (hLp n (by omega) α) hW hWnorm
          (hweak n (by omega) α)
        simpa only [V, W] using hstep
  exact hnode K 0 (fun i : Fin 0 => Fin.elim0 i) (by omega)

theorem ae_memWkp_and_memLp_wkpNorm_of_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    ∀ k, (∀ᵐ t ∂μ,
      MemWkp k p
        (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω) ∧
      MemLp
        (fun t =>
          (iteratedWeakSobolevNorm k p
            (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω).toReal) p μ := by
  intro k
  exact ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree hp hpt hΩ k u
    (fun n _ => hLp n) (fun n _ => hweak n)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
