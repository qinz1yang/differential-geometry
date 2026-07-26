import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateAbs
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateSeries
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuantCover
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Full terminal-slab summation for the late Koch--Lamm potential

The half-open spatial shells form a measurable partition of Euclidean space.
This file first records that geometry and the exact restricted-product-measure
identities needed to sum the shell estimates on the full terminal slab.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- A spatial half-open shell is the preimage of the corresponding radial
half-open interval. -/
theorem klLateShell_eq_pre (x : V) (R : ℝ) (k : ℕ) :
    klLateShell x R k =
      (fun y : V ↦ dist x y) ⁻¹'
        Ico ((k : ℝ) * R) (((k + 1 : ℕ) : ℝ) * R) := by
  ext y
  simp only [klLateShell, mem_diff, Metric.mem_ball, mem_preimage, mem_Ico]
  rw [dist_comm y x]
  constructor
  · rintro ⟨hout, hin⟩
    exact ⟨le_of_not_gt hin, hout⟩
  · rintro ⟨hin, hout⟩
    exact ⟨hout, not_lt_of_ge hin⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Positive-radius half-open shells are pairwise disjoint. -/
theorem klLateShell_disj (x : V) {R : ℝ} (hR : 0 < R) :
    Pairwise (fun i j : ℕ ↦
      Disjoint (klLateShell x R i) (klLateShell x R j)) := by
  have hmono : Monotone (fun k : ℕ ↦ (k : ℝ) * R) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hR.le
  have hI := hmono.pairwise_disjoint_on_Ico_succ
  intro i j hij
  rw [klLateShell_eq_pre, klLateShell_eq_pre]
  simpa using (hI hij).preimage (fun y : V ↦ dist x y)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Positive-radius half-open shells exhaust Euclidean space. -/
theorem klLateShell_union (x : V) {R : ℝ} (hR : 0 < R) :
    ⋃ k : ℕ, klLateShell x R k = Set.univ := by
  let r : ℕ → ℝ := fun k ↦ (k : ℝ) * R
  have hr0 : ∀ k, r ⊥ ≤ r k := by
    intro k
    simpa only [r, Nat.bot_eq_zero, Nat.cast_zero, zero_mul] using
      (mul_nonneg (Nat.cast_nonneg k) hR.le)
  have hr_unbdd : ¬ BddAbove (Set.range r) := by
    intro hr
    rcases hr with ⟨a, ha⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (a / R)
    have hak : a < (k : ℝ) * R := (div_lt_iff₀ hR).mp hk
    exact (not_lt_of_ge (ha ⟨k, rfl⟩)) hak
  have hI : (⋃ k : ℕ, Ico (r k) (r (Order.succ k))) = Ici 0 := by
    simpa only [r, Nat.bot_eq_zero, Nat.cast_zero, zero_mul] using
      (iUnion_Ico_map_succ_eq_Ici hr0 hr_unbdd)
  calc
    (⋃ k : ℕ, klLateShell x R k) =
        (fun y : V ↦ dist x y) ⁻¹'
          (⋃ k : ℕ, Ico (r k) (r (Order.succ k))) := by
      ext y
      simp only [klLateShell_eq_pre, mem_iUnion, mem_preimage, r]
      simp only [Order.succ_eq_add_one]
    _ = (fun y : V ↦ dist x y) ⁻¹' Ici 0 := by rw [hI]
    _ = Set.univ := by
      ext y
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact dist_nonneg

/-- Space-time shell obtained by retaining the whole already-restricted time
factor and selecting one spatial shell. -/
def klLateStShell (x : V) (R : ℝ) (k : ℕ) : Set (ℝ × V) :=
  Set.univ ×ˢ klLateShell x R k

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
/-- Every space-time shell is measurable. -/
theorem klLateSt_mble (x : V) (R : ℝ) (k : ℕ) :
    MeasurableSet (klLateStShell x R k) :=
  MeasurableSet.univ.prod (klLateShell_mble (V := V) x R k)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Positive-radius space-time shells are pairwise disjoint. -/
theorem klLateSt_disj (x : V) {R : ℝ} (hR : 0 < R) :
    Pairwise (fun i j : ℕ ↦
      Disjoint (klLateStShell x R i) (klLateStShell x R j)) := by
  intro i j hij
  exact (klLateShell_disj (V := V) x hR hij).set_prod_right Set.univ Set.univ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Positive-radius space-time shells exhaust the product space. -/
theorem klLateSt_union (x : V) {R : ℝ} (hR : 0 < R) :
    ⋃ k : ℕ, klLateStShell x R k = Set.univ := by
  ext z
  simp only [klLateStShell, mem_iUnion, mem_prod, mem_univ, true_and,
    iff_true]
  have hz : z.2 ∈ ⋃ k : ℕ, klLateShell x R k := by
    rw [klLateShell_union (V := V) x hR]
    exact mem_univ _
  simpa only [mem_iUnion] using hz

omit [Nontrivial V] in
/-- Restricting the full terminal product measure to a spatial set gives the
selected terminal product measure. -/
theorem klTail_restrict (R : ℝ) (S : Set V) :
    (klTailMeasure (V := V) R Set.univ).restrict (Set.univ ×ˢ S) =
      klTailMeasure (V := V) R S := by
  unfold klTailMeasure
  simp only [Measure.restrict_univ]
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_univ]

omit [Nontrivial V] in
/-- The full selected terminal measure is the existing terminal-slab measure. -/
theorem klTerm_eq_tail (R : ℝ) :
    klTermMeasure (V := V) (R ^ 2) =
      klTailMeasure (V := V) R Set.univ := by
  simp only [klTermMeasure, klTailMeasure, Measure.restrict_univ]

/-- The full ordinary terminal-slab potential. -/
def klLateFull0 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z : ℝ × V, klTermKernel (R ^ 2) x z • f z
    ∂klTermMeasure (V := V) (R ^ 2)

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- One parameterized shell is integrable as a set integral against the full
terminal measure. -/
theorem klLateSt_int {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    IntegrableOn (fun z : ℝ × V ↦ klTermKernel (R ^ 2) x z • f z)
      (klLateStShell x R k) (klTailMeasure (V := V) R Set.univ) := by
  rw [IntegrableOn, klLateStShell, klTail_restrict]
  exact (klLateCover_est (V := V) h x hR (Nat.cast_nonneg k) hRT s
    (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)).1

omit [CompleteSpace F] in
/-- One shell's set integral of the integrand norm has the exact summable
Gaussian-polynomial majorant. -/
theorem klLateSt_abs {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V in klLateStShell x R k,
        ‖klTermKernel (R ^ 2) x z • f z‖
        ∂klTailMeasure (V := V) R Set.univ) ≤
      klLateWeight (Module.finrank ℝ V) k *
        (klLateTailC V * (A_q : ℝ)) := by
  rw [klLateStShell, klTail_restrict]
  have habs := klLateShell_abs (V := V) h x hR hRT k s hcard hcover
  calc
    (∫ z : ℝ × V, ‖klTermKernel (R ^ 2) x z • f z‖
        ∂klTailMeasure (V := V) R (klLateShell x R k)) ≤
        (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
          (Real.exp (-((k : ℝ) ^ 2) / 4) *
            (klLateTailC V * (A_q : ℝ))) := habs
    _ = klLateWeight (Module.finrank ℝ V) k *
        (klLateTailC V * (A_q : ℝ)) := by
      unfold klLateWeight
      norm_num [Nat.cast_pow, Nat.cast_mul]
      ring

omit [CompleteSpace F] in
/-- The set integrals of the integrand norm over all shells are summable. -/
theorem klLateAbs_sum {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Summable (fun k : ℕ ↦
      ∫ z : ℝ × V in klLateStShell x R k,
        ‖klTermKernel (R ^ 2) x z • f z‖
        ∂klTailMeasure (V := V) R Set.univ) := by
  let C : ℝ := klLateTailC V * (A_q : ℝ)
  exact Summable.of_nonneg_of_le
    (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    (fun k ↦ by
      simpa only [C] using
        (klLateSt_abs (V := V) h x hR hRT k (s k)
          (hcard k) (hcover k)))
    ((klLateWeight_sum (Module.finrank ℝ V)).mul_right C)

omit [CompleteSpace F] in
/-- The local late-source hypothesis makes the full ordinary terminal-slab
integrand Bochner integrable. -/
theorem klLateFull_int {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ klTermKernel (R ^ 2) x z • f z)
      (klTermMeasure (V := V) (R ^ 2)) := by
  rw [klTerm_eq_tail (V := V) R]
  have hU := integrableOn_iUnion_of_summable_integral_norm
    (fun k ↦ klLateSt_int (V := V) h x hR hRT k (s k)
      (hcover k))
    (klLateAbs_sum (V := V) h x hR hRT s hcard hcover)
  rw [klLateSt_union (V := V) x hR] at hU
  simpa only [IntegrableOn, Measure.restrict_univ] using hU

omit [CompleteSpace F] in
/-- The shell integrals sum to the full ordinary terminal-slab potential. -/
theorem klLateFull_sum {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    HasSum (fun k : ℕ ↦
      klLatePiece0 R f x (klLateShell x R k))
      (klLateFull0 R f x) := by
  let μ := klTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ klTermKernel (R ^ 2) x z • f z
  have hU : IntegrableOn g (⋃ k : ℕ, klLateStShell x R k) μ := by
    rw [klLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ, μ, g,
      ← klTerm_eq_tail (V := V) R] using
      (klLateFull_int (V := V) h x hR hRT s hcard hcover)
  have hsum := hasSum_integral_iUnion
    (f := g) (μ := μ) (fun k ↦ klLateSt_mble (V := V) x R k)
    (klLateSt_disj (V := V) x hR) hU
  convert hsum using 1
  · funext k
    simp only [klLatePiece0, g, μ, klLateStShell]
    rw [klTail_restrict]
  · simp only [klLateFull0, g, μ]
    rw [klLateSt_union (V := V) x hR, Measure.restrict_univ,
      klTerm_eq_tail (V := V) R]

omit [CompleteSpace F] in
/-- The full ordinary terminal-slab potential has the summed scale-free
Koch--Lamm bound. -/
theorem klLateFull_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    ‖klLateFull0 R f x‖ ≤
      klLateSeries (Module.finrank ℝ V) *
        (klLateTailC V * (A_q : ℝ)) := by
  let μ := klTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ klTermKernel (R ^ 2) x z • f z
  let C : ℝ := klLateTailC V * (A_q : ℝ)
  have hint : Integrable g μ := by
    simpa only [μ, g, ← klTerm_eq_tail (V := V) R] using
      (klLateFull_int (V := V) h x hR hRT s hcard hcover)
  have habs := klLateAbs_sum (V := V) h x hR hRT s hcard hcover
  have hmaj : Summable
      (fun k : ℕ ↦ klLateWeight (Module.finrank ℝ V) k * C) :=
    (klLateWeight_sum (Module.finrank ℝ V)).mul_right C
  have hnormU : IntegrableOn (fun z ↦ ‖g z‖)
      (⋃ k : ℕ, klLateStShell x R k) μ := by
    rw [klLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ] using hint.norm
  have hdecomp := integral_iUnion
    (f := fun z ↦ ‖g z‖) (μ := μ)
    (fun k ↦ klLateSt_mble (V := V) x R k)
    (klLateSt_disj (V := V) x hR) hnormU
  rw [klLateSt_union (V := V) x hR, Measure.restrict_univ] at hdecomp
  calc
    ‖klLateFull0 R f x‖ = ‖∫ z, g z ∂μ‖ := by
      simp only [klLateFull0, g, μ]
      rw [klTerm_eq_tail (V := V) R]
    _ ≤ ∫ z, ‖g z‖ ∂μ := norm_integral_le_integral_norm g
    _ = ∑' k : ℕ, ∫ z in klLateStShell x R k, ‖g z‖ ∂μ := hdecomp
    _ ≤ ∑' k : ℕ, klLateWeight (Module.finrank ℝ V) k * C :=
      habs.tsum_le_tsum
        (fun k ↦ by
          simpa only [g, μ, C] using
            (klLateSt_abs (V := V) h x hR hRT k (s k)
              (hcard k) (hcover k))) hmaj
    _ = klLateSeries (Module.finrank ℝ V) * C := by
      rw [tsum_mul_right]
      rfl
    _ = klLateSeries (Module.finrank ℝ V) *
        (klLateTailC V * (A_q : ℝ)) := rfl

omit [CompleteSpace F] in
/-- The full terminal-slab estimate with its Euclidean covering family chosen
canonically from the finite-dimensional quantitative-cover theorem. -/
theorem klLateFull_canon {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klLateFull0 R f x‖ ≤
      klLateSeries (Module.finrank ℝ V) *
        (klLateTailC V * (A_q : ℝ)) := by
  classical
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hR k
  exact klLateFull_norm (V := V) h x hR hRT s hcard hcover

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
