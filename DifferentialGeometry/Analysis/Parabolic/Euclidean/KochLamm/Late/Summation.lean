import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.AbsoluteBounds
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Series
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Covering.Quantitative
import Mathlib.Order.SuccPred.IntervalSucc

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
theorem kochLammLateShell_eq_pre (x : V) (R : ℝ) (k : ℕ) :
    kochLammLateShell x R k =
      (fun y : V ↦ dist x y) ⁻¹'
        Ico ((k : ℝ) * R) (((k + 1 : ℕ) : ℝ) * R) := by
  ext y
  simp only [kochLammLateShell, mem_sdiff, Metric.mem_ball, mem_preimage, mem_Ico]
  rw [dist_comm y x]
  constructor
  · rintro ⟨hout, hin⟩
    exact ⟨le_of_not_gt hin, hout⟩
  · rintro ⟨hin, hout⟩
    exact ⟨hout, not_lt_of_ge hin⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateShell_disj (x : V) {R : ℝ} (hR : 0 < R) :
    Pairwise (fun i j : ℕ ↦
      Disjoint (kochLammLateShell x R i) (kochLammLateShell x R j)) := by
  have hmono : Monotone (fun k : ℕ ↦ (k : ℝ) * R) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hR.le
  have hI := hmono.pairwise_disjoint_on_Ico_succ
  intro i j hij
  rw [kochLammLateShell_eq_pre, kochLammLateShell_eq_pre]
  simpa using (hI hij).preimage (fun y : V ↦ dist x y)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateShell_union (x : V) {R : ℝ} (hR : 0 < R) :
    ⋃ k : ℕ, kochLammLateShell x R k = Set.univ := by
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
    (⋃ k : ℕ, kochLammLateShell x R k) =
        (fun y : V ↦ dist x y) ⁻¹'
          (⋃ k : ℕ, Ico (r k) (r (Order.succ k))) := by
      ext y
      simp only [kochLammLateShell_eq_pre, mem_iUnion, mem_preimage, r]
      simp only [Order.succ_eq_add_one]
    _ = (fun y : V ↦ dist x y) ⁻¹' Ici 0 := by rw [hI]
    _ = Set.univ := by
      ext y
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact dist_nonneg

def kochLammLateStShell (x : V) (R : ℝ) (k : ℕ) : Set (ℝ × V) :=
  Set.univ ×ˢ kochLammLateShell x R k

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem kochLammLateSt_mble (x : V) (R : ℝ) (k : ℕ) :
    MeasurableSet (kochLammLateStShell x R k) :=
  MeasurableSet.univ.prod (kochLammLateShell_mble (V := V) x R k)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateSt_disj (x : V) {R : ℝ} (hR : 0 < R) :
    Pairwise (fun i j : ℕ ↦
      Disjoint (kochLammLateStShell x R i) (kochLammLateStShell x R j)) := by
  intro i j hij
  exact (kochLammLateShell_disj (V := V) x hR hij).set_prod_right Set.univ Set.univ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateSt_union (x : V) {R : ℝ} (hR : 0 < R) :
    ⋃ k : ℕ, kochLammLateStShell x R k = Set.univ := by
  ext z
  simp only [kochLammLateStShell, mem_iUnion, mem_prod, mem_univ, true_and,
    iff_true]
  have hz : z.2 ∈ ⋃ k : ℕ, kochLammLateShell x R k := by
    rw [kochLammLateShell_union (V := V) x hR]
    exact mem_univ _
  simpa only [mem_iUnion] using hz

omit [Nontrivial V] in
theorem kochLammTail_restrict (R : ℝ) (S : Set V) :
    (kochLammTailMeasure (V := V) R Set.univ).restrict (Set.univ ×ˢ S) =
      kochLammTailMeasure (V := V) R S := by
  unfold kochLammTailMeasure
  simp only [Measure.restrict_univ]
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_univ]

omit [Nontrivial V] in
theorem kochLammTerm_eq_tail (R : ℝ) :
    kochLammTermMeasure (V := V) (R ^ 2) =
      kochLammTailMeasure (V := V) R Set.univ := by
  simp only [kochLammTermMeasure, kochLammTailMeasure, Measure.restrict_univ]

def kochLammLatePotential {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z : ℝ × V, kochLammTermKernel (R ^ 2) x z • f z
    ∂kochLammTermMeasure (V := V) (R ^ 2)

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem kochLammLateSt_int {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    IntegrableOn (fun z : ℝ × V ↦ kochLammTermKernel (R ^ 2) x z • f z)
      (kochLammLateStShell x R k) (kochLammTailMeasure (V := V) R Set.univ) := by
  rw [IntegrableOn, kochLammLateStShell, kochLammTail_restrict]
  exact (kochLammLateCover_est (V := V) h x hR (Nat.cast_nonneg k) hRT s
    (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)).1

omit [CompleteSpace F] in
theorem kochLammLateSt_abs {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    (∫ z : ℝ × V in kochLammLateStShell x R k,
        ‖kochLammTermKernel (R ^ 2) x z • f z‖
        ∂kochLammTailMeasure (V := V) R Set.univ) ≤
      kochLammLateWeight (Module.finrank ℝ V) k *
        (kochLammLateTailC V * (A_q : ℝ)) := by
  rw [kochLammLateStShell, kochLammTail_restrict]
  have habs := kochLammLateShell_abs (V := V) h x hR hRT k s hcard hcover
  calc
    (∫ z : ℝ × V, ‖kochLammTermKernel (R ^ 2) x z • f z‖
        ∂kochLammTailMeasure (V := V) R (kochLammLateShell x R k)) ≤
        (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
          (Real.exp (-((k : ℝ) ^ 2) / 4) *
            (kochLammLateTailC V * (A_q : ℝ))) := habs
    _ = kochLammLateWeight (Module.finrank ℝ V) k *
        (kochLammLateTailC V * (A_q : ℝ)) := by
      unfold kochLammLateWeight
      norm_num [Nat.cast_pow, Nat.cast_mul]
      ring

omit [CompleteSpace F] in
theorem kochLammLateAbs_sum {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Summable (fun k : ℕ ↦
      ∫ z : ℝ × V in kochLammLateStShell x R k,
        ‖kochLammTermKernel (R ^ 2) x z • f z‖
        ∂kochLammTailMeasure (V := V) R Set.univ) := by
  let C : ℝ := kochLammLateTailC V * (A_q : ℝ)
  exact Summable.of_nonneg_of_le
    (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    (fun k ↦ by
      simpa only [C] using
        (kochLammLateSt_abs (V := V) h x hR hRT k (s k)
          (hcard k) (hcover k)))
    ((kochLammLateWeight_sum (Module.finrank ℝ V)).mul_right C)

omit [CompleteSpace F] in
theorem kochLammTermKernel_smul_integrable {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ kochLammTermKernel (R ^ 2) x z • f z)
      (kochLammTermMeasure (V := V) (R ^ 2)) := by
  rw [kochLammTerm_eq_tail (V := V) R]
  have hU := integrableOn_iUnion_of_summable_integral_norm
    (fun k ↦ kochLammLateSt_int (V := V) h x hR hRT k (s k)
      (hcover k))
    (kochLammLateAbs_sum (V := V) h x hR hRT s hcard hcover)
  rw [kochLammLateSt_union (V := V) x hR] at hU
  simpa only [IntegrableOn, Measure.restrict_univ] using hU

omit [CompleteSpace F] in
theorem hasSum_klLatePiece_klLatePotential {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    HasSum (fun k : ℕ ↦
      kochLammLatePiece0 R f x (kochLammLateShell x R k))
      (kochLammLatePotential R f x) := by
  let μ := kochLammTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ kochLammTermKernel (R ^ 2) x z • f z
  have hU : IntegrableOn g (⋃ k : ℕ, kochLammLateStShell x R k) μ := by
    rw [kochLammLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ, μ, g,
      ← kochLammTerm_eq_tail (V := V) R] using
      (kochLammTermKernel_smul_integrable (V := V) h x hR hRT s hcard hcover)
  have hsum := hasSum_integral_iUnion
    (f := g) (μ := μ) (fun k ↦ kochLammLateSt_mble (V := V) x R k)
    (kochLammLateSt_disj (V := V) x hR) hU
  convert hsum using 1
  · funext k
    simp only [kochLammLatePiece0, g, μ, kochLammLateStShell]
    rw [kochLammTail_restrict]
  · simp only [kochLammLatePotential, g, μ]
    rw [kochLammLateSt_union (V := V) x hR, Measure.restrict_univ,
      kochLammTerm_eq_tail (V := V) R]

omit [CompleteSpace F] in
theorem norm_klLatePotential_le_of_shellCover {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (s : ℕ → Finset V)
    (hcard : ∀ k, (s k).card ≤
      (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : ∀ k, Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s k, Metric.ball c R) :
    ‖kochLammLatePotential R f x‖ ≤
      kochLammLateSeries (Module.finrank ℝ V) *
        (kochLammLateTailC V * (A_q : ℝ)) := by
  let μ := kochLammTailMeasure (V := V) R Set.univ
  let g : ℝ × V → F := fun z ↦ kochLammTermKernel (R ^ 2) x z • f z
  let C : ℝ := kochLammLateTailC V * (A_q : ℝ)
  have hint : Integrable g μ := by
    simpa only [μ, g, ← kochLammTerm_eq_tail (V := V) R] using
      (kochLammTermKernel_smul_integrable (V := V) h x hR hRT s hcard hcover)
  have habs := kochLammLateAbs_sum (V := V) h x hR hRT s hcard hcover
  have hmaj : Summable
      (fun k : ℕ ↦ kochLammLateWeight (Module.finrank ℝ V) k * C) :=
    (kochLammLateWeight_sum (Module.finrank ℝ V)).mul_right C
  have hnormU : IntegrableOn (fun z ↦ ‖g z‖)
      (⋃ k : ℕ, kochLammLateStShell x R k) μ := by
    rw [kochLammLateSt_union (V := V) x hR]
    simpa only [IntegrableOn, Measure.restrict_univ] using hint.norm
  have hdecomp := integral_iUnion
    (f := fun z ↦ ‖g z‖) (μ := μ)
    (fun k ↦ kochLammLateSt_mble (V := V) x R k)
    (kochLammLateSt_disj (V := V) x hR) hnormU
  rw [kochLammLateSt_union (V := V) x hR, Measure.restrict_univ] at hdecomp
  calc
    ‖kochLammLatePotential R f x‖ = ‖∫ z, g z ∂μ‖ := by
      simp only [kochLammLatePotential, g, μ]
      rw [kochLammTerm_eq_tail (V := V) R]
    _ ≤ ∫ z, ‖g z‖ ∂μ := norm_integral_le_integral_norm g
    _ = ∑' k : ℕ, ∫ z in kochLammLateStShell x R k, ‖g z‖ ∂μ := hdecomp
    _ ≤ ∑' k : ℕ, kochLammLateWeight (Module.finrank ℝ V) k * C :=
      habs.tsum_le_tsum
        (fun k ↦ by
          simpa only [g, μ, C] using
            (kochLammLateSt_abs (V := V) h x hR hRT k (s k)
              (hcard k) (hcover k))) hmaj
    _ = kochLammLateSeries (Module.finrank ℝ V) * C := by
      rw [tsum_mul_right]
      rfl
    _ = kochLammLateSeries (Module.finrank ℝ V) *
        (kochLammLateTailC V * (A_q : ℝ)) := rfl

omit [CompleteSpace F] in
theorem norm_klLatePotential_le {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammLatePotential R f x‖ ≤
      kochLammLateSeries (Module.finrank ℝ V) *
        (kochLammLateTailC V * (A_q : ℝ)) := by
  classical
  choose s hcard hcover using
    fun k : ℕ ↦ exists_shell_cover (V := V) x hR k
  exact norm_klLatePotential_le_of_shellCover (V := V) h x hR hRT s hcard hcover

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
