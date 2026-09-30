import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

structure BoundedSmoothSolutionSequence
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) where
  uSeq : ℕ → E → ℝ
  fSeq : ℕ → E → ℝ
  u_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n)
  is_smooth_weak_solution :
    ∀ n, B.IsSmoothWeakSolution (uSeq n) (fSeq n)
  f_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (fSeq n) 2 (volume.restrict S)
  u_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (uSeq n) 2 (volume.restrict S)
  grad_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d,
        MemLp (fun y : E => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))
          2 (volume.restrict S)
  dataBound : ℝ
  data_bound_nn : 0 ≤ dataBound
  data_integrated_bound :
    ∀ {Ω' : Set E}, IsOpen Ω' → IsCompact (closure Ω') →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        (∫ y in Ω',
            ∑ j : Fin d,
              ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure E)) +
        (∫ y in Ω', (uSeq n y) ^ 2 ∂(volume : Measure E)) +
        (∫ y in Ω', (fSeq n y) ^ 2 ∂(volume : Measure E)) ≤
          C * dataBound

namespace BoundedSmoothSolutionSequence

theorem exists_weak_second_partial_integral_le
    {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω}
    (S : BoundedSmoothSolutionSequence B)
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ (S.uSeq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ K * S.dataBound := by
  obtain ⟨C, hC_nn, h_eng⟩ := NirenbergCrossBounds.local_smooth_solution (d := d) B
    hΩ'' hΩ''_compact_closure h_room
  intro i k n
  obtain ⟨g, hg_l2, hg_partial, Ω', hΩ'_open, _, _,
      hΩ'_compact, hC_bound⟩ :=
    h_eng (S.is_smooth_weak_solution n) (S.f_seq_l2_local n) i k
  obtain ⟨D, hD_nn, hD_bound⟩ :=
    S.data_integrated_bound (Ω' := Ω') hΩ'_open hΩ'_compact
  refine ⟨g, hg_l2, hg_partial, C * D, mul_nonneg hC_nn hD_nn, ?_⟩
  calc
    ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ C * _ := hC_bound
    _ ≤ C * (D * S.dataBound) :=
      mul_le_mul_of_nonneg_left (hD_bound n) hC_nn
    _ = (C * D) * S.dataBound := by ring

end BoundedSmoothSolutionSequence

end DifferentialGeometry.Analysis.Sobolev
