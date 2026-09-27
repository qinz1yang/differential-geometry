import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import Mathlib.Analysis.Normed.Group.Bounded

section

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_bound_of_finite_continuous_family
    {X I : Type*} [TopologicalSpace X] [Finite I]
    {K : Set X} (hK : IsCompact K) (f : I → X → ℝ)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i x, x ∈ K → |f i x| ≤ C := by
  classical
  let _ := Fintype.ofFinite I
  have hfc : ContinuousOn (fun x => fun i => f i x) K := continuousOn_pi.mpr hf
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro i x hx
  exact (norm_le_pi_norm (fun i => f i x) i).trans
    ((hC x hx).trans (le_max_left _ _))

theorem exists_scalar_elliptic_coefficient_bounds_on_compact
    {d : ℕ} {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {K U : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (hb : ∀ j, ContDiffOn ℝ 1 (fun x => b x j) U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K,
      (∀ i j, |a x i j| ≤ C) ∧
      (∀ k i j, |fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single k 1)| ≤ C) ∧
      (∀ j, |b x j| ≤ C) ∧
      (∀ k j, |fderiv ℝ (fun y => b y j) x (EuclideanSpace.single k 1)| ≤ C) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_bound_of_finite_continuous_family hK
    (fun ij : Fin d × Fin d => fun x => a x ij.1 ij.2)
    (fun ij => (ha ij.1 ij.2).continuousOn.mono hKU)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_of_finite_continuous_family hK
    (fun kij : Fin d × Fin d × Fin d => fun x =>
      fderiv ℝ (fun y => a y kij.2.1 kij.2.2) x (EuclideanSpace.single kij.1 1))
    (fun kij => (((ha kij.2.1 kij.2.2).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      continuousOn_const).mono hKU)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_of_finite_continuous_family hK
    (fun j : Fin d => fun x => b x j)
    (fun j => (hb j).continuousOn.mono hKU)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_bound_of_finite_continuous_family hK
    (fun kj : Fin d × Fin d => fun x =>
      fderiv ℝ (fun y => b y kj.2) x (EuclideanSpace.single kj.1 1))
    (fun kj => (((hb kj.2).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      continuousOn_const).mono hKU)
  refine ⟨C₀ + C₁ + C₂ + C₃, by linarith, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact (h₀ (i, j) x hx).trans (by linarith)
  · intro k i j
    exact (h₁ (k, i, j) x hx).trans (by linarith)
  · intro j
    exact (h₂ j x hx).trans (by linarith)
  · intro k j
    exact (h₃ (k, j) x hx).trans (by linarith)

theorem contDiff_divergence_coefficient
    {d : ℕ} {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {n : ℕ∞ω} (ha : ∀ i j, ContDiff ℝ (n + 1) (fun x => a x i j)) (j : Fin d) :
    ContDiff ℝ n (fun x => ∑ i,
      fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1)) := by
  exact ContDiff.sum fun i _ => ((ha i j).fderiv_right le_rfl).clm_apply contDiff_const

theorem exists_smooth_elliptic_coefficient_drift_bounds_on_compact
    {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (B : Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm d Ω)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    (∀ j : Fin d, ContDiff ℝ ∞ (fun x => ∑ i,
      fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1))) ∧
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K,
      (∀ i j, |B.a x i j| ≤ C) ∧
      (∀ k i j, |fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single k 1)| ≤ C) ∧
      (∀ j, |∑ i, fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)| ≤ C) ∧
      (∀ k j, |fderiv ℝ (fun z => ∑ i,
        fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single k 1)| ≤ C) := by
  have hb : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => ∑ i,
      fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)) := by
    intro j
    apply contDiff_divergence_coefficient (n := ∞) _ j
    intro i l
    simpa using B.smooth_a i l
  refine ⟨hb, ?_⟩
  exact exists_scalar_elliptic_coefficient_bounds_on_compact hK isOpen_univ (subset_univ _)
    (fun i j => ((B.smooth_a i j).of_le (by norm_cast)).contDiffOn)
    (fun j => ((hb j).of_le (by norm_cast)).contDiffOn)

end DifferentialGeometry.Analysis

end

end
