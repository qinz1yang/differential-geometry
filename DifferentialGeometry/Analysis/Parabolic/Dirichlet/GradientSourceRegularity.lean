import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem exists_lp_two_term_source_spatial_derivative
    {Z : Type*} [MeasurableSpace Z] {d : ℕ}
    {μ : Measure Z} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (F Y₁ Y₂ : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DY₁ DY₂ : Fin d → Lp ℝ 2
      (μ.prod (volume.restrict Ω)))
    (A₁ A₂ : Z × EuclideanSpace ℝ (Fin d) → ℝ)
    (hA₁ : MemLp A₁ ∞ (μ.prod (volume.restrict Ω)))
    (hA₂ : MemLp A₂ ∞ (μ.prod (volume.restrict Ω)))
    (hDA₁ : ∀ k, MemLp (fun p => fderiv ℝ (fun x => A₁ (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hDA₂ : ∀ k, MemLp (fun p => fderiv ℝ (fun x => A₂ (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth₁ : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => A₁ (t, x)) Ω)
    (hAsmooth₂ : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => A₂ (t, x)) Ω)
    (hYweak₁ : ∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DY₁ k (t, x)) (fun x => Y₁ (t, x)) Ω)
    (hYweak₂ : ∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DY₂ k (t, x)) (fun x => Y₂ (t, x)) Ω)
    (hF : F =ᵐ[μ.prod (volume.restrict Ω)] fun p =>
      A₁ p * Y₁ p + A₂ p * Y₂ p) :
    ∃ DF : Fin d → Lp ℝ 2
        (μ.prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => DF k (t, x)) (fun x => F (t, x)) Ω) ∧
      (∀ k, DF k =ᵐ[μ.prod (volume.restrict Ω)] fun p =>
        A₁ p * DY₁ k p +
          fderiv ℝ (fun x => A₁ (p.1, x)) p.2
            (EuclideanSpace.single k 1) * Y₁ p +
          (A₂ p * DY₂ k p +
            fderiv ℝ (fun x => A₂ (p.1, x)) p.2
              (EuclideanSpace.single k 1) * Y₂ p)) := by
  classical
  let ι := Bool
  let Y : ι → Lp ℝ 2 (μ.prod (volume.restrict Ω)) := fun b =>
    if b then Y₁ else Y₂
  let DY : ι → Fin d →
      Lp ℝ 2 (μ.prod (volume.restrict Ω)) := fun b =>
    if b then DY₁ else DY₂
  let A : ι → Z × EuclideanSpace ℝ (Fin d) → ℝ := fun b => if b then A₁ else A₂
  have hA : ∀ b, MemLp (A b) ∞ (μ.prod (volume.restrict Ω)) := by
    intro b
    cases b
    · simpa [A] using hA₂
    · simpa [A] using hA₁
  have hDA : ∀ b k, MemLp (fun p => fderiv ℝ (fun x => A b (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)) := by
    intro b k
    cases b
    · simpa [A] using hDA₂ k
    · simpa [A] using hDA₁ k
  have hAsmooth : ∀ b, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => A b (t, x)) Ω := by
    intro b
    cases b
    · simpa [A] using hAsmooth₂
    · simpa [A] using hAsmooth₁
  have hYweak : ∀ b k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DY b k (t, x)) (fun x => Y b (t, x)) Ω := by
    intro b k
    cases b
    · simpa [DY, Y] using hYweak₂ k
    · simpa [DY, Y] using hYweak₁ k
  have hF' : F =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ b, A b p * Y b p := by
    filter_upwards [hF] with p hp
    dsimp [ι]
    simpa [Fintype.sum_bool, A, Y, Bool.false_eq_true, add_comm] using hp
  obtain ⟨DF, hDF, hformula, _⟩ :=
    exists_lp_spatial_weak_partials_of_ae_eq_finite_sum hΩ F Y DY A
      hA hDA hAsmooth hYweak hF'
  refine ⟨DF, hDF, ?_⟩
  intro k
  filter_upwards [hformula k] with p hp
  rw [Fintype.sum_bool] at hp
  simp only [A, Y, DY, Bool.false_eq_true, ↓reduceIte] at hp
  simpa [add_comm, add_left_comm, add_assoc] using hp

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
