import DifferentialGeometry.Geometry.Curvature.Surface.FlatTorusTranslation

/-!
# Consumers of FT2

* the shift-segment producer in the periodic-cover form (any onto smooth local diffeomorphism
  `E → M` with lattice fibres, e.g. LFR22's flat covers), and the translation isometries;
* the trivial quotient `ℂ → ℂ`: segments of the Euclidean plane are shifted by translations.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The τ-producer for a flat surface with a periodic cover with lattice fibres. -/
theorem exists_isometryEquiv_shift_segment_of_periodic_cover (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    {cov : E → M} (hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov) (hsurj : Surjective cov)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (hper₁ : ∀ y, cov (y + v₁) = cov y)
    (hper₂ : ∀ y, cov (y + v₂) = cov y)
    (hfib : ∀ y y', cov y = cov y' → ∃ n₁ n₂ : ℤ, y' = y + (n₁ • v₁ + n₂ • v₂))
    (hflat : ∀ x v w, k.sectionalCurvature x v w = 0)
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|) :
    ∃ τ : M ≃ᵢ M, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) := by
  obtain ⟨Ψ, Λ, hΨs, hinv, hfibΨ, hle, hreal⟩ :=
    exists_developing_cover_of_flat hE k hn hnorm hcov hsurj hli hper₁ hper₂ hfib hflat
  exact DifferentialGeometry.Analysis.exists_isometryEquiv_shift_segment_of_quotient hΨs hinv
    hfibΨ hle hreal hs hγ

/-- On a flat torus every translation of the developed plane descends to an isometry: there are
isometries `τ` moving any point to any other point (homogeneity). -/
theorem exists_isometryEquiv_apply_eq_of_flat_torus (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hflat : ∀ x v w, k.sectionalCurvature x v w = 0) (x x' : M) :
    ∃ τ : M ≃ᵢ M, τ x = x' := by
  obtain ⟨cov, v₁, v₂, hcov, hsurj, hli, hper₁, hper₂, hfib⟩ :=
    exists_periodic_cover_of_diffeomorph_addCircle_prod hE Φ
  obtain ⟨Ψ, Λ, hΨs, hinv, hfibΨ, hle, hreal⟩ :=
    exists_developing_cover_of_flat hE k hn hnorm hcov hsurj hli hper₁ hper₂ hfib hflat
  obtain ⟨w, rfl⟩ := hΨs x
  obtain ⟨w', rfl⟩ := hΨs x'
  obtain ⟨τ, hτ⟩ := DifferentialGeometry.Analysis.exists_isometryEquiv_translate hΨs hinv hfibΨ
    hle hreal (w' - w)
  exact ⟨τ, by rw [hτ, add_sub_cancel]⟩

end Bundle.ContMDiffRiemannianMetric

namespace DifferentialGeometry.Analysis

/-- The trivial quotient: a segment of the Euclidean plane is shifted along itself by a
translation. -/
theorem complex_exists_isometryEquiv_shift_segment {γ : ℝ → ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Set.Icc 0 (2 * s), ∀ t' ∈ Set.Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|) :
    ∃ τ : ℂ ≃ᵢ ℂ, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) :=
  exists_isometryEquiv_shift_segment_of_quotient (Ψ := id) (Λ := ⊥) Function.surjective_id
    (fun w l hl => by rw [(AddSubgroup.mem_bot).mp hl, add_zero])
    (fun w w' h => by rw [show w' = w from h.symm, sub_self]; exact zero_mem _)
    (fun _ _ => le_rfl) (fun _ w' => ⟨w', rfl, rfl⟩) hs hγ

end DifferentialGeometry.Analysis
