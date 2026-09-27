import DifferentialGeometry.Topology.Planar.CurveRounding
import DifferentialGeometry.Topology.Embedding.PeriodicCurveIsotopy

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Planar

theorem exists_inscribed_rounding_ambient_isotopy_forall_width
    {γ : ℝ → Schoenflies.Plane} (hγ : ContDiff ℝ ∞ γ)
    (hne : ∀ t, deriv γ t ≠ 0) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (P : Schoenflies.PrePolygon m),
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = γ ((i.val : ℝ) / (m + 3))) ∧
      ∀ σ ∈ Ioo (0 : ℝ) ((1 / (m + 3 : ℝ)) / 2),
      ∃ Φ : ℝ → (Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane),
      ContDiff ℝ ∞ (fun q : ℝ × Schoenflies.Plane => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Schoenflies.Plane => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Schoenflies.Plane) Schoenflies.Plane ∞ ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
        let h := 1 / (m + 3 : ℝ)
        let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h σ
          (fun k : ℤ => γ (k * h))
        Φ τ (γ t) = AffineMap.lineMap (γ t) (g t) τ ∧
          (Φ τ).symm (AffineMap.lineMap (γ t) (g t) τ) = γ t) ∧
      ∃ S : Set Schoenflies.Plane, IsCompact S ∧ ∀ τ : ℝ,
        EqOn (Φ τ) id Sᶜ ∧ EqOn (Φ τ).symm id Sᶜ := by
  obtain ⟨m, P, hmesh, hp, hround⟩ :=
    exists_inscribed_rounding_injOn_interpolation_forall_width hγ hne hperiod hinj hε
  refine ⟨m, P, hmesh, hp, ?_⟩
  intro σ hσ
  obtain ⟨hs, hper, hslice⟩ := hround σ hσ
  let h : ℝ := 1 / (m + 3 : ℝ)
  let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h σ
    (fun k : ℤ => γ (k * h))
  let F := fun q : ℝ × ℝ => AffineMap.lineMap (γ q.2) (g q.2) q.1
  obtain ⟨Φ, hΦ, hΦi, hzero, hmatch, S, hS, _, hfix⟩ :=
    PeriodicCurve.exists_compactly_supported_ambient_isotopy
      (F := F) hs hper (fun τ hτ => (hslice τ hτ).1)
      (fun τ hτ => (hslice τ hτ).2) isOpen_univ (subset_univ _)
  refine ⟨Φ, hΦ, hΦi, hzero, ?_, S, hS, hfix⟩
  intro τ hτ t
  simpa only [F, AffineMap.lineMap_apply_zero] using hmatch τ hτ t

theorem exists_inscribed_rounding_ambient_isotopy
    {γ : ℝ → Schoenflies.Plane} (hγ : ContDiff ℝ ∞ γ)
    (hne : ∀ t, deriv γ t ≠ 0) (hperiod : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (P : Schoenflies.PrePolygon m)
      (Φ : ℝ → (Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)),
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = γ ((i.val : ℝ) / (m + 3))) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Schoenflies.Plane => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Schoenflies.Plane => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, Schoenflies.Plane) Schoenflies.Plane ∞ ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
        let h := 1 / (m + 3 : ℝ)
        let g := DifferentialGeometry.Analysis.roundedPolygonalCurve h (h / 4)
          (fun k : ℤ => γ (k * h))
        Φ τ (γ t) = AffineMap.lineMap (γ t) (g t) τ ∧
          (Φ τ).symm (AffineMap.lineMap (γ t) (g t) τ) = γ t) ∧
      ∃ S : Set Schoenflies.Plane, IsCompact S ∧ ∀ τ : ℝ,
        EqOn (Φ τ) id Sᶜ ∧ EqOn (Φ τ).symm id Sᶜ := by
  obtain ⟨m, P, hm, hp, hround⟩ :=
    exists_inscribed_rounding_ambient_isotopy_forall_width hγ hne hperiod hinj hε
  have hh : 0 < 1 / (m + 3 : ℝ) := by positivity
  obtain ⟨Φ, hΦ⟩ := hround ((1 / (m + 3 : ℝ)) / 4) ⟨by positivity, by linarith⟩
  exact ⟨m, P, Φ, hm, hp, hΦ⟩

theorem exists_inscribed_rounding_diffeomorph_forall_width
    {e : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (he : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (P : Schoenflies.PrePolygon m),
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = e (((i.val : ℝ) / (m + 3) : ℝ) : AddCircle (1 : ℝ))) ∧
      ∀ σ ∈ Ioo (0 : ℝ) ((1 / (m + 3 : ℝ)) / 2),
      ∃ φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      (∀ t : ℝ,
        let h := 1 / (m + 3 : ℝ)
        φ (e (t : AddCircle (1 : ℝ))) =
          DifferentialGeometry.Analysis.roundedPolygonalCurve h σ
            (fun k : ℤ => e ((k * h : ℝ) : AddCircle (1 : ℝ))) t) ∧
      ∃ S : Set Schoenflies.Plane, IsCompact S ∧
        EqOn φ id Sᶜ ∧ EqOn φ.symm id Sᶜ := by
  let γ : ℝ → Schoenflies.Plane := fun t => e (t : AddCircle (1 : ℝ))
  have hγ : ContDiff ℝ ∞ γ := (he.contMDiff.comp AddCircle.contMDiff_coe).contDiff
  have hperiod : Function.Periodic γ 1 := by
    intro t
    simp only [γ, QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]
  have hinj : InjOn γ (Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (p := (1 : ℝ)) (by simpa using hx) (by simpa using hy)).mp
    exact he.isEmbedding.injective hxy
  obtain ⟨m, P, hm, hp, hround⟩ :=
    exists_inscribed_rounding_ambient_isotopy_forall_width hγ
      (fun t => AddCircle.deriv_comp_coe_ne_zero he t) hperiod hinj hε
  refine ⟨m, P, hm, hp, ?_⟩
  intro σ hσ
  obtain ⟨Φ, _, _, _, hmatch, S, hS, hfix⟩ := hround σ hσ
  refine ⟨Φ 1, ?_, S, hS, (hfix 1).1, (hfix 1).2⟩
  intro t
  simpa only [AffineMap.lineMap_apply_one] using (hmatch 1 ⟨by norm_num, le_rfl⟩ t).1

theorem exists_inscribed_rounding_diffeomorph
    {e : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (he : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (P : Schoenflies.PrePolygon m)
      (φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane),
      1 / (m + 3 : ℝ) < ε ∧
      (∀ i, P.vertex i = e (((i.val : ℝ) / (m + 3) : ℝ) : AddCircle (1 : ℝ))) ∧
      (∀ t : ℝ,
        let h := 1 / (m + 3 : ℝ)
        φ (e (t : AddCircle (1 : ℝ))) =
          DifferentialGeometry.Analysis.roundedPolygonalCurve h (h / 4)
            (fun k : ℤ => e ((k * h : ℝ) : AddCircle (1 : ℝ))) t) ∧
      ∃ S : Set Schoenflies.Plane, IsCompact S ∧
        EqOn φ id Sᶜ ∧ EqOn φ.symm id Sᶜ := by
  obtain ⟨m, P, hm, hp, hround⟩ :=
    exists_inscribed_rounding_diffeomorph_forall_width he hε
  have hh : 0 < 1 / (m + 3 : ℝ) := by positivity
  obtain ⟨φ, hφ⟩ := hround ((1 / (m + 3 : ℝ)) / 4) ⟨by positivity, by linarith⟩
  exact ⟨m, P, φ, hm, hp, hφ⟩

end DifferentialGeometry.Topology.Planar
