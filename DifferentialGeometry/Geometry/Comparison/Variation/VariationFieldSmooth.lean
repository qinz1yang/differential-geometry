import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

/-!
# Smoothness of variation fields

This module packages the total-space smoothness of the transverse derivative
of a globally smooth two-parameter manifold variation.
-/

open Bundle Manifold
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private lemma velocity_infty
    (f : ℝ → ℝ → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => f p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun p : ℝ × ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f p.1 p.2)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) :
            TangentBundle I M)) := by
  classical
  rw [contMDiff_infty]
  intro n p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hf.contMDiffAt.of_le
    (by exact_mod_cast le_top :
      (n : WithTop ℕ∞) ≤ ∞), ?_⟩
  have hF_smooth : ContMDiffAt
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) I
      ((n : WithTop ℕ∞) + 1)
      (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u))
      (p₀, p₀.2) := by
    have hfun :
        (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u)) =
          fun r : (ℝ × ℝ) × ℝ => f r.1.1 r.2 := rfl
    rw [hfun]
    have hproj : ContMDiff
        ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : (ℝ × ℝ) × ℝ => (r.1.1, r.2)) :=
      contMDiff_fst.fst.prodMk contMDiff_snd
    exact (hf.comp hproj).contMDiffAt.of_le
      (by exact_mod_cast le_top :
        (n : WithTop ℕ∞) + 1 ≤ ∞)
  have hg_smooth : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n : WithTop ℕ∞)
      (fun q : ℝ × ℝ => q.2) p₀ :=
    contMDiffAt_snd
  have hg₁_smooth : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (n : WithTop ℕ∞) (id : ℝ × ℝ → ℝ × ℝ) p₀ :=
    contMDiffAt_id
  have hg₂_smooth : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n : WithTop ℕ∞)
      (fun _ : ℝ × ℝ => (1 : ℝ)) p₀ :=
    contMDiffAt_const
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f := fun q : ℝ × ℝ => fun u : ℝ => f q.1 u)
    (g := fun q : ℝ × ℝ => q.2)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => (1 : ℝ))
    (x₀ := p₀) (n := (n : WithTop ℕ∞) + 1)
    (m := (n : WithTop ℕ∞))
    hF_smooth hg_smooth hg₁_smooth hg₂_smooth le_rfl
  have hf_cts : Continuous (fun p : ℝ × ℝ => f p.1 p.2) :=
    hf.continuous
  have h_baseSet_open : IsOpen
      ((fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
        (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet) :=
    (Trivialization.open_baseSet _).preimage hf_cts
  have hp₀_in : p₀ ∈
      (fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
        (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
  have h_nhds : ((fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
      (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet) ∈
      nhds p₀ :=
    h_baseSet_open.mem_nhds hp₀_in
  have h_eq : ∀ᶠ p in nhds p₀,
      (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
          ⟨f p.1 p.2,
            mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)⟩).2 =
        inTangentCoordinates 𝓘(ℝ, ℝ) I
          (fun q : ℝ × ℝ => q.2)
          (fun q : ℝ × ℝ => f q.1 q.2)
          (fun q : ℝ × ℝ =>
            mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f q.1 u) q.2)
          p₀ p (1 : ℝ) := by
    filter_upwards [h_nhds] with p hp
    symm
    unfold inTangentCoordinates
    change
      ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).continuousLinearMapAt ℝ
          (f p.1 p.2) ∘L
        mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 ∘L
        ((trivializationAt ℝ
          (TangentSpace (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ)) p₀.2).symmL ℝ p.2 :
            ℝ →L[ℝ] ℝ)) (1 : ℝ) = _
    rw [TangentBundle.symmL_model_space]
    change
      ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).continuousLinearMapAt ℝ
          (f p.1 p.2))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) = _
    change
      ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).linearMapAt ℝ
          (f p.1 p.2))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) = _
    rw [Trivialization.coe_linearMapAt_of_mem _ hp]
  change ContMDiffAt _ 𝓘(ℝ, E) (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
          ⟨f p.1 p.2,
            mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)⟩).2) p₀
  exact h_smooth_mfd.congr_of_eventuallyEq h_eq

/-- The transverse field of a globally smooth two-parameter variation is a
globally smooth section of the tangent bundle along its central curve. -/
theorem varField_smooth
    (f : ℝ → ℝ → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => f p.1 p.2)) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f 0 t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s t) 0 (1 : ℝ)) :
            TangentBundle I M)) := by
  let fSwap : ℝ → ℝ → M := fun t s => f s t
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => fSwap p.1 p.2) := by
    exact hf.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hvel := velocity_infty (I := I) fSwap hswap
  have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (t, (0 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  simpa only [fSwap] using hvel.comp hincl

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
