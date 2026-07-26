import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.DeTurckNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicTension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.InverseFamily

/-!
# The harmonic-map heat-flow gauge produces Ricci--DeTurck flow

This file closes the geometric part of the reverse DeTurck ladder.  Given a
family of diffeomorphisms solving harmonic-map heat flow from a Ricci-flow
metric to a fixed background, its inverse pulls the Ricci flow back to a
Ricci--DeTurck solution.

The theorem is conditional only on the actual harmonic-map family and the
regularity already required by the pullback differentiation API.  It does not
postulate the missing harmonic-map heat-flow existence theorem.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The inverse of a harmonic-map heat-flow gauge pulls a Ricci flow back to
a Ricci--DeTurck solution relative to the fixed target metric.

The sign is fixed by `hmf_neg_gauge`; `symm_gauge_vel` differentiates the
inverse family; and `push_deTurckVF` identifies the pushed-forward source
DeTurck field with the target DeTurck field of the inverse-pulled metric. -/
theorem hmf_inverse_DT
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hRF_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M,
      ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_RF u).inner y a b)
        ((-2 : ℝ) * ricciTensor (I := I) (g_RF s) y a b) (Set.Ici 0) s)
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (diffeoTension (I := I) (g_RF t) g_bg (Ψ_fam t)
            ((Ψ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Ψ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hsymm_joint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => ((Ψ_fam q.1).symm : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_RF : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm).inner x v w)
        (deTurckRicciRHS (I := I) g_bg
          (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm) x v w)
        (Set.Ici 0) t := by
  let W : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun s =>
    deTurckVF (I := I)
      (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm) g_bg
  have hΨneg : ∀ y : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) y) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(W t ((Ψ_fam t : M → M) y)))) := by
    intro y t ht
    have hneg := hmf_target_gauge (I := I) g_RF g_bg T Ψ_fam hHMF y t ht
    simpa only [W] using hneg
  have hInvOde : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => ((Ψ_fam s).symm : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Ψ_fam t).symm (W t)
            (((Ψ_fam t).symm : M → M) x))) := by
    intro x t ht
    exact symm_gauge_vel (I := I) Ψ_fam W T hΨneg hjoint hsymm_joint t ht x
  apply ricci_pullback_DT (I := I) g_RF g_bg T (fun s => (Ψ_fam s).symm)
    hRF_deriv
  · intro x t ht
    simpa only [W] using hInvOde x t ht
  · exact hsymm_joint
  · exact hgram_RF

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
