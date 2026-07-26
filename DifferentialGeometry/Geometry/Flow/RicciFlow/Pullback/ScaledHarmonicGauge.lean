import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicTension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.InverseFamily

/-!
# Density-scaled harmonic-map gauges

This file records the exact pullback equation produced by a harmonic-map
heat equation whose tension field is multiplied by a smooth source scalar.
The scalar in the pulled-back drift is its transport by the inverse gauge;
it is not, in general, a function of the pulled-back metric alone.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- Transport a smooth scalar from the source of a diffeomorphism to its
target.  Thus `transportScalar r Φ = r ∘ Φ⁻¹`. -/
def transportScalar
    (r : ScalarField (I := I) (M := M)) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ScalarField (I := I) (M := M) :=
  ⟨fun y => r (Φ.symm y), r.contMDiff.comp Φ.symm.contMDiff⟩

@[simp] theorem trScalar_apply
    (r : ScalarField (I := I) (M := M)) (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    transportScalar (I := I) r Φ y = r (Φ.symm y) :=
  rfl

@[simp] theorem trScalar_image
    (r : ScalarField (I := I) (M := M)) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    transportScalar (I := I) r Φ (Φ x) = r x := by
  simp only [trScalar_apply, Diffeomorph.symm_apply_apply]

/-- A Ricci flow pulled back by a family whose velocity is the pushforward of
an arbitrary smooth drift `Z` solves Ricci flow plus `ℒ_Z g`.

This is the drift-valued form of `ricci_pullback_DT`.  Keeping the drift
arbitrary is essential for density-scaled gauges, where the transported
scalar multiplying the DeTurck field is spatially varying. -/
theorem ricci_pullback_drift
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (Z : ℝ → VectorField (I := I) (M := M))
    (hRF_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M,
      ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_RF u).inner y a b)
        ((-2 : ℝ) * ricciTensor (I := I) (g_RF s) y a b) (Set.Ici 0) s)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Φ_fam t) (Z t)
            ((Φ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_RF : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_RF s) (Φ_fam s)).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w +
          lieDerivMetric (I := I)
            (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) (Z t) x v w)
        (Set.Ici 0) t := by
  let hPush : ∀ s : ℝ,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
          (Diffeomorph.pushforward (Φ_fam s) (Z s) z)) := fun s =>
    ODE.flowFamily_pushforward_contMDiff (I := I) Φ_fam s (Z s).contMDiff
  let Y : ℝ → VectorField (I := I) (M := M) := fun s =>
    ⟨Diffeomorph.pushforward (Φ_fam s) (Z s), hPush s⟩
  have hYode : ∀ z : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y s ((Φ_fam s : M → M) z))) := by
    intro z s hs
    simpa only [Y] using hΦode z s hs
  intro t ht x v w
  have ht_Ico : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have h_metric := hRF_deriv t ht_Ico ((Φ_fam t : M → M) x)
    (mfderiv I I (Φ_fam t : M → M) x v)
    (mfderiv I I (Φ_fam t : M → M) x w)
  have h_push := flow_slot_pos (I := I) (g_RF t) Y T Φ_fam hYode hjoint
    t ht x v w
  obtain ⟨Q', hQ'⟩ := evalForm_joint (I := I) g_RF T Φ_fam hjoint hgram_RF
    t ht x v w
  have h_total := deTurck_evalForm_chain_hasDerivWithinAt (I := I) g_RF Φ_fam
    t (le_of_lt ht.1) x v w _ _ h_metric h_push hQ'
  have h_ric := ricci_tensor_pullback_natural_under_diffeomorphism
    (I := I) (g_RF t) (Φ_fam t) x v w
  have h_lie :
      lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) (Z t) x v w =
        lieDerivMetric (I := I) (g_RF t) (Y t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    simpa only [Y] using
      (lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
        (I := I) (g_RF t) (Φ_fam t) (Z t) (Z t).contMDiff (hPush t) x v w)
  have h_value :
      ((-2 : ℝ) * ricciTensor (I := I) (g_RF t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w) +
        lieDerivMetric (I := I) (g_RF t) (Y t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) =
      ((-2 : ℝ) * ricciTensor (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w +
        lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) (Z t) x v w) := by
    rw [← h_ric, ← h_lie]
  have h_total' : HasDerivWithinAt
      (fun s : ℝ => (g_RF s).inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((-2 : ℝ) * ricciTensor (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w +
        lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) (Z t) x v w)
      (Set.Ici 0) t := by
    rw [← h_value]
    exact h_total
  have hcurve :
      (fun s : ℝ =>
        (Diffeomorph.pullbackMetric (g_RF s) (Φ_fam s)).inner x v w) =
      (fun s : ℝ => (g_RF s).inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) := by
    funext s
    exact pullback_metric_evaluation_formula (I := I) (g_RF s) (Φ_fam s) x v w
  rwa [hcurve]

/-- Pulling a fixed metric back by a family whose velocity is the pushforward
of `Z` differentiates to `ℒ_Z` of the pulled-back metric. -/
theorem fixed_pullback_drift
    (q : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (Z : ℝ → VectorField (I := I) (M := M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Φ_fam t) (Z t)
            ((Φ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric q (Φ_fam s)).inner x v w)
        (lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric q (Φ_fam t)) (Z t) x v w)
        (Set.Ici 0) t := by
  let hPush : ∀ s : ℝ,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
          (Diffeomorph.pushforward (Φ_fam s) (Z s) z)) := fun s =>
    ODE.flowFamily_pushforward_contMDiff (I := I) Φ_fam s (Z s).contMDiff
  let Y : ℝ → VectorField (I := I) (M := M) := fun s =>
    ⟨Diffeomorph.pushforward (Φ_fam s) (Z s), hPush s⟩
  have hYode : ∀ z : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y s ((Φ_fam s : M → M) z))) := by
    intro z s hs
    simpa only [Y] using hΦode z s hs
  intro t ht x v w
  have h_slot := flow_slot_pos (I := I) q Y T Φ_fam hYode hjoint
    t ht x v w
  have h_lie :
      lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric q (Φ_fam t)) (Z t) x v w =
        lieDerivMetric (I := I) q (Y t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    simpa only [Y] using
      (lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
        (I := I) q (Φ_fam t) (Z t) (Z t).contMDiff (hPush t) x v w)
  have h_slot' : HasDerivWithinAt
      (fun s : ℝ => q.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (lieDerivMetric (I := I)
        (Diffeomorph.pullbackMetric q (Φ_fam t)) (Z t) x v w)
      (Set.Ici 0) t := by
    rw [h_lie]
    exact h_slot
  have hcurve :
      (fun s : ℝ =>
        (Diffeomorph.pullbackMetric q (Φ_fam s)).inner x v w) =
      (fun s : ℝ => q.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) := by
    funext s
    exact pullback_metric_evaluation_formula (I := I) q (Φ_fam s) x v w
  rwa [hcurve]

/-- Multiplying the source tension by `r` produces the negative DeTurck field
multiplied by the transported target scalar `r ∘ Φ⁻¹`. -/
theorem scaled_hmf_target
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (r : ScalarField (I := I) (M := M)) (x : M) :
    r x • diffeoTension (I := I) g h Φ (Φ x) =
      -((transportScalar (I := I) r Φ •
          deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
            VectorField (I := I) (M := M)) (Φ x)) := by
  rw [tension_eq_DT]
  change r x •
      (-(deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        VectorField (I := I) (M := M)) (Φ x)) =
    -((transportScalar (I := I) r Φ) (Φ x) •
      (deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        VectorField (I := I) (M := M)) (Φ x))
  rw [trScalar_image, smul_neg]

/-- The inverse of a source-scaled harmonic-map gauge has velocity
`DΨ⁻¹ ((r ∘ Ψ⁻¹) • W)`.  This is the first-order gauge variable in the
closed `(G, Ψ⁻¹)` formulation. -/
theorem scaled_inv_vel
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (r : ℝ → ScalarField (I := I) (M := M))
    (T : ℝ) (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((r t x) • diffeoTension (I := I) (g_RF t) g_bg (Ψ_fam t)
            ((Ψ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Ψ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hsymm_joint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => ((Ψ_fam p.1).symm : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => ((Ψ_fam s).symm : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Ψ_fam t).symm
            (transportScalar (I := I) (r t) (Ψ_fam t) •
              deTurckVF (I := I)
                (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm) g_bg)
            (((Ψ_fam t).symm : M → M) x))) := by
  let a : ℝ → ScalarField (I := I) (M := M) := fun s =>
    transportScalar (I := I) (r s) (Ψ_fam s)
  let W : ℝ → VectorField (I := I) (M := M) := fun s =>
    a s • deTurckVF (I := I)
      (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm) g_bg
  have hΨneg : ∀ y : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) y) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(W t ((Ψ_fam t : M → M) y)))) := by
    intro y t ht
    simpa only [W, a, scaled_hmf_target] using hHMF y t ht
  intro x t ht
  simpa only [W, a] using
    (symm_gauge_vel (I := I) Ψ_fam W T hΨneg hjoint hsymm_joint t ht x)

/-- The inverse of a density-scaled harmonic-map gauge pulls a Ricci flow
back to Ricci flow with drift
`(r ∘ Ψ⁻¹) • W(Ψ⁻¹* g, g_bg)`.

In particular, the coefficient is the transported *source* scalar.  The
statement deliberately does not replace it by a density ratio formed only
from the pulled-back metric, since that replacement is not natural under a
general diffeomorphism. -/
theorem scaled_hmf_inverse
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (r : ℝ → ScalarField (I := I) (M := M))
    (T : ℝ) (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hRF_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M,
      ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_RF u).inner y a b)
        ((-2 : ℝ) * ricciTensor (I := I) (g_RF s) y a b) (Set.Ici 0) s)
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((r t x) • diffeoTension (I := I) (g_RF t) g_bg (Ψ_fam t)
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
          Integral.Measure.chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm) x v w +
          lieDerivMetric (I := I)
            (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm)
            (transportScalar (I := I) (r t) (Ψ_fam t) •
              deTurckVF (I := I)
                (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm) g_bg)
            x v w)
        (Set.Ici 0) t := by
  let a : ℝ → ScalarField (I := I) (M := M) := fun s =>
    transportScalar (I := I) (r s) (Ψ_fam s)
  let W : ℝ → VectorField (I := I) (M := M) := fun s =>
    a s • deTurckVF (I := I)
      (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm) g_bg
  have hInvOde : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => ((Ψ_fam s).symm : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Ψ_fam t).symm (W t)
            (((Ψ_fam t).symm : M → M) x))) := by
    intro x t ht
    simpa only [W, a] using
      (scaled_inv_vel (I := I) g_RF g_bg r T Ψ_fam hHMF hjoint hsymm_joint x t ht)
  apply ricci_pullback_drift (I := I) g_RF T (fun s => (Ψ_fam s).symm) W
    hRF_deriv
  · intro x t ht
    exact hInvOde x t ht
  · exact hsymm_joint
  · exact hgram_RF

/-- The inverse density-scaled gauge transports the fixed background metric
by the same drift that appears in `scaled_hmf_inverse`.

For `H = Ψ⁻¹* g_bg`, its exact equation is
`∂ₜH = ℒ_((r ∘ Ψ⁻¹) • W(G,g_bg)) H`. -/
theorem scaled_bg_inverse
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (r : ℝ → ScalarField (I := I) (M := M))
    (T : ℝ) (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((r t x) • diffeoTension (I := I) (g_RF t) g_bg (Ψ_fam t)
            ((Ψ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Ψ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hsymm_joint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => ((Ψ_fam p.1).symm : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric g_bg (Ψ_fam s).symm).inner x v w)
        (lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric g_bg (Ψ_fam t).symm)
          (transportScalar (I := I) (r t) (Ψ_fam t) •
            deTurckVF (I := I)
              (Diffeomorph.pullbackMetric (g_RF t) (Ψ_fam t).symm) g_bg)
          x v w)
        (Set.Ici 0) t := by
  let a : ℝ → ScalarField (I := I) (M := M) := fun s =>
    transportScalar (I := I) (r s) (Ψ_fam s)
  let W : ℝ → VectorField (I := I) (M := M) := fun s =>
    a s • deTurckVF (I := I)
      (Diffeomorph.pullbackMetric (g_RF s) (Ψ_fam s).symm) g_bg
  have hInvOde : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => ((Ψ_fam s).symm : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Ψ_fam t).symm (W t)
            (((Ψ_fam t).symm : M → M) x))) := by
    intro x t ht
    simpa only [W, a] using
      (scaled_inv_vel (I := I) g_RF g_bg r T Ψ_fam hHMF hjoint hsymm_joint x t ht)
  apply fixed_pullback_drift (I := I) g_bg T (fun s => (Ψ_fam s).symm) W
  · intro x t ht
    exact hInvOde x t ht
  · exact hsymm_joint

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
