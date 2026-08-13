import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.DeTurckNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Metric
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.Pullback.PushforwardVF
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
theorem connDiff_neg (g h : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    connDiff (I := I) h g x u v = -connDiff (I := I) g h x u v := by
  have hcycle := connDiff_cocycle (I := I) g h h x u v
  rw [connDiff_self] at hcycle
  exact eq_neg_of_add_eq_zero_left hcycle.symm

def idTension (g h : SmoothRiemannianMetric I M) :
    ∀ x : M, TangentSpace I x := fun x =>
  ∑ i : Fin (Module.finrank ℝ E),
    connDiff (I := I) h g x
      (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x)

omit [SigmaCompactSpace M] in
theorem idTension_eq (g h : SmoothRiemannianMetric I M) (x : M) :
    idTension (I := I) g h x =
      -(deTurckVF (I := I) g h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
  classical
  rw [deTurckVF_eq_orthoFrame_trace (I := I) g h x]
  rw [idTension, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact connDiff_neg (I := I) g h x
    (smoothOrthoFrame (I := I) g x i x)
    (smoothOrthoFrame (I := I) g x i x)

def idTensionVF (g h : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  -(deTurckVF (I := I) g h)

omit [SigmaCompactSpace M] in
@[simp] theorem idTensionVF_apply
    (g h : SmoothRiemannianMetric I M) (x : M) :
    idTensionVF (I := I) g h x = idTension (I := I) g h x := by
  rw [idTensionVF, idTension_eq]
  rfl

def diffeoTension (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) : ∀ y : M, TangentSpace I y :=
  Diffeomorph.pushforward Φ
    (idTension (I := I) g (Diffeomorph.pullbackMetric h Φ))

theorem tension_image (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    diffeoTension (I := I) g h Φ (Φ x) =
      -mfderiv I I (Φ : M → M) x
        ((deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [diffeoTension, Diffeomorph.pushforward_image,
    idTension_eq, map_neg]

theorem tension_eq_push (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    diffeoTension (I := I) g h Φ y =
      -Diffeomorph.pushforward Φ
        (deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ)) y := by
  obtain ⟨x, rfl⟩ := Φ.surjective y
  change diffeoTension (I := I) g h Φ (Φ x) =
    -Diffeomorph.pushforward Φ
      (deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ)) (Φ x)
  rw [Diffeomorph.pushforward_image]
  exact tension_image (I := I) g h Φ x
theorem tension_eq_DT (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    diffeoTension (I := I) g h Φ y =
      -(deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y := by
  rw [tension_eq_push, push_deTurckVF]

theorem hmf_neg_gauge
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I M) (T : ℝ)
    (Φ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Φ s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (diffeoTension (I := I) (g t) h (Φ t) ((Φ t : M → M) x)))) :
    ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Φ s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-Diffeomorph.pushforward (Φ t)
            (deTurckVF (I := I) (g t)
              (Diffeomorph.pullbackMetric h (Φ t)))
            ((Φ t : M → M) x))) := by
  intro x t ht
  simpa only [tension_eq_push] using hHMF x t ht

theorem hmf_target_gauge
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I M) (T : ℝ)
    (Φ : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hHMF : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Φ s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (diffeoTension (I := I) (g t) h (Φ t) ((Φ t : M → M) x)))) :
    ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Φ s : M → M) x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I)
            (Diffeomorph.pullbackMetric (g t) (Φ t).symm) h :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
            ((Φ t : M → M) x))) := by
  intro x t ht
  simpa only [tension_eq_DT] using hHMF x t ht

@[simp] theorem tension_refl
    (g h : SmoothRiemannianMetric I M) (x : M) :
    diffeoTension (I := I) g h (Diffeomorph.refl I M ∞) x =
      -(deTurckVF (I := I) g h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
  simp only [diffeoTension, Diffeomorph.pullbackMetric_refl,
    Diffeomorph.pushforward_refl]
  exact idTension_eq (I := I) g h x

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
