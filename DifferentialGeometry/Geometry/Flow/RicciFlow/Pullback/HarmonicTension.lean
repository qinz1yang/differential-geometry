import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.DeTurckNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF

/-!
# Harmonic-map tension for diffeomorphisms

For a diffeomorphism `Φ : M → M`, the tension of

```text
Φ : (M, g) → (M, g_bg)
```

can be read on the domain by pulling the target metric back.  The resulting
domain vector is the `g`-trace of
`∇^(Φ*g_bg) - ∇^g`; pushing that vector through `dΦ` gives the usual tension
at the target point.  This formulation avoids choosing coordinates or a
connection on a not-yet-constructed mapping-space bundle.

The identity-map specialization proves the sign needed by the reverse
DeTurck gauge: its tension is `- deTurckVF g g_bg`.
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
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

/-- Reversing the two Levi-Civita connections reverses the sign of their
connection-difference tensor. -/
theorem connDiff_neg (g h : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    connDiff (I := I) h g x u v = -connDiff (I := I) g h x u v := by
  have hcycle := connDiff_cocycle (I := I) g h h x u v
  rw [connDiff_self] at hcycle
  exact eq_neg_of_add_eq_zero_left hcycle.symm

/-- The tension of the identity map `(M,g) → (M,h)`, defined intrinsically
as the `g`-orthonormal-frame trace of `∇^h - ∇^g`. -/
def idTension (g h : SmoothRiemannianMetric I M) :
    ∀ x : M, TangentSpace I x := fun x =>
  ∑ i : Fin (Module.finrank ℝ E),
    connDiff (I := I) h g x
      (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x)

/-- The identity-map tension has the opposite sign from the DeTurck vector
field, because `deTurckVF g h` traces `∇^g - ∇^h`. -/
theorem idTension_eq (g h : SmoothRiemannianMetric I M) (x : M) :
    idTension (I := I) g h x =
      -(deTurckVF (I := I) g h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
  classical
  rw [deTurckVF_eq_orthoFrame_trace (I := I) g h x]
  simp only [idTension, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact connDiff_neg (I := I) g h x
    (smoothOrthoFrame (I := I) g x i x)
    (smoothOrthoFrame (I := I) g x i x)

/-- The smooth bundled identity-map tension field.  The preceding theorem
identifies its value with the intrinsic connection trace. -/
def idTensionVF (g h : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  -(deTurckVF (I := I) g h)

@[simp] theorem idTensionVF_apply
    (g h : SmoothRiemannianMetric I M) (x : M) :
    idTensionVF (I := I) g h x = idTension (I := I) g h x := by
  rw [idTensionVF, idTension_eq]
  rfl

/-- The tension vector field of a diffeomorphism
`Φ : (M,g) → (M,h)`, expressed as the pushforward of the identity tension
from `(M,g)` to `(M, Φ*h)`.

Evaluating this target vector field at `Φ x` gives the standard tension along
the map at the source point `x`. -/
def diffeoTension (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) : ∀ y : M, TangentSpace I y :=
  Diffeomorph.pushforward Φ
    (idTension (I := I) g (Diffeomorph.pullbackMetric h Φ))

/-- At the image of a source point, diffeomorphism tension is the differential
of `Φ` applied to the negative DeTurck field of `g` relative to `Φ*h`. -/
theorem tension_image (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    diffeoTension (I := I) g h Φ (Φ x) =
      -mfderiv I I (Φ : M → M) x
        ((deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [diffeoTension, Diffeomorph.pushforward_image,
    idTension_eq, map_neg]

/-- Diffeomorphism tension is the negative pushed-forward DeTurck vector
field.  This target-vector-field form is the one used when differentiating the
inverse gauge family. -/
theorem tension_eq_push (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    diffeoTension (I := I) g h Φ y =
      -Diffeomorph.pushforward Φ
        (deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ)) y := by
  obtain ⟨x, rfl⟩ := Φ.surjective y
  rw [tension_image, Diffeomorph.pushforward_image]

/-- Naturality identifies diffeomorphism tension with the negative DeTurck
field of the inverse-pulled source metric on the target. -/
theorem tension_eq_DT (g h : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    diffeoTension (I := I) g h Φ y =
      -(deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y := by
  rw [tension_eq_push, push_deTurckVF]

/-- A harmonic-map heat equation written with `diffeoTension` has exactly the
negative pushed-forward gauge velocity required by the inverse-family lemma
`symm_gauge_vel`. -/
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

/-- Target-metric form of harmonic-map heat flow: its velocity is the
negative DeTurck field of the inverse-pulled source metric. -/
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

/-- At the identity diffeomorphism, diffeomorphism tension reduces exactly to
the negative DeTurck vector field. -/
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
