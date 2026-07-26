import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Naturality.CovariantDerivativePointwise

/-!
# Naturality of the connection difference under a diffeomorphism

This file proves the connection-level transport identity needed to identify a
harmonic-map tension with the DeTurck vector field of the pushed-forward
metric.  The proof uses the already established pointwise naturality of each
Levi-Civita covariant derivative and subtracts the two identities.
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

private theorem pull_symm_cancel
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric
        (Diffeomorph.pullbackMetric g Φ.symm) Φ = g := by
  rw [DifferentialGeometry.Diffeomorph.pullbackMetric_trans,
    Φ.self_trans_symm, DifferentialGeometry.Diffeomorph.pullbackMetric_refl]

/-- Simultaneously transporting both Levi-Civita endpoints carries their
connection difference through the differential of a diffeomorphism.

The source endpoints are `g` and `Φ*h`.  On the target they become
`(Φ⁻¹)*g` and `h`, respectively. -/
theorem connDiff_push
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (u v : TangentSpace I x) :
    mfderiv I I (Φ : M → M) x
        (connDiff (I := I) g (Diffeomorph.pullbackMetric h Φ) x u v) =
      connDiff (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h (Φ x)
        (mfderiv I I (Φ : M → M) x u)
        (mfderiv I I (Φ : M → M) x v) := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  have hσ : MDiffAt (T% fun z => σ z) x := σ.mdifferentiableAt
  have hpushSmooth :
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
          (Diffeomorph.pushforward Φ (fun z => σ z) y)) :=
    ODE.flowFamily_pushforward_contMDiff (I := I) (fun _ : ℝ => Φ) 0 σ.contMDiff
  have hpush : MDiffAt
      (T% fun y => Diffeomorph.pushforward Φ (fun z => σ z) y) (Φ x) :=
    hpushSmooth.mdifferentiableAt (by simp)
  have hnatG :=
    LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise
      (I := I) (Diffeomorph.pullbackMetric g Φ.symm) Φ v hσ
  have hcancel := pull_symm_cancel (I := I) g Φ
  rw [hcancel] at hnatG
  have hnatH :=
    LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise
      (I := I) h Φ v hσ
  have htgt := connDiff_apply (I := I)
    (Diffeomorph.pullbackMetric g Φ.symm) h hpush
    (mfderiv I I (Φ : M → M) x v)
  rw [Diffeomorph.pushforward_image, hσx] at htgt
  calc
    mfderiv I I (Φ : M → M) x
        (connDiff (I := I) g (Diffeomorph.pullbackMetric h Φ) x u v) =
      mfderiv I I (Φ : M → M) x
        (connDiff (I := I) g (Diffeomorph.pullbackMetric h Φ) x (σ x) v) := by
          rw [hσx]
    _ = mfderiv I I (Φ : M → M) x
        ((LeviCivita (I := I) g).toFun (fun z => σ z) x v -
          (LeviCivita (I := I) (Diffeomorph.pullbackMetric h Φ)).toFun
            (fun z => σ z) x v) := by
          rw [connDiff_apply (I := I) g
            (Diffeomorph.pullbackMetric h Φ) hσ v]
    _ = mfderiv I I (Φ : M → M) x
          ((LeviCivita (I := I) g).toFun (fun z => σ z) x v) -
        mfderiv I I (Φ : M → M) x
          ((LeviCivita (I := I) (Diffeomorph.pullbackMetric h Φ)).toFun
            (fun z => σ z) x v) := by rw [map_sub]
    _ = (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ.symm)).toFun
          (Diffeomorph.pushforward Φ (fun z => σ z)) (Φ x)
          (mfderiv I I (Φ : M → M) x v) -
        (LeviCivita (I := I) h).toFun
          (Diffeomorph.pushforward Φ (fun z => σ z)) (Φ x)
          (mfderiv I I (Φ : M → M) x v) := by
          rw [hnatG, hnatH]
    _ = connDiff (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h (Φ x)
        (mfderiv I I (Φ : M → M) x u)
        (mfderiv I I (Φ : M → M) x v) := htgt.symm

/-- Pushing the DeTurck vector field of `g` relative to `Φ*h` through
`dΦ` gives the DeTurck vector field of the pushed-forward metric
`(Φ⁻¹)*g` relative to `h`.

This is the trace of `connDiff_push`.  The pushed-forward source
`g`-orthonormal frame is orthonormal for `(Φ⁻¹)*g`, so the two
connection-difference traces agree term by term. -/
theorem deTurckVF_push
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    mfderiv I I (Φ : M → M) x
        ((deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ) :
          Cₘ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      (deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₘ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (Φ x) := by
  classical
  let F : Fin (Module.finrank ℝ E) → TangentSpace I (Φ x) := fun i =>
    mfderiv I I (Φ : M → M) x
      (smoothOrthoFrame (I := I) g x i x)
  have hF : ∀ i j,
      (Diffeomorph.pullbackMetric g Φ.symm).inner (Φ x) (F i) (F j) =
        if i = j then 1 else 0 := by
    intro i j
    simp only [F, Diffeomorph.pullbackMetric_inner, Φ.symm_apply_apply,
      Diffeomorph.mfderiv_symm_self]
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [deTurckVF_eq_trace (I := I) g
    (Diffeomorph.pullbackMetric h Φ) x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]
  rw [map_sum]
  rw [deTurckVF_eq_trace (I := I) (Diffeomorph.pullbackMetric g Φ.symm)
    h (Φ x) F hF]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa only [F] using connDiff_push (I := I) g h Φ x
    (smoothOrthoFrame (I := I) g x i x)
    (smoothOrthoFrame (I := I) g x i x)

/-- Vector-field form of `deTurckVF_push`: pushing forward the source
DeTurck field gives the target DeTurck field at every target point. -/
theorem push_deTurckVF
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    Diffeomorph.pushforward Φ
        (deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ)) y =
      (deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₘ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y := by
  obtain ⟨x, rfl⟩ := Φ.surjective y
  rw [Diffeomorph.pushforward_image]
  exact deTurckVF_push (I := I) g h Φ x

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
