import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.CovariantDerivativePointwise
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

omit [NeZero (Module.finrank ℝ E)] in
private theorem pull_symm_cancel
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric
        (Diffeomorph.pullbackMetric g Φ.symm) Φ = g := by
  rw [Diffeomorph.pullbackMetric_trans, Φ.self_trans_symm,
    Diffeomorph.pullbackMetric_refl]
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
  have hσ :
      MDiffAt (fun y : M => (⟨y, σ y⟩ : TangentBundle I M)) x :=
    σ.mdifferentiableAt
  have hpushSmooth :=
    DifferentialGeometry.Analysis.ODE.flowFamily_pushforward_contMDiff (E := E) (H := H)
      (M := M) (I := I)
      (fun _ : ℝ => Φ) (0 : ℝ) (Y := fun z => σ z) σ.contMDiff
  have hpush :
      MDiffAt
        (fun y : M => (⟨y,
          Diffeomorph.pushforward Φ (fun z => σ z) y⟩ : TangentBundle I M))
        (Φ x) :=
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
  have hpushImage := Diffeomorph.pushforward_image (E := E) (H := H) (M := M)
    (I := I) Φ (fun z => σ z) x
  rw [hpushImage, hσx] at htgt
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

theorem deTurckVF_push
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    mfderiv I I (Φ : M → M) x
        ((deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      (deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (Φ x) := by
  classical
  let F : Fin (Module.finrank ℝ E) → TangentSpace I (Φ x) := fun i =>
    mfderiv I I (Φ : M → M) x
      (smoothOrthoFrame (I := I) g x i x)
  have hF : ∀ i j,
      (Diffeomorph.pullbackMetric g Φ.symm).inner (Φ x) (F i) (F j) =
        if i = j then 1 else 0 := by
    intro i j
    have hcancel := pull_symm_cancel (I := I) g Φ
    have hinner := congrArg
      (fun metric : SmoothRiemannianMetric I M =>
        metric.inner x (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x j x)) hcancel
    change (Diffeomorph.pullbackMetric
      (Diffeomorph.pullbackMetric g Φ.symm) Φ).inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) at hinner
    rw [Diffeomorph.pullbackMetric_inner] at hinner
    exact hinner.trans
      (smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
  rw [deTurckVF_eq_orthonormal_trace (I := I) g
    (Diffeomorph.pullbackMetric h Φ) x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]
  rw [map_sum]
  rw [deTurckVF_eq_orthonormal_trace (I := I) (Diffeomorph.pullbackMetric g Φ.symm)
    h (Φ x) F hF]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa only [F] using connDiff_push (I := I) g h Φ x
    (smoothOrthoFrame (I := I) g x i x)
    (smoothOrthoFrame (I := I) g x i x)

theorem push_deTurckVF
    (g h : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    Diffeomorph.pushforward Φ
        (deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ)) y =
      (deTurckVF (I := I) (Diffeomorph.pullbackMetric g Φ.symm) h :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y := by
  obtain ⟨x, rfl⟩ := Φ.surjective y
  exact (Diffeomorph.pushforward_image (E := E) (H := H) (M := M) (I := I) Φ
    (fun z => deTurckVF (I := I) g (Diffeomorph.pullbackMetric h Φ) z) x).trans
      (deTurckVF_push (I := I) g h Φ x)
end DifferentialGeometry.PDE.RicciFlow.Pullback

end
