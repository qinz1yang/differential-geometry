import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℝ × M → F} {m n : WithTop ℕ∞}

theorem ContMDiffOn.time_derivWithin {J : Set ℝ} {U : Set M}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n f (J ×ˢ U))
    (hJ : UniqueDiffOn ℝ J) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) m
      (fun p : ℝ × M => derivWithin (fun t => f (t, p.2)) J p.1) (J ×ˢ U) := by
  intro p₀ hp₀
  have harg : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) n (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      ((J ×ˢ U) ×ˢ J) (p₀, p₀.1) :=
    contMDiffWithinAt_snd.prodMk contMDiffWithinAt_fst.snd
  have hcomp : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, F) n (fun q : (ℝ × M) × ℝ => f (q.2, q.1.2))
      ((J ×ˢ U) ×ˢ J) (p₀, p₀.1) :=
    (hf p₀ hp₀).comp (f := fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      (g := f) (p₀, p₀.1) harg (fun q hq => ⟨hq.2, hq.1.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F))
    (f := fun (p : ℝ × M) (t : ℝ) => f (t, p.2))
    (g := fun p : ℝ × M => p.1) (g₁ := fun p : ℝ × M => p)
    (g₂ := fun _ : ℝ × M => (1 : ℝ)) (x₀ := p₀)
    hcomp contMDiffWithinAt_fst contMDiffWithinAt_id contMDiffWithinAt_const hmn
    (mapsTo_id _) hp₀ (fun _ hp => hp.1) hJ.uniqueMDiffOn
  convert hd using 1
  funext p
  simp only [inTangentCoordinates, mfderivWithin_eq_fderivWithin]
  dsimp only [ContinuousLinearMap.inCoordinates]
  simp only [Prod.mk.eta, TangentBundle.continuousLinearMapAt_model_space,
    TangentBundle.symmL_model_space]
  change derivWithin (fun t => f (t, p.2)) J p.1 =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2)))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2))).symm
        (fderivWithin ℝ (fun t => f (t, p.2)) J p.1
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm 1))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rfl
