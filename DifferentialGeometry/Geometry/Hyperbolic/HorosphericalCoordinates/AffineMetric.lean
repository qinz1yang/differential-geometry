import DifferentialGeometry.Geometry.Hyperbolic.HorosphericalCoordinates

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

open Horospherical

theorem riemannianMetric_inner_horosphericalLogDiffeomorph_symm_affine
    (m : ℕ) (a b : ℝ) (p v w : Horizontal m × ℝ) :
    let F : Horizontal m × ℝ → Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))) :=
      fun x => (horosphericalLogDiffeomorph m).symm (x.1, a * x.2 + b)
    riemannianMetric.inner (F p)
      (mfderiv 𝓘(ℝ, Horizontal m × ℝ)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) F p
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v))
      (mfderiv 𝓘(ℝ, Horizontal m × ℝ)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) F p
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm w)) =
      Real.exp (-2 * (a * p.2 + b)) * inner ℝ v.1 w.1 + a ^ 2 * v.2 * w.2 := by
  let A : Horizontal m × ℝ → Horizontal m × ℝ := fun x => (x.1, a * x.2 + b)
  let L : Horizontal m × ℝ →L[ℝ] Horizontal m × ℝ :=
    (ContinuousLinearMap.fst ℝ (Horizontal m) ℝ).prod
      (a • ContinuousLinearMap.snd ℝ (Horizontal m) ℝ)
  have hA (x : Horizontal m × ℝ) : HasFDerivAt A L x := by
    exact (ContinuousLinearMap.fst ℝ (Horizontal m) ℝ).hasFDerivAt.prodMk
      (((ContinuousLinearMap.snd ℝ (Horizontal m) ℝ).hasFDerivAt.const_mul a).add_const b)
  have hd (x u : Horizontal m × ℝ) :
      mfderiv 𝓘(ℝ, Horizontal m × ℝ) 𝓘(ℝ, Horizontal m × ℝ) A x
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm u) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (A x)).symm (L u) := by
    rw [mfderiv_eq_fderiv, (hA x).fderiv]
    rfl
  change riemannianMetric.inner ((horosphericalLogDiffeomorph m).symm (A p))
    (mfderiv _ _ ((horosphericalLogDiffeomorph m).symm ∘ A) p
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v))
    (mfderiv _ _ ((horosphericalLogDiffeomorph m).symm ∘ A) p
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm w)) = _
  rw [mfderiv_comp_apply p
      ((horosphericalLogDiffeomorph m).symm.contMDiff.mdifferentiableAt (by simp))
      (hA p).hasMFDerivAt.mdifferentiableAt,
    mfderiv_comp_apply p
      ((horosphericalLogDiffeomorph m).symm.contMDiff.mdifferentiableAt (by simp))
      (hA p).hasMFDerivAt.mdifferentiableAt,
    hd, hd, riemannianMetric_inner_horosphericalLogDiffeomorph_symm]
  change Real.exp (-2 * (a * p.2 + b)) * inner ℝ v.1 w.1 +
    (a * v.2) * (a * w.2) = _
  ring

end DifferentialGeometry.Hyperboloid
