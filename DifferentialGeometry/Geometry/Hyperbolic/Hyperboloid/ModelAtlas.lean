import DifferentialGeometry.Geometry.Hyperbolic.HorosphericalCoordinates
import DifferentialGeometry.Geometry.Thurston.Atlas

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

open Horospherical

private def horosphericalCoordinateLinearEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] Horizontal 2 × ℝ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => (WithLp.toLp 2 ![p 0, p 1], p 2)
    invFun := fun p => WithLp.toLp 2 ![p.1 0, p.1 1, p.2]
    left_inv := by
      intro p
      ext i
      fin_cases i <;> rfl
    right_inv := by
      intro p
      apply Prod.ext
      · ext i
        fin_cases i <;> rfl
      · rfl
    map_add' := by
      intro p q
      apply Prod.ext
      · ext i
        fin_cases i <;> rfl
      · rfl
    map_smul' := by
      intro a p
      apply Prod.ext
      · ext i
        fin_cases i <;> rfl
      · rfl }

private def horosphericalModelDiffeomorph :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 3)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ Hyperboloid (EuclideanSpace ℝ (Fin 3)) :=
  horosphericalCoordinateLinearEquiv.toDiffeomorph.trans (horosphericalLogDiffeomorph 2).symm

private theorem mfderiv_horosphericalCoordinateLinearEquiv
    (p : EuclideanSpace ℝ (Fin 3))
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) p) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, Horizontal 2 × ℝ)
      horosphericalCoordinateLinearEquiv p v =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (horosphericalCoordinateLinearEquiv p)).symm
        (horosphericalCoordinateLinearEquiv (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v)) := by
  rw [mfderiv_eq_fderiv, horosphericalCoordinateLinearEquiv.hasFDerivAt.fderiv]
  rfl

private theorem riemannianMetric_inner_horosphericalModelDiffeomorph
    (p : EuclideanSpace ℝ (Fin 3))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) p) :
    riemannianMetric.inner (horosphericalModelDiffeomorph p)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        horosphericalModelDiffeomorph p v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        horosphericalModelDiffeomorph p w) =
      Real.exp (-2 * p 2) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) 0 *
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w) 0 +
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) 1 *
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w) 1) +
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) 2 *
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w) 2 := by
  change riemannianMetric.inner
    ((horosphericalLogDiffeomorph 2).symm (horosphericalCoordinateLinearEquiv p))
    (mfderiv _ _ ((horosphericalLogDiffeomorph 2).symm ∘ horosphericalCoordinateLinearEquiv) p v)
    (mfderiv _ _ ((horosphericalLogDiffeomorph 2).symm ∘ horosphericalCoordinateLinearEquiv) p w) = _
  rw [mfderiv_comp_apply p ((horosphericalLogDiffeomorph 2).symm.contMDiff.mdifferentiableAt (by simp))
      ((horosphericalCoordinateLinearEquiv.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply p ((horosphericalLogDiffeomorph 2).symm.contMDiff.mdifferentiableAt (by simp))
      ((horosphericalCoordinateLinearEquiv.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)),
    mfderiv_horosphericalCoordinateLinearEquiv, mfderiv_horosphericalCoordinateLinearEquiv,
    riemannianMetric_inner_horosphericalLogDiffeomorph_symm]
  let V := NormedSpace.fromTangentSpace (𝕜 := ℝ) p v
  let W := NormedSpace.fromTangentSpace (𝕜 := ℝ) p w
  change Real.exp (-2 * p 2) * inner ℝ (WithLp.toLp 2 ![V 0, V 1])
    (WithLp.toLp 2 ![W 0, W 1]) + V 2 * W 2 = _
  simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem hasThurstonAtlas_riemannianMetric :
    GC.Geometry.HasThurstonAtlas (riemannianMetric (E := EuclideanSpace ℝ (Fin 3))) .hyperbolic := by
  intro x
  refine ⟨horosphericalModelDiffeomorph.toPartialDiffeomorph, Set.mem_univ x, ?_⟩
  intro p hp v w
  change riemannianMetric.inner (horosphericalModelDiffeomorph p)
    (mfderiv _ _ horosphericalModelDiffeomorph p v)
    (mfderiv _ _ horosphericalModelDiffeomorph p w) =
    GC.Geometry.coordinateInner .hyperbolic p
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w)
  rw [riemannianMetric_inner_horosphericalModelDiffeomorph]
  rw [show -2 * p 2 = -(p 2) + -(p 2) by ring, Real.exp_add]
  simp only [GC.Geometry.coordinateInner, GC.Geometry.coordinateCoframe, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

end DifferentialGeometry.Hyperboloid
