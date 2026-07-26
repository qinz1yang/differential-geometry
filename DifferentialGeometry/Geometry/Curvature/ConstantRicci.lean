import DifferentialGeometry.Geometry.Curvature.MetricSectional
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound

/-!
# Ricci curvature of a constant-curvature metric

This file contracts the invariant constant-curvature operator formula to the
corresponding Ricci tensor and lower bound.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

omit [I.Boundaryless] in
/-- The constant-curvature operator formula contracts to
`Ric = (dim - 1) c g`. -/
theorem ricci_of_op
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (hOp : ∀ X Y Z : TangentSpace I x,
      riemannOp (LeviCivita (I := I) g) x X Y Z =
        c • (g.inner x Y Z • X - g.inner x X Z • Y))
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ((Module.finrank ℝ E : ℝ) - 1) * c * g.inner x v w := by
  classical
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x v w B hB]
  have hparseval :
      g.inner x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x v (B i) * g.inner x (B i) w :=
    g_inner_eq_orthonormal_parseval_sum (I := I) g x v w B hB
  have hterm (i : Fin (Module.finrank ℝ E)) :
      g.inner x
          (riemannOp (LeviCivita (I := I) g) x (B i) v w)
          (B i) =
        c * g.inner x v w -
          c * (g.inner x v (B i) * g.inner x (B i) w) := by
    rw [hOp]
    simp only [map_smul, map_sub, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, hB i i, if_pos]
    rw [g.symm x (B i) w]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  have hconst :
      (∑ _i : Fin (Module.finrank ℝ E), c * g.inner x v w) =
        (Module.finrank ℝ E : ℝ) * (c * g.inner x v w) := by
    simp
  rw [hconst, ← Finset.mul_sum, ← hparseval]
  ring

/-- A full lowered constant-curvature formula implies
`Ric = (dim - 1) c g`. -/
theorem ricci_of_rm
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (hRm : ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Z W =
        c * (g.inner x Y Z * g.inner x X W -
          g.inner x X Z * g.inner x Y W))
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ((Module.finrank ℝ E : ℝ) - 1) * c * g.inner x v w := by
  apply ricci_of_op (I := I) g x c
  · exact riemannOp_of_rm (I := I) (M := M) g x c hRm

/-- A constant sectional-curvature numerator identity gives the exact Ricci
tensor formula. -/
theorem ricci_of_sec
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y))
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ((Module.finrank ℝ E : ℝ) - 1) * c * g.inner x v w := by
  apply ricci_of_rm (I := I) g x c
  exact metricRm_of_sec (I := I) (M := M) g x c (hsec x)

/-- A constant sectional-curvature numerator identity supplies the matching
global lower Ricci bound. -/
theorem ricciBound_of_sec
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * c) := by
  intro x v
  rw [ricci_of_sec (I := I) g c hsec x v v]

end DifferentialGeometry.Integral.Connection

end
