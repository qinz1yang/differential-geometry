import DifferentialGeometry.Geometry.Curvature.AlgebraicForm
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Geometry.Curvature.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Sectional curvature determines metric curvature

This file adapts the algebraic polarization theorem to the canonical lowered
Riemann tensor of a smooth metric.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

private noncomputable def negRmForm
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → Real :=
  fun X Y Z W => -metricRm04StdAt (I := I) (M := M) g x X Y Z W

private noncomputable def metricModel
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → Real :=
  fun X Y Z W =>
    g.inner x X Z * g.inner x Y W - g.inner x Y Z * g.inner x X W

private theorem negRm_isAlg
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsAlgCurvForm (negRmForm (I := I) (M := M) g x) := by
  let K := metricCurvData (I := I) (M := M) g
  let Rm := metricRm04At (I := I) (M := M) g x
  have hadd (X₁ X₂ Y Z W : TangentSpace I x) :
      Rm (vec4 (I := I) (X₁ + X₂) Y Z W) =
        Rm (vec4 (I := I) X₁ Y Z W) +
          Rm (vec4 (I := I) X₂ Y Z W) := by
    have h :=
      Rm.map_update_add (vec4 (I := I) 0 Y Z W) (0 : Fin 4) X₁ X₂
    change
      Rm (vec4 (I := I) (X₁ + X₂) Y Z W) =
        Rm (vec4 (I := I) X₁ Y Z W) +
          Rm (vec4 (I := I) X₂ Y Z W) at h
    exact h
  have hsmul (a : Real) (X Y Z W : TangentSpace I x) :
      Rm (vec4 (I := I) (a • X) Y Z W) =
        a * Rm (vec4 (I := I) X Y Z W) := by
    have h :=
      Rm.map_update_smul (vec4 (I := I) 0 Y Z W) (0 : Fin 4) a X
    change
      Rm (vec4 (I := I) (a • X) Y Z W) =
        a * Rm (vec4 (I := I) X Y Z W) at h
    exact h
  have hinput : ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x Y X Z W =
        -metricRm04StdAt (I := I) (M := M) g x X Y Z W := by
    intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 X Y Z W)
  have houtput : ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Z W =
        -metricRm04StdAt (I := I) (M := M) g x X Y W Z := by
    intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 X Y Z W)
  have hfirst : ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Z W +
          metricRm04StdAt (I := I) (M := M) g x Y Z X W +
          metricRm04StdAt (I := I) (M := M) g x Z X Y W = 0 := by
    intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (firstBianchiAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 X Y Z W)
  refine
    { add_left := ?_
      smul_left := ?_
      anti_first := ?_
      anti_last := ?_
      bianchi := ?_ }
  · intro X₁ X₂ Y Z W
    dsimp [negRmForm, metricRm04StdAt, tensor04StdAt, Rm]
    rw [hadd]
    ring
  · intro a X Y Z W
    dsimp [negRmForm, metricRm04StdAt, tensor04StdAt, Rm]
    rw [hsmul]
    ring
  · intro X Y Z W
    dsimp [negRmForm]
    linarith [hinput X Y Z W]
  · intro X Y Z W
    dsimp [negRmForm]
    linarith [houtput X Y Z W]
  · intro X Y Z W
    dsimp [negRmForm]
    linarith [hfirst X Y Z W]

private theorem metricModel_isAlg
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsAlgCurvForm (metricModel (I := I) (M := M) g x) := by
  refine
    { add_left := ?_
      smul_left := ?_
      anti_first := ?_
      anti_last := ?_
      bianchi := ?_ }
  · intro X₁ X₂ Y Z W
    simp only [metricModel, map_add, ContinuousLinearMap.add_apply]
    ring
  · intro a X Y Z W
    simp only [metricModel, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · intro X Y Z W
    simp only [metricModel]
    ring
  · intro X Y Z W
    simp only [metricModel]
    ring
  · intro X Y Z W
    simp only [metricModel]
    rw [g.symm x Y X, g.symm x Z X, g.symm x Z Y]
    ring

/-- A pointwise constant-sectional-curvature identity determines the full
canonical lowered Riemann tensor. -/
theorem metricRm_of_sec
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real)
    (hsec : ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Z W =
        c * (g.inner x Y Z * g.inner x X W -
          g.inner x X Z * g.inner x Y W) := by
  let B := negRmForm (I := I) (M := M) g x
  let S := metricModel (I := I) (M := M) g x
  have hB : IsAlgCurvForm B := negRm_isAlg (I := I) (M := M) g x
  have hS : IsAlgCurvForm S := metricModel_isAlg (I := I) (M := M) g x
  have hdiag : ∀ X Y : TangentSpace I x,
      B X Y X Y = (fun a b d e => c * S a b d e) X Y X Y := by
    intro X Y
    have hskew := hB.anti_last X Y X Y
    have hmodel :
        S X Y X Y =
          g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y := by
      dsimp [S, metricModel]
      rw [g.symm x Y X]
    dsimp [B, negRmForm] at hskew
    have hskew' :
        -metricRm04StdAt (I := I) (M := M) g x X Y X Y =
          metricRm04StdAt (I := I) (M := M) g x X Y Y X := by
      linarith
    change
      -metricRm04StdAt (I := I) (M := M) g x X Y X Y =
        c * S X Y X Y
    rw [hskew', hsec X Y, hmodel]
  have heq := hB.ext (hS.smul c) hdiag
  intro X Y Z W
  have h := heq X Y Z W
  dsimp [B, negRmForm, S, metricModel] at h
  linarith

/-- A full lowered metric-curvature formula determines the corresponding
curvature operator by nondegeneracy of the metric. -/
theorem riemannOp_of_rm
    [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real)
    (hRm : ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Z W =
        c * (g.inner x Y Z * g.inner x X W -
          g.inner x X Z * g.inner x Y W)) :
    ∀ X Y Z : TangentSpace I x,
      riemannOp (LeviCivita (I := I) g) x X Y Z =
        c • (g.inner x Y Z • X - g.inner x X Z • Y) := by
  intro X Y Z
  apply tangentFlatLinear_injective_gen (I := I) g x
  ext W
  rw [tangentFlatLinear_apply_gen, tangentFlatLinear_apply_gen,
    g.symm x (riemannOp (LeviCivita (I := I) g) x X Y Z) W,
    riemannOp_eq_chartRiemannCLM_apply,
    ← metricRm04StdAt_eq_chartRiemannCLM, hRm]
  simp only [map_smul, map_sub, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]

/-- Scaling a positive constant-sectional-curvature metric by its curvature
constant gives the full curvature-one Riemann formula. -/
theorem metricRm_scale_one
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real) (hc : 0 < c)
    (hsec : ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ X Y Z W : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M)
          (scaleMetric (I := I) c hc g) x X Y Z W =
        (scaleMetric (I := I) c hc g).inner x Y Z *
            (scaleMetric (I := I) c hc g).inner x X W -
          (scaleMetric (I := I) c hc g).inner x X Z *
            (scaleMetric (I := I) c hc g).inner x Y W := by
  have hdiag : ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M)
          (scaleMetric (I := I) c hc g) x X Y Y X =
        (1 : Real) *
          ((scaleMetric (I := I) c hc g).inner x X X *
              (scaleMetric (I := I) c hc g).inner x Y Y -
            (scaleMetric (I := I) c hc g).inner x X Y *
              (scaleMetric (I := I) c hc g).inner x X Y) := by
    intro X Y
    rw [metricRmStd_scale (I := I) c hc g x X Y Y X, hsec X Y]
    simp only [scaleMetric_inner, one_mul]
    ring
  simpa only [one_mul] using
    (metricRm_of_sec (I := I) (M := M)
      (scaleMetric (I := I) c hc g) x 1 hdiag)

end DifferentialGeometry.Integral.Connection
