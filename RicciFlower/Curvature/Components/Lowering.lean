import RicciFlower.Curvature.Components.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

/-!
# Curvature output lowering and skewness

This submodule is part of the split `RicciFlower.Curvature.Components` API.
-/

/-- A lowered `(0,4)` tensor is obtained from a `(1,3)` tensor by lowering the
output slot with the metric. -/
def Rm04LowersRm13At
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) =
      Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)

/-- Lowering a realized `(1,3)` curvature tensor by the metric gives a
realized lowered `(0,4)` curvature tensor for the same connection. -/
theorem rm04RealizesLower
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hLower : forall x : M,
      Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x)) :
    Rm04RealizesConnection (I := I) g cov Rm04 := by
  intro W X Y Z x
  rw [hLower x (W x) (X x) (Y x) (Z x)]
  have h := hRm13 X Y Z x
    (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (W x)))
  simpa [tangentFlatLinear_apply, cotangentToDual_apply] using h

/-- Realized `(1,3)` and lowered `(0,4)` curvature tensors are related by
metric lowering at a point. -/
theorem rm04LowersRm13At_of_realizes
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) :
    Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) := by
  intro W X Y Z
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Z
  let alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W)
  have h04 := hRm04 Wsec Xsec Ysec Zsec x
  have h13 := hRm13 Xsec Ysec Zsec x alpha
  have h04' :
      Rm04 x (vec4 W X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p)) x) := by
    simpa [hWsec, hXsec, hYsec, hZsec] using h04
  have h13' :
      Rm13 x
          (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
          (vec3 X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p)) x) := by
    simpa [alpha, hXsec, hYsec, hZsec, tangentFlatLinear_apply, cotangentToDual_apply] using h13
  exact h04'.trans h13'.symm

/-- Metric skew-adjointness of the curvature endomorphism in `(1,3)` form:
`g(W,R(X,Y)Z) = -g(Z,R(X,Y)W)`. -/
def Rm13MetricSkewAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z) =
      -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W)

/-- Last-pair metric skew for a lowered Riemann tensor in RicciFlower's slot
order `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`. -/
def Rm04OutputSkewAt
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) = -Rm04 (vec4 Z X Y W)

theorem rm13MetricSkewAt_of_rm04_outputSkew
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hSkew : Rm04OutputSkewAt (I := I) Rm04) :
    Rm13MetricSkewAt (I := I) g x Rm13 := by
  intro W X Y Z
  calc
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)
        = Rm04 (vec4 W X Y Z) := (hLower W X Y Z).symm
    _ = -Rm04 (vec4 Z X Y W) := hSkew W X Y Z
    _ = -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W) := by rw [hLower Z X Y W]

/-- Metric skew-adjointness of `(1,3)` curvature follows from a lowered
realization and output skew-adjointness of the lowered tensor. -/
theorem rm13MetricSkewAt_of_realizes_outputSkew
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M}
    (hSkew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_rm04_outputSkew (I := I) g (Rm13 x) (Rm04 x)
    (rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x)
    hSkew
end Realized
end RicciFlower
