import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Remainder
import DifferentialGeometry.Geometry.Curvature.RicciAction

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
section Core

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  classical
  set m : Fin 2 → TangentSpace I x := fun a => if a = 0 then u₁ else Z with hm
  have hupd : ∀ u : TangentSpace I x,
      Function.update m 0 u = (fun a : Fin 2 => if a = 0 then u else Z) := by
    intro u
    funext a
    fin_cases a <;> simp [hm]
  calc
    q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
        q (Function.update m 0 (u₁ + u₂)) := by rw [hupd]
    _ = q (Function.update m 0 u₁) + q (Function.update m 0 u₂) :=
      q.map_update_add m 0 u₁ u₂
    _ = q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by rw [hupd, hupd]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift02_sub_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ - u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) -
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  have h := drift02_add_left (I := I) q (u₁ - u₂) u₂ Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTri_split
    (q₁ q₂ : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A₁ A₂ : TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] TangentSpace I x) :
    lowerTri (I := I) q₁ A₁ - lowerTri (I := I) q₂ A₂ =
      lowerTri (I := I) (q₁ - q₂) A₁ + lowerTri (I := I) q₂ (A₁ - A₂) := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval (lowerTri (I := I) q₁ A₁ - lowerTri (I := I) q₂ A₂) v =
    Tensor0SSpace.eval
      (lowerTri (I := I) (q₁ - q₂) A₁ + lowerTri (I := I) q₂ (A₁ - A₂)) v
  rw [Tensor0SSpace.eval_sub, Tensor0SSpace.eval_add,
    lowerTri_apply, lowerTri_apply, lowerTri_apply, lowerTri_apply,
    Tensor0SSpace.eval_sub]
  have hA :
      (((A₁ - A₂) (v 0)) (v 1)) (v 2) =
        ((A₁ (v 0)) (v 1)) (v 2) - ((A₂ (v 0)) (v 1)) (v 2) := rfl
  rw [hA]
  have hsub := drift02_sub_left (I := I) q₂
    (((A₁ (v 0)) (v 1)) (v 2)) (((A₂ (v 0)) (v 1)) (v 2)) (v 3)
  change Tensor0SSpace.eval q₂
      (fun a : Fin 2 => if a = 0 then
        ((A₁ (v 0)) (v 1)) (v 2) - ((A₂ (v 0)) (v 1)) (v 2) else v 3) =
    Tensor0SSpace.eval q₂
        (fun a : Fin 2 => if a = 0 then ((A₁ (v 0)) (v 1)) (v 2) else v 3) -
      Tensor0SSpace.eval q₂
        (fun a : Fin 2 => if a = 0 then ((A₂ (v 0)) (v 1)) (v 2) else v 3) at hsub
  rw [hsub]
  ring

omit [SigmaCompactSpace M] in
theorem lowerRm_eq_rm04 (g : SmoothRiemannianMetric I M) (x : M) :
    lowerTri (I := I) (metricTensorField (I := I) g x)
        (riemannOp (metricCov (I := I) g) x) =
      metricRm04At (I := I) g x := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval
      (lowerTri (I := I) (metricTensorField (I := I) g x)
        (riemannOp (metricCov (I := I) g) x)) v =
    Tensor0SSpace.eval (metricRm04At (I := I) g x) v
  have hv : vec4 (I := I) (v 0) (v 1) (v 2) (v 3) = v := by
    funext a
    fin_cases a <;> simp [vec4]
  have hleft :
      Tensor0SSpace.eval
          (lowerTri (I := I) (metricTensorField (I := I) g x)
            (riemannOp (metricCov (I := I) g) x)) v =
        g.inner x ((((riemannOp (metricCov (I := I) g) x) (v 0)) (v 1)) (v 2)) (v 3) := by
    rw [lowerTri_apply, metricTensorField_eval]
    simp
  calc
    Tensor0SSpace.eval
        (lowerTri (I := I) (metricTensorField (I := I) g x)
          (riemannOp (metricCov (I := I) g) x)) v =
        g.inner x ((((riemannOp (metricCov (I := I) g) x) (v 0)) (v 1)) (v 2)) (v 3) := hleft
    _ = Tensor0SSpace.eval (metricRm04At (I := I) g x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) :=
      (metricRm04At_inner (I := I) g x (v 0) (v 1) (v 2) (v 3)).symm
    _ = Tensor0SSpace.eval (metricRm04At (I := I) g x) v :=
      congrArg (Tensor0SSpace.eval (metricRm04At (I := I) g x)) hv

omit [SigmaCompactSpace M] in
theorem ricciDrift_sub (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    ricciDrift04 (I := I) g₁ x - ricciDrift04 (I := I) g₂ x =
      driftSlots (I := I)
        (lowerTri (I := I)
          (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
          (riemannOp (metricCov (I := I) g₁) x)) +
      driftSlots (I := I)
        (lowerTri (I := I) (metricRicciAt (I := I) g₂ x)
          (rmDiffVec (I := I) g₁ g₂ x)) := by
  rw [ricciDrift04, ricciDrift04, driftSlots_sub, lowerTri_split, driftSlots_add]
  rfl

variable [NeZero (Module.finrank Real E)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDriftSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 4
        (ricciDrift04 (I := I) g₁ x - ricciDrift04 (I := I) g₂ x) ≤
      32 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x) +
        normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x) := by
  let U : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowerTri (I := I)
      (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
      (riemannOp (metricCov (I := I) g₁) x)
  let V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowerTri (I := I) (metricRicciAt (I := I) g₂ x)
      (rmDiffVec (I := I) g₁ g₂ x)
  have hU0 := lowerTriSq_le (I := I) g₁
    (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
    (riemannOp (metricCov (I := I) g₁) x)
  have hV0 := lowerTriSq_le (I := I) g₁
    (metricRicciAt (I := I) g₂ x)
    (rmDiffVec (I := I) g₁ g₂ x)
  have hU : normSq0S (I := I) g₁ x 4 (driftSlots (I := I) U) ≤
      16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x)) := by
    refine (driftSlotsSq_le (I := I) g₁ U).trans ?_
    rw [lowerRm_eq_rm04] at hU0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hU0 (by norm_num : (0 : Real) ≤ 16)
  have hV : normSq0S (I := I) g₁ x 4 (driftSlots (I := I) V) ≤
      16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x) := by
    refine (driftSlotsSq_le (I := I) g₁ V).trans ?_
    rw [← rmDiffLowAt_eq_lowerTri, ← rmDiffSq_def] at hV0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hV0 (by norm_num : (0 : Real) ≤ 16)
  have houter := normSq0S_add_le (I := I) g₁ x 4
    (driftSlots (I := I) U) (driftSlots (I := I) V)
  rw [ricciDrift_sub]
  change normSq0S (I := I) g₁ x 4
      (driftSlots (I := I) U + driftSlots (I := I) V) ≤ _
  calc
    normSq0S (I := I) g₁ x 4
        (driftSlots (I := I) U + driftSlots (I := I) V) ≤
      2 * normSq0S (I := I) g₁ x 4 (driftSlots (I := I) U) +
        2 * normSq0S (I := I) g₁ x 4 (driftSlots (I := I) V) := houter
    _ ≤
      2 * (16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x))) +
      2 * (16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hU (by norm_num))
          (mul_le_mul_of_nonneg_left hV (by norm_num))
    _ = _ := by ring

end Core

section Components

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDrift_low
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    lowOfComp (I := I) g basis
        (fun i j k l =>
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis i) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis p) (basis j) (basis k) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis j) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis p) (basis k) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis k) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis j) (basis p) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis p)))) =
      ricciDrift04 (I := I) g x := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  exact ricciDrift_comp (I := I) g basis gInv hinv i j k l

end Components

end DifferentialGeometry.PDE.RicciFlow
