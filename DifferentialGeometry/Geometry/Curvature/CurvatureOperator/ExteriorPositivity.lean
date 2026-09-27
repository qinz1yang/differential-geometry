import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

namespace exteriorPower

open DifferentialGeometry.Geometry.Curvature
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem exists_sum_smul_wedge (z : ⋀[ℝ]^2 E) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → E),
      ∑ i, c i • ιMulti ℝ 2 ![v i, w i] = z := by
  classical
  have hz : z ∈ Submodule.span ℝ ((ιMulti ℝ 2 (M := E)) '' Set.univ) := by
    rw [Set.image_univ, ιMulti_span]
    trivial
  obtain ⟨t, _, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).mp hz
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, c ∘ e, fun i => (e i).val 0, fun i => (e i).val 1, ?_⟩
  calc
    ∑ i, (c ∘ e) i • ιMulti ℝ 2 ![(e i).val 0, (e i).val 1] =
        ∑ i, c (e i) • ιMulti ℝ 2 (e i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      ext j
      fin_cases j <;> rfl
    _ = ∑ i, c i • ιMulti ℝ 2 i.val := e.sum_comp (fun i : t => c i • ιMulti ℝ 2 i.val)
    _ = z := hc

private theorem inner_traceNormalizedCurvatureEndomorphism_sum_wedge
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]))
    {n : ℕ} (c : Fin n → ℝ) (v w : Fin n → E) :
    ⟪traceNormalizedCurvatureEndomorphism T hT (∑ i, c i • ιMulti ℝ 2 ![v i, w i]),
      ∑ i, c i • ιMulti ℝ 2 ![v i, w i]⟫ =
      2 * ∑ i, ∑ j, c i * c j * T ![v i, w i, w j, v j] := by
  rw [map_sum, sum_inner]
  simp only [map_smul, inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_traceNormalizedCurvatureEndomorphism_ιMulti,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem traceNormalizedCurvatureEndomorphism_isPositive_iff
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    (traceNormalizedCurvatureEndomorphism T hT).toLinearMap.IsPositive ↔
      ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → E),
        0 ≤ ∑ i, ∑ j, c i * c j * T ![v i, w i, w j, v j] := by
  constructor
  · intro h n c v w
    have hnonneg := h.inner_nonneg_left (∑ i, c i • ιMulti ℝ 2 ![v i, w i])
    change 0 ≤ ⟪traceNormalizedCurvatureEndomorphism T hT _, _⟫ at hnonneg
    rw [inner_traceNormalizedCurvatureEndomorphism_sum_wedge] at hnonneg
    linarith
  · intro h
    apply (LinearMap.isPositive_iff _).mpr
    refine ⟨traceNormalizedCurvatureEndomorphism_isSymmetric T hT, ?_⟩
    intro z
    obtain ⟨n, c, v, w, rfl⟩ := exists_sum_smul_wedge z
    change 0 ≤ ⟪traceNormalizedCurvatureEndomorphism T hT _, _⟫
    rw [inner_traceNormalizedCurvatureEndomorphism_sum_wedge]
    exact mul_nonneg (by norm_num) (h n c v w)

end exteriorPower

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
private theorem tensor04StdAt_eq_apply {x : M}
    (A : Tensor04At (I := I) (M := M) x) (a b c d : TangentSpace I x) :
    tensor04StandardAt A a b c d = A ![a, b, c, d] := by
  unfold tensor04StandardAt
  congr 1
  ext k
  fin_cases k <;> rfl

theorem traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
    {x : M} (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (ι : F →L[ℝ] TangentSpace I x) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := (A : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StandardAt (A : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        exact tensor04StdAt_eq_apply _ a b c d
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp A.property
    (exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => ι))
      (hT.compContinuousLinearMap ι)).toLinearMap.IsPositive := by
  intro T hT
  apply (exteriorPower.traceNormalizedCurvatureEndomorphism_isPositive_iff _ _).mpr
  intro n c v w
  have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hA n c
    (fun i => ι (v i)) (fun i => ι (w i))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change (A : Tensor04At (I := I) (M := M) x)
    (fun k => ι (![v i, w i, w j, v j] k)) =
      (A : Tensor04At (I := I) (M := M) x)
        (vec4 (ι (v i)) (ι (w i)) (ι (w j)) (ι (v j)))
  congr 1
  ext k
  fin_cases k <;> rfl

theorem traceNormalizedCurvatureEndomorphism_pullback_isPositive_iff_mem_nonnegativeCone
    {x : M} (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := (A : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StandardAt (A : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        exact tensor04StdAt_eq_apply _ a b c d
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp A.property
    (exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
      (hT.compContinuousLinearMap ι.toContinuousLinearMap)).toLinearMap.IsPositive ↔
        A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  intro T hT
  constructor
  · intro h
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have hnonneg := (exteriorPower.traceNormalizedCurvatureEndomorphism_isPositive_iff _ _).mp h
      n c (fun i => ι.symm (v i)) (fun i => ι.symm (w i))
    convert hnonneg using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [tensor04StdAt_eq_apply]
    change (A : Tensor04At (I := I) (M := M) x) ![v i, w i, w j, v j] =
      (A : Tensor04At (I := I) (M := M) x)
        (fun k => ι (![ι.symm (v i), ι.symm (w i), ι.symm (w j), ι.symm (v j)] k))
    congr 1
    ext k
    fin_cases k <;> simp
  · intro h
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      A h ι.toContinuousLinearMap


theorem traceNormalizedCurvatureEndomorphism_metric_pullback_isPositive
    [T2Space M] (g : SmoothRiemannianMetric I M) (x : M)
    (hR : (⟨metricRm04At g x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (ι : F →L[ℝ] TangentSpace I x) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ := metricRm04At g x
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      exact mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    (exteriorPower.traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => ι))
      (hT.compContinuousLinearMap ι)).toLinearMap.IsPositive := by
  exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
    ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ hR ι

end DifferentialGeometry.Geometry.Curvature
