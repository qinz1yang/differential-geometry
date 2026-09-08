import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable local instance twoFormExteriorImageFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite

private theorem twoFormMetricData_inner_pullback_musical
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (g : SmoothRiemannianMetric I M) (x : M)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫)
    (u v : ⋀[ℝ]^2 F) :
    (twoFormMetricData g x).inner
      (ι.continuousAlternatingMapCongrLeft (exteriorPower.musicalEquiv 2 u))
      (ι.continuousAlternatingMapCongrLeft (exteriorPower.musicalEquiv 2 v)) =
      2 * ⟪u, v⟫ := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let b' := b.toBasis.map ι.toLinearEquiv
  have horth : ∀ i j, g.inner x (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    exact (hmetric (b i) (b j)).trans (b.inner_eq_ite i j)
  rw [twoFormMetricData_inner, Tensor0SBundle.inner0S_identity_eq_sum g x 2 b'
    (metricInverseInBasis_identity_of_orthonormal g b' horth)]
  have hs := exteriorPower.sum_mul_eq_factorial_mul_inner 2 b
    (exteriorPower.musicalEquiv 2 u) (exteriorPower.musicalEquiv 2 v)
  norm_num only [ContinuousLinearEquiv.symm_apply_apply, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_one] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [component0S_apply, twoFormTensorAt_apply]
  change (exteriorPower.musicalEquiv 2 u) (fun i => ι.symm (b' (j i))) *
    (exteriorPower.musicalEquiv 2 v) (fun i => ι.symm (b' (j i))) = _
  simp only [b', Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply, OrthonormalBasis.coe_toBasis]

theorem map_traceNormalizedCurvatureEndomorphism_range
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ F = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (C : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
      (C : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StdAt (C : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StdAt
        congr 1
        ext k
        fin_cases k <;> rfl
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp C.property
    Submodule.map
      (((exteriorPower.musicalEquiv (E := F) 2).trans
        (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))).toLinearMap)
      (exteriorPower.traceNormalizedCurvatureEndomorphism
        (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
        (hT.compContinuousLinearMap ι.toContinuousLinearMap)).range =
      curvatureOperatorImageAt g x C := by
  intro T hT
  let e := (exteriorPower.musicalEquiv (E := F) 2).trans
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
  let R := exteriorPower.traceNormalizedCurvatureEndomorphism
    (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
    (hT.compContinuousLinearMap ι.toContinuousLinearMap)
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    e.toLinearEquiv.finiteDimensional
  have hker : Submodule.map e.toLinearMap R.ker = curvatureOperatorKernelAt g x C :=
    map_traceNormalizedCurvatureEndomorphism_ker hdim g x C ι hmetric
  have hincl : Submodule.map e.toLinearMap R.range ≤ curvatureOperatorImageAt g x C := by
    rintro a ⟨u, ⟨v, rfl⟩, rfl⟩
    rw [curvatureOperatorImageAt_eq_orthogonal_kernel]
    rw [MetricFiberData.mem_orthogonal]
    intro b hb
    rw [← hker] at hb
    obtain ⟨w, hw, rfl⟩ := hb
    have hzero : R w = 0 := hw
    change (twoFormMetricData g x).inner (e w) (e (R v)) = 0
    have hip : (twoFormMetricData g x).inner (e w) (e (R v)) = 2 * ⟪w, R v⟫ :=
      twoFormMetricData_inner_pullback_musical g x ι hmetric w (R v)
    rw [hip]
    have hsym := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric
      (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
      (hT.compContinuousLinearMap ι.toContinuousLinearMap) w v
    change ⟪R w, v⟫ = ⟪w, R v⟫ at hsym
    rw [← hsym, hzero, inner_zero_left, mul_zero]
  apply Submodule.eq_of_le_of_finrank_eq hincl
  rw [LinearEquiv.finrank_map_eq e.toLinearEquiv]
  exact traceNormalizedCurvatureEndomorphism_pullback_finrank_range hdim g x C ι hmetric

theorem map_traceNormalizedCurvatureEndomorphism_range_contractionAnnihilator
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ F = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (C : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
      (C : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StdAt (C : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StdAt
        congr 1
        ext k
        fin_cases k <;> rfl
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp C.property
    Submodule.map ι.toLinearMap
      (ContinuousAlternatingMap.contractionAnnihilator
        (Submodule.map (exteriorPower.musicalEquiv (E := F) 2).toLinearMap
          (exteriorPower.traceNormalizedCurvatureEndomorphism
            (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
            (hT.compContinuousLinearMap ι.toContinuousLinearMap)).range)) =
      curvatureOperatorImageAnnihilatorAt g x C := by
  intro T hT
  apply ContinuousAlternatingMap.map_contractionAnnihilator_of_map_eq
  rw [← Submodule.map_comp]
  exact map_traceNormalizedCurvatureEndomorphism_range hdim g x C ι hmetric

theorem mem_curvatureOperatorImageAnnihilatorAt_pullback_musical_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : Module.finrank ℝ F = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (C : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hmetric : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫) :
    let T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
      (C : Tensor04At (I := I) (M := M) x)
    let hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d]) := by
      have heq : tensor04StdAt (C : Tensor04At (I := I) (M := M) x) =
          fun a b c d => T ![a, b, c, d] := by
        funext a b c d
        unfold tensor04StdAt
        congr 1
        ext k
        fin_cases k <;> rfl
      rw [← heq]
      exact mem_algebraicCurvatureTensorSubmodule.mp C.property
    ∀ v : F,
      ι v ∈ curvatureOperatorImageAnnihilatorAt g x C ↔
        v ∈ ContinuousAlternatingMap.contractionAnnihilator
          (Submodule.map (exteriorPower.musicalEquiv (E := F) 2).toLinearMap
            (exteriorPower.traceNormalizedCurvatureEndomorphism
              (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
              (hT.compContinuousLinearMap ι.toContinuousLinearMap)).range) := by
  intro T hT v
  rw [← map_traceNormalizedCurvatureEndomorphism_range_contractionAnnihilator
    hdim g x C ι hmetric]
  constructor
  · rintro ⟨u, hu, heq⟩
    have : u = v := ι.injective heq
    simpa [this] using hu
  · intro hv
    exact ⟨v, hv, rfl⟩


end DifferentialGeometry.Geometry.Curvature
