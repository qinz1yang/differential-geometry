import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section
open Bundle
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem pullback_musical_curvatureBivectorBasis
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (x : M) (ι : F ≃L[ℝ] TangentSpace I x) (b : OrthonormalBasis (Fin 3) ℝ F) (i : Fin 3) :
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
      (exteriorPower.musicalEquiv 2 (curvatureBivectorBasis b i)) =
    curvatureTwoFormBasisAt (b.toBasis.map ι.toLinearEquiv) i := by
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => b.toBasis.map ι.toLinearEquiv)
  intro v
  change (exteriorPower.musicalEquiv 2 (curvatureBivectorBasis b i))
      (fun k => ι.symm ((b.toBasis.map ι.toLinearEquiv) (v k))) = _
  simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply, OrthonormalBasis.coe_toBasis]
  change (exteriorPower.musicalEquiv 2 (curvatureBivectorBasis b i)) (fun k => b (v k)) =
    (curvatureTwoFormBasisAt (b.toBasis.map ι.toLinearEquiv) i) (fun k => ι (b (v k)))
  rw [curvatureBivectorBasis_apply, exteriorPower.musicalEquiv_ιMulti_apply,
    curvatureTwoFormBasisAt_apply, ContinuousAlternatingMap.elementaryCovector_apply]
  have hdual (j k : Fin 3) :
      ((b.toBasis.map ι.toLinearEquiv).cDualBasis j) (ι (b k)) = if j = k then 1 else 0 := by
    exact (b.toBasis.map ι.toLinearEquiv).cDualBasis_apply_self j k
  rw [← Matrix.det_transpose]
  congr 1
  ext j k
  change ⟪![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2] j, b (v k)⟫ = _
  rw [hdual]
  fin_cases i <;> fin_cases j <;> exact b.inner_eq_ite _ _

theorem curvatureOperatorPairingAt_pullback_musical
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
    ∀ u v : ⋀[ℝ]^2 F,
      curvatureOperatorPairingAt g x C
        (ι.continuousAlternatingMapCongrLeft (exteriorPower.musicalEquiv 2 u))
        (ι.continuousAlternatingMapCongrLeft (exteriorPower.musicalEquiv 2 v)) =
      ⟪exteriorPower.traceNormalizedCurvatureEndomorphism
          (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
          (hT.compContinuousLinearMap ι.toContinuousLinearMap) u, v⟫ := by
  intro T hT
  let b := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim)
  let b' := b.toBasis.map ι.toLinearEquiv
  let e := (exteriorPower.musicalEquiv (E := F) 2).trans
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
  let R := exteriorPower.traceNormalizedCurvatureEndomorphism
    (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
    (hT.compContinuousLinearMap ι.toContinuousLinearMap)
  have horth : OrthonormalBasisAt g x b' := by
    intro i j
    simpa only [b', Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
      ContinuousLinearEquiv.coe_toLinearEquiv, delta3] using
      (hmetric (b i) (b j)).trans (b.inner_eq_ite i j)
  have hb (i : Fin 3) : e (curvatureBivectorBasis b i) = curvatureTwoFormBasisAt b' i :=
    pullback_musical_curvatureBivectorBasis x ι b i
  have hbil : (curvatureOperatorBilinearAt g x C).compl₁₂ e.toLinearMap e.toLinearMap =
      (innerₗ (⋀[ℝ]^2 F)).comp R.toLinearMap := by
    apply (curvatureBivectorBasis b).toBasis.ext
    intro i
    apply (curvatureBivectorBasis b).toBasis.ext
    intro j
    change curvatureOperatorPairingAt g x C (e (curvatureBivectorBasis b i))
      (e (curvatureBivectorBasis b j)) = ⟪R (curvatureBivectorBasis b i), curvatureBivectorBasis b j⟫
    rw [hb, hb, curvatureOperatorPairingAt_curvatureTwoFormBasisAt g x b' horth C]
    dsimp only [R]
    rw [curvatureBivectorBasis_apply, curvatureBivectorBasis_apply,
      exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti]
    change 2 * (C : Tensor04At (I := I) (M := M) x)
        (vec4 (ι (b (bivectorIndex3 i).1)) (ι (b (bivectorIndex3 i).2))
          (ι (b (bivectorIndex3 j).2)) (ι (b (bivectorIndex3 j).1))) =
      2 * (C : Tensor04At (I := I) (M := M) x)
        (fun k => ι (![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2,
          b (bivectorIndex3 j).2, b (bivectorIndex3 j).1] k))
    congr 2
    ext k
    fin_cases k <;> rfl
  intro u v
  exact LinearMap.congr_fun (LinearMap.congr_fun hbil u) v

theorem traceNormalizedCurvatureEndomorphism_eq_zero_iff_mem_curvatureOperatorKernelAt
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
    ∀ u : ⋀[ℝ]^2 F,
      exteriorPower.traceNormalizedCurvatureEndomorphism
        (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
        (hT.compContinuousLinearMap ι.toContinuousLinearMap) u = 0 ↔
      ι.continuousAlternatingMapCongrLeft (exteriorPower.musicalEquiv 2 u) ∈
        curvatureOperatorKernelAt g x C := by
  intro T hT u
  let e := (exteriorPower.musicalEquiv (E := F) 2).trans
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
  let R := exteriorPower.traceNormalizedCurvatureEndomorphism
    (T.compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
    (hT.compContinuousLinearMap ι.toContinuousLinearMap)
  have hp (v w : ⋀[ℝ]^2 F) : curvatureOperatorPairingAt g x C (e v) (e w) = ⟪R v, w⟫ :=
    curvatureOperatorPairingAt_pullback_musical hdim g x C ι hmetric v w
  constructor
  · intro hu a
    obtain ⟨v, rfl⟩ := e.surjective a
    change curvatureOperatorPairingAt g x C (e u) (e v) = 0
    rw [hp, show R u = 0 from hu, inner_zero_left]
  · intro hu
    have hzero := hu (e (R u))
    change curvatureOperatorPairingAt g x C (e u) (e (R u)) = 0 at hzero
    rw [hp] at hzero
    exact inner_self_eq_zero.mp hzero

theorem map_traceNormalizedCurvatureEndomorphism_ker
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
        (hT.compContinuousLinearMap ι.toContinuousLinearMap)).ker =
      curvatureOperatorKernelAt g x C := by
  intro T hT
  let e := (exteriorPower.musicalEquiv (E := F) 2).trans
    (ι.continuousAlternatingMapCongrLeft (ι := Fin 2))
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (traceNormalizedCurvatureEndomorphism_eq_zero_iff_mem_curvatureOperatorKernelAt
      hdim g x C ι hmetric u).mp (LinearMap.mem_ker.mp hu)
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    apply LinearMap.mem_ker.mpr
    apply (traceNormalizedCurvatureEndomorphism_eq_zero_iff_mem_curvatureOperatorKernelAt
      hdim g x C ι hmetric (e.symm a)).mpr
    exact (e.apply_symm_apply a).symm ▸ ha

end DifferentialGeometry.Geometry.Curvature
