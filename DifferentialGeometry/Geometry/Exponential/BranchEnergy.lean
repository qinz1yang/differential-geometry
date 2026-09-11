import DifferentialGeometry.Geometry.Exponential.Inverse.Radius
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem branchEnergy_eikonal
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {q : M} (hq : q ∈ B.dom) :
    g.inner q (gradientFun g (branchEnergy g B) q) (gradientFun g (branchEnergy g B) q) =
      2 * branchEnergy g B q := by
  let u := (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q)
  have hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source := by
    dsimp only [u]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact B.hom.map_target hq
  have hqexp : expMapIntrinsic g hEnorm p u = q := B.right_inv hq
  have hgrad := grad_branchEnergy B hu
  have hspeed := intrinsicGeodesic_speedSq_eq g hEnorm p u 1
  have hnorm : g.inner (expMapIntrinsic g hEnorm p u)
      (gradientFun g (branchEnergy g B) (expMapIntrinsic g hEnorm p u))
      (gradientFun g (branchEnergy g B) (expMapIntrinsic g hEnorm p u)) = g.inner p u u := by
    rw [hgrad]
    exact hspeed
  have h := branchEnergy_exp B hu
  rw [hqexp] at hnorm h
  rw [hnorm, h]
  ring

theorem hasDerivAt_comp_intrinsicGeodesic
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {u : TangentSpace I p}
    (hu : tangentSpaceModelContinuousLinearEquiv (I := I) p u ∈ B.hom.source)
    {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (expMapIntrinsic g hEnorm p u)) :
    HasDerivAt (fun t : ℝ => f (intrinsicGeodesic g hEnorm p u t))
      (g.inner (expMapIntrinsic g hEnorm p u)
        (gradientFun g f (expMapIntrinsic g hEnorm p u))
        (gradientFun g (branchEnergy g B) (expMapIntrinsic g hEnorm p u))) 1 := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (intrinsicGeodesic g hEnorm p u) 1 :=
    ((intrinsicGeodesic_contMDiffOn g hEnorm p u).contMDiffAt
      Filter.univ_mem).mdifferentiableAt one_ne_zero
  have h := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I f
    (intrinsicGeodesic g hEnorm p u) 1 hf hγ
  apply h.congr_deriv
  rw [inner_gradientFun, grad_branchEnergy B hu]
  rfl

end DifferentialGeometry.Geometry.Riemannian.Exponential
