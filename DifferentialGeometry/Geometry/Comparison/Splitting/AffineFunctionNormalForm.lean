import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionFlow
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FixedBasePartialDiffeomorph
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
theorem affineFunction_differential_surjective
    (g : SmoothRiemannianMetric I M) (b : M → ℝ)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) : Function.Surjective (mvfderiv (I := I) b p) := by
  have hL : mvfderiv (I := I) b p (gradientFun (I := I) g b p) = 1 :=
    (inner_gradientFun (I := I) g b p (gradientFun (I := I) g b p)).symm.trans (hunit p)
  intro a
  refine ⟨a • gradientFun (I := I) g b p, ?_⟩
  rw [map_smul, hL]
  exact mul_one a

omit [I.Boundaryless] in
theorem affineFunction_kernel_finrank
    (g : SmoothRiemannianMetric I M) (b : M → ℝ)
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) : Module.finrank ℝ (mvfderiv (I := I) b p).ker + 1 = Module.finrank ℝ E := by
  let L : E →L[ℝ] ℝ := mvfderiv (I := I) b p
  change Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E
  have hrange : LinearMap.range L.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (affineFunction_differential_surjective (I := I) g b hunit p)
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  erw [hrange, finrank_top, Module.finrank_self] at h
  exact (Nat.add_comm _ 1).trans h

end Local

variable [NeZero (Module.finrank ℝ E)]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem affineFunction_comp_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (v : TangentSpace I p) (t : ℝ) :
    b (intrinsicGeodesic (I := I) g hEnorm p v t) =
      b p + t * mvfderiv (I := I) b p v := by
  let c := intrinsicGeodesic (I := I) g hEnorm p v
  let K := mvfderiv (I := I) b p v
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c := intrinsicGeodesic_contMDiff (I := I) g hEnorm p v
  have hgeo : IsGeodesic (I := I) g c := intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hbc : ContDiff ℝ ∞ (b ∘ c) := contMDiff_iff_contDiff.mp (hb.comp hc)
  have hsecond (s : ℝ) : deriv (deriv (b ∘ c)) s = 0 := by
    have h := deriv2_comp_geo_on (I := I) g isOpen_univ hb.contMDiffOn hc hgeo
      (t := s) (mem_univ (c s))
    change deriv (deriv (b ∘ c)) s = hessFun (I := I) g b (c s)
      (mfderiv 𝓘(ℝ, ℝ) I c s 1) (mfderiv 𝓘(ℝ, ℝ) I c s 1) at h
    simpa only [hH, LinearMap.zero_apply] using h
  have hfirst0 : deriv (b ∘ c) 0 = K := by
    have hd := deriv_comp_mfderiv_along I b c 0
      (hb.mdifferentiable (by simp) (c 0)) (hc.mdifferentiable (by simp) 0)
    change deriv (b ∘ c) 0 = mvfderiv (I := I) b (c 0)
      (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E) at hd
    have hv : @Eq E (mfderiv 𝓘(ℝ, ℝ) I c 0 1) v :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
    have hc0 : c 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
    have hvalue : mvfderiv (I := I) b (c 0) v = mvfderiv (I := I) b p v :=
      congrArg (fun q => (mvfderiv (I := I) b q : E →L[ℝ] ℝ) v) hc0
    exact hd.trans ((congrArg (fun u : E => mvfderiv (I := I) b (c 0) u) hv).trans hvalue)
  have hfirst (s : ℝ) : deriv (b ∘ c) s = K :=
    (is_const_of_deriv_eq_zero
      ((ContDiff.iterate_deriv 1 hbc).differentiable (by simp)) hsecond s 0).trans hfirst0
  have hd (s : ℝ) : HasDerivAt (b ∘ c) K s := by
    have h := (hbc.differentiable (by simp) s).hasDerivAt
    rw [hfirst] at h
    exact h
  have hz (s : ℝ) : HasDerivAt (fun r => b (c r) - r * K) 0 s := by
    simpa only [Function.comp_apply, one_mul, sub_self] using!
      (hd s).sub ((hasDerivAt_id s).mul_const K)
  have hconst := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  change b (c t) - t * K = b (c 0) - 0 * K at hconst
  have hc0 : c 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  rw [hc0, zero_mul, sub_zero] at hconst
  exact sub_eq_iff_eq_add.mp hconst

theorem affineFunction_expMapIntrinsic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p : M) (v : TangentSpace I p) :
    b (expMapIntrinsic (I := I) g hEnorm p v) = b p + mvfderiv (I := I) b p v := by
  have h := affineFunction_comp_intrinsicGeodesic (I := I) g hEnorm hb hH p v 1
  rw [one_mul] at h
  exact h

theorem affineFunction_normalCoordinate_formula
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p q : M)
    (hq : q ∈ (standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.target) :
    b q = b p + mvfderiv (I := I) b p ((standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.symm q) := by
  have h := affineFunction_expMapIntrinsic (I := I) g hEnorm hb hH p
    ((standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.symm q)
  have hexp : expMapIntrinsic (I := I) g hEnorm p
      ((standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.symm q) = q :=
    (standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.right_inv hq
  rw [hexp] at h
  exact h

theorem affineFunction_normalCoordinate_level_iff
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hH : ∀ p, hessFun (I := I) g b p = 0) (p q : M)
    (hq : q ∈ (standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.target) :
    b q = b p ↔ (standardDiagonalInverseBranch (I := I) g hEnorm p).fixedBasePartialDiffeomorph.symm q ∈
      (mvfderiv (I := I) b p).ker := by
  rw [affineFunction_normalCoordinate_formula (I := I) g hEnorm hb hH p q hq]
  exact add_eq_left

end DifferentialGeometry.Geometry.Topology

end
