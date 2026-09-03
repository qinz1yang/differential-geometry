import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureActionZero

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

structure CurvatureActionParameters where
  rankTwo : ℝ
  rankThree : ℝ

noncomputable def curvatureActionParameters (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : CurvatureActionParameters where
  rankTwo := uniformPtCurvZeroC d Λ Kb₀ Kb₁
  rankThree := uniformPtCurvThreeC d Λ Kb₀ Kb₁

structure HasUniformCurvatureActionBounds
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters) : Prop where
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    IsCurvAction0 (I := I) (M := M) g 2 K.rankTwo ∧
      IsCurvAction0 (I := I) (M := M) g 3 K.rankThree

theorem has_uniform_curvature_action_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ
      (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  refine ⟨?_⟩
  intro g hEq hjet
  have hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ Λ * gBase.inner x v v :=
    fun x v => hEq.2 x (Set.mem_univ x) v
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  constructor
  · simpa only [curvatureActionParameters] using
      (uniformCurvAction0_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)
  · simpa only [curvatureActionParameters] using
      (uniformCurvAction3_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)

theorem exists_uniform_curvature_action_parameters
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : CurvatureActionParameters, HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K := by
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  exact ⟨curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁,
    has_uniform_curvature_action_bounds (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'⟩

noncomputable def convexH2C (K : CurvatureActionParameters) : ℝ :=
  h2CovsumC K.rankTwo

noncomputable def convexH3C (K : CurvatureActionParameters) : ℝ :=
  h3CovsumC K.rankTwo K.rankThree

structure ConvexJetConstants where
  h2C : ℝ
  h3C : ℝ

noncomputable def convexJetConstants (K : CurvatureActionParameters) : ConvexJetConstants where
  h2C := convexH2C K
  h3C := convexH3C K

structure HasUniformConvexPerturbationJetBounds
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (C : ConvexJetConstants) : Prop where
  h2_nonneg : 0 ≤ C.h2C
  h3_nonneg : 0 ≤ C.h3C
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.h2C * R) ^ 2) ∧
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.h3C * R) ^ 2)

private theorem convex_hs_norm_le
    (g : SmoothRiemannianMetric I M) (q : ℝ)
    (T T' : SmoothCcTensor g 0 2) {R s : ℝ} (_hR : 0 ≤ R)
    (hT : ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ ≤ R)
    (hT' : ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ ≤ R)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖ccTensorToHs (I := I) (M := M) g 2 q
      (convexPerturbation (I := I) g T T' s)‖ ≤ R := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  rw [show convexPerturbation (I := I) g T T' s =
      (1 - s) • T' + s • T from rfl,
    ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
  calc
    ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T' +
        s • ccTensorToHs (I := I) (M := M) g 2 q T‖
        ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          ‖s • ccTensorToHs (I := I) (M := M) g 2 q T‖ := norm_add_le _ _
    _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
      add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
        (mul_le_mul_of_nonneg_left hT hs0)
    _ = R := by ring

theorem convex_h23_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters)
    (hK : HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K) :
    HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ (convexJetConstants K) := by
  refine ⟨h2CovsumC_nonneg K.rankTwo,
    h3CovsumC_nonneg K.rankTwo K.rankThree, ?_⟩
  intro g hEq hjet
  obtain ⟨hact₂, hact₃⟩ := hK.bounds g hEq hjet
  constructor
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 2 T T' hR hT hT' hs
    have hsum := covsum_hs_two (I := I) (M := M) g 2 hact₂
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h2CovsumC K.rankTwo * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath (h2CovsumC_nonneg K.rankTwo))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 3 T T' hR hT hT' hs
    have hsum := covsum_hs_three (I := I) (M := M) g 2 hact₂ hact₃
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h3CovsumC K.rankTwo K.rankThree * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath
          (h3CovsumC_nonneg K.rankTwo K.rankThree))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)

theorem convex_jets_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters)
    (hK : HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K) :
    ∃ C : ConvexJetConstants, HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C :=
  ⟨convexJetConstants K, convex_h23_of_act (I := I) (M := M) gBase Λ K hK⟩

theorem uniform_convex_perturbation_sobolev_two_three_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ
      (convexJetConstants
        (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁)) := by
  exact convex_h23_of_act (I := I) (M := M) gBase Λ
    (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁)
    (has_uniform_curvature_action_bounds (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁)

theorem exists_convex_jets
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ConvexJetConstants, HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C := by
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  exact convex_jets_of_act (I := I) (M := M) gBase Λ K hK

end RicciFlow
end PDE
end DifferentialGeometry

end
