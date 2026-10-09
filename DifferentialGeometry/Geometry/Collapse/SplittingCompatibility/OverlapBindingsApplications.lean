import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RiemannianOverlapBindings
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RiemannianUniformCompatibility
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# Consumers: the AC76 producer feeding the FC23 and FC19 bindings on actual manifolds

* `exists_overlap_comparison_parameter_riemannian` (consumer of
  `exists_coisometry_overlap_comparison_of_splittingCompatible` and of the Riemannian AC76 producer):
  there is `σ` such that at every point of a complete Riemannian manifold with sectional curvature
  `≥ −σ` on `B(p, σ⁻¹)` and no `(k+1, ν)`-splitting, any two normalized splittings of error `σ`
  and ranks `j ≤ k` satisfy FC23's conclusion (one coisometry, value error `τ + 24 j τ` on the short
  buffer, FC22 derivative comparison on the tested domain) under the packet's own tests.
* `exists_centered_affine_c1_parameter_riemannian` (consumer of
  `centered_affine_c1_of_splittingCompatible`, which consumes
  `norm_sub_comp_le_of_splittingCompatible_common_endpoints`): the same `σ` gives FC19's `C¹`
  comparison of the original adapted coordinates on actual manifolds.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff InnerProductSpace ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

section FC23

namespace GC.MetricGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]
  {T : M → Type v} [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
  [∀ x, CompleteSpace (T x)]

/-- FC23 with AC76's compatibility produced on an actual manifold. -/
theorem exists_overlap_comparison_parameter_riemannian (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ Module.finrank ℝ E)
    {τ ν a : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1)
    (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B)
        (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) σ)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) σ)
        (S D : Set M), S ⊆ ball p τ⁻¹ → (∀ x ∈ S, ‖(ψ.toFun x).fst‖ ≤ a) →
      ∀ (dF : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin j))
        (dG : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin k)) {αF αG ℓ₀ t β δ : ℝ},
        0 ≤ αF → 0 < ℓ₀ → 0 < t → 0 ≤ β → 0 ≤ δ →
        (∀ x ∈ D, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1 + αF) →
        (∀ x ∈ D, ‖dG x‖ ≤ 1 + αG) → D ⊆ S →
        (∀ x ∈ D, ∀ i : Fin j, ∃ w : T x, ‖w‖ = 1 ∧ ∃ y z : M, ∃ ℓ : ℝ, ℓ₀ ≤ ℓ ∧ z ∈ S ∧
          ℓ - β ≤ (φ.toFun y).fst i - (φ.toFun x).fst i ∧
          (φ.toFun y).fst i - (φ.toFun z).fst i ≤ ℓ - t + δ ∧
          |dF x w i - ((φ.toFun y).fst i - (φ.toFun x).fst i) / ℓ| ≤ αF ∧
          ‖dG x w - t⁻¹ • ((ψ.toFun z).fst - (ψ.toFun x).fst)‖ ≤ αG) →
        ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
          Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x ∈ S, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ τ + 24 * j * τ) ∧
          ∀ x ∈ D, ‖dF x - Λ.comp (dG x)‖ ≤ 2 * Real.sqrt (j * (4 * max (αF + β / ℓ₀)
            (αG + (β + δ + 2 * (τ + 24 * j * τ)) / t) +
              max (αF + β / ℓ₀) (αG + (β + δ + 2 * (τ + 24 * j * τ)) / t) ^ 2)) := by
  obtain ⟨σ, hσ, hσone, hprop⟩ :=
    exists_splitting_compatibility_parameter_riemannian.{u} (I := I) hj hjk hkn hτ hτone hν hνone
  refine ⟨σ, hσ, hσone, fun p hsec hno A B _ _ a₀ b₀ φ ψ S D hS hSa dF dG αF αG ℓ₀ t β δ
    hαF hℓ₀ ht hβ hδ hF hG hDS htests => ?_⟩
  exact exists_coisometry_overlap_comparison_of_splittingCompatible φ ψ
    (hprop M g hmetric p hsec hno A B a₀ b₀ φ ψ) S D ha0 ha ha2 hS hSa dF dG hαF hℓ₀ ht hβ hδ
    hF hG hDS htests

end GC.MetricGeometry

end FC23

section FC19

namespace DifferentialGeometry.Geometry.Fibration

variable {E : Type uE} {H : Type uH} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  [CompleteSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- FC19's `C¹` comparison with AC76's compatibility produced on the actual manifold. -/
theorem exists_centered_affine_c1_parameter_riemannian (g : SmoothRiemannianMetric I M)
    (hmetric : IsMetricNorm g) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ Module.finrank ℝ E)
    {τ ν a : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1)
    (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (GC.MetricGeometry.KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B)
        (φ : GC.MetricGeometry.KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) σ)
        (ψ : GC.MetricGeometry.KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) σ)
        (F : M → EuclideanSpace ℝ (Fin j)) (G : M → EuclideanSpace ℝ (Fin k))
        {L T s H₀ α : ℝ}, H₀ ≤ τ⁻¹ → H₀ ≤ σ⁻¹ → H₀ + σ ≤ a → 0 < L → 0 ≤ T → 0 ≤ α →
        T + 2 * (3 * σ) < s → L + s + 3 * (3 * σ) < H₀ →
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin j)) 1 F (ball p L) →
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 G (ball p L) →
        (∀ x ∈ ball p L, ∀ i : Fin j,
          ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + α) →
        (∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + α) →
        (∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
          ∀ w ∈ minimizingInitialDirections g hmetric x y,
            ‖mvfderiv I F x w - (dist x y)⁻¹ • ((φ.toFun y).fst - (φ.toFun x).fst)‖ ≤ α) →
        (∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
          ∀ w ∈ minimizingInitialDirections g hmetric x y,
            ‖mvfderiv I G x w - (dist x y)⁻¹ • ((ψ.toFun y).fst - (ψ.toFun x).fst)‖ ≤ α) →
        ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
          Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x ∈ ball p H₀, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ (1 + 24 * j) * τ) ∧
          ∀ x ∈ ball p L,
            max ‖F x - (Λ (G x) + (F p - Λ (G p)))‖
              ‖mvfderiv I F x - Λ.comp (mvfderiv I G x)‖ ≤
              max 1 L * (2 * Real.sqrt (j * (4 * (α + (3 * (3 * σ) + 2 * ((1 + 24 * j) * τ)) /
                (s - 2 * (3 * σ))) + (α + (3 * (3 * σ) + 2 * ((1 + 24 * j) * τ)) /
                  (s - 2 * (3 * σ))) ^ 2))) := by
  obtain ⟨σ, hσ, hσone, hprop⟩ :=
    GC.MetricGeometry.exists_splitting_compatibility_parameter_riemannian.{u} (I := I)
      hj hjk hkn hτ hτone hν hνone
  refine ⟨σ, hσ, hσone, fun p hsec hno A B _ _ a₀ b₀ φ ψ F G L T s H₀ α hHτ hHσ hHa hL hT hα
    hs hH hF hG hDF hDG htestF htestG => ?_⟩
  exact centered_affine_c1_of_splittingCompatible g hmetric F G φ ψ
    (hprop M g (DifferentialGeometry.Geometry.Collapse.riemannianEDistOf_eq_ofReal_dist g hmetric)
      p hsec hno A B a₀ b₀ φ ψ)
    ha0 ha ha2 hHτ hHσ hHa hL hT hα hs hH hF hG hDF hDG htestF htestG

end DifferentialGeometry.Geometry.Fibration

end FC19
