import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.OverlapBindings
import DifferentialGeometry.Geometry.Fibration.RiemannianOverlapConsumers

/-!
# FC19 on actual Riemannian manifolds from AC76's compatibility witness

Blueprint `master207B.tex`, FC19 (`lem:fibration-common-endpoints`, B:1293–1347) and its binding
paragraph (B:1363–1371: "AC79 and AC76 provide the recentering and metric compatibility route …
aligned with a SINGLE isometry to obtain `A, b₀, E` uniformly on the enlarged radius-`H` domain").

`centered_affine_c1_of_splittingCompatible`: on a complete connected Riemannian manifold, a rank-`j`
map `φ` that is `τ`-compatible with a rank-`k` map `ψ` at `p` (AC76's output) and `C¹` coordinates
`F, G` satisfying the ORIGINAL adapted tests against `φ₁, ψ₁` along every minimizing direction give
ONE coisometry `Λ` such that `F − (Λ G + b)` is `C¹`-small on `B(p,L)` (`b = F(p) − Λ G(p)`), with
FC19's constant `2 max(1,L) √(j(4ε' + ε'²))`, `ε' = α + (9ε + 2(1 + 24 j)τ)/(s − 6ε)`. The metric
step is `norm_sub_comp_le_of_splittingCompatible_common_endpoints`; the integration is the existing
`centered_affine_c1_of_mfderiv_bound`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Fibration

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  [CompleteSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **FC19 with AC76's compatibility data, on actual manifolds.** -/
theorem centered_affine_c1_of_splittingCompatible {j k : ℕ} {A B : Type*} [MetricSpace A]
    [MetricSpace B] (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin j)) (G : M → EuclideanSpace ℝ (Fin k))
    {p : M} {a₀ : A} {b₀ : B} {δ₁ ε τ a L T s H₀ α : ℝ}
    (φ : GC.MetricGeometry.KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) δ₁)
    (ψ : GC.MetricGeometry.KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : GC.MetricGeometry.SplittingCompatible φ ψ τ) (ha0 : 0 < a)
    (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) (hHτ : H₀ ≤ τ⁻¹) (hHε : H₀ ≤ ε⁻¹)
    (hHa : H₀ + ε ≤ a) (hL : 0 < L) (hT : 0 ≤ T) (hα : 0 ≤ α) (hs : T + 2 * (3 * ε) < s)
    (hH : L + s + 3 * (3 * ε) < H₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin j)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ i : Fin j,
      ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + α)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I F x w - (dist x y)⁻¹ • ((φ.toFun y).fst - (φ.toFun x).fst)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I G x w - (dist x y)⁻¹ • ((ψ.toFun y).fst - (ψ.toFun x).fst)‖ ≤ α) :
    ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x ∈ ball p H₀, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ (1 + 24 * j) * τ) ∧
      ∀ x ∈ ball p L,
        max ‖F x - (Λ (G x) + (F p - Λ (G p)))‖ ‖mvfderiv I F x - Λ.comp (mvfderiv I G x)‖ ≤
          max 1 L * (2 * Real.sqrt (j * (4 * (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) /
            (s - 2 * (3 * ε))) + (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) /
              (s - 2 * (3 * ε))) ^ 2))) := by
  obtain ⟨Λ, b, hΛ, hval, hd⟩ :=
    GC.MetricGeometry.norm_sub_comp_le_of_splittingCompatible_common_endpoints
      (TX := fun x : M => TangentSpace I x) φ ψ hcomp ha0 ha ha2 hHτ hHε hHa hT hα hs hH
      (minimizingInitialDirections g hmetric) (minimizingInitialDirections_nonempty g hmetric)
      (fun _x _y _w hw => hw.1) (mvfderiv I F) (mvfderiv I G) hDF hDG htestF htestG
  refine ⟨Λ, b, hΛ, hval, ?_⟩
  have hh := centered_affine_c1_of_mfderiv_bound g hmetric F G Λ p hL
    (c := 2 * Real.sqrt (j * (4 * (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) /
      (s - 2 * (3 * ε))) + (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) /
        (s - 2 * (3 * ε))) ^ 2))) (by positivity) hF hG hd
  dsimp only at hh
  exact fun x hx => (hh x hx).2

end DifferentialGeometry.Geometry.Fibration
