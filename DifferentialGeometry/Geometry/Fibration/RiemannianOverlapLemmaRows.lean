import DifferentialGeometry.Geometry.Fibration.RiemannianOverlapConsumers

/-!
# FC19 and FC22 as rows: common endpoints / asymmetric tests on a complete Riemannian manifold

Blueprint `master207B.tex`, FC19 (`lem:fibration-common-endpoints`, B:1293–1338) and FC22
(`lem:fibration-asymmetric-tests`, B:1451–1503). Both rows are LEMMAS; their kernels are Codex X86
`Fibration.centered_affine_c1_of_common_endpoints` and
`Fibration.centered_affine_c1_of_long_short_tests` (`RiemannianOverlapConsumers.lean`). The actual
bindings of FC22 on the final family are TCP03's edge / slim / zero blocks (`tcp03_edge_row`,
`tcp03_slim_row`, `tcp03_zero_row`), EGP04 and SGP03 (all accepted); its integration step on the
packets is `centered_c1_of_pointwise_derivative` (C14-FC19 G1). FC19's common-domain variant has
no consumer in the active route (PBR01 B:10061–10062, B:10250; audit B:10872–10874; FC22's note
B:1499–1503; TCP03's circle block re-runs the same argument pointwise), so no actual-overlap
binding is built for it.

* `fc19_row_RFC`: FC19 (distortion `≤ δ` and `δ`-coverage of `φ = (u, z)` on `B(p, H)`,
  `φ(p) = (0, z₀)`, `|Ψ − Au − b₀| ≤ E` on `B(p, H)`, `F, G` of class `C¹` on `B(p, L)`, the
  original tests along EVERY minimizing initial unit vector from `x ∈ B(p, L)` to `y ∈ B(p, H)`,
  `d(x, y) > T`): with `ε = α + (3δ + 2E)/(s − 2δ)`, `b = F(p) − AG(p)`, the value and derivative
  errors of `F − (AG + b)` on `B(p, L)` are at most `2 max(1, L) √(k(4ε + ε²))`.
* `fc22_row_RFC`: FC22 (minimizing unit-speed segment from `x` of length `ℓ = d(x, y) ≥ ℓ₀ > t > 0`,
  `y = γ(ℓ)`, `z = γ(t)`, `w = γ̇(0)`; the raw tests; `A`, `b₀` aligned at `x` and `z` only), same
  conclusion with `ε = max(α_F + β/ℓ₀, α_G + (β + δ + 2E)/t)`.
* Strengthenings: the unused hypotheses `1 ≤ k ≤ m`, `ε ≤ 1` (both rows) and `α_G ≥ 0` (FC22) are
  dropped; the verbatim forms are the two `example`s.
* Consumers `fc19_row_le_RFC`, `fc22_row_le_RFC`: under `ε ≤ 1` the bound is at most
  `2 max(1, L) √(5k)`.
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

/-- **FC22** (`lem:fibration-asymmetric-tests`, B:1451). On `D = B(p, L)` in a complete connected
Riemannian manifold, `F : D → ℝᵏ`, `G : D → ℝᵐ` of class `C¹` with `|dF_a| ≤ 1 + α_F`,
`‖DG‖ ≤ 1 + α_G`; for every `x ∈ D` and component `a` a minimizing unit-speed segment from `x` to
`y` (`ℓ = d(x, y) ≥ ℓ₀`) with short point `z = γ(t)`, `0 < t < ℓ₀`, the raw inequalities
`Ψ_a(y) − Ψ_a(x) ≥ ℓ − β`, `Ψ_a(y) − Ψ_a(z) ≤ ℓ − t + δ` and the tests
`|dF_a(w) − (Ψ_a(y) − Ψ_a(x))/ℓ| ≤ α_F`, `‖DG(w) − (u(z) − u(x))/t‖ ≤ α_G`; a coisometry `A`
and `b₀` with `|Ψ − Au − b₀| ≤ E` at `x` and at `z`. Then with
`ε = max(α_F + β/ℓ₀, α_G + (β + δ + 2E)/t)` and `b = F(p) − AG(p)`, at every `x ∈ D` both the value
and the derivative error of `F − (AG + b)` are at most `2 max(1, L) √(k(4ε + ε²))`. -/
theorem fc22_row_RFC {k m : ℕ}
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) {L αF αG ℓ₀ t β δ E₀ : ℝ}
    (hL : 0 < L) (hαF : 0 ≤ αF) (ht : t ∈ Ioo 0 ℓ₀)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + αF)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + αG)
    (halign : ∀ x ∈ ball p L, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (htests : ∀ x ∈ ball p L, ∀ a : Fin k,
      ∃ (y z : M) (w : TangentSpace I x),
        w ∈ minimizingInitialDirections g hmetric x y ∧
        z = intrinsicGeodesic g hmetric x w t ∧ ℓ₀ ≤ dist x y ∧
        ‖Ψ z - A (u z) - b₀‖ ≤ E₀ ∧
        dist x y - β ≤ Ψ y a - Ψ x a ∧
        Ψ y a - Ψ z a ≤ dist x y - t + δ ∧
        |mvfderiv I F x w a - (Ψ y a - Ψ x a) / dist x y| ≤ αF ∧
        ‖mvfderiv I G x w - t⁻¹ • (u z - u x)‖ ≤ αG) :
    let ε := max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t)
    let b := F p - A (G p)
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + b)‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) :=
  centered_affine_c1_of_long_short_tests g hmetric F G u Ψ A hA b₀ p hL hαF ht hβ hδ hE hF hG
    hDF hDG halign htests

/-- FC22 with the blueprint's hypotheses verbatim (`1 ≤ k ≤ m`, `α_G ≥ 0`, `ε ≤ 1` included). -/
example {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) {L αF αG ℓ₀ t β δ E₀ : ℝ}
    (hL : 0 < L) (hαF : 0 ≤ αF) (hαG : 0 ≤ αG) (ht : 0 < t) (htℓ : t < ℓ₀)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + αF)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + αG)
    (halign : ∀ x ∈ ball p L, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (htests : ∀ x ∈ ball p L, ∀ a : Fin k,
      ∃ (y z : M) (w : TangentSpace I x),
        w ∈ minimizingInitialDirections g hmetric x y ∧
        z = intrinsicGeodesic g hmetric x w t ∧ ℓ₀ ≤ dist x y ∧
        ‖Ψ z - A (u z) - b₀‖ ≤ E₀ ∧
        dist x y - β ≤ Ψ y a - Ψ x a ∧
        Ψ y a - Ψ z a ≤ dist x y - t + δ ∧
        |mvfderiv I F x w a - (Ψ y a - Ψ x a) / dist x y| ≤ αF ∧
        ‖mvfderiv I G x w - t⁻¹ • (u z - u x)‖ ≤ αG)
    (hε : max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t) ≤ 1) :
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + (F p - A (G p)))‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (k * (4 * max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t) +
          max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t) ^ 2)) := by
  have _ : (1 ≤ k ∧ k ≤ m) ∧ 0 ≤ αG ∧ _ ≤ (1 : ℝ) := ⟨⟨hk, hkm⟩, hαG, hε⟩
  exact fc22_row_RFC g hmetric F G u Ψ A hA b₀ p hL hαF ⟨ht, htℓ⟩ hβ hδ hE hF hG hDF hDG halign
    htests

/-- **Consumer of FC22**: when `ε ≤ 1` (the blueprint's standing assumption) the `C¹` error of
`F − (AG + b)` on `B(p, L)` is at most `2 max(1, L) √(5k)`. -/
theorem fc22_row_le_RFC {k m : ℕ}
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) {L αF αG ℓ₀ t β δ E₀ : ℝ}
    (hL : 0 < L) (hαF : 0 ≤ αF) (ht : t ∈ Ioo 0 ℓ₀)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + αF)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + αG)
    (halign : ∀ x ∈ ball p L, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (htests : ∀ x ∈ ball p L, ∀ a : Fin k,
      ∃ (y z : M) (w : TangentSpace I x),
        w ∈ minimizingInitialDirections g hmetric x y ∧
        z = intrinsicGeodesic g hmetric x w t ∧ ℓ₀ ≤ dist x y ∧
        ‖Ψ z - A (u z) - b₀‖ ≤ E₀ ∧
        dist x y - β ≤ Ψ y a - Ψ x a ∧
        Ψ y a - Ψ z a ≤ dist x y - t + δ ∧
        |mvfderiv I F x w a - (Ψ y a - Ψ x a) / dist x y| ≤ αF ∧
        ‖mvfderiv I G x w - t⁻¹ • (u z - u x)‖ ≤ αG)
    (hε : max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t) ≤ 1) :
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + (F p - A (G p)))‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (5 * k) := by
  intro x hx
  have h := fc22_row_RFC g hmetric F G u Ψ A hA b₀ p hL hαF ht hβ hδ hE hF hG hDF hDG halign
    htests x hx
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity))
  set ε := max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t)
  have hε0 : 0 ≤ ε := by
    have h1 : 0 ≤ αF + β / ℓ₀ := add_nonneg hαF (div_nonneg hβ (ht.1.trans ht.2).le)
    exact h1.trans (le_max_left _ _)
  have hq : 4 * ε + ε ^ 2 ≤ 5 := by nlinarith only [hε0, hε]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith only [hq, hk]

/-- **FC19** (`lem:fibration-common-endpoints`, B:1293). On a complete connected Riemannian
manifold, with `L > 0`, `T, α, δ, E ≥ 0`, `s > T + 2δ`, `H > L + s + 3δ`, a product map
`φ = (u, z) : B(p, H) → ℝᵐ × Z` with `φ(p) = (0, z₀)`, distortion at most `δ` and covering the
radius-`(H − δ)` ball to error `δ`; a coisometry `A` and `b₀` with `|Ψ − Au − b₀| ≤ E` on `B(p, H)`;
`F : B(p, L) → ℝᵏ`, `G : B(p, L) → ℝᵐ` of class `C¹` with `|dF_a| ≤ 1 + α`, `‖DG‖ ≤ 1 + α`, and the
original tests along every minimizing initial unit vector from `x ∈ B(p, L)` to `y ∈ B(p, H)`,
`d(x, y) > T`. Then with `ε = α + (3δ + 2E)/(s − 2δ)` and `b = F(p) − AG(p)`, at every
`x ∈ B(p, L)` both the value and the derivative error of `F − (AG + b)` are at most
`2 max(1, L) √(k(4ε + ε²))`. -/
theorem fc19_row_RFC {k m : ℕ} {Z : Type*} [PseudoMetricSpace Z]
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (z : M → Z)
    (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) (z₀ : Z) {L T s H₀ δ E₀ α : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀) (hα : 0 ≤ α)
    (hs : T + 2 * δ < s) (hH : L + s + 3 * δ < H₀)
    (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H₀, ∀ y ∈ ball p H₀,
      |dist (WithLp.toLp 2 (u x, z x)) (WithLp.toLp 2 (u y, z y)) - dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H₀ - δ →
        ∃ y ∈ ball p H₀, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hΨ : ∀ x ∈ ball p H₀, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + α)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I F x w - (dist x y)⁻¹ • (Ψ y - Ψ x)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I G x w - (dist x y)⁻¹ • (u y - u x)‖ ≤ α) :
    let ε := α + (3 * δ + 2 * E₀) / (s - 2 * δ)
    let b := F p - A (G p)
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + b)‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) :=
  centered_affine_c1_of_common_endpoints g hmetric F G u z Ψ A hA b₀ p z₀ hL hT hδ hE hα hs hH
    hup hzp hdist hcover hΨ hF hG hDF hDG htestF htestG

/-- FC19 with the blueprint's hypotheses verbatim (`1 ≤ k ≤ m` and `ε ≤ 1` included). -/
example {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) {Z : Type*} [PseudoMetricSpace Z]
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (z : M → Z)
    (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) (z₀ : Z) {L T s H₀ δ E₀ α : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀) (hα : 0 ≤ α)
    (hs : T + 2 * δ < s) (hH : L + s + 3 * δ < H₀)
    (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H₀, ∀ y ∈ ball p H₀,
      |dist (WithLp.toLp 2 (u x, z x)) (WithLp.toLp 2 (u y, z y)) - dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H₀ - δ →
        ∃ y ∈ ball p H₀, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hΨ : ∀ x ∈ ball p H₀, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + α)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I F x w - (dist x y)⁻¹ • (Ψ y - Ψ x)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I G x w - (dist x y)⁻¹ • (u y - u x)‖ ≤ α)
    (hε : α + (3 * δ + 2 * E₀) / (s - 2 * δ) ≤ 1) :
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + (F p - A (G p)))‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (k * (4 * (α + (3 * δ + 2 * E₀) / (s - 2 * δ)) +
          (α + (3 * δ + 2 * E₀) / (s - 2 * δ)) ^ 2)) := by
  have _ : (1 ≤ k ∧ k ≤ m) ∧ _ ≤ (1 : ℝ) := ⟨⟨hk, hkm⟩, hε⟩
  exact fc19_row_RFC g hmetric F G u z Ψ A hA b₀ p z₀ hL hT hδ hE hα hs hH hup hzp hdist hcover hΨ
    hF hG hDF hDG htestF htestG

/-- **Consumer of FC19**: when `ε ≤ 1` the `C¹` error of `F − (AG + b)` on `B(p, L)` is at most
`2 max(1, L) √(5k)`. -/
theorem fc19_row_le_RFC {k m : ℕ} {Z : Type*} [PseudoMetricSpace Z]
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (u : M → EuclideanSpace ℝ (Fin m)) (z : M → Z)
    (Ψ : M → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) (b₀ : EuclideanSpace ℝ (Fin k))
    (p : M) (z₀ : Z) {L T s H₀ δ E₀ α : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hE : 0 ≤ E₀) (hα : 0 ≤ α)
    (hs : T + 2 * δ < s) (hH : L + s + 3 * δ < H₀)
    (hup : u p = 0) (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H₀, ∀ y ∈ ball p H₀,
      |dist (WithLp.toLp 2 (u x, z x)) (WithLp.toLp 2 (u y, z y)) - dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H₀ - δ →
        ∃ y ∈ ball p H₀, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hΨ : ∀ x ∈ ball p H₀, ‖Ψ x - A (u x) - b₀‖ ≤ E₀)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hDF : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + α)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I F x w - (dist x y)⁻¹ • (Ψ y - Ψ x)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H₀, T < dist x y →
      ∀ w ∈ minimizingInitialDirections g hmetric x y,
        ‖mvfderiv I G x w - (dist x y)⁻¹ • (u y - u x)‖ ≤ α)
    (hε : α + (3 * δ + 2 * E₀) / (s - 2 * δ) ≤ 1) :
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + (F p - A (G p)))‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (5 * k) := by
  intro x hx
  have h := fc19_row_RFC g hmetric F G u z Ψ A hA b₀ p z₀ hL hT hδ hE hα hs hH hup hzp hdist
    hcover hΨ hF hG hDF hDG htestF htestG x hx
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity))
  set ε := α + (3 * δ + 2 * E₀) / (s - 2 * δ)
  have hε0 : 0 ≤ ε := add_nonneg hα (div_nonneg (by positivity) (by linarith only [hs, hT]))
  have hq : 4 * ε + ε ^ 2 ≤ 5 := by nlinarith only [hε0, hε]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith only [hq, hk]

end DifferentialGeometry.Geometry.Fibration
