import DifferentialGeometry.Geometry.Fibration.RiemannianDirectionalComparison
import DifferentialGeometry.Geometry.Metric.Approximation.CommonEndpointTests
import DifferentialGeometry.Analysis.InnerProductSpace.OverlapComparisonChain

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

/-- Initial velocities of SAME actual minimizing intrinsic geodesics. -/
def minimizingInitialDirections
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g) (x y : M) :
    Set (TangentSpace I x) :=
  {w | ‖w‖ = 1 ∧ intrinsicGeodesic g hmetric x w (dist x y) = y}

/-- Complete smooth Hopf--Rinow supplies these directions without a certificate input. -/
theorem minimizingInitialDirections_nonempty
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (x y : M) (hxy : x ≠ y) : (minimizingInitialDirections g hmetric x y).Nonempty := by
  obtain ⟨v, hv, hn⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing g hmetric x y
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hnv : ‖v‖ = dist x y := by
    have hh := hmetric x v
    rw [← ofReal_norm, hn, ← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hh
    have he := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (norm_nonneg v),
      ENNReal.toReal_ofReal dist_nonneg] using he
  let w : TangentSpace I x := (dist x y)⁻¹ • v
  refine ⟨w, ?_, ?_⟩
  · simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd, hnv,
      inv_mul_cancel₀ hd.ne']
  · change intrinsicGeodesic g hmetric x w (dist x y) = y
    rw [← intrinsicGeodesic_smul]
    have hscale : dist x y • w = v := by
      simp only [w, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    rw [hscale, ← expMapIntrinsic_def]
    exact hv

/-- FC19: original metric cover and long tests give actual native C1 comparison. -/
theorem centered_affine_c1_of_common_endpoints {k m : ℕ} {Z : Type*} [PseudoMetricSpace Z]
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
        2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
  let ε := α + (3 * δ + 2 * E₀) / (s - 2 * δ)
  have hd := GC.MetricGeometry.norm_sub_comp_le_of_common_endpoints u z Ψ A hA b₀
    hT hδ hE hα hs hH hup hzp hdist hcover hΨ
    (minimizingInitialDirections g hmetric)
    (minimizingInitialDirections_nonempty g hmetric)
    (fun _x _y _w hw => hw.1) (mvfderiv I F) (mvfderiv I G) hDF hDG htestF htestG
  have hh := centered_affine_c1_of_mfderiv_bound g hmetric F G A p hL
    (c := 2 * Real.sqrt (k * (4 * ε + ε ^ 2))) (by positivity) hF hG hd
  dsimp only at hh ⊢
  intro x hx
  convert (hh x hx).2 using 1
  ring

/-- FC22: actual minimizing long/short tests feed the SAME native integration. -/
theorem centered_affine_c1_of_long_short_tests {k m : ℕ}
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
        2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
  let ε := max (αF + β / ℓ₀) (αG + (β + δ + 2 * E₀) / t)
  have hd (x : M) (hx : x ∈ ball p L) :
      ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
    apply InnerProductSpace.norm_sub_comp_le_of_long_short_tests u Ψ A hA b₀
      (mvfderiv I F x) (mvfderiv I G x) hαF (ht.1.trans ht.2) ht.1 hβ hδ hE
      (hDF x hx) (hDG x hx) x (halign x hx)
    intro a
    obtain ⟨y, z, w, hw, _hz, hℓ, hza, hlong, hshort, htF, htG⟩ := htests x hx a
    exact ⟨w, hw.1, y, z, dist x y, hℓ, hza, hlong, hshort, htF, htG⟩
  have hh := centered_affine_c1_of_mfderiv_bound g hmetric F G A p hL
    (c := 2 * Real.sqrt (k * (4 * ε + ε ^ 2))) (by positivity) hF hG hd
  dsimp only at hh ⊢
  intro x hx
  convert (hh x hx).2 using 1
  ring

end DifferentialGeometry.Geometry.Fibration
