import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductDistance

/-!
# Consumers of R2 (product metric with the product distance)

* `splittingProduct_vertical_unit`: the vertical field `∂_u = (u, 0)` of `F × Z`, pushed to `M`,
  is the splitting frame, has `g`-length `‖u‖`, and its geodesics are the vertical lines;
* `splittingProductMetric_dist_eq`: the real distance form of R2.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

/-- The pushed vertical field: the splitting frame, of `g`-length `‖u‖`, with the vertical lines
as its geodesics. -/
theorem splittingProduct_vertical_unit
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (u : F),
      g.inner (splittingProductDiffeomorph g hr hnorm e p)
          (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p ((u, 0) : F × P))
          (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p ((u, 0) : F × P)) =
        ‖u‖ ^ 2 ∧
      ∀ s : ℝ, splittingProductDiffeomorph g hr hnorm e (p.1 + s • u, p.2) =
        g.expMap (⟨splittingProductDiffeomorph g hr hnorm e p,
          s • mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p ((u, 0) : F × P)⟩ :
            TangentBundle I M) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro p u
  rw [mfderiv_splittingProductDiffeomorph_fst g hr hnorm e p u]
  refine ⟨?_, splittingProductDiffeomorph_vertical g hr hnorm e p u⟩
  rw [inner_splittingFrame g hr hnorm e, real_inner_self_eq_norm_sq]

/-- **R2, distance form.** The Riemannian distance of `du² + h` is the real `ℓ²` distance. -/
theorem splittingProductMetric_dist_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
      ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ p q : F × {x : M // (e x).fst = 0},
      (riemannianEDist IP p q).toReal = Real.sqrt (dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
    ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
  intro p q
  have h := WithLp.prod_dist_sq_eq_add_sq (toLp 2 p) (toLp 2 q)
  change dist (toLp 2 p) (toLp 2 q) ^ 2 = dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2 at h
  rw [splittingProductMetric_riemannianEDist g hr hnorm e p q, ← dist_edist, ← h,
    Real.sqrt_sq dist_nonneg]

end DifferentialGeometry.Geometry.ExactSplitting
