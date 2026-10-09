import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductMetric
import DifferentialGeometry.Geometry.Metric.Isometry.FiniteManifoldRegularity

/-!
# The same whole splitting diffeomorphism at the final finite order

The actual product metric is the original map's pullback. The native metric bootstrap upgrades
both directions without changing the zero factor, its atlas, or the splitting equivalence.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp
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

def splittingProductDiffeomorph
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    Diffeomorph IP I (F × {x : M // (e x).fst = 0}) M ((r : ℕ∞ω) + 2) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  apply MetricIsometry.upgradeMetricDiffeomorph (splittingProductMetric g hr hnorm e) g
    (splittingProductInitialDiffeomorph g hr hnorm e) hr
  intro p v w
  exact (splittingProductMetric_inner g hr hnorm e p v w).trans
    (splittingProductMap_metric g hr hnorm e p v w).symm

theorem splittingProductDiffeomorph_toEquiv
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    (splittingProductDiffeomorph g hr hnorm e).toEquiv = splittingProductEquiv e := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  rfl

theorem contMDiff_splittingProductMap_final
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ContMDiff IP I ((r : ℕ∞ω) + 2) (splittingProductMap e) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  exact (splittingProductDiffeomorph g hr hnorm e).contMDiff

theorem splittingProductDiffeomorph_expMap
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (u : F) (z : {x : M // (e x).fst = 0}),
      splittingProductDiffeomorph g hr hnorm e (u, z) =
        g.expMap (⟨z.val, splittingFrame g e z.val u⟩ : TangentBundle I M) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  exact splittingProductMap_eq_expMap g hr hnorm e

theorem splittingProductDiffeomorph_metric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      g.inner (splittingProductDiffeomorph g hr hnorm e p)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p v)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2 := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  exact splittingProductMap_metric g hr hnorm e

private theorem realProductFinal_enorm : ∀ (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x v v)) := by
  intro x v
  change ‖(v : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : ℝ) v))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

local instance realProductFinalDimension : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

def realProductFinalDiffeomorph :=
  splittingProductDiffeomorph (r := 2) realFrameMetric le_rfl realProductFinal_enorm
    realFrameSplitting.{0}

end DifferentialGeometry.Geometry.ExactSplitting
