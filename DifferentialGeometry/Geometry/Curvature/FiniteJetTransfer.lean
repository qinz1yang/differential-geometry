import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetLocality
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetRestriction
import DifferentialGeometry.Geometry.Curvature.FiniteNumeratorTransfer
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction

/-!
# Second-order numerator transfer by jet replacement

An arbitrary section `T` of `(0,2)`-tensors on `M` with small metric covariant derivatives up to
order two at `x` controls the curvature numerator of every smooth metric `g'`, defined on an open
neighbourhood `U` of `x` on which `M` has no boundary, whose difference with the reference metric
has the same second-order chart jet as `T` at `x`. This is the explicit conversion of finite
second-order data into smooth second-order data used by the cusp curvature binding.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter TopologicalSpace DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Jet replacement transfer (G2-T).** If the restriction of `T` to `U` and the difference
`g' - G` have the same second-order chart jet at `x`, the `k ≤ 2` smallness of `T` at `x` gives the
`ε (360 + K)` numerator estimate for `g'`. -/
theorem abs_metricRm04_sub_le_of_chart_jet_replacement (G : SmoothRiemannianMetric I M)
    (U : Opens M) [T2Space U] [BoundarylessManifold I U] (g' : SmoothRiemannianMetric I U)
    (T : (x : M) → Tensor0SSpace 2 I x) (x : U) {ε K : ℝ} (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → tensor0SFiberNorm G x (2 + k)
      (iteratedMetricCovariantDerivative G 2 T k x) ≤ ε)
    (hT : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T z))))
      (Set.range I) (extChartAt I x x))
    (hS : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (finiteMetricDifference g' (G.restrictOpen U))) (Set.range I) (extChartAt I x x))
    (h0 : tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T z)))
        (extChartAt I x x) =
      tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (finiteMetricDifference g' (G.restrictOpen U)) (extChartAt I x x))
    (h1 : fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T z))))
        (Set.range I) (extChartAt I x x) =
      fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
        (finiteMetricDifference g' (G.restrictOpen U))) (Set.range I) (extChartAt I x x))
    (h2 : fderivWithin ℝ (fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
          (fun z : U => Tensor0SSpace.ofModel (I := I) (x := z) (Tensor0SSpace.toModel (T z))))
        (Set.range I)) (Set.range I) (extChartAt I x x) =
      fderivWithin ℝ (fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := U) 2 x
          (finiteMetricDifference g' (G.restrictOpen U))) (Set.range I))
        (Set.range I) (extChartAt I x x))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita (G.restrictOpen U)) x u v w
      Real.sqrt ((G.restrictOpen U).inner x r r) ≤
        K * Real.sqrt ((G.restrictOpen U).inner x u u) *
          Real.sqrt ((G.restrictOpen U).inner x v v) *
          Real.sqrt ((G.restrictOpen U).inner x w w))
    (v w : TangentSpace I x) :
    |metricRm04StandardAt g' x v w w v - metricRm04StandardAt G (x : M) v w w v| ≤
      ε * (360 + K) * G.inner x v v * G.inner x w w := by
  have hsmallU (k : ℕ) (hk : k ≤ 2) :
      metricDerivNorm k g' (G.restrictOpen U) (G.restrictOpen U) x ≤ ε := by
    rw [← finiteMetricDifference_norm_eq,
      ← iteratedMetricCovariantDerivative_eq_of_chart_jet (G.restrictOpen U) _ _ x hT hS h0 h1 h2
        hk, tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen]
    exact hsmall k hk
  have hrestr : metricRm04StandardAt (G.restrictOpen U) x v w w v =
      metricRm04StandardAt G (x : M) v w w v := by
    rw [metricRm04StandardAt_restrictOpen]
    simp only [DifferentialGeometry.mfderiv_subtype_val_apply]
  rw [← hrestr]
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmallU 0 (by norm_num))
  have h := abs_metricRm04_sub_le_of_small_metric_derivatives g' (G.restrictOpen U) x hε
    hsmallU v w w v
  apply h.trans
  have hR := hmodel v w w
  dsimp only at hR
  have hinner (a b : TangentSpace I x) : (G.restrictOpen U).inner x a b = G.inner x a b := rfl
  calc
    ε * (360 * Real.sqrt ((G.restrictOpen U).inner x v v) *
          Real.sqrt ((G.restrictOpen U).inner x w w) *
          Real.sqrt ((G.restrictOpen U).inner x w w) +
        Real.sqrt ((G.restrictOpen U).inner x
          (riemannOp (LeviCivita (G.restrictOpen U)) x v w w)
          (riemannOp (LeviCivita (G.restrictOpen U)) x v w w))) *
        Real.sqrt ((G.restrictOpen U).inner x v v)
      ≤ ε * (360 * Real.sqrt ((G.restrictOpen U).inner x v v) *
          Real.sqrt ((G.restrictOpen U).inner x w w) *
          Real.sqrt ((G.restrictOpen U).inner x w w) +
        K * Real.sqrt ((G.restrictOpen U).inner x v v) *
          Real.sqrt ((G.restrictOpen U).inner x w w) *
          Real.sqrt ((G.restrictOpen U).inner x w w)) *
        Real.sqrt ((G.restrictOpen U).inner x v v) := by gcongr
    _ = ε * (360 + K) * (Real.sqrt ((G.restrictOpen U).inner x v v)) ^ 2 *
        (Real.sqrt ((G.restrictOpen U).inner x w w)) ^ 2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (metric_inner_self_nonneg (G.restrictOpen U) x v),
        Real.sq_sqrt (metric_inner_self_nonneg (G.restrictOpen U) x w), hinner, hinner]

end DifferentialGeometry.Geometry.Curvature
