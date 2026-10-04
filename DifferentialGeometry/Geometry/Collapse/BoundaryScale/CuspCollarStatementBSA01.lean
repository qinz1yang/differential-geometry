import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightHessian

/-!
# BSA01 in full (statement G with the second fundamental form clause)

Blueprint 207B, BSA01 (`B:7591`): every clause, the second fundamental form clause `II ≥ g/4` in
the corrected chart-free form of
`docs/geometrization/chapter13/errata-boundary-geometry-G-II-20261004.md` (the `g`-dual norm of
`dζ`, written out), together with the remaining clauses `bsa01_clauses_except_II`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA01, clause (v): `II ≥ g/4` on every boundary component** (corrected chart-free form). For
`K ≥ 1` and `0 ≤ δ ≤ 1/100`, on every boundary component of a nearly cuspidal boundary, with
`ζ_i` the height of the `i`-th collar: `g(v,v)/4 · |dζ_i(u)| ≤ −Hess_g ζ_i(v,v) · √g(u,u)` whenever
`dζ_i(v) = 0`. -/
theorem bsa01_second_fundamental_form {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 100) (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) :
    ∀ y ∈ B.component i, ∀ v u : TangentSpace W.model y,
      mvfderiv W.model (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0) y v = 0 →
      g.inner y v v / 4 *
          |mvfderiv W.model (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0)
            y u| ≤
        -((CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0) y v v) *
          Real.sqrt (g.inner y u u) :=
  (B.collar i).inner_div_four_mul_abs_le_neg_hessian_height hK hδ0 hδ

/-- **BSA01 (all clauses).** There is `δStar > 0` such that every nearly cuspidal boundary with
`K ≥ 2` and `0 ≤ δ ≤ δStar` satisfies the second fundamental form clause `II ≥ g/4` (corrected
form) on every boundary component, together with all the clauses of `bsa01_clauses_except_II`. -/
theorem bsa01_row :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
      (∀ (i : Fin B.count), ∀ y ∈ B.component i, ∀ v u : TangentSpace W.model y,
        mvfderiv W.model (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0) y v = 0 →
        g.inner y v v / 4 *
            |mvfderiv W.model (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0)
              y u| ≤
          -((CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
            (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0) y v v) *
            Real.sqrt (g.inner y u u)) ∧
      (∀ (i : Fin B.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
        ∀ u w : TangentSpace W.model ((B.collar i).toFun q),
          -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
              metricRm04StandardAt g ((B.collar i).toFun q) u w w u ∧
            metricRm04StandardAt g ((B.collar i).toFun q) u w w u ≤
              -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2)) ∧
      (∀ (i : Fin B.count), ∀ q ∈ cuspDomain,
        (∀ u : TangentSpace W.model ((B.collar i).toFun q),
          |(show ℝ from mfderiv W.model 𝓘(ℝ, ℝ)
            (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0)
            ((B.collar i).toFun q) u)| ≤ 1.01 * Real.sqrt (g.inner _ u u)) ∧
        ∃ u : TangentSpace W.model ((B.collar i).toFun q),
          (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ)
            (fun y => (Function.invFunOn (B.collar i).toFun cuspDomain y).2.val 0)
            ((B.collar i).toFun q) u) = 1 ∧ Real.sqrt (g.inner _ u u) ≤ 1.01) ∧
      (∀ (i : Fin B.count) (p : CuspHalfSpace), p.2.val 0 ≤ 96 →
        (∀ r : ℝ, r ≤ 1 → riemannianBallOf g ((B.collar i).toFun p) r ⊆
            (B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 98}) ∧
        (∀ r : ℝ, r ≤ 1 →
          ballVolume g ((B.collar i).toFun p) r ≤ ENNReal.ofReal (1000 * δ ^ 2 * r)) ∧
        1 ≤ curvatureRadius g ((B.collar i).toFun p) ∧
          curvatureRadius g ((B.collar i).toFun p) < 3) ∧
      (∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
        ∃ i, ∃ x : Torus, ∃ z₁ : ℝ, 0 ≤ z₁ ∧ z₁ < 11 ∧
          (B.collar i).toFun (x, halfSpaceOneLift z₁) = p) ∧
      (ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
        curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) ∧
      (∀ (i : Fin B.count) (x y : Torus),
        riemannianEDistOf (B.collar i).cusp.torusMetric x y ≤ ENNReal.ofReal (2 * δ)) ∧
      ∀ i : Fin B.count, (Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (B.collar i).cusp.torusMetric univ).toReal ≤ 4 * Real.pi * δ ^ 2 := by
  obtain ⟨δS, hδS, h⟩ := bsa01_clauses_except_II.{u}
  refine ⟨min δS (1 / 100), lt_min hδS (by norm_num), ?_⟩
  intro W g K δ hK hδ0 hδ B
  have hδS' : δ ≤ δS := hδ.trans (min_le_left _ _)
  have hδc : δ ≤ 1 / 100 := hδ.trans (min_le_right _ _)
  exact ⟨fun i => bsa01_second_fundamental_form (by omega) hδ0 hδc B i,
    h W g K δ hK hδ0 hδS' B⟩

end DifferentialGeometry.Geometry.Collapse
