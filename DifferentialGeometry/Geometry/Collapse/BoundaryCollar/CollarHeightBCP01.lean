import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightGeometry
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarSublevel
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightHessian

/-!
# Row BCP01: the smooth original collar height (binding)

* `CuspEmbedding.abs_hessian_height_le`: from the order-one metric-error estimate Z-H of lane
  FT-C (`CuspEmbedding.abs_hessian_height_add_le`: `Hess_g ζ(de a, de b) = −½ e^{-z} g_T(a₁, b₁)
  + O(2δ)`), `|Hess_g ζ(de a, de b)| ≤ (1/2 + 2δ) |a|_H |b|_H` on the whole collar.
* `CuspEmbedding.bcp01` (row BCP01, analytic clauses (a), (b) and the inner collar (c), ONE `η`):
  for `0 ≤ δ ≤ 1/1000`, `K ≥ 1` and `0 < ε ≤ 1/1000` there are smooth `η` and `F` on `W` such
  that on the band `2 ≤ z ≤ 98`
  - (BCP01.a, `g`-norms) `|η − ζ| < ε`, `|d(η − ζ)(u)| ≤ ε(1 − δ)^{-1}|u|_g`,
    `|Hess_g(η − ζ)(u, w)| ≤ ε(1 − δ)^{-1}|u|_g|w|_g`;
  - (BCP01.b) `|dη(u)| ≤ (1 + 1/200)|u|_g`, some `u` with `(199/200)|u|_g ≤ dη(u)`,
    `|Hess_g η(u, w)| ≤ (3/2)|u|_g|w|_g`, `.99 < ∂_z η < 1.01`;
  and (BCP01.c, row E6 of lane B-5b with this `η`) `F = η` on `2 ≤ z ≤ 95`,
  `{F ≤ 90} = e{z ≤ 2 ∨ (z ≤ 98 ∧ η ≤ 90)}` is a compact manifold with boundary `X ∪ {F = 90}`,
  diffeomorphic to `T² × [a, 90]` as a pair (`T² × {a}` onto `X`, `F` the second coordinate).
* `NearlyCuspidalBoundary.bcp01_analytic`: (a) and (b) in the `i`-th collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The horizontal part of the model metric is bounded by the model metric. -/
theorem cusp_abs_exp_torus_inner_le (H : HyperbolicCusp) (p : CuspHalfSpace)
    (a b : TangentSpace halfCollarModel p) :
    |Real.exp (-(p.2.val 0)) * H.torusMetric.inner p.1 a.1 b.1| ≤
      Real.sqrt (H.metric.inner p a a) * Real.sqrt (H.metric.inner p b b) := by
  set c : ℝ := Real.exp (-(p.2.val 0)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hA := metric_inner_self_nonneg H.torusMetric p.1 a.1
  have hB := metric_inner_self_nonneg H.torusMetric p.1 b.1
  have hcs := SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic H.torusMetric p.1
    a.1 b.1
  have ha : c * H.torusMetric.inner p.1 a.1 a.1 ≤ H.metric.inner p a a := by
    rw [H.metric_formula]
    nlinarith [mul_self_nonneg (a.2 0)]
  have hb : c * H.torusMetric.inner p.1 b.1 b.1 ≤ H.metric.inner p b b := by
    rw [H.metric_formula]
    nlinarith [mul_self_nonneg (b.2 0)]
  calc |c * H.torusMetric.inner p.1 a.1 b.1|
      = c * |H.torusMetric.inner p.1 a.1 b.1| := by rw [abs_mul, abs_of_pos hc0]
    _ ≤ c * (Real.sqrt (H.torusMetric.inner p.1 a.1 a.1) *
          Real.sqrt (H.torusMetric.inner p.1 b.1 b.1)) :=
        mul_le_mul_of_nonneg_left hcs hc0.le
    _ = Real.sqrt (c * H.torusMetric.inner p.1 a.1 a.1) *
          Real.sqrt (c * H.torusMetric.inner p.1 b.1 b.1) := by
        rw [Real.sqrt_mul hc0.le, Real.sqrt_mul hc0.le]
        have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
        calc c * (Real.sqrt (H.torusMetric.inner p.1 a.1 a.1) *
              Real.sqrt (H.torusMetric.inner p.1 b.1 b.1))
            = (Real.sqrt c * Real.sqrt c) * (Real.sqrt (H.torusMetric.inner p.1 a.1 a.1) *
              Real.sqrt (H.torusMetric.inner p.1 b.1 b.1)) := by rw [hcc]
          _ = _ := by ring
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)

/-- **The collar height has bounded Hessian** (from Z-H, lane FT-C): on the whole collar,
`|Hess_g ζ(de a, de b)| ≤ (1/2 + 2δ) |a|_H |b|_H` for `0 ≤ δ ≤ 1/4`, `K ≥ 1`. -/
theorem CuspEmbedding.abs_hessian_height_le (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (a b : TangentSpace halfCollarModel p) :
    |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p a)
        (mfderiv halfCollarModel W.model e.toFun p b)| ≤
      (1 / 2 + 2 * δ) * Real.sqrt (e.cusp.metric.inner p a a) *
        Real.sqrt (e.cusp.metric.inner p b b) := by
  have hZ := e.abs_hessian_height_add_le hK hδ0 hδ hp a b
  have hm := cusp_abs_exp_torus_inner_le e.cusp p a b
  set h := (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
    (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
    (mfderiv halfCollarModel W.model e.toFun p a)
    (mfderiv halfCollarModel W.model e.toFun p b) with hh
  set m := Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 b.1 with hmdef
  set A := Real.sqrt (e.cusp.metric.inner p a a) with hA
  set B := Real.sqrt (e.cusp.metric.inner p b b) with hB
  have hAB : 0 ≤ A * B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have key : ∀ x : ℝ, |x + 1 / 2 * m| ≤ 2 * δ * A * B → |x| ≤ (1 / 2 + 2 * δ) * A * B := by
    intro x hx
    have h1 := abs_le.mp hx
    have h2 := abs_le.mp hm
    rw [abs_le]
    constructor <;> nlinarith
  exact key _ hZ

/-- **Row BCP01** (analytic clauses (a), (b) and the inner collar (c), with ONE `η`). -/
theorem CuspEmbedding.bcp01 (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ (η F : W.Carrier → ℝ) (a : ℝ) (har : a < 90), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) u| ≤ ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w| ≤
            ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
              Real.sqrt (g.inner (e.toFun p) w w)) ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model η (e.toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∃ u : TangentSpace W.model (e.toFun p), 0 < mvfderiv W.model η (e.toFun p) u ∧
          199 / 200 * Real.sqrt (g.inner (e.toFun p) u u) ≤ mvfderiv W.model η (e.toFun p) u) ∧
        (∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
              (e.toFun p) u w| ≤
            3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w)) ∧
        99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) ∧
          (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) < 101 / 100) ∧
      (∀ p : CuspHalfSpace, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 95 → F (e.toFun p) = η (e.toFun p)) ∧
      (∀ y, F y ≤ 90 ↔ ∃ p ∈ cuspDomain, e.toFun p = y ∧
        (p.2.val 0 ≤ 2 ∨ (p.2.val 0 ≤ 98 ∧ η y ≤ 90))) ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ 90},
        letI := cs
        IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ 90} ∧
        ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ 90} => x.1) ∧
        (∀ y : {x : W.Carrier // F x ≤ 90}, (𝓡∂ 3).IsBoundaryPoint y ↔
          (y.1 ∈ X ∨ F y.1 = 90)) ∧
        haveI : Fact (a < 90) := ⟨har⟩
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a 90)
            {x : W.Carrier // F x ≤ 90} ∞,
          (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ X ↔ p.2.1 = a := by
  obtain ⟨η, F, a, har, hη, hF, hZ, hmid, hchar, hprod⟩ :=
    e.exists_innerCollar_diffeomorph_torus_Icc hK hε
  refine ⟨η, F, a, har, hη, hF, fun p hp h2 h98 => ?_, hmid, hchar, hprod⟩
  obtain ⟨h0, h1, h2'⟩ := hZ p hp h2 h98
  obtain ⟨ha1, ha2⟩ := e.bcp01a_of_contract hδ0 (by linarith) hη hε.le hp h1 h2'
  obtain ⟨hb1, hb2, hb3⟩ := e.bcp01b_differential_of_contract hδ hη hε.le hε1 hp h1
  have hz : 0 < p.2.val 0 := by linarith
  have hH := e.bcp01b_hessian_le_of_contract hK hδ hη hε.le hε1 (by linarith) (by linarith) hp hz
    h2' (e.abs_hessian_height_le hK hδ0 (by linarith) hp)
  exact ⟨h0, ha1, ha2, hb1, hb2, hH, hb3⟩

/-- BCP01 (a), (b) in the `i`-th collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.bcp01_analytic (B : NearlyCuspidalBoundary W g K δ)
    (i : Fin B.count) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η ((B.collar i).toFun p) - p.2.val 0| < ε ∧
        (∀ u : TangentSpace W.model ((B.collar i).toFun p),
          |mvfderiv W.model η ((B.collar i).toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner ((B.collar i).toFun p) u u)) ∧
        ∀ u w : TangentSpace W.model ((B.collar i).toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
              ((B.collar i).toFun p) u w| ≤
            3 / 2 * Real.sqrt (g.inner ((B.collar i).toFun p) u u) *
              Real.sqrt (g.inner ((B.collar i).toFun p) w w) := by
  obtain ⟨η, -, -, -, hη, -, hb, -⟩ := (B.collar i).bcp01 hK hδ0 hδ hε hε1
  exact ⟨η, hη, fun p hp h2 h98 =>
    ⟨(hb p hp h2 h98).1, (hb p hp h2 h98).2.2.2.1, (hb p hp h2 h98).2.2.2.2.2.1⟩⟩

end DifferentialGeometry.Geometry.Collapse
