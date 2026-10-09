import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLowerApplications
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Geometry.Metric.Approximation.ProductComparisonSplitting
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# The actual Kleiner–Lott splitting of a cusp collar (foundation F-f.B, row BCP02.a/b)

Let `e : CuspEmbedding W g K δ X`, `q₀` a point of the cusp domain at height `z₀`, `r > 0` a
scale and `R = β⁻¹ + β`. In the rescaled distance `r⁻¹ d_g` of `W` (`MetricSpace.rescale` of
`inducedMetricSpace g`, `[ConnectedSpace W.Carrier]`), the map
`F(x) = ((z(e⁻¹x) − z₀)/r, t(e⁻¹x))` into `ℝ ×₂ T`, where `T` is the torus with the distance
`r⁻¹ e^{−z₀/2} d_{g_T}` (the complete residual flat factor `r⁻² e^{−z₀} g_T`, NOT a point), is
the splitting map of BCP02 (blueprint 207B, `B:8212–8321`).

* `CuspEmbedding.exists_preimage_of_riemannianEDistOf_lt` (slab membership): a point at
  `g`-distance `< √(1−δ) a/2` from `e q₀` is `e q` with `|z(q) − z₀| < a`.
* `CuspEmbedding.frozen_bilipschitz_toReal` (BCP02.b, real form): two points within
  `2√(1−δ) ρ₁` of `e q₀` satisfy `√(1−δ) e^{−4ρ₁} Q ≤ d_g ≤ √((1+δ) e^{4ρ₁}) Q`, where
  `Q = √(Δz² + e^{−z₀} d_T²)` (F-f.L and F-f.U on the slab of half-width `4ρ₁`).
* `CuspEmbedding.riemannianEDistOf_lift_le` (coverage): `d_g(e(t, z₀ + s), e q₀)` is at most
  `√((1+δ) e^{|s|} (s² + e^{−z₀} d_T(t, t₀)²))`.
* `CuspEmbedding.hasEuclideanSplitting_frozen` (F-f.B, explicit budget): the rank-one
  splitting at `e q₀` at scale `β` of the rescaled carrier, under explicit numerical
  inequalities on `δ`, `r R` and the distortion `a`.
* `CuspEmbedding.hasEuclideanSplitting_frozen_of_small` (F-f.B, clean form): for `0 < β < 1`,
  `5 ≤ z₀ ≤ 95`, `0 ≤ δ ≤ β²/1000`, `0 < r ≤ β³/2000`.

The torus factor is `Torus` with `(inducedMetricSpace g_T).rescale (r⁻¹ e^{−z₀/2})`, passed
explicitly (the global metric of `Circle × Circle` is not used).
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Slab membership.** A point at `g`-distance `< √(1 − δ) a/2` from `e q₀` is `e q` for a
point `q` of the cusp domain with `|z(q) − z(q₀)| < a` (`z(q₀) + a < 100`). -/
theorem CuspEmbedding.exists_preimage_of_riemannianEDistOf_lt (e : CuspEmbedding W g K δ X)
    {q₀ : CuspHalfSpace} {a : ℝ} (hup : q₀.2.val 0 + a < cuspDepth) {y : W.Carrier}
    (hy : riemannianEDistOf g (e.toFun q₀) y < ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) :
    ∃ q ∈ cuspDomain, e.toFun q = y ∧ |q.2.val 0 - q₀.2.val 0| < a := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  have ha : 0 ≤ a := by
    by_contra hneg
    push Not at hneg
    have h0 : Real.sqrt (1 - δ) * (a / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)
    rw [ENNReal.ofReal_of_nonpos h0] at hy
    exact absurd hy (not_lt.mpr bot_le)
  change Manifold.riemannianEDist W.model (e.toFun q₀) y < _ at hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  have hq₀ : |q₀.2.val 0 - q₀.2.val 0| ≤ a / 2 := by
    rw [sub_self, abs_zero]
    linarith
  obtain ⟨c, -, hcd, hce⟩ := e.exists_slab_lift_of_pathELength_lt hγ hup hq₀ hγ0 hlen
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  exact ⟨c 1, (hcd 1 h1).1, (hce 1 h1).trans hγ1, (hcd 1 h1).2⟩

/-- **BCP02.b, real form.** Two points within `2√(1 − δ) ρ₁` of `e q₀`, `4ρ₁ < z₀`,
`z₀ + 8ρ₁ < 100`, are `e q`, `e q'` with heights within `4ρ₁` of `z₀`, and
`√(1−δ) e^{−4ρ₁} Q ≤ d_g(e q, e q') ≤ √((1+δ) e^{4ρ₁}) Q`, `Q = √(Δz² + e^{−z₀} d_T²)`. -/
theorem CuspEmbedding.frozen_bilipschitz_toReal [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace} {ρ₁ : ℝ}
    (hlow : 4 * ρ₁ < q₀.2.val 0) (hup : q₀.2.val 0 + 8 * ρ₁ < cuspDepth) {x x' : W.Carrier}
    (hx : riemannianEDistOf g (e.toFun q₀) x <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)))
    (hx' : riemannianEDistOf g (e.toFun q₀) x' <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2))) :
    ∃ q ∈ cuspDomain, ∃ q' ∈ cuspDomain, e.toFun q = x ∧ e.toFun q' = x' ∧
      |q.2.val 0 - q₀.2.val 0| < 4 * ρ₁ ∧ |q'.2.val 0 - q₀.2.val 0| < 4 * ρ₁ ∧
      Real.sqrt (1 - δ) * (Real.exp (-(8 * ρ₁) / 2) *
          Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-(q₀.2.val 0)) *
            (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2)) ≤
        (riemannianEDistOf g x x').toReal ∧
      (riemannianEDistOf g x x').toReal ≤ Real.sqrt ((1 + δ) * Real.exp (8 * ρ₁ / 2) *
          ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-(q₀.2.val 0)) *
            (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2)) := by
  have hup4 : q₀.2.val 0 + 4 * ρ₁ < cuspDepth := by
    have hρ : 0 ≤ ρ₁ := by
      by_contra hneg
      push Not at hneg
      have h0 : Real.sqrt (1 - δ) * (4 * ρ₁ / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)
      rw [ENNReal.ofReal_of_nonpos h0] at hx
      exact absurd hx (not_lt.mpr bot_le)
    linarith
  obtain ⟨q, hq, rfl, hqz⟩ := e.exists_preimage_of_riemannianEDistOf_lt hup4 hx
  obtain ⟨q', hq', rfl, hqz'⟩ := e.exists_preimage_of_riemannianEDistOf_lt hup4 hx'
  have hd : riemannianEDistOf g (e.toFun q) (e.toFun q') <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (8 * ρ₁ / 2)) := by
    have hsum : ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) +
        ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) =
        ENNReal.ofReal (Real.sqrt (1 - δ) * (8 * ρ₁ / 2)) := by
      have hnn : 0 ≤ Real.sqrt (1 - δ) * (4 * ρ₁ / 2) := by
        rcases le_or_gt 0 ρ₁ with h | h
        · positivity
        · exfalso
          have h0 : Real.sqrt (1 - δ) * (4 * ρ₁ / 2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)
          rw [ENNReal.ofReal_of_nonpos h0] at hx
          exact absurd hx (not_lt.mpr bot_le)
      rw [← ENNReal.ofReal_add hnn hnn]
      congr 1
      ring
    calc riemannianEDistOf g (e.toFun q) (e.toFun q')
        ≤ riemannianEDistOf g (e.toFun q) (e.toFun q₀) +
            riemannianEDistOf g (e.toFun q₀) (e.toFun q') :=
          riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) +
            ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
          rw [riemannianEDistOf_comm g (e.toFun q) (e.toFun q₀)]
          exact ENNReal.add_lt_add hx hx'
      _ = _ := hsum
  have hl : 8 * ρ₁ / 2 < q₀.2.val 0 := by linarith
  have hp : |q.2.val 0 - q₀.2.val 0| ≤ 8 * ρ₁ / 2 := by linarith
  have hp' : |q'.2.val 0 - q₀.2.val 0| ≤ 8 * ρ₁ / 2 := by linarith
  obtain ⟨hL, hU⟩ := e.frozen_two_sided hl hup hp hp' hd
  have hne : riemannianEDistOf g (e.toFun q) (e.toFun q') ≠ ⊤ := riemannianEDistOf_ne_top g _ _
  refine ⟨q, hq, q', hq', rfl, rfl, hqz, hqz', ?_, ?_⟩
  · exact (ENNReal.ofReal_le_iff_le_toReal hne).mp hL
  · exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hU

/-- **Coverage distance.** `d_g(e(t, z₀ + s), e q₀) ≤ √((1+δ) e^{|s|} (s² + e^{−z₀} d_T(t, t₀)²))`
for `|s| < z₀`, `z₀ + |s| < 100`. -/
theorem CuspEmbedding.riemannianEDistOf_lift_le (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace}
    (t : Torus) {s : ℝ} (hs : |s| < q₀.2.val 0) (hs' : q₀.2.val 0 + |s| < 100) :
    riemannianEDistOf g (e.toFun (t, halfSpaceOneLift (q₀.2.val 0 + s))) (e.toFun q₀) ≤
      ENNReal.ofReal (Real.sqrt ((1 + δ) * Real.exp |s| * (s ^ 2 + Real.exp (-(q₀.2.val 0)) *
        (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal ^ 2))) := by
  have hz : ((t, halfSpaceOneLift (q₀.2.val 0 + s)) : CuspHalfSpace).2.val 0 =
      q₀.2.val 0 + s := by
    change (halfSpaceOneLift (q₀.2.val 0 + s)).1 0 = _
    rw [halfSpaceOneLift_val_zero, max_eq_left]
    linarith [neg_abs_le s]
  have hp : |((t, halfSpaceOneLift (q₀.2.val 0 + s)) : CuspHalfSpace).2.val 0 - q₀.2.val 0| ≤
      |s| := by
    rw [hz, add_sub_cancel_left]
  have hp' : |q₀.2.val 0 - q₀.2.val 0| ≤ |s| := by
    rw [sub_self, abs_zero]
    exact abs_nonneg s
  have h := e.riemannianEDistOf_le_frozen_product hs hs' hp hp'
  rw [hz] at h
  have hsq : (q₀.2.val 0 - (q₀.2.val 0 + s)) ^ 2 = s ^ 2 := by ring
  rw [hsq] at h
  exact h

/-- `e⁻¹ (e q) = q` on the cusp domain. -/
private theorem collarSplit_inv (e : CuspEmbedding W g K δ X) {q : CuspHalfSpace}
    (hq : q ∈ cuspDomain) : invFunOn e.toFun cuspDomain (e.toFun q) = q :=
  e.injOn_cuspDomain.leftInvOn_invFunOn hq

/-- **F-f.B (explicit budget), any model of the torus factor.** Let `φT : T² → Y` be onto a
metric space `Y` with `d_Y(φT t, φT t') = r⁻¹ e^{−z₀/2} d_{g_T}(t, t')`. With `R = β⁻¹ + β`, the
frozen chart map `x ↦ ((z(e⁻¹x) − z₀)/r, φT(t(e⁻¹x)))` into `ℝ ×₂ Y` is `(1 ± a)`-bi-Lipschitz on
the `r⁻¹ d_g`-ball of radius `R` and onto the target ball; hence `e q₀` has a rank-one splitting
at scale `β` in the rescaled carrier. -/
theorem CuspEmbedding.hasEuclideanSplitting_of_torus_isometry [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace} {β a r : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ha : 0 ≤ a) (ha1 : a < 1) (herr : 2 * a * (β⁻¹ + β) < β / 4) (hr : 0 < r)
    (hlow : 4 * (r * (β⁻¹ + β)) < q₀.2.val 0)
    (hup : q₀.2.val 0 + 8 * (r * (β⁻¹ + β)) < cuspDepth) (hδ : δ < 3 / 4)
    (hL : Real.exp (4 * (r * (β⁻¹ + β))) ≤ (1 + a) * Real.sqrt (1 - δ))
    (hU : (1 - a) ^ 2 * ((1 + δ) * Real.exp (4 * (r * (β⁻¹ + β)))) ≤ 1)
    (hC : (1 + δ) * Real.exp (r * (β⁻¹ + β)) * (β⁻¹ + β - β / 4) ^ 2 ≤ (β⁻¹ + β) ^ 2)
    {Y : Type} [MetricSpace Y] (φT : Torus → Y) (hφT : Surjective φT)
    (hdY : ∀ t t' : Torus, dist (φT t) (φT t') =
      r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric t t').toReal) :
    @HasEuclideanSplitting.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
      (e.toFun q₀) 1 β := by
  set R : ℝ := β⁻¹ + β with hR
  set ρ₁ : ℝ := r * R with hρ₁
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  have hR0 : 0 < R := by positivity
  have hρ0 : 0 < ρ₁ := mul_pos hr hR0
  have hδ0 : 0 ≤ δ := e.delta_nonneg
  have hs0 : 1 / 2 < Real.sqrt (1 - δ) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  let mX : MetricSpace W.Carrier := (inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)
  have hdX : ∀ x x' : W.Carrier, @dist W.Carrier mX.toDist x x' =
      r⁻¹ * (riemannianEDistOf g x x').toReal := fun _ _ => rfl
  let F : W.Carrier → WithLp 2 (ℝ × Y) := fun x =>
    WithLp.toLp 2 (((invFunOn e.toFun cuspDomain x).2.val 0 - z₀) / r,
      φT (invFunOn e.toFun cuspDomain x).1)
  have hq₀ : q₀ ∈ cuspDomain := by
    change q₀.2.val 0 < cuspDepth
    linarith
  have hFq : ∀ q ∈ cuspDomain, F (e.toFun q) = WithLp.toLp 2 ((q.2.val 0 - z₀) / r, φT q.1) := by
    intro q hq
    simp only [F, collarSplit_inv e hq]
  -- the target distance of two chart values
  have hdF : ∀ q q' : CuspHalfSpace,
      dist (WithLp.toLp 2 ((q.2.val 0 - z₀) / r, φT q.1) : WithLp 2 (ℝ × Y))
          (WithLp.toLp 2 ((q'.2.val 0 - z₀) / r, φT q'.1)) =
        r⁻¹ * Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) *
          (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2) := by
    intro q q'
    have h := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 ((q.2.val 0 - z₀) / r, φT q.1) : WithLp 2 (ℝ × Y))
      (WithLp.toLp 2 ((q'.2.val 0 - z₀) / r, φT q'.1))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, hdY] at h
    have hexp : Real.exp (-z₀ / 2) ^ 2 = Real.exp (-z₀) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hrhs : 0 ≤ r⁻¹ * Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) *
        (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2) := by positivity
    have hsq : (r⁻¹ * Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) *
        (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2)) ^ 2 =
        |(q.2.val 0 - z₀) / r - (q'.2.val 0 - z₀) / r| ^ 2 +
          (r⁻¹ * Real.exp (-z₀ / 2) *
            (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs, mul_pow, mul_pow, hexp]
      field_simp
      ring
    rw [← hsq] at h
    exact (sq_eq_sq₀ dist_nonneg hrhs).mp h
  refine @hasEuclideanSplitting_one_of_bilipschitz_product W.Carrier mX Y _ (e.toFun q₀)
    (φT q₀.1) β a hβ hβ1 ha ha1 herr F ?_ ?_ ?_
  · rw [hFq q₀ hq₀, ← hz₀, sub_self, zero_div]
  · -- distortion
    intro x x' hx hx'
    rw [hdX] at hx hx' ⊢
    have hball : ∀ y : W.Carrier, r⁻¹ * (riemannianEDistOf g y (e.toFun q₀)).toReal ≤ R →
        riemannianEDistOf g (e.toFun q₀) y <
          ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
      intro y hy
      have hle : (riemannianEDistOf g y (e.toFun q₀)).toReal ≤ ρ₁ := by
        rw [hρ₁]
        have := (inv_mul_le_iff₀ hr).mp hy
        linarith
      rw [riemannianEDistOf_comm, ← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g _ _)]
      refine (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mpr ?_
      nlinarith
    obtain ⟨q, hq, q', hq', rfl, rfl, -, -, hlo, hhi⟩ :=
      e.frozen_bilipschitz_toReal (ρ₁ := ρ₁) (by rw [hρ₁]; linarith) (by rw [hρ₁]; linarith)
        (hball x hx) (hball x' hx')
    rw [hFq q hq, hFq q' hq', hdF q q']
    set Q : ℝ := Real.sqrt ((q'.2.val 0 - q.2.val 0) ^ 2 + Real.exp (-z₀) *
      (riemannianEDistOf e.cusp.torusMetric q.1 q'.1).toReal ^ 2) with hQ
    set D : ℝ := (riemannianEDistOf g (e.toFun q) (e.toFun q')).toReal with hD
    have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
    have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
    have he8 : Real.exp (-(8 * ρ₁) / 2) = (Real.exp (4 * ρ₁))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    have he8' : Real.exp (8 * ρ₁ / 2) = Real.exp (4 * ρ₁) := by
      congr 1
      ring
    rw [he8] at hlo
    rw [he8'] at hhi
    have hE : 0 < Real.exp (4 * ρ₁) := Real.exp_pos _
    have hsq : 0 < Real.sqrt (1 - δ) := by linarith
    -- upper: Q ≤ (1 + a) D
    have hQD : Q ≤ (1 + a) * D := by
      have h1 : Real.sqrt (1 - δ) * Q ≤ Real.exp (4 * ρ₁) * D := by
        have := hlo
        rw [← mul_assoc, mul_comm (Real.sqrt (1 - δ)), mul_assoc] at this
        have h2 := (inv_mul_le_iff₀ hE).mp this
        linarith
      have h3 : Real.sqrt (1 - δ) * Q ≤ (1 + a) * Real.sqrt (1 - δ) * D := by
        calc Real.sqrt (1 - δ) * Q ≤ Real.exp (4 * ρ₁) * D := h1
          _ ≤ (1 + a) * Real.sqrt (1 - δ) * D := mul_le_mul_of_nonneg_right hL hD0
      nlinarith
    -- lower: (1 - a) D ≤ Q
    have hDQ : (1 - a) * D ≤ Q := by
      have hS : (1 - a) * Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) ≤ 1 := by
        have h1a : 0 ≤ 1 - a := by linarith
        have hsq' : Real.sqrt ((1 - a) ^ 2 * ((1 + δ) * Real.exp (4 * ρ₁))) ≤ 1 := by
          have h1 := Real.sqrt_le_sqrt hU
          rwa [Real.sqrt_one] at h1
        rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1a] at hsq'
      have hhi' : D ≤ Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) * Q := by
        rw [hD, hQ, ← Real.sqrt_mul (by positivity)]
        exact hhi
      have h1a : 0 ≤ 1 - a := by linarith
      calc (1 - a) * D ≤ (1 - a) * (Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁)) * Q) :=
            mul_le_mul_of_nonneg_left hhi' h1a
        _ = ((1 - a) * Real.sqrt ((1 + δ) * Real.exp (4 * ρ₁))) * Q := by ring
        _ ≤ 1 * Q := mul_le_mul_of_nonneg_right hS hQ0
        _ = Q := one_mul Q
    have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
    constructor
    · calc (1 - a) * (r⁻¹ * D) = r⁻¹ * ((1 - a) * D) := by ring
        _ ≤ r⁻¹ * Q := mul_le_mul_of_nonneg_left hDQ hrinv.le
    · calc r⁻¹ * Q ≤ r⁻¹ * ((1 + a) * D) := mul_le_mul_of_nonneg_left hQD hrinv.le
        _ = (1 + a) * (r⁻¹ * D) := by ring
  · -- coverage by exact preimages
    intro y hy
    set s : ℝ := y.fst with hs
    obtain ⟨t, ht⟩ := hφT y.snd
    have hy2 := WithLp.prod_dist_sq_eq_add_sq y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero] at hy2
    rw [← hs, ← ht, hdY] at hy2
    have hdy0 : 0 ≤ dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) := dist_nonneg
    have hβR : 0 ≤ R - β / 4 := by
      have : β / 4 < R := by
        rw [hR]
        have := inv_pos.mpr hβ
        linarith
      linarith
    have hsabs : |s| ≤ R := by
      have h1 : |s| ^ 2 ≤ dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2 := by
        rw [hy2]
        nlinarith [sq_nonneg (r⁻¹ * Real.exp (-z₀ / 2) *
          (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal)]
      have h2 := abs_le_of_sq_le_sq' h1 hdy0
      have h3 : |s| ≤ dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) := h2.2
      linarith
    have hrs : |r * s| ≤ ρ₁ := by
      rw [abs_mul, abs_of_pos hr, hρ₁]
      exact mul_le_mul_of_nonneg_left hsabs hr.le
    have hlo' : |r * s| < z₀ := by linarith
    have hup' : z₀ + |r * s| < 100 := by
      have : z₀ + 8 * ρ₁ < 100 := hup
      linarith
    let q : CuspHalfSpace := (t, halfSpaceOneLift (z₀ + r * s))
    have hqz : q.2.val 0 = z₀ + r * s := by
      change (halfSpaceOneLift (z₀ + r * s)).1 0 = _
      rw [halfSpaceOneLift_val_zero, max_eq_left]
      linarith [neg_abs_le (r * s)]
    have hq : q ∈ cuspDomain := by
      change q.2.val 0 < cuspDepth
      rw [hqz]
      have : z₀ + |r * s| < 100 := hup'
      have h := le_abs_self (r * s)
      change z₀ + r * s < 100
      linarith
    refine ⟨e.toFun q, ?_, ?_⟩
    · rw [hdX]
      have hcov := e.riemannianEDistOf_lift_le (q₀ := q₀) t hlo' hup'
      have hle : (riemannianEDistOf g (e.toFun q) (e.toFun q₀)).toReal ≤
          Real.sqrt ((1 + δ) * Real.exp |r * s| * ((r * s) ^ 2 + Real.exp (-z₀) *
            (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal ^ 2)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hcov
      have hexp : Real.exp (-z₀ / 2) ^ 2 = Real.exp (-z₀) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      -- the bracket is `r² · dist(y, base)²`
      have hbr : (r * s) ^ 2 + Real.exp (-z₀) *
          (riemannianEDistOf e.cusp.torusMetric t q₀.1).toReal ^ 2 =
          r ^ 2 * dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2 := by
        rw [hy2, sq_abs, mul_pow, mul_pow, mul_pow, hexp]
        field_simp
      rw [hbr] at hle
      have hexpR : Real.exp |r * s| ≤ Real.exp ρ₁ := Real.exp_le_exp.mpr hrs
      have hroot : Real.sqrt ((1 + δ) * Real.exp |r * s| *
          (r ^ 2 * dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2)) ≤ r * R := by
        rw [show r * R = Real.sqrt ((r * R) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        refine Real.sqrt_le_sqrt ?_
        have hdy : dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2 ≤ (R - β / 4) ^ 2 :=
          pow_le_pow_left₀ hdy0 hy 2
        have hC' : (1 + δ) * Real.exp |r * s| * (R - β / 4) ^ 2 ≤ R ^ 2 := by
          calc (1 + δ) * Real.exp |r * s| * (R - β / 4) ^ 2
              ≤ (1 + δ) * Real.exp ρ₁ * (R - β / 4) ^ 2 := by gcongr
            _ ≤ R ^ 2 := hC
        calc (1 + δ) * Real.exp |r * s| * (r ^ 2 * dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2)
            = r ^ 2 * ((1 + δ) * Real.exp |r * s| *
                dist y (WithLp.toLp 2 ((0 : ℝ), φT q₀.1)) ^ 2) := by ring
          _ ≤ r ^ 2 * ((1 + δ) * Real.exp |r * s| * (R - β / 4) ^ 2) := by gcongr
          _ ≤ r ^ 2 * R ^ 2 := by gcongr
          _ = (r * R) ^ 2 := by ring
      have := hle.trans hroot
      rw [inv_mul_le_iff₀ hr]
      exact this
    · rw [hFq q hq, hqz]
      have hyq : WithLp.toLp 2 ((z₀ + r * s - z₀) / r, φT q.1) = y := by
        have h1 : (z₀ + r * s - z₀) / r = s := by
          field_simp
          ring
        rw [h1]
        change WithLp.toLp 2 (y.fst, φT t) = y
        rw [ht]
        rfl
      rw [hyq, dist_self]
      positivity

/-- **F-f.B (explicit budget).** The torus factor is `T²` itself with the distance
`r⁻¹ e^{−z₀/2} d_{g_T}` (the residual flat factor `r⁻² e^{−z₀} g_T`). -/
theorem CuspEmbedding.hasEuclideanSplitting_frozen [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace} {β a r : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ha : 0 ≤ a) (ha1 : a < 1) (herr : 2 * a * (β⁻¹ + β) < β / 4) (hr : 0 < r)
    (hlow : 4 * (r * (β⁻¹ + β)) < q₀.2.val 0)
    (hup : q₀.2.val 0 + 8 * (r * (β⁻¹ + β)) < cuspDepth) (hδ : δ < 3 / 4)
    (hL : Real.exp (4 * (r * (β⁻¹ + β))) ≤ (1 + a) * Real.sqrt (1 - δ))
    (hU : (1 - a) ^ 2 * ((1 + δ) * Real.exp (4 * (r * (β⁻¹ + β)))) ≤ 1)
    (hC : (1 + δ) * Real.exp (r * (β⁻¹ + β)) * (β⁻¹ + β - β / 4) ^ 2 ≤ (β⁻¹ + β) ^ 2) :
    @HasEuclideanSplitting.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
      (e.toFun q₀) 1 β :=
  @CuspEmbedding.hasEuclideanSplitting_of_torus_isometry W g K δ X _ e q₀ β a r hβ hβ1 ha ha1
    herr hr hlow hup hδ hL hU hC Torus
    ((inducedMetricSpace e.cusp.torusMetric).rescale (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
      (mul_pos (inv_pos.mpr hr) (Real.exp_pos _))) id surjective_id (fun _ _ => rfl)

/-- `e^x (1 − x) ≤ 1`. -/
private theorem collarSplit_exp_mul_le (x : ℝ) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 0 < Real.exp x := Real.exp_pos x
  nlinarith

/-- The scale budget: `r (β⁻¹ + β) ≤ β²/1000` for `r ≤ β³/2000`, `0 < β < 1`. -/
theorem collarSplit_scale_le {β r : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hrβ : r ≤ β ^ 3 / 2000) : r * (β⁻¹ + β) ≤ β ^ 2 / 1000 := by
  have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  have h1 : r * β⁻¹ ≤ β ^ 2 / 2000 := by
    calc r * β⁻¹ ≤ β ^ 3 / 2000 * β⁻¹ := mul_le_mul_of_nonneg_right hrβ (inv_pos.mpr hβ).le
      _ = β ^ 2 / 2000 * (β * β⁻¹) := by ring
      _ = β ^ 2 / 2000 := by rw [hinv, mul_one]
  have h2 : r * β ≤ β ^ 2 / 2000 := by
    have : β ^ 4 ≤ β ^ 2 := pow_le_pow_of_le_one hβ.le hβ1.le (by norm_num)
    nlinarith
  nlinarith

/-- **F-f.B (clean form).** For `0 < β < 1`, a point `q₀` at height `5 ≤ z₀ ≤ 95`,
`δ ≤ β²/1000` and `0 < r ≤ β³/2000`, the rescaled carrier `(W, r⁻¹ d_g)` has a rank-one splitting
at `e q₀` at scale `β`; the splitting map is the frozen chart into `ℝ ×₂ (T², r⁻¹e^{−z₀/2} d_{g_T})`. -/
theorem CuspEmbedding.hasEuclideanSplitting_frozen_of_small [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X) {q₀ : CuspHalfSpace} {β r : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hz5 : 5 ≤ q₀.2.val 0) (hz95 : q₀.2.val 0 ≤ 95) (hδ : δ ≤ β ^ 2 / 1000) (hr : 0 < r)
    (hrβ : r ≤ β ^ 3 / 2000) :
    @HasEuclideanSplitting.{u, 0} W.Carrier ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr))
      (e.toFun q₀) 1 β := by
  have hδ0 : 0 ≤ δ := e.delta_nonneg
  set b : ℝ := β ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hb1 : b < 1 := by nlinarith
  set ρ₁ : ℝ := r * (β⁻¹ + β) with hρ₁
  have hρ : ρ₁ ≤ b / 1000 := collarSplit_scale_le hβ hβ1 hrβ
  have hρ0 : 0 < ρ₁ := mul_pos hr (by positivity)
  have hsqrt : 1 - δ ≤ Real.sqrt (1 - δ) := by
    have h0 : 0 ≤ 1 - δ := by nlinarith
    have h1 : 1 - δ ≤ 1 := by linarith
    calc 1 - δ = Real.sqrt ((1 - δ) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - δ) := Real.sqrt_le_sqrt (by nlinarith)
  have hE4 := collarSplit_exp_mul_le (4 * ρ₁)
  have hE1 := collarSplit_exp_mul_le ρ₁
  have hE4p : 0 < Real.exp (4 * ρ₁) := Real.exp_pos _
  have hE1p : 0 < Real.exp ρ₁ := Real.exp_pos _
  refine e.hasEuclideanSplitting_frozen (a := b / 40) hβ hβ1 (by positivity) (by linarith) ?_ hr
    ?_ ?_ (by nlinarith) ?_ ?_ ?_
  · -- herr
    have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have h3 : β ^ 3 < 4 * β := by nlinarith
    calc 2 * (b / 40) * (β⁻¹ + β) = β / 20 * (β * β⁻¹) + β ^ 3 / 20 := by rw [hb]; ring
      _ = β / 20 + β ^ 3 / 20 := by rw [hinv, mul_one]
      _ < β / 4 := by linarith
  · linarith
  · have : q₀.2.val 0 + 8 * ρ₁ < 100 := by linarith
    simpa [cuspDepth] using this
  · -- hL
    have hprod : 1 ≤ (1 + b / 40) * (1 - δ) * (1 - 4 * ρ₁) := by
      have h1 : 1 - δ - 4 * ρ₁ ≤ (1 - δ) * (1 - 4 * ρ₁) := by nlinarith
      have h2 : 1 - b / 200 ≤ 1 - δ - 4 * ρ₁ := by linarith
      nlinarith
    have hpos : 0 < 1 - 4 * ρ₁ := by linarith
    have h1 : Real.exp (4 * ρ₁) ≤ (1 + b / 40) * (1 - δ) := by
      have : Real.exp (4 * ρ₁) * (1 - 4 * ρ₁) ≤ (1 + b / 40) * (1 - δ) * (1 - 4 * ρ₁) := by
        linarith
      exact le_of_mul_le_mul_right this hpos
    calc Real.exp (4 * ρ₁) ≤ (1 + b / 40) * (1 - δ) := h1
      _ ≤ (1 + b / 40) * Real.sqrt (1 - δ) := by gcongr
  · -- hU
    have hsq : (1 - b / 40) ^ 2 ≤ 1 - b / 40 := by nlinarith
    have h2 : (1 - b / 40) * (1 + δ) ≤ 1 - 4 * ρ₁ := by nlinarith
    have h3 : (1 - b / 40) ^ 2 * (1 + δ) ≤ 1 - 4 * ρ₁ := by nlinarith
    nlinarith
  · -- hC
    set R : ℝ := β⁻¹ + β with hR
    have hRβ : R * β = 1 + b := by
      rw [hR, hb, add_mul, inv_mul_cancel₀ hβ.ne']
      ring
    have hR0 : 0 < R := by positivity
    have hRb : R - β / 4 ≤ R * (1 - b / 8) := by nlinarith
    have hR4 : 0 ≤ R - β / 4 := by nlinarith
    have hsq : (R - β / 4) ^ 2 ≤ R ^ 2 * (1 - b / 8) := by
      have h1 : (R - β / 4) ^ 2 ≤ (R * (1 - b / 8)) ^ 2 := pow_le_pow_left₀ hR4 hRb 2
      have h2 : (1 - b / 8) ^ 2 ≤ 1 - b / 8 := by nlinarith
      nlinarith [sq_nonneg R]
    have h3 : (1 + δ) * (1 - b / 8) ≤ 1 - ρ₁ := by nlinarith
    have h4 : (1 + δ) * Real.exp ρ₁ * (1 - b / 8) ≤ 1 := by nlinarith
    calc (1 + δ) * Real.exp ρ₁ * (R - β / 4) ^ 2 ≤ (1 + δ) * Real.exp ρ₁ * (R ^ 2 * (1 - b / 8)) :=
          by gcongr
      _ = R ^ 2 * ((1 + δ) * Real.exp ρ₁ * (1 - b / 8)) := by ring
      _ ≤ R ^ 2 * 1 := by gcongr
      _ = R ^ 2 := mul_one _

end DifferentialGeometry.Geometry.Collapse
