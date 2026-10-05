import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBinding
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeLocality

/-!
# LC88 / BCP04: the original-metric transport clauses of T2 (lane BDRY-5, G19)

Review 45 §2.2 / §2.6 (T2 (iv), binding): on one tail, with the completion `ĝ = g°` on `{D ≥ 4}`
and the ORIGINAL scale `ρ` with BCP04.a (every radius budgeted, `n ≥ 32 C`):

* `scaledSplittingRank_completion_eq_BDRY5`: the scaled splitting ranks of `(W°, d_ĝ, ρ ∘ val)`
  and `(W, d_g, ρ)` agree on `U₀ = {D > 5}`;
* `consumer_domain_completion_BDRY5`: every per-centre consumer domain `B_ĝ(j, 4 C ρ(j))` at
  `j ∈ U₀` is the actual `g`-ball of `W`, and on `B_ĝ(j, C ρ(j))` the distances are those of `W`;
* `infDist_weakEdge_completion_eq_BDRY5`: the weak-edge distance of `ĝ` equals that of `g` on the
  active edge domain `B_ĝ(j, 200 Δ ρ(j))` of every `j ∈ U₀` lying in the closure of the weak-edge
  set of `ĝ` (an edge centre), by the metric locality `infDist_weakEdge_eq_of_ballIsometry_BDRY5`
  along `val` on `B_ĝ(j, (600Δ + 2β⁻¹) ρ(j))`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Transport

variable (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- **Ranks on `U₀`.** With BCP04.a and `32 R_β ≤ n`, `R_β = 1 + Σ_{k ≤ 3} |β_k⁻¹|`, the scaled
splitting ranks of `(W°, d_ĝ, ρ ∘ val)` and `(W, d_g, ρ)` agree at every point with `D > 5`. -/
theorem scaledSplittingRank_completion_eq_BDRY5
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 32 * (1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹|) ≤ n) :
    ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary W g x →
      @scaledSplittingRank.{0, 0} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
          (fun y => ρ y) (fun y => hρ y) β x =
        @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) ρ hρ β x.val := by
  intro x hx
  set R : ℝ := 1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹| with hR
  have h0 := abs_nonneg (β 0)⁻¹
  have h1 := abs_nonneg (β 1)⁻¹
  have h2 := abs_nonneg (β 2)⁻¹
  have h3 := abs_nonneg (β 3)⁻¹
  have hRpos : 0 < R := by rw [hR]; linarith
  have hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ R := by
    intro k hk
    interval_cases k
    · exact (le_abs_self _).trans (by rw [hR]; linarith)
    · exact (le_abs_self _).trans (by rw [hR]; linarith)
    · exact (le_abs_self _).trans (by rw [hR]; linarith)
    · exact (le_abs_self _).trans (by rw [hR]; linarith)
  have hb := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp (C := 4 * R / 3)
    (by positivity) (by linarith) x hx
  have he : 3 * (4 * R / 3) * ρ x + 4 = 4 * (R * ρ x) + 4 := by ring
  rw [he] at hb
  exact scaledSplittingRank_cut_eq_BDRY1 W g ĝ (by norm_num) heq ρ hρ β hRpos hβR x hb.le

/-- **Consumer domains are actual `g`-balls.** With BCP04.a and `32 C ≤ n`: at every `j ∈ W°`
with `D(j) > 5`, `val '' B_ĝ(j, 4 C ρ(j)) = B_g(j, 4 C ρ(j))`, and on `B_ĝ(j, C ρ(j))` the
distances of `ĝ` are those of `W`. -/
theorem consumer_domain_completion_BDRY5
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n C : ℝ} (hC : 0 ≤ C)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 32 * C ≤ n) :
    letI := inducedMetricSpace ĝ
    ∀ j : W.pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary W g j →
      Subtype.val '' Metric.ball j (4 * C * ρ j) = riemannianBallOf g j.val (4 * C * ρ j) ∧
      ∀ y ∈ Metric.ball j (C * ρ j), ∀ z ∈ Metric.ball j (C * ρ j),
        riemannianEDistOf g y.val z.val = edist y z := by
  let _ := inducedMetricSpace ĝ
  intro j hj
  have hb := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp (C := 4 * C / 3)
    (by positivity) (by linarith) j hj
  have he : 3 * (4 * C / 3) * ρ j + 4 = 4 * C * ρ j + 4 := by ring
  rw [he] at hb
  have hr : 0 ≤ 4 * C * ρ j := by have := hρ j; positivity
  refine ⟨?_, fun y hy z hz => ?_⟩
  · rw [inducedMetricSpace_ball ĝ j _]
    exact image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq j hr hb.le
  · rw [inducedMetricSpace_ball ĝ j _] at hy hz
    have h4 : C * ρ j = 4 * C * ρ j / 4 := by ring
    rw [h4] at hy hz
    rw [inducedMetricSpace_edist ĝ y z]
    exact (riemannianEDistOf_cut_eq_BDRY1 W g ĝ (by norm_num) heq j hr hb.le hy hz).symm

/-- **Weak-edge distance locality on the active edge domains (T2 (iv)).** For `ĝ = g°` on
`{D ≥ 4}`, `ĝ ≥ g°`, the ORIGINAL scale `ρ` (`Λ`-Lipschitz, `600 Δ Λ ≤ 1`, BCP04.a,
`32 (600 Δ + 2 β⁻¹) ≤ n`) and `j ∈ W°` with `D(j) > 5` in the closure of the `(Δ, β, σ)`-edge set
of `(W°, d_ĝ)` at scale `ρ`: on `B_ĝ(j, 200 Δ ρ(j))` the distance to the closure of that set equals
the `g`-distance in `W` to the closure of the edge set of `(W, d_g)`. -/
theorem infDist_weakEdge_completion_eq_BDRY5
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Λ Δ β σ n : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β)
    (hΛ : 0 ≤ Λ) (hΔΛ : 600 * Δ * Λ ≤ 1)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 32 * (600 * Δ + 2 * β⁻¹) ≤ n)
    (j : W.pieceInterior ⊤) (hj : ENNReal.ofReal 5 < distanceToBoundary W g j)
    (hjA : j ∈ closure {y : W.pieceInterior ⊤ |
      @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
        y Δ β σ}) :
    letI := inducedMetricSpace ĝ
    ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
      Metric.infDist x (closure {y : W.pieceInterior ⊤ |
          @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
            (inv_pos.mpr (hρ y))) y Δ β σ}) =
        @Metric.infDist W.Carrier (inducedMetricSpace g).toPseudoMetricSpace
          x.val (@closure W.Carrier _ {y : W.Carrier |
            @isEdgePoint.{0, 0} _ ((inducedMetricSpace g).rescale (ρ y)⁻¹
              (inv_pos.mpr (hρ y))) y Δ β σ}) := by
  let mN : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro x hx
  have hρj := hρ j
  have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
  set Rb : ℝ := (600 * Δ + 2 * β⁻¹) * ρ j with hRb
  have hRb0 : 0 ≤ Rb := by positivity
  have hb := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp
    (C := 4 * (600 * Δ + 2 * β⁻¹) / 3) (by positivity) (by linarith) j hj
  have he : 3 * (4 * (600 * Δ + 2 * β⁻¹) / 3) * ρ j + 4 = 4 * Rb + 4 := by rw [hRb]; ring
  rw [he] at hb
  have hb1 : ENNReal.ofReal (Rb + 4) ≤ distanceToBoundary W g j :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hb.le
  have hballN : ∀ r, ball j r = riemannianBallOf ĝ j r := fun r => inducedMetricSpace_ball ĝ j r
  have hdN : ∀ y z : W.pieceInterior ⊤, dist y z = (riemannianEDistOf ĝ y z).toReal :=
    fun y z => inducedMetricSpace_dist ĝ y z
  have hdist : ∀ y ∈ ball j Rb, ∀ z ∈ ball j Rb,
      @dist W.Carrier (inducedMetricSpace g).toDist y.val z.val = dist y z := by
    intro y hy z hz
    rw [hballN] at hy hz
    have h4 : Rb = 4 * Rb / 4 := by ring
    rw [h4] at hy hz
    rw [inducedMetricSpace_dist g, hdN,
      riemannianEDistOf_cut_eq_BDRY1 W g ĝ (by norm_num) heq j (by linarith) hb.le hy hz]
  have himage : Subtype.val '' ball j Rb =
      @ball W.Carrier (inducedMetricSpace g).toPseudoMetricSpace j.val Rb := by
    rw [hballN, inducedMetricSpace_ball g j.val _]
    exact image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq j hRb0 hb1
  have hlipN := lipschitzWith_comp_val_completion_BDRY5 W g ĝ hle hlip
  have hbud : ∀ y ∈ ball j (3 * (200 * Δ * ρ j)),
      3 * (200 * Δ * ρ j) + β⁻¹ * ρ y ≤ Rb := by
    intro y hy
    have hl := hlipN.dist_le_mul y j
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hl
    have hyj : dist y j < 3 * (200 * Δ * ρ j) := hy
    have hρy : ρ y ≤ 2 * ρ j := by
      have h1 : ρ y - ρ j ≤ Λ * dist y j := (le_abs_self _).trans hl
      have h2 : Λ * dist y j ≤ Λ * (3 * (200 * Δ * ρ j)) :=
        mul_le_mul_of_nonneg_left hyj.le hΛ
      have h3 : Λ * (3 * (200 * Δ * ρ j)) ≤ ρ j := by nlinarith
      linarith
    have h4 : β⁻¹ * ρ y ≤ β⁻¹ * (2 * ρ j) := mul_le_mul_of_nonneg_left hρy hβi.le
    rw [hRb]
    nlinarith
  have key := infDist_weakEdge_eq_of_ballIsometry_BDRY5 (m := inducedMetricSpace g) Subtype.val ρ hρ
    (fun y => ρ y) (fun y => hρ y) (fun _ => rfl) (by positivity) hβ hdist himage hbud hjA x hx
  convert key using 3

end Transport

end DifferentialGeometry.Geometry.Collapse
