import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBinding

/-!
# Level margins of the enriched boundary base family (lane BCG-2, review 51 P1-A)

Review 51, question 3 (binding, constants corrected): every consumed radius is budgeted by BCP04.a
at ONE late `n`, on the completed interior `(W°, d_ĝ)` with `ĝ ≥ g°` (so `d_g ≤ d_ĝ`).

* `ofReal_lt_of_near_level_BCG2` (the general helper of review 51): `D(p) ≥ c + m`,
  `d_ĝ(a, p) < Cρ(a)`, `(c + 3)C ≤ mn` and BCP04.a at `a` give `D(a) > c`
  (`ofReal_ten_lt_of_near_BDRY5` is the case `c = 10`);
* `margin_level_completion_BCG2`: the margin of the revised edge regions — `p ∈ {D ≥ 35}`,
  `d_ĝ(a, p) < Δρ(a)` ⇒ `a ∈ {D > 20}`, for `23Δ ≤ 15n` (not the old `13Δ ≤ 10n`);
* `ofReal_lt_of_near_centre_BCG2` (centre form): `D(a) > c₁`, `d_ĝ(a, x) < Cρ(a)`,
  `(c₁ + 3)C ≤ (c₁ − c₀)n` and BCP04.a at `a` give `D(x) > c₀`;
* `ball_subset_level_completion_BCG2`: for `a ∈ {D > 20}` the ball `B_ĝ(a, 1000Δρ(a))` lies in
  `{D > 10}`, for `2300Δ ≤ n` (the domain of every revised edge packet, radius `1000Δρ ⊇ 100Δρ`);
* BCF02 replacement eligibility (B:9770–9790): `ten_delta_scale_lt_third_BCG2` (BCP04.a and
  `33Δ ≤ n` give `10Δρ(q) < D(q)/3` on `D(q) ≥ 35`), `replacement_level_of_third_BCG2`
  (`10Δρ(q) < D(q)/3`, `d_g(q, p) < 10Δρ(q)` ⇒ `D(p) > 2D(q)/3 ≥ 70/3`), and the tail form
  `replacement_eligible_BCG2` (`D(p) > 20` for every strong witness `p` with `d_g(q, p) < 10Δρ(q)`).
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

section Margins

variable (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

omit [ConnectedSpace W.Carrier] in
/-- BCP04.a at a point forces a finite distance to the boundary. -/
theorem distanceToBoundary_ne_top_of_bcp04a_BCG2 {p : W.Carrier} {r n : ℝ}
    (hbcp : n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
      (distanceToBoundary W g p).toReal / r) :
    distanceToBoundary W g p ≠ ⊤ := by
  intro htop
  rw [htop, ENNReal.toReal_top] at hbcp
  simp at hbcp

/-- **The general level helper (review 51).** A point `a` of `W°` that is `C ρ_a`-close for `d_ĝ`
to a point `p` with `D(p) ≥ c + m` has `D(a) > c`, by BCP04.a at `a` and `(c + 3) C ≤ m n`. -/
theorem ofReal_lt_of_near_level_BCG2
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (a p : W.pieceInterior ⊤) {ρa c m C n : ℝ} (hρa : 0 < ρa) (hc : 0 ≤ c) (hm : 0 < m)
    (hCn : (c + 3) * C ≤ m * n)
    (hbcp : n * (distanceToBoundary W g a).toReal / ((distanceToBoundary W g a).toReal + 3) <
      (distanceToBoundary W g a).toReal / ρa)
    (hp : ENNReal.ofReal (c + m) ≤ distanceToBoundary W g p)
    (hap : riemannianEDistOf ĝ a p < ENNReal.ofReal (C * ρa)) :
    ENNReal.ofReal c < distanceToBoundary W g a := by
  by_contra hca
  have hDa : distanceToBoundary W g a ≤ ENNReal.ofReal c := not_lt.mp hca
  have htop : distanceToBoundary W g a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDa
  set d := (distanceToBoundary W g a).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdc : d ≤ c := by
    rw [hd, ← ENNReal.ofReal_le_ofReal_iff hc, ENNReal.ofReal_toReal htop]
    exact hDa
  have hdpos : 0 < d := by
    by_contra hd0'
    have hd00 : d = 0 := le_antisymm (not_lt.mp hd0') hd0
    rw [hd00] at hbcp
    simp at hbcp
  have hnρ : n * ρa < d + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρa] at hbcp
    nlinarith
  -- `C ρ_a < m`
  have hCρ : C * ρa < m := by
    by_cases hC : C ≤ 0
    · nlinarith
    have hCpos : 0 < C := lt_of_not_ge hC
    have hn : 0 < n := by
      by_contra hn0
      have : m * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.mp hn0)
      nlinarith
    have h1 : C * (n * ρa) < C * (c + 3) := mul_lt_mul_of_pos_left (by linarith) hCpos
    nlinarith
  have : Nonempty (W.pieceInterior ⊤) := ⟨a⟩
  have hdist := (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle a p).trans_lt hap
  have htri := distanceToBoundary_le_add W g p.val a.val
  rw [riemannianEDistOf_comm] at htri
  have hlt : distanceToBoundary W g p < ENNReal.ofReal (c + m) := by
    calc distanceToBoundary W g p ≤ distanceToBoundary W g a + riemannianEDistOf g a.val p.val :=
          htri
      _ < ENNReal.ofReal c + ENNReal.ofReal m :=
          ENNReal.add_lt_add_of_le_of_lt htop hDa
            (hdist.trans_le (ENNReal.ofReal_le_ofReal hCρ.le))
      _ = ENNReal.ofReal (c + m) := by rw [← ENNReal.ofReal_add hc hm.le]
  exact (lt_irrefl _) (hp.trans_lt hlt)

/-- **The margin of the revised edge regions on `(W°, d_ĝ)`**: `p ∈ {D ≥ 35}`,
`d_ĝ(a, p) < Δ ρ(a)` ⇒ `a ∈ {D > 20}`, for `23 Δ ≤ 15 n` and BCP04.a. -/
theorem margin_level_completion_BCG2
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Δ n : ℝ} (hΔn : 23 * Δ ≤ 15 * n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p) :
    letI := inducedMetricSpace ĝ
    ∀ p ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 35 ≤ distanceToBoundary W g x}, ∀ a,
      dist a p < Δ * ρ a →
        a ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 20 < distanceToBoundary W g x} := by
  let _ := inducedMetricSpace ĝ
  intro p hp a hap
  obtain ⟨s, hs, hsD⟩ := exists_pos_ofReal_le_distanceToBoundary_BDRY1 W g a
  have hDa : 0 < distanceToBoundary W g a := (ENNReal.ofReal_pos.mpr hs).trans_le hsD
  have hvz : riemannianEDistOf ĝ a p < ENNReal.ofReal (Δ * ρ a) := by
    rw [inducedMetricSpace_hmetric ĝ a p]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hap
  refine ofReal_lt_of_near_level_BCG2 W g ĝ hle a p (hρ a) (by norm_num : (0 : ℝ) ≤ 20)
    (by norm_num : (0 : ℝ) < 15) (by linarith) (hbcp a hDa) ?_ hvz
  have h35 : (20 : ℝ) + 15 = 35 := by norm_num
  rw [h35]
  exact hp

/-- **Centre form of the level helper.** A point `x` that is `C ρ_a`-close for `d_ĝ` to a point
`a` with `D(a) > c₁` has `D(x) > c₀`, by BCP04.a at `a` and `(c₁ + 3) C ≤ (c₁ − c₀) n`. -/
theorem ofReal_lt_of_near_centre_BCG2
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (a x : W.pieceInterior ⊤) {ρa c₀ c₁ C n : ℝ} (hρa : 0 < ρa) (hc₀ : 0 ≤ c₀) (hc01 : c₀ < c₁)
    (hCn : (c₁ + 3) * C ≤ (c₁ - c₀) * n)
    (hbcp : n * (distanceToBoundary W g a).toReal / ((distanceToBoundary W g a).toReal + 3) <
      (distanceToBoundary W g a).toReal / ρa)
    (ha : ENNReal.ofReal c₁ < distanceToBoundary W g a)
    (hax : riemannianEDistOf ĝ a x < ENNReal.ofReal (C * ρa)) :
    ENNReal.ofReal c₀ < distanceToBoundary W g x := by
  have htop := distanceToBoundary_ne_top_of_bcp04a_BCG2 W g hbcp
  set d := (distanceToBoundary W g a).toReal with hd
  have hdc : c₁ < d := by
    rw [hd]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) htop).mp ha
  have hnρ : n * ρa < d + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρa] at hbcp
    nlinarith
  have hC : 0 < C := by
    by_contra hC0
    have h0 : ENNReal.ofReal (C * ρa) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hC0) hρa.le)
    rw [h0] at hax
    exact ENNReal.not_lt_zero hax
  have hn : 0 < n := by
    by_contra hn0
    have : (c₁ - c₀) * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hn0)
    nlinarith
  have hCle : C ≤ n := by nlinarith
  -- `C ρ_a ≤ d − c₀`
  have hCρ : C * ρa ≤ d - c₀ := by
    have h1 : C * (n * ρa) ≤ C * (d + 3) := mul_le_mul_of_nonneg_left hnρ.le hC.le
    have h2 : C * (d + 3) ≤ (d - c₀) * n := by nlinarith
    have h3 : n * (C * ρa) ≤ n * (d - c₀) := by nlinarith
    exact le_of_mul_le_mul_left h3 hn
  by_contra hx
  have hDx : distanceToBoundary W g x ≤ ENNReal.ofReal c₀ := not_lt.mp hx
  have hxtop : distanceToBoundary W g x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDx
  have : Nonempty (W.pieceInterior ⊤) := ⟨a⟩
  have hdist := (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle a x).trans_lt hax
  have htri := distanceToBoundary_le_add W g a.val x.val
  have hlt : distanceToBoundary W g a < ENNReal.ofReal d := by
    calc distanceToBoundary W g a ≤ distanceToBoundary W g x + riemannianEDistOf g a.val x.val :=
          htri
      _ < ENNReal.ofReal c₀ + ENNReal.ofReal (C * ρa) :=
          ENNReal.add_lt_add_of_le_of_lt hxtop hDx hdist
      _ = ENNReal.ofReal (c₀ + C * ρa) := by
          rw [← ENNReal.ofReal_add hc₀ (by positivity)]
      _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal (by linarith)
  rw [hd, ENNReal.ofReal_toReal htop] at hlt
  exact (lt_irrefl _) hlt

/-- **The domain of a revised edge packet** (review 51, question 2): for `a ∈ {D > 20}` the ball
`B_ĝ(a, 1000Δρ(a))` lies in `{D > 10}`, for `2300 Δ ≤ n` and BCP04.a. -/
theorem ball_subset_level_completion_BCG2
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Δ n : ℝ} (hΔn : 2300 * Δ ≤ n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p) :
    letI := inducedMetricSpace ĝ
    ∀ a ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 20 < distanceToBoundary W g x},
      ball a (1000 * Δ * ρ a) ⊆
        {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} := by
  let _ := inducedMetricSpace ĝ
  intro a ha x hx
  have hDa : 0 < distanceToBoundary W g a := lt_of_le_of_lt zero_le ha
  have hax : riemannianEDistOf ĝ a x < ENNReal.ofReal (1000 * Δ * ρ a) := by
    rw [inducedMetricSpace_hmetric ĝ a x]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr ?_
    rw [dist_comm]
    exact hx
  exact ofReal_lt_of_near_centre_BCG2 W g ĝ hle a x (hρ a) (by norm_num : (0 : ℝ) ≤ 10)
    (by norm_num : (10 : ℝ) < 20) (by linarith) (hbcp a hDa) ha hax

omit [ConnectedSpace W.Carrier] in
/-- **BCF02's fixed-buffer bound** (B:9779–9781): BCP04.a and `33 Δ ≤ n` give
`10 Δ ρ(q) < D(q)/3` at every `q` with `D(q) ≥ 35`. -/
theorem ten_delta_scale_lt_third_BCG2 (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Δ n : ℝ}
    (hΔ : 0 ≤ Δ) (hΔn : 33 * Δ ≤ n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (q : W.Carrier) (hq : ENNReal.ofReal 35 ≤ distanceToBoundary W g q) :
    10 * Δ * ρ q < (distanceToBoundary W g q).toReal / 3 := by
  have hpos : 0 < distanceToBoundary W g q :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hq
  have h := hbcp q hpos
  have htop := distanceToBoundary_ne_top_of_bcp04a_BCG2 W g h
  set d := (distanceToBoundary W g q).toReal with hd
  have hd35 : 35 ≤ d := by
    rw [hd]
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hq
  have hρq := hρ q
  have hnρ : n * ρ q < d + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρq] at h
    nlinarith
  rcases hΔ.eq_or_lt with hΔ0 | hΔpos
  · rw [← hΔ0]
    linarith
  have hn : 0 < n := by linarith
  have h1 : 30 * Δ * (n * ρ q) ≤ 30 * Δ * (d + 3) :=
    mul_le_mul_of_nonneg_left hnρ.le (by positivity)
  have h2 : 30 * Δ * (d + 3) < d * n := by nlinarith
  have h3 : n * (30 * Δ * ρ q) < n * d := by nlinarith
  have h4 : 30 * Δ * ρ q < d := lt_of_mul_lt_mul_left h3 hn.le
  linarith

omit [ConnectedSpace W.Carrier] in
/-- **BCF02's replacement eligibility, one witness** (B:9781–9785): if `10Δρ(q) < D(q)/3` and
`d_g(q, p) < 10Δρ(q)`, then `D(p) > 2D(q)/3`; in particular `D(p) > 70/3` when `D(q) ≥ 35`. -/
theorem replacement_level_of_third_BCG2 (ρ : W.Carrier → ℝ) {Δ : ℝ} (q p : W.Carrier)
    (hq : ENNReal.ofReal 35 ≤ distanceToBoundary W g q)
    (htop : distanceToBoundary W g q ≠ ⊤)
    (hthird : 10 * Δ * ρ q < (distanceToBoundary W g q).toReal / 3)
    (hqp : riemannianEDistOf g q p < ENNReal.ofReal (10 * Δ * ρ q)) :
    ENNReal.ofReal (70 / 3) < distanceToBoundary W g p := by
  set d := (distanceToBoundary W g q).toReal with hd
  have hd35 : 35 ≤ d := by
    rw [hd]
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hq
  by_contra hp
  have hDp : distanceToBoundary W g p ≤ ENNReal.ofReal (70 / 3) := not_lt.mp hp
  have hptop : distanceToBoundary W g p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDp
  have htri := distanceToBoundary_le_add W g q p
  have hlt : distanceToBoundary W g q < ENNReal.ofReal d := by
    calc distanceToBoundary W g q ≤ distanceToBoundary W g p + riemannianEDistOf g q p := htri
      _ < ENNReal.ofReal (70 / 3) + ENNReal.ofReal (d / 3) :=
          ENNReal.add_lt_add_of_le_of_lt hptop hDp
            (hqp.trans_le (ENNReal.ofReal_le_ofReal hthird.le))
      _ = ENNReal.ofReal (70 / 3 + d / 3) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by linarith)]
      _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal (by linarith)
  rw [hd, ENNReal.ofReal_toReal htop] at hlt
  exact (lt_irrefl _) hlt

omit [ConnectedSpace W.Carrier] in
/-- **BCF02's replacement eligibility on the tail** (B:9770–9790): for BCP04.a at `n` with
`33 Δ ≤ n`, every strong witness `p` with `d_g(q, p) < 10Δρ(q)` of a point `q` with `D(q) ≥ 35`
has `D(p) > 20`, so the maximality of the SAME revised edge family (centres at `D > 20`) applies. -/
theorem replacement_eligible_BCG2 (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Δ n : ℝ}
    (hΔ : 0 ≤ Δ) (hΔn : 33 * Δ ≤ n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (q p : W.Carrier) (hq : ENNReal.ofReal 35 ≤ distanceToBoundary W g q)
    (hqp : riemannianEDistOf g q p < ENNReal.ofReal (10 * Δ * ρ q)) :
    ENNReal.ofReal 20 < distanceToBoundary W g p := by
  have hpos : 0 < distanceToBoundary W g q :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hq
  have htop := distanceToBoundary_ne_top_of_bcp04a_BCG2 W g (hbcp q hpos)
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by norm_num : (20 : ℝ) ≤ 70 / 3))
    (replacement_level_of_third_BCG2 W g ρ q p hq htop
      (ten_delta_scale_lt_third_BCG2 W g ρ hρ hΔ hΔn hbcp q hq) hqp)

end Margins

end DifferentialGeometry.Geometry.Collapse
