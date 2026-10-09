import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightBinding
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightCircleDifferential

/-!
# BCG02 at a circle reference on the LC88 boundary data: value AND differential clause (lane BCG-7, G6)

Blueprint 207B, BCG02 (`B:8822–8958`), circle references, bound to the boundary data of LC88 exactly as
BCG-1's value binding `bcg02_circle_value_BCG1` (collar packet `P` with its OWN height `η_b`, the
ORIGINAL scale `ρ`, the completion `ĝ = g°` on `{D ≥ 4}`, BCP04.a at `n`, the regionalised packets `F`
on `(W°, d_ĝ, ρ ∘ val)`): if the `b`th closed boundary support meets `D_a = B_g(j, 10ρ(j))` at a
circle centre `j`, then with `U_b = (η_b − η_b(j))/ρ(j)` there is ONE unit row `A_b : ℝ² → ℝ¹` with

* `‖e₀U_b − A_b(η_a − η_a(j))‖ < θ` on `B_ĝ(j, 10ρ(j))` (the value clause), and
* `‖DU_b − (A_bDη_a)₀‖ < θ` at every point of `B_ĝ(j, 10ρ(j))`, norms of `ρ(j)⁻²ĝ` (the differential
  clause), `η_a` the circle chart coordinate.

Extra requests beyond the value binding (BCG02: "reference adapted qualities, raw errors and cusp norm
errors below `θ²/10⁸`, and impose `2r∂(12L + 1000) < θ²/10⁸`"; here with the circle's constants):
`θ < 1`, `γ, β₂ ≤ θ²/10⁷`, `ε_B, w₀ ≤ θ²/(4·10⁷)` (B4's norm error `2(ε_B + w₀)`), B5's physical-scale
clause `2ρ(e_i q)(12L_b + 1000) < θ²/10⁸` on `z ≤ 96` (`L_b ≥ 0`; T3B/BCUSP-1 G5 conjunct), and
`32·130 ≤ n` (consumer balls `B_ĝ(j, 520ρ(j))` for the test geodesics).

Route: BCG-1's binding (BCG01.b band, BCP02 splitting with coordinate EXACTLY `U_b`, transport to
`W°`), then BCG-7 G5's abstract step with `U = U_b`; its two analytic inputs come from BCG-7 G2:
`abs_mvfderiv_affineHeight_completion_le_BCG7` (B4 norm on `W°`; every point of `D_a` is a band point
`19 < z < 91` by BCG01.b, `D > 4` by the consumer-domain clause) and `bcg02_taylor_test_BCG7` (B4's
Taylor certificate along the normalized test geodesics, which stay in `B_ĝ(j, 520ρ(j)) ⊆ {D > 4}`).

* `bcg02_circle_differential_BCG7` (per carrier); consumer `abs_le_of_differential_clause_BCG7` (the
  shape of the differential clause with a reference norm bound `|h u| ≤ C|u|` gives `|f u| ≤ (C + θ)|u|`,
  the form in which BCG03's model-block bounds use `DU_b`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG02 at a circle reference on the LC88 boundary data: value AND differential clause with ONE unit
row** (see the module docstring). -/
theorem bcg02_circle_differential_BCG7 {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n Lb : ℝ}
      (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)),
      1 ≤ K → 0 ≤ Λ →
      (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
      32 * η⁻¹ ≤ n → 0 < β 1 → 2 * β 1 ≤ η → w₀ ≤ β 1 ^ 2 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
      10 * Λ ≤ 1 / 2 → 3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → σ⁻¹ ≤ Lmax →
      γ ≤ θ ^ 2 / 10000000 → β 2 ≤ θ ^ 2 / 10000000 → εB ≤ θ ^ 2 / 40000000 →
      w₀ ≤ θ ^ 2 / 40000000 → 0 ≤ Lb →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        2 * ρ ((P.cusp.collar i).toFun q) * (12 * Lb + 1000) < θ ^ 2 / 10 ^ 8) →
      32 * 130 ≤ n →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.circle.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb), riemannianEDistOf g j.val x < ENNReal.ofReal (10 * ρ j)) →
      ∃ Ab : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 10 * ρ j →
          ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
            Ab ((let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord y) -
              (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
                c.coord j))‖ < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j)
              x u -
            Ab (mvfderiv 𝓘(ℝ, E3) (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord)
              x u) 0| ≤
            θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
              x u u) := by
  obtain ⟨σ, hσ, hσ1, η₀, hη₀, habs⟩ := bcg02_circle_differential_of_split_BCG7 hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, min η₀ (1 / 2), lt_min hη₀ (by norm_num), min_le_right _ _, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n Lb ĝ hK
    hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛ10 hν3 hβ3 hβ2 hσL hγθ hβθ hεθ hwθ hLb hB5 hn130 hcN
    U₁ U₂ hU₁ F j hj bb hmeet
  let instM_BCG1 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  set η : ℝ := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hρj : 0 < ρ j := hρ j
  have hβ14 : β 1 ≤ 1 / 4 := by linarith
  have hβ13 : β 1 ^ 3 ≤ 1 / 64 := by
    have h := pow_le_pow_left₀ hβ1.le hβ14 3
    norm_num at h ⊢
    linarith
  have hβ3pos : 0 < β 1 ^ 3 := pow_pos hβ1 3
  have hb2 : β 1 ^ 2 ≤ 1 / 16 := by nlinarith only [hβ1, hβ14]
  have hεB4 : εB ≤ 1 / 4 := by linarith only [hεβ, hb2]
  -- BCG01.b: the reference centre is a band point of the `bb`th collar, `ρ(j) < 2 r_∂`
  have hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < β 1 ^ 3 / 1000 := fun i q hq => by
    have := hcol i q hq
    linarith
  obtain ⟨hρ2, hband⟩ := P.bcg01_reference_domain hεB4 hρ hΛ hlip hsmall (L := 11) (C := 10)
    (by norm_num) (by norm_num) (by linarith only [hΛ10] : Λ * 10 ≤ 1 / 2)
    (by nlinarith only [hβ13] : β 1 ^ 3 / 1000 * (1000 * 11) < 1) hmeet
  have hjD : riemannianEDistOf g j.val j.val < ENNReal.ofReal (10 * ρ j) := by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨q₀, -, hq₀j, hz19, hz91, hη19, hη91⟩ := hband j.val hjD
  -- BCP02 at `p_a = j` with coordinate EXACTLY `U_b`
  have hρη : ρ j ≤ η ^ 3 / 2000 := by
    have h8 : (2 * β 1) ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (by positivity) hβη 3
    linarith only [hρ2, h8, (by ring : (2 * β 1) ^ 3 = 8 * β 1 ^ 3), pow_pos hη 3]
  have hwη : w₀ ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    linarith only [hwβ, h4, (by ring : (2 * β 1) ^ 2 = 4 * β 1 ^ 2), sq_nonneg (β 1)]
  have hεη : εB ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    linarith only [hεβ, h4, (by ring : (2 * β 1) ^ 2 = 4 * β 1 ^ 2), sq_nonneg (β 1)]
  have hε1000 : εB ≤ 1 / 1000 := by linarith only [hεβ, hb2]
  have hηj5 : 5 ≤ P.height bb ((P.cusp.collar bb).toFun q₀) := by rw [hq₀j]; linarith
  have hηj95 : P.height bb ((P.cusp.collar bb).toFun q₀) ≤ 95 := by rw [hq₀j]; linarith
  have hKL := P.exists_kleinerLott_height_BCG1 hK hε1000 bb q₀ hρj hη (by linarith) hwη hεη hρη
    (by linarith) (by linarith) hηj5 hηj95
  let mT : MetricSpace Torus := (inducedMetricSpace (P.cusp.collar bb).cusp.torusMetric).rescale
    ((ρ j)⁻¹ * Real.exp (-(q₀.2.val 0) / 2)) (mul_pos (inv_pos.mpr hρj) (Real.exp_pos _))
  obtain ⟨t₀, f, hf⟩ := hKL
  -- transport to `(W°, R_a⁻¹ d_ĝ)` on the consumer ball
  have hj5 : ENNReal.ofReal 5 < distanceToBoundary W g j := hU₁ j (F.circle.centres_subset hj).1
  have hη0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  obtain ⟨-, hdistC⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ hη0 hbcp hn j hj5
  obtain ⟨himgC, -⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ (C := η⁻¹ / 4)
    (by positivity) hbcp (by linarith) j hj5
  have h4 : 4 * (η⁻¹ / 4) * ρ j = η⁻¹ * ρ j := by ring
  rw [h4] at himgC
  have hballN : @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ =
      @ball (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toPseudoMetricSpace j (η⁻¹ * ρ j) := by
    rw [← MetricSpace.rescale_ball (inducedMetricSpace ĝ) (ρ j)⁻¹ (inv_pos.mpr hρj) j
      (η⁻¹ * ρ j)]
    congr 1
    field_simp
  have hballW : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j.val η⁻¹ =
      riemannianBallOf g j.val (η⁻¹ * ρ j) := by
    rw [← inducedMetricSpace_ball g j.val (η⁻¹ * ρ j),
      ← MetricSpace.rescale_ball (inducedMetricSpace g) (ρ j)⁻¹ (inv_pos.mpr hρj) j.val
      (η⁻¹ * ρ j)]
    congr 1
    field_simp
  have hiso : ∀ x ∈ @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹,
      ∀ y ∈ @ball (W.pieceInterior ⊤)
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹,
      @dist W.Carrier ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist
          x.val y.val =
        @dist (W.pieceInterior ⊤)
          ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist x y := by
    intro x hx y hy
    rw [hballN] at hx hy
    have he := hdistC x hx y hy
    rw [MetricSpace.rescale_dist, MetricSpace.rescale_dist]
    congr 1
    change (riemannianEDistOf g x.val y.val).toReal =
      @dist (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toDist x y
    rw [he]
    rfl
  have himg : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j.val η⁻¹ ⊆
      Subtype.val '' @ball (W.pieceInterior ⊤)
        ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ := by
    rw [hballW, hballN, ← himgC]
  have himg' : @ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace
        ((P.cusp.collar bb).toFun q₀) η⁻¹ ⊆
      Subtype.val '' @ball (W.pieceInterior ⊤)
        ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j η⁻¹ := by
    rw [hq₀j]
    exact himg
  let φ := @KleinerLottApprox.transportBall_BCG1 (W.pieceInterior ⊤) W.Carrier
    (WithLp 2 (ℝ × Torus)) ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj))
    ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ η f Subtype.val j
    hq₀j.symm hiso himg'
  have hθ2 : θ ^ 2 < 1 := by nlinarith only [hθ, hθ1]
  have hU : ∀ y : W.pieceInterior ⊤, (@KleinerLottApprox.toFun (W.pieceInterior ⊤) _
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst =
      (P.height bb y - P.height bb j) / ρ j := by
    intro y
    change (@KleinerLottApprox.toFun W.Carrier _
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f y.val).fst = _
    rw [hf, hq₀j]
  -- B5: the physical scale bounds `ρ(j)`
  have hρθ : ρ j ≤ θ ^ 2 / 10000000000 := by
    have h := hB5 bb q₀ (by linarith only [hz91])
    rw [hq₀j] at h
    have h1 : 2 * ρ j * 1000 ≤ 2 * ρ j * (12 * Lb + 1000) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLb]) (by positivity)
    linarith only [h, h1, sq_nonneg θ]
  have h4C : 4 * 130 * ρ j ≤ 1 := by linarith only [hρθ, hθ2]
  obtain ⟨-, hdist130⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ (C := 130)
    (by norm_num) hbcp hn130 j hj5
  -- every point of `D_a = B_ĝ(j, 10ρ(j))` is a band point of the `bb`th collar
  have hpos : ∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j → ∃ p ∈ cuspDomain,
      (P.cusp.collar bb).toFun p = x.val ∧ 19 < p.2.val 0 ∧ p.2.val 0 < 91 := by
    intro x hx
    have hxj : riemannianEDistOf g j.val x.val < ENNReal.ofReal (10 * ρ j) := by
      rw [hdist130 j (mem_ball_self (by positivity)) x (mem_ball.mpr (by linarith only [hx, hρj])), edist_dist,
        dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hx
    obtain ⟨q, hq, hqx, hz19, hz91, -, -⟩ := hband x.val hxj
    exact ⟨q, hq, hqx, hz19, hz91⟩
  have hδN0 : 0 ≤ 2 * (εB + w₀) := by
    have h1 : 0 < εB := P.tolerance_pos
    have h2 : 0 ≤ w₀ := (P.cusp.collar bb).delta_nonneg
    positivity
  obtain ⟨Ab, hAb, hval, hdiff⟩ := @habs (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ hcN _ ĝ
    (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V U₁ U₂ F hν3 hβ3 hβ2 hσL hγθ hβθ j hj Torus mT t₀ η hηη₀ φ
    (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j) hU (δN := 2 * (εB + w₀))
    hδN0 (by linarith only [hεθ, hwθ]) hρθ
    (fun x hx u => by
      obtain ⟨p, hp, hpx, hz19, hz91⟩ := hpos x hx
      have hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g x :=
        le_of_lt (lt_distanceToBoundary_of_consumer_BCG7 W g ĝ heq ρ hρ (C := 130) (by norm_num)
          hbcp hn130 j hj5 h4C x (by linarith only [hx, hρj]))
      exact abs_mvfderiv_affineHeight_completion_le_BCG7 W g ĝ P hK hε1000 heq bb hp
        (by linarith only [hz19]) (by linarith only [hz91]) x hpx.symm hD (P.height bb j) hρj u)
    (by
      dsimp only
      intro x hx w hw ℓ hℓ hℓ500
      have hxj : dist x j < 10 * ρ j := by
        have h : (ρ j)⁻¹ * dist x j < 10 := hx
        rw [inv_mul_lt_iff₀ hρj] at h
        linarith only [h]
      obtain ⟨p, hp, hpx, hz19, hz91⟩ := hpos x hxj
      have hρℓ : ρ j * ℓ ≤ 500 * ρ j := by
        have := mul_le_mul_of_nonneg_left hℓ500 hρj.le
        linarith only [this]
      exact bcg02_taylor_test_BCG7 W g ĝ P hK hε1000 heq ρ hρ (C := 130) (by norm_num) hbcp hn130
        bb (a := P.height bb j) hρj hcN j hj5 h4C x w hw _ rfl ℓ hℓ
        (by linarith only [hxj, hρℓ, hρj]) p hpx (by linarith only [hz19, hρℓ, h4C])
        (by linarith only [hz91, hρℓ, h4C]))
  exact ⟨Ab, hAb, hval, hdiff⟩

/-- **Consumer: the differential clause bounds `DU_b`.** If `|f u − h u| ≤ θ'|u|_g` with `θ' < θ` and
`|h u| ≤ C|u|_g`, then `|f u| ≤ (C + θ)|u|_g` (`f = DU_b`, `h = (A_bDη_a)₀`). -/
theorem abs_le_of_differential_clause_BCG7 {V : Type*} (q : V → ℝ) (f h : V → ℝ) {θ C : ℝ}
    (hq : ∀ u, 0 ≤ q u) (hdiff : ∃ θ' < θ, ∀ u, |f u - h u| ≤ θ' * q u)
    (hh : ∀ u, |h u| ≤ C * q u) (u : V) : |f u| ≤ (C + θ) * q u := by
  obtain ⟨θ', hθ', hle⟩ := hdiff
  have h1 : |f u| ≤ |f u - h u| + |h u| := by
    have := abs_add_le (f u - h u) (h u)
    rwa [sub_add_cancel] at this
  have h2 : θ' * q u ≤ θ * q u := mul_le_mul_of_nonneg_right hθ'.le (hq u)
  calc |f u| ≤ |f u - h u| + |h u| := h1
    _ ≤ θ' * q u + C * q u := add_le_add (hle u) (hh u)
    _ ≤ (C + θ) * q u := by linarith

end DifferentialGeometry.Geometry.Collapse
