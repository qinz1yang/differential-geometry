import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsB

/-!
# BCG02 at a slim reference (lane BCG-4)

Blueprint 207B, BCG02 (`B:8822–8889`), slim references: "for slim references [the absence of a
`(2, β₂)`-splitting] is their one-stratum property. Use AC76 and FC20 with ranks one and one as in
EGP03 and SGP02, obtaining a sign and the same raw comparison"; the value estimate follows once the
raw error and the slim value tolerance `v_s` (the enriched family's `slim_value`, LFR19) are below
`θ/4`. The reference domain is `D_a = B(p_a, .95 L R_a)`, `L = 10⁶Δ`.

* `bcg02_slim_value_of_split_BCG4`: the abstract step on an enriched boundary family
  `F : LocalPacketsOnB` — at every slim centre `j`, every rank-one Kleiner–Lott approximation `φ`
  of `(X, ρ(j)⁻¹d, j)` into `ℝ ×₂ T` of quality `≤ η` gives one sign `a` with
  `|u(y) − a(u_j(y) − u_j(j))| < θ` on `B(j, 950000Δρ(j))` (`u = (φ ·).fst`, `u_j` the slim
  coordinate `coord_BCG2`). The exclusion quality is `ν` with `3ν ≤ β₂ < 1` (one-stratum
  property, `KleinerLottApprox.weaken`); the slim split itself is the second factor map
  (quality `β₁`, `3β₁ ≤ σ`).
* `bcg02_slim_value_BCG4`: the LC88 binding (per carrier; hypotheses = producer clauses and the
  parameter requests), same route as `bcg02_edge_value_on_BCG2` with `C = 950000Δ`, `L = 10⁶Δ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **BCG02's value clause at a slim reference, abstract step** (enriched boundary family). For
`θ > 0`, an exclusion quality `ν < 1` and `Δ ≥ 1`: an early `σ` and a rank-one quality bound `η`;
at every slim centre `j` of `F` (with `3ν ≤ β₂ < 1`, `3β₁ ≤ σ`, `σ⁻¹ ≤ Lmax`,
`2β₁(950000Δ + 1) ≤ 1`, `vs ≤ θ/4`), every rank-one Kleiner–Lott `ε₁`-approximation `φ` of
`(X, ρ(j)⁻¹ d, j)` into `ℝ ×₂ T` (`ε₁ ≤ η`) gives one sign `a` with
`|u(y) − a(u_j(y) − u_j(j))| < θ` on `B(j, 950000Δρ(j))`. -/
theorem bcg02_slim_value_of_split_BCG4 {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hν1 : ν < 1)
    (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs U₁ U₂ Ue₁ Ue₂),
      3 * ν ≤ β 2 → β 2 < 1 → σ⁻¹ ≤ Lmax → 3 * β 1 ≤ σ → β 1 * (2 * (950000 * Δ + 1)) ≤ 1 →
      vs ≤ θ / 4 →
      ∀ (j : X) (hj : j ∈ F.slim.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ y, dist y j < 950000 * Δ * ρ j →
        |(@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _ φ y).fst -
          a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| < θ := by
  set H : ℝ := 950000 * Δ with hH
  have hH0 : 0 < H := by rw [hH]; linarith
  set τ' : ℝ := min (θ / 200) (1 / (2 * (H + 1))) with hτdef
  have hτ : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτθ : τ' ≤ θ / 200 := min_le_left _ _
  have hτH : τ' ≤ 1 / (2 * (H + 1)) := min_le_right _ _
  have hτ1 : τ' < 1 := by
    have : 1 / (2 * (H + 1)) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have ha : 20 * τ' ≤ H + 1 := by linarith
  have ha2 : 2 * (H + 1) ≤ τ'⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hτ]
    rwa [one_div] at hτH
  obtain ⟨σ, hσ, hσ1, hk⟩ := exists_sign_raw_alignment_real_complete_BCG1 hτ hτ1 hν hν1 ha ha2
  obtain ⟨η, hη, hk⟩ := hk 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂
    Ue₁ Ue₂ F hν2 hβ2 hσL h3β hβH hvs j hj Tm _ t₀ ε₁ hε₁ φ
  have hρj := hρ j
  have hjU : j ∈ U₁ := (F.slim.centres_subset hj).1
  have hsec := F.sectional_buffer σ⁻¹ (inv_pos.mpr hσ) hσL j hjU
  -- the one-stratum property: no `(2, ν)`-splitting at the slim centre
  have hrank : scaledSplittingRank ρ hρ β j = ((1 : Fin 4) : ℕ) := (F.slim.centres_subset hj).2.1
  have hno2 := (scaledSplittingRank_eq_iff.mp hrank).2.2 2 (by decide) (by decide)
  have hno : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) j 2 ν := by
    rintro ⟨Y, mY, q, ⟨f⟩⟩
    exact hno2 ⟨Y, mY, q, ⟨@KleinerLottApprox.weaken X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj))
      _ _ _ _ _ _ f hν2 hβ2⟩⟩
  have hr1 : ρ j / ρ j = 1 := div_self hρj.ne'
  let c := F.slim.centre j hj
  let _ : MetricSpace c.Z := c.instZ
  obtain ⟨a, ha, hlin⟩ := hk X g hmetric ρ hρ j j hsec hno (by rw [hr1]; norm_num)
    (by rw [hr1]; norm_num) (by rw [dist_self, zero_mul]) Tm c.Z t₀ c.z hε₁ h3β hβH φ c.split
  refine ⟨a, ha, fun y hy => ?_⟩
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hψj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      c.split j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ c.split]
    rfl
  have hmain := hlin y (by rw [mem_ball]; exact hy)
  rw [hr1, hφj, one_mul, mul_zero, sub_zero] at hmain
  have hΔρ : 0 < Δ * ρ j := mul_pos (by linarith) hρj
  have hyL : y ∈ ball j (10 ^ 6 * Δ * ρ j) := by
    rw [mem_ball]
    have h1 : 950000 * Δ * ρ j ≤ 10 ^ 6 * Δ * ρ j := by nlinarith
    linarith
  have hjL : j ∈ ball j (10 ^ 6 * Δ * ρ j) := mem_ball_self (by positivity)
  have ha1 : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  set u := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst
  set p := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
    c.split y).fst
  set cy := (F.slim.centre j hj).coord_BCG2 y
  set cj := (F.slim.centre j hj).coord_BCG2 j
  have hv1 : |cy - p| < vs := F.slim_value j hj y hyL
  have hv2 : |cj - 0| < vs := by
    have h := F.slim_value j hj j hjL
    rw [← hψj]
    exact h
  rw [sub_zero] at hv2
  have e1 : |a * (p - cy)| < vs := by
    rw [abs_mul, ha1, one_mul, abs_sub_comm]
    exact hv1
  have e2 : |a * cj| < vs := by
    rw [abs_mul, ha1, one_mul]
    exact hv2
  have hsplit : u - a * (cy - cj) = (u - a * p) + a * (p - cy) + a * cj := by ring
  calc |u - a * (cy - cj)| = |(u - a * p) + a * (p - cy) + a * cj| := by rw [hsplit]
    _ ≤ |(u - a * p) + a * (p - cy)| + |a * cj| := abs_add_le _ _
    _ ≤ |u - a * p| + |a * (p - cy)| + |a * cj| := by gcongr; exact abs_add_le _ _
    _ < 50 * τ' + vs + vs := by linarith
    _ ≤ θ := by linarith

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG02's value clause at a slim reference on the LC88 boundary data** (enriched boundary family
`F : LocalPacketsOnB`). If the `b`th closed boundary support meets `D_a = B_g(j, 950000Δρ(j))`
(`.95L`, `L = 10⁶Δ`) at a slim centre `j`: one sign `a_b` with `|U_b − a_b(u_j − u_j(j))| < θ` on
`B(j, 950000Δρ(j))`, `U_b = (η_b − η_b(j))/ρ(j)`, `u_j` the slim coordinate. -/
theorem bcg02_slim_value_BCG4 {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hν1 : ν < 1)
    (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs : ℝ}
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
      950000 * Δ * Λ ≤ 1 / 2 → 1000000 * Δ * β 1 ^ 3 < 1 → 3 * ν ≤ β 2 → β 2 < 1 →
      σ⁻¹ ≤ Lmax → 3 * β 1 ≤ σ → β 1 * (2 * (950000 * Δ + 1)) ≤ 1 → vs ≤ θ / 4 →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.slim.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        ∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
          |(P.height bb y - P.height bb j) / ρ j -
            a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| < θ := by
  obtain ⟨σ, hσ, hσ1, η₀, hη₀, habs⟩ := bcg02_slim_value_of_split_BCG4 hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, min η₀ (1 / 2), lt_min hη₀ (by norm_num), min_le_right _ _, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs ĝ hK hΛ
    hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛC hβΔ hν2 hβ2 hσL h3β hβH hvs hcN U₁ U₂ Ue₁ Ue₂ hU₁ F j
    hj bb hmeet
  let instM_BCG1 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  set η : ℝ := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hρj : 0 < ρ j := hρ j
  have hβ14 : β 1 ≤ 1 / 4 := by linarith
  have hβ3pos : 0 < β 1 ^ 3 := pow_pos hβ1 3
  have hεB4 : εB ≤ 1 / 4 := by nlinarith
  -- BCG01.b: the reference centre is a band point of the `bb`th collar, `ρ(j) < 2 r_∂`
  have hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < β 1 ^ 3 / 1000 := fun i q hq => by
    have := hcol i q hq
    linarith
  obtain ⟨hρ2, hband⟩ := P.bcg01_reference_domain hεB4 hρ hΛ hlip hsmall (L := 1000000 * Δ)
    (C := 950000 * Δ) (by linarith) (by linarith)
    (by linarith only [hΛC] : Λ * (950000 * Δ) ≤ 1 / 2)
    (by linarith only [hβΔ] : β 1 ^ 3 / 1000 * (1000 * (1000000 * Δ)) < 1) hmeet
  have hjD : riemannianEDistOf g j.val j.val < ENNReal.ofReal (950000 * Δ * ρ j) := by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨q₀, -, hq₀j, hz19, hz91, hη19, hη91⟩ := hband j.val hjD
  -- BCP02 at `p_a = j` with coordinate EXACTLY `U_b`
  have hρη : ρ j ≤ η ^ 3 / 2000 := by
    have h8 : (2 * β 1) ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (by positivity) hβη 3
    nlinarith
  have hwη : w₀ ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    nlinarith
  have hεη : εB ≤ η ^ 2 / 1000 := by
    have h4 : (2 * β 1) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hβη 2
    nlinarith
  have hε1000 : εB ≤ 1 / 1000 := by nlinarith
  have hηj5 : 5 ≤ P.height bb ((P.cusp.collar bb).toFun q₀) := by rw [hq₀j]; linarith
  have hηj95 : P.height bb ((P.cusp.collar bb).toFun q₀) ≤ 95 := by rw [hq₀j]; linarith
  have hKL := P.exists_kleinerLott_height_BCG1 hK hε1000 bb q₀ hρj hη (by linarith) hwη hεη hρη
    (by linarith) (by linarith) hηj5 hηj95
  let mT : MetricSpace Torus := (inducedMetricSpace (P.cusp.collar bb).cusp.torusMetric).rescale
    ((ρ j)⁻¹ * Real.exp (-(q₀.2.val 0) / 2)) (mul_pos (inv_pos.mpr hρj) (Real.exp_pos _))
  obtain ⟨t₀, f, hf⟩ := hKL
  -- transport to `(W°, R_a⁻¹ d_ĝ)` on the consumer ball
  have hj5 : ENNReal.ofReal 5 < distanceToBoundary W g j := hU₁ j (F.slim.centres_subset hj).1
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
  obtain ⟨Ab, hAb, hval⟩ := @habs (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ hcN _ ĝ
    (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β σs Kf σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ F hν2 hβ2 hσL h3β hβH hvs j hj Torus mT t₀ η hηη₀ φ
  refine ⟨Ab, hAb, fun y hy => ?_⟩
  have hfy : (@KleinerLottApprox.toFun (W.pieceInterior ⊤) _
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst =
      (P.height bb y - P.height bb j) / ρ j := by
    change (@KleinerLottApprox.toFun W.Carrier _
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f y.val).fst = _
    rw [hf, hq₀j]
  have h := hval y hy
  rw [hfy] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
