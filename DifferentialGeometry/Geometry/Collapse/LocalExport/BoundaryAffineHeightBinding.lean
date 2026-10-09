import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryTransport
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02KL
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar

/-!
# BCG02, value clause at a circle reference, on the LC88 boundary data (lane BCG-1, G2)

Blueprint 207B, BCG02 (`B:8822–8889`), circle references, bound to the boundary data of LC88: the
collar packet `P` with its OWN height `η_b` (the SAME physical cusp height), the ORIGINAL scale `ρ`
on `W` (collar smallness `ρ ≤ β₁³/2000`), the completion `ĝ = g°` on `{D ≥ 4}` and the regionalised
packets `F` on `(W°, d_ĝ, ρ ∘ val)`. If the `b`th closed boundary support meets
`D_a = B_g(p_a, 10 R_a)` at a circle centre `p_a = j`, `R_a = ρ(j)`, then with
`U_b = (η_b − η_b(p_a))/R_a`:

`‖U_b − A_b(η_a − η_a(p_a))‖ < θ` on `B(j, 10ρ(j))`, for ONE unit row `A_b : ℝ² → ℝ¹`.

Route: BCG01.b puts `p_a` in the band (`19 < z, η_b < 91`) with `R_a < 2r_∂`; BCP02 at `p_a` with
coordinate EXACTLY `U_b` (`BoundaryCollarPacket.exists_kleinerLott_height_BCG1`); transport of
that splitting from `(W, R_a⁻¹ d_g)` to `(W°, R_a⁻¹ d_ĝ)` on the consumer ball
(`consumer_domain_completion_BDRY5`, BCP04.a at `n ≥ 32η⁻¹`); AC76 + FC20/21 and the circle value
error (`bcg02_circle_value_of_split_BCG1`).

* `bcg02_circle_value_BCG1` (per carrier; its hypotheses are clauses of the LC88 producer and the
  parameter requests `3β₂ ≤ σ`, `σ⁻¹ ≤ Lmax`, `γ ≤ θ/4`, `2β₁ ≤ η`, `w₀, ε_B ≤ β₁²/1000`).
The differential clause of BCG02 is not here (sheet `build-logs/resume/sheet-BCG-1.md`).
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

/-- **BCG02's value clause at a circle reference on the LC88 boundary data.** -/
theorem bcg02_circle_value_BCG1 {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n : ℝ}
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
      10 * Λ ≤ 1 / 2 → 3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → σ⁻¹ ≤ Lmax → γ ≤ θ / 4 →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V U₁ U₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.circle.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb), riemannianEDistOf g j.val x < ENNReal.ofReal (10 * ρ j)) →
      ∃ Ab : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
        ∀ y : W.pieceInterior ⊤, dist y j < 10 * ρ j →
          ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
            Ab ((let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord y) -
              (let c := F.circle.chart j hj;
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
                c.coord j))‖ < θ := by
  obtain ⟨σ, hσ, hσ1, η₀, hη₀, habs⟩ := bcg02_circle_value_of_split_BCG1 hθ hν hν1
  refine ⟨σ, hσ, hσ1, min η₀ (1 / 2), lt_min hη₀ (by norm_num), min_le_right _ _, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n ĝ hK hΛ
    hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛ10 hν3 hβ3 hβ2 hσL hγ hcN U₁ U₂ hU₁ F j hj bb hmeet
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
  have hεB4 : εB ≤ 1 / 4 := by nlinarith
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
  obtain ⟨Ab, hAb, hval⟩ := @habs (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ hcN _ ĝ
    (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V U₁ U₂ F hν3 hβ3 hβ2 hσL hγ j hj Torus mT t₀ η hηη₀ φ
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
