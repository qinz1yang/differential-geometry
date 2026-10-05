import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeDifferential
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFR

/-!
# BCG02 at a slim reference: value AND differential clause with ONE sign (lane BCG-8, G9)

Blueprint 207B, BCG02 (`B:8822–8958`), slim references (`D_a = B(p_a, .95LR_a)`, `L = 10⁶Δ`): the
one-stratum property excludes a `(2, β₂)`-splitting at the slim centre, the raw comparison gives a
sign `a`, and the slim chart (LC85/LFR19: `(1 + σ_s)`-Lipschitz coordinate, test on
`B(L) × B(L/σ_s)` with separation `> L`) supplies the reference side of the differential check.

* `SlimCentreOn.split_test_BCG8`: the slim chart at its centre with its test on the SAME splitting
  `split` (coordinate vanishes at `j`, Lipschitz bound for `ρ(j)⁻¹d`, differentiable on
  `B(j, 10⁶Δρ(j))`, the chart test);
* `bcg02_slim_differential_of_split_BCG8`: abstract step on an enriched boundary family
  `F : LocalPacketsOnB` — for `θ < 1`, `ν < 1`, `Δ ≥ 1`: an early `σ` and a rank-one quality bound
  `η`; at every slim centre `j`, every rank-one approximation `φ` with real coordinate `U`
  (`‖DU‖ ≤ 1 + δ_N` in `R⁻²g`, BCG02.b along the normalized test geodesics up to length `10⁶Δ + 2`
  on `B(j, 950000Δρ(j))`) gives ONE sign `a` with the value clause `|U − a(η_j − η_j(j))| < θ` and the
  differential clause `‖DU − aDη_j‖ < θ` on `B(j, 950000Δρ(j))`. Requests: `3ν ≤ β₂ < 1`,
  `σ⁻¹ ≤ L_max`, `3β₁ ≤ σ`, `β₁(2(1950002Δ + 1)) ≤ 1` (raw comparison on the whole test domain
  `B(j, (1950000Δ + 2)ρ(j))`), `v_s ≤ θ/4`, `0 < σ_s ≤ θ²/10⁷`, `β₁, δ_N ≤ θ²/10⁷`,
  `ρ(j)(10⁶Δ + 2) ≤ θ²/10⁷`. Axis length `10⁶Δ + 1` (separation `10⁶Δ` of the slim test);
* `bcg02_slim_differential_BCG8`: the LC88 binding (per carrier; BCG-4's `bcg02_slim_value_BCG4`
  hypotheses with `β₁(2(950000Δ + 1)) ≤ 1` replaced by `β₁(2(1950002Δ + 1)) ≤ 1`, plus `θ < 1`,
  `0 < σ_s ≤ θ²/10⁷`, `β₁ ≤ θ²/10⁷`, `ε_B, w₀ ≤ θ²/(4·10⁷)`, `10⁶Δ ≤ L_b`, B5's physical-scale clause
  `2ρ(e_i q)(12L_b + 1000) < θ²/10⁸` on `z ≤ 96`, `32·10⁶Δ ≤ n`); route as BCG-7 G8: BCG01.b band,
  BCP02 splitting with coordinate EXACTLY `U_b`, transport to `W°`, B4 norm and Taylor from BCG-7 G2
  (test geodesics stay in `B_ĝ(j, 4·10⁶Δρ(j)) ⊆ {D > 4}`);
* consumer `bcg02_slim_differential_BFR_BCG8` (the binding at the final boundary family
  `F : LocalPacketsOnBFR`, through `F.toLocalPacketsOnB`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section SlimTest

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- **The slim chart at its centre, with its test on the SAME splitting** (normalized scale): the
slim coordinate `η_j = coord_BCG2` vanishes at `j`, is `(1 + σ_s)`-Lipschitz for `ρ(j)⁻¹d`, is
differentiable on `B(j, 10⁶Δρ(j))`, and satisfies the slim chart test against the slim splitting
`split` on `B(10⁶Δ) × B(10⁶Δ/σ_s)` with separation `> 10⁶Δ`. -/
theorem SlimCentreOn.split_test_BCG8 {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ σs) :
    c.coord_BCG2 j = 0 ∧
    (∀ x y, |c.coord_BCG2 x - c.coord_BCG2 y| ≤ (1 + σs) * ((ρ j)⁻¹ * dist x y)) ∧
    (∀ x, dist x j < 10 ^ 6 * Δ * ρ j →
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord_BCG2 x) ∧
    (let cS : X → ℝ := c.coord_BCG2;
      let sp := c.split;
      let hMc : CompleteSpace X := ‹CompleteSpace X›;
      letI := c.instZ;
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
        isMetricNorm_of_riemannianBundle gR;
      ∀ x ∈ ball j (10 ^ 6 * Δ), ∀ x' ∈ ball j (10 ^ 6 * Δ / σs), 10 ^ 6 * Δ < dist x x' →
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
        intrinsicGeodesic gR hnR x w (dist x x') = x' →
        |mvfderiv 𝓘(ℝ, E3) cS x w -
          ((@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
              sp x').fst -
            (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
              sp x).fst) / dist x x'| < σs) := by
  have hρj := hρ j
  let C := c.packet
  let _ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  refine ⟨?_, fun x y => ?_, fun x hx => ?_, ?_⟩
  · change C.coord j = 0
    exact C.coord_center
  · have h := C.lipschitz.dist_le_mul x y
    rw [Real.coe_toNNReal _ (by linarith)] at h
    exact h
  · have hxd : x ∈ C.domain := by
      apply C.closedBall_subset_domain
      change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist x j ≤ 10 ^ 6 * Δ
      rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hρj]
      linarith
    exact (C.contMDiffOn_coord.contMDiffAt (C.isOpen_domain.mem_nhds hxd)).mdifferentiableAt
      (by simp)
  · dsimp only
    intro x hx x' hx' hsep w hw hgeo
    exact C.test x hx x' hx' hsep w hw hgeo

end SlimTest

/-- **BCG02 at a slim reference, value and differential clause with ONE sign** (abstract step on an
enriched boundary family `F : LocalPacketsOnB`; see the module docstring). -/
theorem bcg02_slim_differential_of_split_BCG8 {θ ν Δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hν : 0 < ν) (hν1 : ν < 1) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs U₁ U₂ Ue₁ Ue₂),
      3 * ν ≤ β 2 → β 2 < 1 → σ⁻¹ ≤ Lmax → 3 * β 1 ≤ σ → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
      vs ≤ θ / 4 → 0 < σs → σs ≤ θ ^ 2 / 10000000 → β 1 ≤ θ ^ 2 / 10000000 →
      ∀ (j : X) (hj : j ∈ F.slim.centres) (Tm : Type) [MetricSpace Tm] (t₀ : Tm) {ε₁ : ℝ},
      ε₁ ≤ η →
      ∀ φ : @KleinerLottApprox X (WithLp 2 (ℝ × Tm)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
          (WithLp.toLp 2 (0, t₀)) ε₁,
      ∀ U : X → ℝ, (∀ y, (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)))
          _ _ _ _ φ y).fst = U y) →
      ∀ {δN : ℝ}, 0 ≤ δN → δN ≤ θ ^ 2 / 10000000 →
      ρ j * (1000000 * Δ + 2) ≤ θ ^ 2 / 10000000 →
      (∀ x, dist x j < 950000 * Δ * ρ j → ∀ u : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) U x u| ≤ (1 + δN) * Real.sqrt
          ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u)) →
      (let hMc : CompleteSpace X := ‹CompleteSpace X›;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j));
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc;
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g;
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR;
        ∀ x ∈ ball j (950000 * Δ), ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1000000 * Δ + 2 → |mvfderiv 𝓘(ℝ, E3) U x w -
            (U (intrinsicGeodesic gR hnR x w ℓ) - U x) / ℓ| ≤ ρ j * ℓ) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y, dist y j < 950000 * Δ * ρ j →
          |U y - a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| <
            θ) ∧
        ∀ x, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) U x u - a * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u| ≤
            θ' * Real.sqrt
              ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g).inner x u u) := by
  set H : ℝ := 1950002 * Δ with hH
  have hH0 : 0 < H := by rw [hH]; linarith
  set τ' : ℝ := min (θ ^ 2 / 10000000000) (1 / (2 * (H + 1))) with hτdef
  have hτ : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτθ : τ' ≤ θ ^ 2 / 10000000000 := min_le_left _ _
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
  intro X mX instC instM hXc instS g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs U₁ U₂ Ue₁ Ue₂ F hν2 hβ2 hσL h3β hβH hvs hσs0 hσsθ hβθ j hj Tm _ t₀ ε₁ hε₁ φ U hU δN
    hδN0 hδN hρθ hnorm htay
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
  obtain ⟨hc0, hlipc, hdiffc, htestc⟩ := c.split_test_BCG8 hσs0.le
  obtain ⟨a, ha, hlin⟩ := hk X g hmetric ρ hρ j j hsec hno (by rw [hr1]; norm_num)
    (by rw [hr1]; norm_num) (by rw [dist_self, zero_mul]) Tm c.Z t₀ c.z hε₁ h3β hβH φ c.split
  have hφj : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      φ j).fst = 0 := by
    rw [@KleinerLottApprox.basepoint X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ]
    rfl
  have hraw : ∀ y, dist y j < H * ρ j →
      |U y - a * (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
        c.split y).fst| ≤ 50 * τ' := by
    intro y hy
    have hmain := hlin y (by rw [mem_ball]; exact hy)
    rw [hr1, hφj, one_mul, mul_zero, sub_zero, hU y] at hmain
    exact hmain
  have ha1 : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hθ2 : θ ^ 2 < θ := by nlinarith only [hθ, hθ1]
  refine ⟨a, ha, fun y hy => ?_, fun x hx => ?_⟩
  · -- the value clause with the same sign (LFR19's `slim_value`)
    have hyL : y ∈ ball j (10 ^ 6 * Δ * ρ j) := by
      rw [mem_ball]
      have h1 : 950000 * Δ * ρ j ≤ 10 ^ 6 * Δ * ρ j := by nlinarith only [hΔ, hρj]
      linarith only [hy, h1]
    have hv : |c.coord_BCG2 y - (@KleinerLottApprox.toFun X _
        (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ c.split y).fst| < vs :=
      F.slim_value j hj y hyL
    change |U y - a * (c.coord_BCG2 y - c.coord_BCG2 j)| < θ
    rw [hc0, sub_zero]
    set fy := (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
      c.split y).fst
    set cy := c.coord_BCG2 y
    have hr := hraw y (by
      have : 950000 * Δ * ρ j ≤ H * ρ j := by rw [hH]; nlinarith only [hΔ, hρj]
      linarith only [hy, this])
    have h2 : |a * (fy - cy)| < vs := by
      rw [abs_mul, ha1, one_mul, abs_sub_comm]
      exact hv
    have hsplit : U y - a * cy = (U y - a * fy) + a * (fy - cy) := by ring
    calc |U y - a * cy| = |(U y - a * fy) + a * (fy - cy)| := by rw [hsplit]
      _ ≤ |U y - a * fy| + |a * (fy - cy)| := abs_add_le _ _
      _ < 50 * τ' + vs := by linarith only [hr, h2]
      _ ≤ θ := by linarith only [hτθ, hvs, hθ2, hθ]
  · -- the differential clause, at the normalized metric
    have hxR : x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (950000 * Δ) := by
      change (ρ j)⁻¹ * dist x j < 950000 * Δ
      rw [inv_mul_lt_iff₀ hρj]
      linarith only [hx]
    have hraw' : ∀ y, @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toDist y j <
        10 ^ 6 * Δ + 1 + 950000 * Δ + 1 →
        |U y - a * (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _
          c.split y).fst| < 100 * τ' := by
      intro y hy
      change (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ + 1 + 950000 * Δ + 1 at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      have h1 := hraw y (by
        have : ρ j * (10 ^ 6 * Δ + 1 + 950000 * Δ + 1) ≤ H * ρ j := by
          rw [hH]; nlinarith only [hΔ, hρj]
        linarith only [hy, this])
      linarith only [h1, hτ]
    have hdiff' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (10 ^ 6 * Δ), MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord_BCG2 y := by
      intro y hy
      change (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hdiffc y (by linarith only [hy])
    have hnc' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (950000 * Δ), ∀ u : TangentSpace 𝓘(ℝ, E3) y, |mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 y u| ≤
          (1 + σs) * Real.sqrt
            ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 950000 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      have hyb : y ∈ ball j (10 ^ 6 * Δ * ρ j) := mem_ball.mpr (by nlinarith only [hy, hΔ, hρj])
      have h := norm_mvfderiv_le_of_lipschitz_rescale_BCG7 g hmetric isOpen_ball hyb
        (hdiffc y (mem_ball.mp hyb)) (L := 1 + σs) (by linarith only [hσs0]) hρj
        (fun y' _ z' _ => by rw [Real.norm_eq_abs]; exact hlipc y' z') u
      rwa [Real.norm_eq_abs] at h
    have hnU' : ∀ y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)).toPseudoMetricSpace j
        (950000 * Δ), ∀ u : TangentSpace 𝓘(ℝ, E3) y, |mvfderiv 𝓘(ℝ, E3) U y u| ≤
          (1 + δN) * Real.sqrt
            ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g).inner y u u) := by
      intro y hy u
      change (ρ j)⁻¹ * dist y j < 950000 * Δ at hy
      rw [inv_mul_lt_iff₀ hρj] at hy
      exact hnorm y (by linarith only [hy]) u
    have hβpos : 0 < β 1 :=
      @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ c.split
    have hβinv : 2 * (1950002 * Δ + 1) ≤ (β 1)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hβpos, ← one_div, le_div_iff₀ (by positivity)]
      linarith only [hβH]
    have hfar : 10 ^ 6 * Δ + 1 + 950000 * Δ + 1 ≤ 10 ^ 6 * Δ / σs := by
      rw [le_div_iff₀ hσs0]
      have hσ7 : σs ≤ 1 / 10000000 := by nlinarith only [hσsθ, hθ, hθ1]
      nlinarith only [hσ7, hσs0, hΔ]
    have htestc' := htestc
    dsimp only at htestc' htay
    let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj)
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρj) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    exact @bcg02_differential_normalized_sign_BCG7 E3 _ _ _ _ E3 _ 𝓘(ℝ, E3) _ X
      (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) instC instM instS
      (radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hρj))
      (radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hρj))
      ((mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hρj)).mpr hXc)
      (radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hρj))
      gR hnR c.Z c.instZ j c.z (β 1) c.split a ha c.coord_BCG2 U θ (10 ^ 6 * Δ + 1)
      (950000 * Δ) (10 ^ 6 * Δ) (10 ^ 6 * Δ / σs) (10 ^ 6 * Δ) σs (100 * τ') δN (ρ j) hθ hθ1
      (by linarith only [hβθ, hθ2, hθ1, hθ]) (by linarith only [hΔ])
      (by linarith only [hβinv, hΔ]) (by linarith only [hΔ]) hfar (by linarith only [hΔ])
      hσs0.le (by linarith only [hτ]) hδN0 hρj.le
      (by linarith only [hδN, hσsθ, hρθ, hτθ, hβθ, sq_nonneg θ]) hraw' hdiff' htestc' hnc' hnU'
      (fun x' hx' w hw ℓ hℓ hℓL => htay x' hx' w hw ℓ hℓ (by linarith only [hℓL])) x hxR

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG02 at a slim reference on the LC88 boundary data: value AND differential clause with ONE
sign** (enriched boundary family `F : LocalPacketsOnB`; see the module docstring). -/
theorem bcg02_slim_differential_BCG8 {θ ν Δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs Lb : ℝ}
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
      σ⁻¹ ≤ Lmax → 3 * β 1 ≤ σ → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 → vs ≤ θ / 4 →
      0 < σs → σs ≤ θ ^ 2 / 10000000 → β 1 ≤ θ ^ 2 / 10000000 → εB ≤ θ ^ 2 / 40000000 →
      w₀ ≤ θ ^ 2 / 40000000 → 1000000 * Δ ≤ Lb →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        2 * ρ ((P.cusp.collar i).toFun q) * (12 * Lb + 1000) < θ ^ 2 / 10 ^ 8) →
      32 * (1000000 * Δ) ≤ n →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOnB (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.slim.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
          |(P.height bb y - P.height bb j) / ρ j -
            a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
          ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j)
              x u - a * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u| ≤
            θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
              x u u) := by
  obtain ⟨σ, hσ, hσ1, η₀, hη₀, habs⟩ := bcg02_slim_differential_of_split_BCG8 hθ hθ1 hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, min η₀ (1 / 2), lt_min hη₀ (by norm_num), min_le_right _ _, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs Lb ĝ hK
    hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛC hβΔ hν2 hβ2 hσL h3β hβH hvs hσs0 hσsθ hβθ hεθ hwθ
    hLb hB5 hnC hcN U₁ U₂ Ue₁ Ue₂ hU₁ F j hj bb hmeet
  let instM_BCG1 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  set η : ℝ := min η₀ (1 / 2) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hρj : 0 < ρ j := hρ j
  have hβ14 : β 1 ≤ 1 / 4 := by linarith
  have hβ3pos : 0 < β 1 ^ 3 := pow_pos hβ1 3
  have hb2 : β 1 ^ 2 ≤ 1 / 16 := by nlinarith only [hβ1, hβ14]
  have hεB4 : εB ≤ 1 / 4 := by linarith only [hεβ, hb2]
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
  have hθ2 : θ ^ 2 < 1 := by nlinarith only [hθ, hθ1]
  have hU : ∀ y : W.pieceInterior ⊤, (@KleinerLottApprox.toFun (W.pieceInterior ⊤) _
      ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ φ y).fst =
      (P.height bb y - P.height bb j) / ρ j := by
    intro y
    change (@KleinerLottApprox.toFun W.Carrier _
      ((inducedMetricSpace g).rescale (ρ j)⁻¹ (inv_pos.mpr hρj)) _ _ _ _ f y.val).fst = _
    rw [hf, hq₀j]
  -- B5: the physical scale bounds `ρ(j)(10⁶Δ + 2)`
  have hρθ : ρ j * (1000000 * Δ + 2) ≤ θ ^ 2 / 10000000 := by
    have h := hB5 bb q₀ (by linarith only [hz91])
    rw [hq₀j] at h
    have h1 : 2 * ρ j * (12 * (1000000 * Δ) + 1000) ≤ 2 * ρ j * (12 * Lb + 1000) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLb]) (by positivity)
    have h2 : ρ j * (1000000 * Δ + 2) ≤ 2 * ρ j * (12 * (1000000 * Δ) + 1000) := by
      nlinarith only [hρj, hΔ]
    linarith only [h, h1, h2, sq_nonneg θ]
  have hρΔ : 4 * (1000000 * Δ) * ρ j ≤ 1 := by
    have h1 : 4 * (1000000 * Δ) * ρ j ≤ 4 * (ρ j * (1000000 * Δ + 2)) := by
      nlinarith only [hρj, hΔ]
    linarith only [h1, hρθ, hθ2]
  obtain ⟨-, hdistC'⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ (C := 1000000 * Δ)
    (by linarith only [hΔ]) hbcp hnC j hj5
  -- every point of `D_a = B_ĝ(j, 950000Δρ(j))` is a band point of the `bb`th collar
  have hpos : ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ p ∈ cuspDomain,
      (P.cusp.collar bb).toFun p = x.val ∧ 19 < p.2.val 0 ∧ p.2.val 0 < 91 := by
    intro x hx
    have hxC : dist x j < 1000000 * Δ * ρ j := by nlinarith only [hx, hΔ, hρj]
    have hxj : riemannianEDistOf g j.val x.val < ENNReal.ofReal (950000 * Δ * ρ j) := by
      rw [hdistC' j (mem_ball_self (by positivity)) x (mem_ball.mpr hxC), edist_dist, dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hx
    obtain ⟨q, hq, hqx, hz19, hz91, -, -⟩ := hband x.val hxj
    exact ⟨q, hq, hqx, hz19, hz91⟩
  have hδN0 : 0 ≤ 2 * (εB + w₀) := by
    have h1 : 0 < εB := P.tolerance_pos
    have h2 : 0 ≤ w₀ := (P.cusp.collar bb).delta_nonneg
    positivity
  obtain ⟨a, ha, hval, hdiff⟩ := @habs (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ hcN _ ĝ
    (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β σs Kf σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ F hν2 hβ2 hσL h3β hβH hvs hσs0 hσsθ hβθ j hj Torus
    mT t₀ η hηη₀ φ (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j) hU
    (δN := 2 * (εB + w₀)) hδN0 (by linarith only [hεθ, hwθ]) hρθ
    (fun x hx u => by
      obtain ⟨p, hp, hpx, hz19, hz91⟩ := hpos x hx
      have hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g x :=
        le_of_lt (lt_distanceToBoundary_of_consumer_BCG7 W g ĝ heq ρ hρ (C := 1000000 * Δ)
          (by linarith only [hΔ]) hbcp hnC j hj5 hρΔ x (by nlinarith only [hx, hΔ, hρj]))
      exact abs_mvfderiv_affineHeight_completion_le_BCG7 W g ĝ P hK hε1000 heq bb hp
        (by linarith only [hz19]) (by linarith only [hz91]) x hpx.symm hD (P.height bb j) hρj u)
    (by
      dsimp only
      intro x hx w hw ℓ hℓ hℓL
      have hxj : dist x j < 950000 * Δ * ρ j := by
        have h : (ρ j)⁻¹ * dist x j < 950000 * Δ := hx
        rw [inv_mul_lt_iff₀ hρj] at h
        linarith only [h]
      obtain ⟨p, hp, hpx, hz19, hz91⟩ := hpos x hxj
      have hρℓ : ρ j * ℓ ≤ ρ j * (1000000 * Δ + 2) := mul_le_mul_of_nonneg_left hℓL hρj.le
      have hsmall : 2 * (ρ j * ℓ) ≤ 1 := by linarith only [hρℓ, hρθ, hθ2]
      exact bcg02_taylor_test_BCG7 W g ĝ P hK hε1000 heq ρ hρ (C := 1000000 * Δ)
        (by linarith only [hΔ]) hbcp hnC bb (a := P.height bb j) hρj hcN j hj5 hρΔ x w hw _ rfl ℓ
        hℓ (by nlinarith only [hxj, hρℓ, hρj, hΔ]) p hpx (by linarith only [hz19, hsmall])
        (by linarith only [hz91, hsmall]))
  exact ⟨a, ha, hval, hdiff⟩

/-- **Consumer: BCG02 (value AND differential, ONE sign) at the slim references of the final boundary
family** `F : LocalPacketsOnBFR` (through `F.toLocalPacketsOnB`). -/
theorem bcg02_slim_differential_BFR_BCG8 {θ ν Δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs Lb ζ Λz : ℝ}
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
      σ⁻¹ ≤ Lmax → 3 * β 1 ≤ σ → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 → vs ≤ θ / 4 →
      0 < σs → σs ≤ θ ^ 2 / 10000000 → β 1 ≤ θ ^ 2 / 10000000 → εB ≤ θ ^ 2 / 40000000 →
      w₀ ≤ θ ^ 2 / 40000000 → 1000000 * Δ ≤ Lb →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        2 * ρ ((P.cusp.collar i).toFun q) * (12 * Lb + 1000) < θ ^ 2 / 10 ^ 8) →
      32 * (1000000 * Δ) ≤ n →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOnBFR (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁
          Ue₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.slim.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
          |(P.height bb y - P.height bb j) / ρ j -
            a * ((F.slim.centre j hj).coord_BCG2 y - (F.slim.centre j hj).coord_BCG2 j)| < θ) ∧
        ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
          ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => (P.height bb y - P.height bb j) / ρ j)
              x u - a * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u| ≤
            θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner
              x u u) := by
  obtain ⟨σ, hσ, hσ1, η, hη, hη2, h⟩ := bcg02_slim_differential_BCG8 hθ hθ1 hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, η, hη, hη2, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs Lb ζ Λz ĝ
    hK hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛC hβΔ hν2 hβ2 hσL h3β hβH hvs hσs0 hσsθ hβθ hεθ
    hwθ hLb hB5 hnC hcN U₁ U₂ Ue₁ Ue₂ hU₁ F j hj bb hmeet
  let instM_BCG8 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  exact h W g P ρ hρ ĝ hK hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛC hβΔ hν2 hβ2 hσL h3β hβH
    hvs hσs0 hσsθ hβθ hεθ hwθ hLb hB5 hnC hcN U₁ U₂ Ue₁ Ue₂ hU₁ F.toLocalPacketsOnB j hj bb hmeet

end DifferentialGeometry.Geometry.Collapse
