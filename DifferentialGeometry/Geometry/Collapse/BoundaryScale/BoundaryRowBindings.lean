import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarStatementG
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarPinching
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBalls
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightDifferential
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLocalization
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleSmoothApplications
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.VolumeLowerEverywhere
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CurvatureBuffers

/-!
# Chapter 14 boundary rows bound on statements E, G, H (BSA01, BSA04, BSA06, BCP04.a, BCP05.a)

Thin bindings of the blueprint 207B rows to the delivered producers (no new hypothesis):
* `bsa01_clauses_except_II`: every clause of BSA01 (`B:7591`) except the second fundamental form
  clause `II ≥ g/4`: the cusp pinching on `z ≤ 98` (FT-C), the two-sided `‖dz‖` bound on the
  whole collar, the unit ball, volume and curvature-scale clauses at heights `z ≤ 96` (the
  blueprint says `95`), the localisation `d ≤ 10 ⇒ z < 11`, BSA01.c, and the torus diameter and
  area bounds (BDY-G, B-5a, FT-C).
* `bsa04_row`, `bsa04_row_counterexample`: BSA04 (`B:7838`), (a) at EVERY point and (c) on the
  whole ball, for one member and along the counterexample ratios `δ_n` (every `n ≥ 3`); BSA01's
  near-boundary input is G's first consumer clause.
* `bsa06_clauses_of_scale`, `bsa06_row`, `bsa06_row_eventually`: BSA06 (`B:7979`) and BCP04.a
  (`B:8443`) for every scale `0 < ρ ≤ 2 r(w')`, then for the smooth scale of BSA05 (BDY-H's
  `H_bsa05`, `H_bsa05_eventually`); BSA02 is not used.
* `bcp05a_zeroBall_small_of_scale`: BCP05.a (`B:8617`): a ball `B(z, R⁰)`, `R⁰ ≤ V ρ(z)`, `V < n`,
  meeting a collar at height `≤ 98` has `R_z < 3`, `ρ(z) < 3/n`, `R⁰ < 3V/n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ### BSA01 without the II clause -/

/-- **BSA01, every clause except `II ≥ g/4`.** There is `δStar > 0` such that every nearly
cuspidal boundary with `K ≥ 2` and `0 ≤ δ ≤ δStar` has: the pinching `-1/2 ≤ sec ≤ -1/8` on
`z ≤ 98`; `|dz(u)| ≤ 1.01‖u‖` with a vector `dz(u) = 1`, `‖u‖ ≤ 1.01` on the whole collar; at
heights `z ≤ 96` and radii `r ≤ 1`: the ball stays in `e{z < 98}`, `vol B ≤ 1000 δ² r` and
`1 ≤ R < 3`; every point with `d(p, ∂W) ≤ 10` in a collar at height `< 11`; on a connected
carrier `d(p, ∂W) < ⊤` and `R_p ≤ d(p, ∂W) + 3`; `diam g_T ≤ 2δ` and `Area g_T ≤ 4πδ²`. -/
theorem bsa01_clauses_except_II :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
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
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  obtain ⟨δ₁, hδ₁, hpin⟩ := cusp_sectional_pinching.{u}
  refine ⟨min (min δG δ₁) (1 / 100), lt_min (lt_min hδG hδ₁) (by norm_num), ?_⟩
  intro W g K δ hK hδ0 hδ B
  have hδG' : δ ≤ δG := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₁' : δ ≤ δ₁ := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ ≤ 1 / 100 := hδ.trans (min_le_right _ _)
  have hpinB : ∀ (i : Fin B.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar i).toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
            metricRm04StandardAt g ((B.collar i).toFun q) u w w u ∧
          metricRm04StandardAt g ((B.collar i).toFun q) u w w u ≤
            -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) :=
    fun i q hq hq98 u w => hpin W g K δ _ (B.collar i) hK hδ0 hδ₁' q hq hq98 u w
  refine ⟨hpinB,
    fun i q hq => (B.collar i).height_invFunOn_differential_bounds_of_le_hundredth hδc hq,
    fun i p hp => ⟨fun r hr => (B.collar i).riemannianBallOf_subset_image_height_lt hδc hp hr,
      fun r hr => B.ballVolume_le_thousand hδc i hp hr,
      (B.collar i).curvatureRadius_mem_Ico hδc (hpinB i) hp⟩,
    fun p hp => B.exists_collar_height_lt_eleven hδc hp,
    (hG W g K δ hK hδ0 hδG' B).2,
    fun i x y => B.torus_riemannianEDistOf_le_two_mul hδc i x y,
    fun i => B.torus_area_le_four_pi_mul_sq hδc i⟩

/-! ### BSA04 -/

/-- **BSA04 (one member).** There is `δStar > 0` such that, for a nearly cuspidal boundary with
`K ≥ 2`, `0 ≤ δ ≤ δStar`, the static collapse and derivative control, `n ≥ 3` and
`δ · 16 n⁴ ≤ 1`: (BSA04.a) `2 n r_p(1/n) < R_p` at EVERY point, and (BSA04.c) for `C < n`,
`1/n ≤ w < ω₃` the bounds `|∇^k Rm| ≤ A'(C, w) r_p(w)^{-k-2}` on the whole ball
`B(p, C r_p(w))`. -/
theorem bsa04_row :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ → ∀ {A : ℝ → ℝ}, curvatureDerivativesControlled g K A δ →
      ∀ {n : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → ∀ p : W.Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p ∧
        ∀ {C w : ℝ}, C < n → n⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
          ∀ k ≤ K, ∀ q ∈ riemannianBallOf g p (C * firstVolumeScale g p w),
            curvatureDerivativeNorm g k q ≤
              boundaryDerivativeConstant A K C w * (firstVolumeScale g p w ^ (k + 2))⁻¹ := by
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  refine ⟨δG, hδG, ?_⟩
  intro W g K δ hK hδ0 hδ B hcoll A hderiv n hn hδn p
  have hstand := ofReal_two_mul_firstVolumeScale_lt_curvatureRadius_of_boundary_data W g hn hδ0
    hδn hcoll (hG W g K δ hK hδ0 hδ B).1 p
  have hn4 : 0 ≤ n ^ 4 := pow_nonneg (by linarith) 4
  have hδn' : δ * n ^ 4 ≤ 1 := by nlinarith [mul_nonneg hδ0 hn4]
  exact ⟨hstand, fun hCn hwn hwc =>
    curvatureDerivativeNorm_le_on_firstVolumeScale_ball g hderiv (by linarith) hδn' hstand hCn
      hwn hwc⟩

/-- **BSA04 along the counterexample ratios.** With `δStar` of `bsa04_row`, `0 < δ₀ ≤ δStar` and
`K ≥ 2`, every sequence of carriers with nearly cuspidal boundaries, static collapse and derivative
control at `δ_n = boundaryCounterexampleRatio δ₀ n` satisfies (BSA04.a) and (BSA04.c) at every
point, for EVERY `n ≥ 3` (the uniform tail). -/
theorem bsa04_row_counterexample :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
      (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ n : ℕ, 3 ≤ n → ∀ p : (W n).Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) < curvatureRadius (g n) p ∧
        ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
          ∀ k ≤ K, ∀ q ∈ riemannianBallOf (g n) p (C * firstVolumeScale (g n) p w),
            curvatureDerivativeNorm (g n) k q ≤
              boundaryDerivativeConstant A K C w * (firstVolumeScale (g n) p w ^ (k + 2))⁻¹ := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A W g B hcoll hder n hn p
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  exact h4 (W n) (g n) K _ hK (boundaryCounterexampleRatio_pos hδ₀ hn1).le
    ((boundaryCounterexampleRatio_le δ₀ n).trans hδ₀S) (B n) (hcoll n) (hder n)
    (by exact_mod_cast hn) (boundaryCounterexampleRatio_mul_le δ₀ hn1) p

/-! ### Real forms of the standing inequality -/

/-- With `R_p ≤ d + 3`, `d = ofReal D`: the curvature scale is finite and `R_p.toReal ≤ D + 3`. -/
theorem toReal_curvatureRadius_le_of_le_add_three (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {p : W.Carrier} {D : ℝ} (hD : 0 ≤ D)
    (hd : distanceToBoundary W g p = ENNReal.ofReal D)
    (hR : curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) :
    curvatureRadius g p ≠ ⊤ ∧ (curvatureRadius g p).toReal ≤ D + 3 := by
  rw [hd, ← ENNReal.ofReal_add hD (by norm_num)] at hR
  have htop : curvatureRadius g p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR
  refine ⟨htop, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hR
  rwa [ENNReal.toReal_ofReal (by linarith)] at h

/-- The standing inequality at a finite curvature scale, read for `u = r_p(w')` with `1/n ≤ w'`:
`2 n u < R_p.toReal`. -/
theorem two_mul_firstVolumeScale_lt_toReal_of_standing (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier) {n w' : ℝ} (hn : 0 < n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (htop : curvatureRadius g p ≠ ⊤) :
    2 * n * firstVolumeScale g p w' < (curvatureRadius g p).toReal := by
  have hle := firstVolumeScale_anti_of_le g p (inv_pos.mpr hn) hwn
  have h0 := firstVolumeScale_nonneg g p n⁻¹
  have hlt := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop).mp hstand
  nlinarith

/-! ### BSA06 and BCP04.a -/

/-- **BSA06 and BCP04.a for every scale `0 < ρ ≤ 2 r(w')`.** There is `δStar > 0` such that, for
a connected carrier with nearly cuspidal boundary (`K ≥ 2`, `0 ≤ δ ≤ δStar`), static collapse,
derivative control with `A > 0`, `n ≥ 3`, `δ · 16 n⁴ ≤ 1`, `1/n ≤ w' < ω₃`, at EVERY point: the
LPA01 volume lower bound `w'/(24 ∫₀¹ sinh²) ≤ vol B(p, ρ)/ρ³`, the sectional buffer of `ρ⁻² g`
on its ball of radius `n/4`, the whole-ball derivative bounds `2^{K+2} A'(2R+2, w')`
(`2R + 2 < n`); BCP04.a `n d/(d+3) < d/ρ` where `d > 0`; BSA06.a `n/2 < d/ρ` where `d > 10`,
and then every scaled ball `B(p, b ρ)`, `b ≤ n/2`, is interior. -/
theorem bsa06_clauses_of_scale :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ → ∀ {A : ℝ → ℝ}, curvatureDerivativesControlled g K A δ →
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {n w' : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
        w' < euclideanThreeUnitBallVolume →
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), (∀ p, ρ p ≤ 2 * firstVolumeScale g p w') →
      ∀ p : W.Carrier,
        w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p (ρ p)).toReal / ρ p ^ 3 ∧
        (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
          SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
            (-((n / 4) ^ 2)⁻¹)) ∧
        (∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p R,
            curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρ p)) k y ≤
              (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w') ∧
        (0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / ρ p) ∧
        (ENNReal.ofReal 10 < distanceToBoundary W g p →
          n / 2 < (distanceToBoundary W g p).toReal / ρ p ∧
          ∀ b : ℝ, b ≤ n / 2 →
            riemannianBallOf g p (b * ρ p) ⊆ W.model.interior W.Carrier) := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row.{u}
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  refine ⟨min δS δG, lt_min hδS hδG, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll A hderiv hA n w' hn hδn hwn hwc ρ hρ hρu p
  have hnpos : 0 < n := by linarith
  have hstand := (h4 W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B hcoll hderiv hn hδn p).1
  have hn4 : 0 ≤ n ^ 4 := pow_nonneg hnpos.le 4
  have hδn' : δ * n ^ 4 ≤ 1 := by nlinarith [mul_nonneg hδ0 hn4]
  obtain ⟨hdtop, hR⟩ := (hG W g K δ hK hδ0 (hδ.trans (min_le_right _ _)) B).2 ‹_› p
  set D := (distanceToBoundary W g p).toReal with hDdef
  have hdeq : distanceToBoundary W g p = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal hdtop.ne).symm
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  obtain ⟨hRtop, hRD⟩ := toReal_curvatureRadius_le_of_le_add_three W g hD0 hdeq hR
  have h2nu := two_mul_firstVolumeScale_lt_toReal_of_standing W g p hnpos hstand hwn hRtop
  refine ⟨(volume_lower_at_modified_scale_of_standing_everywhere W g p (by linarith) hwn (hρ p)
      (hρu p)).2,
    normalizedCenterMetric_sectional_of_standing g p hnpos hstand hwn (hρ p) (hρu p),
    normalizedCenterMetric_derivative_bounds_of_standing g p hderiv hA (by linarith) hδn'
      hstand hwn hwc (hρ p) (hρu p), fun hd => ?_, fun hd => ⟨?_, fun b hb => ?_⟩⟩
  · have hD : 0 < D := by
      rw [hdeq] at hd
      exact ENNReal.ofReal_pos.mp hd
    exact mul_div_add_three_lt_distance_div_scale hD hRD h2nu (hρ p) (hρu p)
  · have hD : 10 < D := by
      rw [hdeq] at hd
      exact (ENNReal.ofReal_lt_ofReal_iff'.mp hd).1
    exact half_lt_distance_div_scale hD hRD h2nu (hρ p) (hρu p)
  · have hst : ENNReal.ofReal (2 * n * firstVolumeScale g p w') < curvatureRadius g p :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by
        have := firstVolumeScale_nonneg g p w'
        positivity) hRtop).mpr h2nu
    exact riemannianBallOf_scaled_subset_interior W g hd hR hst (hρ p) (hρu p) hb

/-- **BSA06 with the smooth scale of BSA05, and BCP04.a.** On the uniform tail of statement H
(`S = 1 + 2/Λ`, `w' = w/(2S³)`), for a connected carrier with nearly cuspidal boundary, static
collapse and derivative control with `A > 0`, there is ONE `ρ` carrying BSA05 (smooth, positive,
`r_p(w)/2 ≤ ρ ≤ 2 r_p(w')`, `Λ`-Lipschitz, `ρ < ε` on every collar region `z ≤ 96` on the
`ε`-tail) and, at EVERY point, the BSA06 volume, sectional and derivative clauses, BCP04.a where
`d > 0`, and BSA06.a with the interior containment where `d > 10`. -/
theorem bsa06_row :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
      boundaryVolumeCollapsed W g δ → ∀ {A : ℝ → ℝ}, curvatureDerivativesControlled g K A δ →
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        δ * (16 * n ^ 4) ≤ 1 →
        1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∃ ρ : W.Carrier → ℝ, ∃ hρ : ∀ p, 0 < ρ p, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ p, firstVolumeScale g p w / 2 ≤ ρ p ∧
            ρ p ≤ 2 * firstVolumeScale g p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
          (∀ ε > 0, 1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (ε / 4) ^ 2 →
            ∀ (i : Fin B.count) (p : CuspHalfSpace), p.2.val 0 ≤ 96 →
              ρ ((B.collar i).toFun p) < ε) ∧
          ∀ p : W.Carrier,
            w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
                (ballVolume g p (ρ p)).toReal / ρ p ^ 3 ∧
            (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
              SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
                (-((n / 4) ^ 2)⁻¹)) ∧
            (∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
              ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p R,
                curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρ p)) k y ≤
                  (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                    (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
            (0 < distanceToBoundary W g p →
              n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
                (distanceToBoundary W g p).toReal / ρ p) ∧
            (ENNReal.ofReal 10 < distanceToBoundary W g p →
              n / 2 < (distanceToBoundary W g p).toReal / ρ p ∧
              ∀ b : ℝ, b ≤ n / 2 →
                riemannianBallOf g p (b * ρ p) ⊆ W.model.interior W.Carrier) := by
  obtain ⟨δH, hδH, hH⟩ := H_bsa05.{u}
  obtain ⟨δC, hδC, hC⟩ := bsa06_clauses_of_scale.{u}
  refine ⟨min δH δC, lt_min hδH hδC, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll A hderiv hA Λ w n hΛ hw hwc hn h2S hnw hδn hδa
  obtain ⟨ρ, hsm, hpos, hbd, hlip, hcol⟩ := hH W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B
    hcoll hΛ hw hwc hn h2S hnw hδn hδa
  have hS : 1 < 2 * (1 + 2 / Λ) ^ 3 := by
    have h1 : 1 ≤ 1 + 2 / Λ := le_add_of_nonneg_right (by positivity)
    nlinarith [one_le_pow₀ (n := 3) h1]
  have hw'c : w / (2 * (1 + 2 / Λ) ^ 3) < euclideanThreeUnitBallVolume := by
    have hlt : w / (2 * (1 + 2 / Λ) ^ 3) < w := div_lt_self hw hS
    linarith [euclideanThreeUnitBallVolume_pos]
  exact ⟨ρ, hpos, hsm, hbd, hlip, hcol, hC W g K δ hK hδ0 (hδ.trans (min_le_right _ _)) B hcoll
    hderiv hA hn hδn hnw hw'c ρ hpos fun p => (hbd p).2⟩

/-- **BSA06 along the counterexample ratios.** For `0 < δ₀ ≤ δStar`, `K ≥ 2`, `A > 0`, `Λ > 0`,
`0 < w < ω₃/4`, every sequence of connected carriers with nearly cuspidal boundaries, static
collapse and derivative control at `δ_n = boundaryCounterexampleRatio δ₀ n` has scales `ρ_n` with,
on one tail, BSA05.a and all BSA06 / BCP04.a clauses at every point (with `α = n`), and, for every
`ε > 0`, `ρ_n < ε` on every collar region `z ≤ 96` on a further tail. -/
theorem bsa06_row_eventually :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n : ℕ in atTop, ∃ hρ : ∀ p, 0 < ρ n p,
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p : (W n).Carrier,
                w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
                    (ballVolume (g n) p (ρ n p)).toReal / ρ n p ^ 3 ∧
                (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p
                    ((n : ℝ) / 4),
                  SectionalBoundedBelowAt (normalizedCenterMetric (g n) (ρ n p) (hρ p)) y
                    (-(((n : ℝ) / 4) ^ 2)⁻¹)) ∧
                (∀ R : ℝ, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
                  ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p R,
                    curvatureDerivativeNorm (normalizedCenterMetric (g n) (ρ n p) (hρ p)) k y ≤
                      (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                        (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
                (0 < distanceToBoundary (W n) (g n) p →
                  n * (distanceToBoundary (W n) (g n) p).toReal /
                      ((distanceToBoundary (W n) (g n) p).toReal + 3) <
                    (distanceToBoundary (W n) (g n) p).toReal / ρ n p) ∧
                (ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
                  (n : ℝ) / 2 < (distanceToBoundary (W n) (g n) p).toReal / ρ n p ∧
                  ∀ b : ℝ, b ≤ (n : ℝ) / 2 →
                    riemannianBallOf (g n) p (b * ρ n p) ⊆
                      (W n).model.interior (W n).Carrier)) ∧
            ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δH, hδH, hH⟩ := H_bsa05_eventually.{u}
  obtain ⟨δC, hδC, hC⟩ := bsa06_clauses_of_scale.{u}
  refine ⟨min δH δC, lt_min hδH hδC, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A hA W _ g B hcoll hder Λ w hΛ hw hwc
  obtain ⟨ρ, hev, hcol⟩ := hH hδ₀ (hδ₀S.trans (min_le_left _ _)) K hK W g B hcoll hΛ hw hwc
  refine ⟨ρ, ?_, hcol⟩
  have hS : 1 < 2 * (1 + 2 / Λ) ^ 3 := by
    have h1 : 1 ≤ 1 + 2 / Λ := le_add_of_nonneg_right (by positivity)
    nlinarith [one_le_pow₀ (n := 3) h1]
  have hw'c : w / (2 * (1 + 2 / Λ) ^ 3) < euclideanThreeUnitBallVolume := by
    have hlt : w / (2 * (1 + 2 / Λ) ^ 3) < w := div_lt_self hw hS
    linarith [euclideanThreeUnitBallVolume_pos]
  filter_upwards [hev, eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw] with n hn htail
  obtain ⟨hsm, hpos, hbd, hlip⟩ := hn
  obtain ⟨h3, -, hnw, hδ0, hδn, -⟩ := htail
  exact ⟨hpos, hsm, hbd, hlip, hC (W n) (g n) K _ hK hδ0
    ((boundaryCounterexampleRatio_le δ₀ n).trans (hδ₀S.trans (min_le_right _ _))) (B n)
    (hcoll n) (hder n) hA h3 hδn hnw hw'c (ρ n) hpos fun p => (hbd p).2⟩

/-! ### BCP05.a -/

/-- **BCP05.a.** There is `δStar > 0` such that, for a nearly cuspidal boundary (`K ≥ 2`,
`0 ≤ δ ≤ δStar`) with static collapse, `n ≥ 3`, `δ · 16 n⁴ ≤ 1`, `1/n ≤ w'`, and any scale
`0 < ρ ≤ 2 r(w')`: a ball `B(z, R⁰)` with `R⁰ ≤ V ρ(z)`, `V < n`, containing a collar point
`e_i(q)` of height `≤ 98` has `R_z < 3`, `ρ(z) < 3/n` and `R⁰ < 3V/n`. -/
theorem bcp05a_zeroBall_small_of_scale :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
      boundaryVolumeCollapsed W g δ →
      ∀ {n w' : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
      ∀ ρ : W.Carrier → ℝ, (∀ p, 0 < ρ p) → (∀ p, ρ p ≤ 2 * firstVolumeScale g p w') →
      ∀ (i : Fin B.count) (q : CuspHalfSpace), q.2.val 0 ≤ 98 →
      ∀ (z : W.Carrier) {R₀ V : ℝ}, (B.collar i).toFun q ∈ riemannianBallOf g z R₀ →
        R₀ ≤ V * ρ z → V < n →
        curvatureRadius g z < 3 ∧ ρ z < 3 / n ∧ R₀ < 3 * V / n := by
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  obtain ⟨δ₁, hδ₁, hpin⟩ := cusp_sectional_pinching.{u}
  refine ⟨min δG δ₁, lt_min hδG hδ₁, ?_⟩
  intro W g K δ hK hδ0 hδ B hcoll n w' hn hδn hwn ρ hρ hρu i q hq z R₀ V hx hR₀ hVn
  have hnpos : 0 < n := by linarith
  have hstand := ofReal_two_mul_firstVolumeScale_lt_curvatureRadius_of_boundary_data W g hn hδ0
    hδn hcoll (hG W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B).1 z
  have hle := firstVolumeScale_anti_of_le g z (inv_pos.mpr hnpos) hwn
  have hscale : ENNReal.ofReal (n * ρ z) < curvatureRadius g z := by
    refine (ENNReal.ofReal_le_ofReal ?_).trans_lt hstand
    nlinarith [hρu z]
  have hqd : q ∈ cuspDomain := by
    change q.2.val 0 < cuspDepth
    rw [cuspDepth]
    linarith
  obtain ⟨v, w, hgram⟩ := exists_carrier_gram_pos W g ((B.collar i).toFun q)
  exact zeroBall_small_of_negative_plane g hx hR₀ (hρ z) hVn hscale v w hgram
    (hpin W g K δ _ (B.collar i) hK hδ0 (hδ.trans (min_le_right _ _)) q hqd hq v w).2

end DifferentialGeometry.Geometry.Collapse
