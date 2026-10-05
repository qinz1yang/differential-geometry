import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings

/-!
# BSA05 with STRICT LC02 bounds (BDRY-4, for T2 clause (i) of the LC88 boundary packet)

The frozen T2 (LC88 boundary route, review 45) asks for the strict bounds
`r_p(w)/2 < ρ(p) < 2 r_p(w')`, as LC02 and the closed producer state them; the delivered BSA05
chain (`exists_smooth_scale_of_envelope` → `H_smooth_scale` → `H_bsa05_eventually` →
`bsa06_row_eventually`) exports only `≤`. Its smoothing step already proves the strict form: with
`l ≤ f ≤ u`, `m = min f > 0` and `|ρ - f| < min (m/2) (Λ/2)`, one has `ρ > f - m/2 ≥ f/2 ≥ l/2`
and `ρ < f + m/2 ≤ (3/2) f ≤ (3/2) u < 2u`. This module re-proves the chain with the strict
conclusions (new names, the delivered statements are unchanged):

* `exists_smooth_scale_of_envelope_strict_BDRY4` (the smoothing step, strict);
* `H_smooth_scale_strict_BDRY4` (BSA05.a, strict);
* `H_bsa05_eventually_strict_BDRY4` (BSA05 along the counterexample ratios, strict);
* `bsa06_row_eventually_strict_BDRY4` (BSA06 / BCP04.a clauses on the same scale, strict);
* consumer `eventually_strict_scale_boundary_BDRY4`: T2 clause (i) verbatim (`2 * Λ⁻¹`, strict
  bounds, collar smallness for every `ε > 0` on a further tail).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- BSA05 smoothing step with STRICT bounds: a pairwise envelope `l p - (Λ/2) d(p, q) ≤ u q` with
`l > 0` gives a smooth (up to the boundary) positive `Λ`-Lipschitz scale `ρ` with
`l / 2 < ρ < 2 u`. -/
theorem exists_smooth_scale_of_envelope_strict_BDRY4 (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    {l u : W.Carrier → ℝ} {Λ : ℝ} (hΛ : 0 < Λ) (hl : ∀ p, 0 < l p)
    (henv : ∀ p q, l p - Λ / 2 * (riemannianEDistOf g p q).toReal ≤ u q) :
    ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
      (∀ p, l p / 2 < ρ p ∧ ρ p < 2 * u p) ∧
      ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y := by
  obtain ⟨f, hfc, hf, hlf⟩ : ∃ f : W.Carrier → ℝ, Continuous f ∧
      (∀ x y, ENNReal.ofReal |f x - f y| ≤
        ENNReal.ofReal (Λ / 2) * riemannianEDistOf g x y) ∧
      ∀ p, l p ≤ f p ∧ f p ≤ u p := by
    let := inducedMetricSpace g
    obtain ⟨f, hflip, hlf⟩ :=
      exists_lipschitz_between_of_envelope (by positivity : (0 : ℝ) ≤ Λ / 2) henv
    refine ⟨f, hflip.continuous, fun x y => ?_, hlf⟩
    have h := hflip.edist_le_mul x y
    rw [edist_dist, Real.dist_eq] at h
    exact h
  rcases isEmpty_or_nonempty W.Carrier with hM | hM
  · exact ⟨fun _ => 0, fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨x₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hfc.continuousOn
  have hm : 0 < f x₀ := (hl x₀).trans_le (hlf x₀).1
  have hmf : ∀ p, f x₀ ≤ f p := fun p => hmin (mem_univ p)
  set ε : ℝ := min (f x₀ / 2) (Λ / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨ρ, hρ, hclose, L, hL, hlip⟩ :=
    CompactCarrier.exists_smooth_scalar_approx W g hf hε0
  have hεm : ε ≤ f x₀ / 2 := min_le_left _ _
  have hεΛ : ε ≤ Λ / 2 := min_le_right _ _
  have hlow : ∀ p, l p / 2 < ρ p := by
    intro p
    have h1 := (abs_lt.mp (hclose p)).1
    have h2 := hmf p
    have h3 := (hlf p).1
    linarith
  refine ⟨ρ, hρ, fun p => (half_pos (hl p)).trans (hlow p), fun p => ⟨hlow p, ?_⟩,
    fun x y => (hlip x y).trans ?_⟩
  · have h1 := (abs_lt.mp (hclose p)).2
    have h2 := hmf p
    have h3 := (hlf p).2
    linarith
  · gcongr
    linarith

/-- **BSA05.a with strict bounds.** On the uniform tail of `H_envelope`, a smooth positive
`Λ`-Lipschitz `ρ` on all of `W` with `r_p(w)/2 < ρ(p) < 2 r_p(w')`. -/
theorem H_smooth_scale_strict_BDRY4 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        δ * (16 * n ^ 4) ≤ 1 →
        1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
          (∀ p, firstVolumeScale g p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y := by
  obtain ⟨δStar, hδStar, hH⟩ := H_envelope.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll Λ w n hΛ hw hwc hn hnS hnw hδn hδa
  exact exists_smooth_scale_of_envelope_strict_BDRY4 W g hΛ
    (fun p => firstVolumeScale_pos_everywhere W g p hw hwc)
    (hH W g K δ hK hδ0 hδ B hcoll hΛ hw hwc hn hnS hnw hδn hδa)

/-- **BSA05 along the boundary counterexample sequence, strict bounds.** One smooth scale `ρ_n`
per member: smooth, positive, `Λ`-Lipschitz, `r_p(w)/2 < ρ_n(p) < 2 r_p(w')` on one tail, and for
every `ε > 0`, `ρ_n < ε` on all collar regions `0 ≤ z ≤ 96` of all components on a further tail. -/
theorem H_bsa05_eventually_strict_BDRY4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧ (∀ p, 0 < ρ n p) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              ∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δStar, hδStar, hS⟩ := H_smooth_scale_strict_BDRY4.{u}
  refine ⟨min δStar (1 / 100), lt_min hδStar (by norm_num), ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  have hδle (n : ℕ) : boundaryCounterexampleRatio δ₀ n ≤ min δStar (1 / 100) :=
    (boundaryCounterexampleRatio_le δ₀ n).trans hδ₀S
  have hex : ∀ n : ℕ, ∃ ρ : (W n).Carrier → ℝ,
      (3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧ (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧
        0 ≤ boundaryCounterexampleRatio δ₀ n ∧
        boundaryCounterexampleRatio δ₀ n * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2) →
      ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
        (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
        ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y := by
    intro n
    by_cases htail : 3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧
        (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧ 0 ≤ boundaryCounterexampleRatio δ₀ n ∧
        boundaryCounterexampleRatio δ₀ n * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2
    · obtain ⟨h3, h2S, hnw, hδ0, hδn, hδa⟩ := htail
      obtain ⟨ρ, hρ⟩ := hS (W n) (g n) K _ hK hδ0 ((hδle n).trans (min_le_left _ _)) (B n)
        (hcoll n) hΛ hw hwc h3 h2S hnw hδn hδa
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨fun _ => 0, fun h => absurd h htail⟩
  choose ρ hρ using hex
  refine ⟨ρ, ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw] with n hn
    exact hρ n hn
  · have hc : 0 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (ε / 4) ^ 2 :=
      mul_pos hw' (pow_pos (lt_min (by norm_num) (by positivity)) 2)
    filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw,
      eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀ hc] with n hn hsmall
    intro i p hp
    exact (B n).lt_of_le_two_mul_firstVolumeScale ((hδle n).trans (min_le_right _ _)) hw' hε
      hsmall (fun p => ((hρ n hn).2.2.1 p).2.le) i hp

/-- **BSA06 along the counterexample ratios, strict LC02 bounds.** `bsa06_row_eventually` with
`r_p(w)/2 < ρ_n(p) < 2 r_p(w')`. -/
theorem bsa06_row_eventually_strict_BDRY4 :
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
              (∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
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
  obtain ⟨δH, hδH, hH⟩ := H_bsa05_eventually_strict_BDRY4.{u}
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
    (hcoll n) (hder n) hA h3 hδn hnw hw'c (ρ n) hpos fun p => (hbd p).2.le⟩

/-- **Consumer: T2 clause (i) verbatim.** Along the counterexample ratios, one scale `ρ_n` with,
on one tail, smoothness, positivity, the `Λ`-Lipschitz bound for `g_n`, the STRICT LC02 bounds
written as in T2 (`2 * Λ⁻¹`), and for every `ε > 0` the collar smallness `ρ_n ≤ ε` on `z ≤ 96` on
a further tail. -/
theorem eventually_strict_scale_boundary_BDRY4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, (∀ p, 0 < ρ n p) ∧
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (q : CuspHalfSpace),
              q.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun q) ≤ ε := by
  obtain ⟨δStar, hδStar, hH⟩ := H_bsa05_eventually_strict_BDRY4.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  obtain ⟨ρ, hev, hcol⟩ := hH hδ₀ hδ₀S K hK W g B hcoll hΛ hw hwc
  refine ⟨ρ, ?_, fun ε hε => ?_⟩
  · filter_upwards [hev] with n hn
    obtain ⟨hsm, hpos, hbd, hlip⟩ := hn
    refine ⟨hpos, hsm, hlip, fun p => ?_⟩
    rw [← div_eq_mul_inv]
    exact hbd p
  · filter_upwards [hcol ε hε] with n hn
    exact fun i q hq => (hn i q hq).le

end DifferentialGeometry.Geometry.Collapse
