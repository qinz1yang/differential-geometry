import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarStatementG
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarComparison
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.StandingSequence
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleEverywhere
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

/-!
# The BSA05 envelope at all pairs of a nearly cuspidal carrier (statement H)

Blueprint 207B, BSA05 (`B:7915`), first paragraph of the proof; route R3, statement H of
`design-boundary-geometry-20261004.md` (errata E8 = disposition D8, review §8). With
`S = 1 + 2/Λ`, `w' = w/(2S³)`, `a = b₀/(2S)`, `b₀ = 1/100`, on the uniform tail
(`3 ≤ n`, `2S < n`, `1/n ≤ w'`, `δ·16n⁴ ≤ 1`, `1000δ² < w'a²`) the envelope
`r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` holds for ALL `p, q`, boundary points included.

A violation gives `0 < u < l`, `d < (S - 1) l` (`l = r_p(w)`, `u = r_q(w')`), hence
`B(p, l) ⊆ B(q, Sl)` and `V_q(Sl) ≥ w l³ = 2S³ w' l³`, while BSA04.a and `n > 2S` give `4Sl < R_p`.
* Interior branch, `Sl < d(q, ∂W)`: B2 (`localBishopGromov_real_cross_of_distanceToBoundary`)
  at the centre `q` with outer radius `Sl`, inner radius `u`, `κ = (4Sl)⁻²` gives the relative
  comparison with constant `e^{1/2} < 2`
  (`ballVolume_toReal_mul_cube_le_exp_half_of_distanceToBoundary`).
* Near branch, `d(q, ∂W) ≤ Sl`: then `d(p, ∂W) < 2Sl`; `d(p, ∂W) > 10` is excluded by
  `R_p ≤ d(p, ∂W) + 3`; G's volume bound at `p` gives `l ≤ r_p(w') < a`, so `d(q, ∂W) ≤ Sl < b₀/2`
  and Q (`NearlyCuspidalBoundary.collar_comparison`) on `[u, Sl]` gives the constant `< 3/2 < 2`.

BSA02 (Bishop–Gromov up to a convex boundary) is NOT used and stays open (disposition D5).

* `NearlyCuspidalBoundary.firstVolumeScale_sub_le`: the envelope at one pair, with G's two
  consumer clauses as hypotheses;
* `H_envelope`: the frozen interface, verbatim, with `δStar = min δ_G (1/1000)`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- Relative volume comparison below the boundary distance with the buffer constant `e^{1/2}`:
if `R < d(q, ∂W)` and `sec ≥ -(4R)⁻²` on `B(q, R)`, then `V_q(R) s³ ≤ e^{1/2} R³ V_q(s)` for
`0 < s ≤ R` (B2 and the crude model bounds `c₃ t³ ≤ V_{-k²}(t) ≤ c₃ t³ e^{2kt}`). -/
theorem ballVolume_toReal_mul_cube_le_exp_half_of_distanceToBoundary (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (q : W.Carrier) {s R : ℝ} (hs : 0 < s)
    (hsR : s ≤ R) (hdepth : ENNReal.ofReal R < distanceToBoundary W g q)
    (hsec : ∀ y ∈ riemannianBallOf g q R, SectionalBoundedBelowAt g y (-((4 * R) ^ 2)⁻¹)) :
    (ballVolume g q R).toReal * s ^ 3 ≤ Real.exp (1 / 2) * R ^ 3 * (ballVolume g q s).toReal := by
  have hR : 0 < R := hs.trans_le hsR
  set κ : ℝ := ((4 * R) ^ 2)⁻¹ with hκdef
  have hκ : 0 ≤ κ := inv_nonneg.mpr (sq_nonneg _)
  have hBG := localBishopGromov_real_cross_of_distanceToBoundary W g q hκ hs hsR hdepth hsec
  have hVs : euclideanUnitBallVolume 3 * s ^ 3 ≤ modelVolume (-κ) 3 s :=
    sectionalThree_euclidean_le_model hκ hs.le
  have hVR : modelVolume (-κ) 3 R ≤ euclideanUnitBallVolume 3 * R ^ 3 * Real.exp (1 / 2) := by
    have hq : 0 ≤ (4 * R)⁻¹ := inv_nonneg.mpr (by positivity)
    have h := modelVolume_neg_sq_three_le hq hR.le
    have hκq : κ = (4 * R)⁻¹ ^ 2 := by rw [hκdef, inv_pow]
    have hexp : 2 * (4 * R)⁻¹ * R = 1 / 2 := by
      field_simp
      ring
    rwa [hκq, ← hexp]
  have hc := euclideanUnitBallVolume_pos 3
  have hX : 0 ≤ (ballVolume g q R).toReal := ENNReal.toReal_nonneg
  have hY : 0 ≤ (ballVolume g q s).toReal := ENNReal.toReal_nonneg
  have key : euclideanUnitBallVolume 3 * ((ballVolume g q R).toReal * s ^ 3) ≤
      euclideanUnitBallVolume 3 * (Real.exp (1 / 2) * R ^ 3 * (ballVolume g q s).toReal) := by
    calc euclideanUnitBallVolume 3 * ((ballVolume g q R).toReal * s ^ 3)
        = (ballVolume g q R).toReal * (euclideanUnitBallVolume 3 * s ^ 3) := by ring
      _ ≤ (ballVolume g q R).toReal * modelVolume (-κ) 3 s :=
          mul_le_mul_of_nonneg_left hVs hX
      _ ≤ modelVolume (-κ) 3 R * (ballVolume g q s).toReal := hBG
      _ ≤ (euclideanUnitBallVolume 3 * R ^ 3 * Real.exp (1 / 2)) * (ballVolume g q s).toReal :=
          mul_le_mul_of_nonneg_right hVR hY
      _ = euclideanUnitBallVolume 3 * (Real.exp (1 / 2) * R ^ 3 * (ballVolume g q s).toReal) := by
          ring
  exact le_of_mul_le_mul_left key hc

/-- **BSA05 envelope at one pair** (statement H, kernel). On a connected compact carrier with a
nearly cuspidal boundary, `0 ≤ δ ≤ 1/1000`, the static collapse beyond distance `10`, and G's two
consumer clauses (near data within `10` of `∂W`; `R_p ≤ d(p, ∂W) + 3`), on the uniform tail the
envelope `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` holds at the pair `p, q` (boundary points allowed). -/
theorem NearlyCuspidalBoundary.firstVolumeScale_sub_le {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hcoll : boundaryVolumeCollapsed W g δ)
    (hnear : ∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
      1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
        ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a))
    (hfar : ∀ p, curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3)
    {Λ w n : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < euclideanThreeUnitBallVolume / 4)
    (hn : 3 ≤ n) (hnS : 2 * (1 + 2 / Λ) < n) (hnw : n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3))
    (hδn : δ * (16 * n ^ 4) ≤ 1)
    (hδa : 1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2)
    (p q : W.Carrier) :
    firstVolumeScale g p w - Λ / 2 * (riemannianEDistOf g p q).toReal ≤
      firstVolumeScale g q (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  set S := 1 + 2 / Λ with hSdef
  set w' := w / (2 * S ^ 3) with hw'def
  set a := (1 / 100) / (2 * S) with hadef
  have h2Λ : 0 < 2 / Λ := div_pos two_pos hΛ
  have hS1 : 1 < S := by linarith
  have hS0 : 0 < S := by linarith
  have hS3 : 1 < 2 * S ^ 3 := by nlinarith [one_le_pow₀ (n := 3) hS1.le]
  have hw' : 0 < w' := div_pos hw (by linarith)
  have hw'w : w' < w := div_lt_self hw hS3
  have hw2 : w = 2 * S ^ 3 * w' := by
    rw [hw'def]
    field_simp
  have hw'c : w' < euclideanThreeUnitBallVolume / 4 := hw'w.trans hwc
  obtain ⟨hl, hVl, -⟩ := firstVolumeScale_spec_everywhere W g p hw hwc
  obtain ⟨hu, hVu, -⟩ := firstVolumeScale_spec_everywhere W g q hw' hw'c
  set l := firstVolumeScale g p w
  set u := firstVolumeScale g q w'
  set d := (riemannianEDistOf g p q).toReal
  by_contra hfail
  have hfail' : u < l - Λ / 2 * d := lt_of_not_ge hfail
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hΛd : Λ / 2 * d < l := by linarith
  have hul : u < l := by nlinarith
  have hdS : d < S * l - l := by
    have h1 : S * l - l = 2 / Λ * l := by rw [hSdef]; ring
    have h2 : d * Λ = 2 * (Λ / 2 * d) := by ring
    rw [h1, div_mul_eq_mul_div, lt_div_iff₀ hΛ]
    linarith
  have hSl0 : 0 < S * l := mul_pos hS0 hl
  have huSl : u ≤ S * l := hul.le.trans (le_mul_of_one_le_left hl.le hS1.le)
  -- the distance is finite (connected carrier)
  have hdfin : riemannianEDistOf g p q ≠ ⊤ := riemannianEDistOf_ne_top g p q
  have hdeq : riemannianEDistOf g p q = ENNReal.ofReal d := (ENNReal.ofReal_toReal hdfin).symm
  -- `B(p, l) ⊆ B(q, Sl)` and `V_q(Sl) ≥ w l³`
  have hincl1 : riemannianBallOf g p l ⊆ riemannianBallOf g q (S * l) := by
    intro y hy
    change riemannianEDistOf g p y < ENNReal.ofReal l at hy
    change riemannianEDistOf g q y < ENNReal.ofReal (S * l)
    calc riemannianEDistOf g q y ≤ riemannianEDistOf g q p + riemannianEDistOf g p y :=
          riemannianEDistOf_triangle g q p y
      _ < ENNReal.ofReal d + ENNReal.ofReal l := by
          rw [riemannianEDistOf_comm g q p, hdeq]
          exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy
      _ = ENNReal.ofReal (d + l) := (ENNReal.ofReal_add hd0 hl.le).symm
      _ ≤ ENNReal.ofReal (S * l) := ENNReal.ofReal_le_ofReal (by linarith)
  have hVSl : w * l ^ 3 ≤ (ballVolume g q (S * l)).toReal := by
    rw [← hVl]
    exact ENNReal.toReal_mono (ballVolume_ne_top g q _) (MeasureTheory.measure_mono hincl1)
  -- BSA04.a and `n > 2S`: `4Sl < R_p`
  have hstand :=
    ofReal_two_mul_firstVolumeScale_lt_curvatureRadius_of_boundary_data W g hn hδ0 hδn hcoll
      hnear p
  have hn0 : 0 < n := by linarith
  have hlr : l ≤ firstVolumeScale g p n⁻¹ :=
    firstVolumeScale_anti_of_le g p (inv_pos.mpr hn0) (hnw.trans hw'w.le)
  have h4 : 4 * (S * l) ≤ 2 * n * firstVolumeScale g p n⁻¹ := by
    nlinarith [mul_lt_mul_of_pos_right hnS hl,
      mul_le_mul_of_nonneg_left hlr (by linarith : (0 : ℝ) ≤ 2 * n)]
  have hR4 : ENNReal.ofReal (4 * (S * l)) < curvatureRadius g p :=
    (ENNReal.ofReal_le_ofReal h4).trans_lt hstand
  -- the common contradiction: a relative comparison on `[u, Sl]` with a constant `< 2`
  have hfinal : ∀ C : ℝ, C < 2 →
      (ballVolume g q (S * l)).toReal * u ^ 3 ≤ C * (S * l) ^ 3 * (ballVolume g q u).toReal →
        False := by
    intro C hC h
    rw [hVu] at h
    have h1 : w * l ^ 3 * u ^ 3 ≤ (ballVolume g q (S * l)).toReal * u ^ 3 :=
      mul_le_mul_of_nonneg_right hVSl (by positivity)
    have hP : 0 < S ^ 3 * l ^ 3 * u ^ 3 * w' := by positivity
    have h2 : 2 * (S ^ 3 * l ^ 3 * u ^ 3 * w') ≤ C * (S ^ 3 * l ^ 3 * u ^ 3 * w') := by
      calc 2 * (S ^ 3 * l ^ 3 * u ^ 3 * w') = w * l ^ 3 * u ^ 3 := by rw [hw2]; ring
        _ ≤ (ballVolume g q (S * l)).toReal * u ^ 3 := h1
        _ ≤ C * (S * l) ^ 3 * (w' * u ^ 3) := h
        _ = C * (S ^ 3 * l ^ 3 * u ^ 3 * w') := by ring
    have h3 := le_of_mul_le_mul_right h2 hP
    linarith
  rcases lt_or_ge (ENNReal.ofReal (S * l)) (distanceToBoundary W g q) with hint | hnearq
  · -- interior branch: B2 at `q` with outer radius `Sl`
    have hincl2 : riemannianBallOf g q (S * l) ⊆ riemannianBallOf g p (4 * (S * l)) := by
      intro y hy
      change riemannianEDistOf g q y < ENNReal.ofReal (S * l) at hy
      change riemannianEDistOf g p y < ENNReal.ofReal (4 * (S * l))
      calc riemannianEDistOf g p y ≤ riemannianEDistOf g p q + riemannianEDistOf g q y :=
            riemannianEDistOf_triangle g p q y
        _ < ENNReal.ofReal d + ENNReal.ofReal (S * l) := by
            rw [hdeq]
            exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy
        _ = ENNReal.ofReal (d + S * l) := (ENNReal.ofReal_add hd0 hSl0.le).symm
        _ ≤ ENNReal.ofReal (4 * (S * l)) := ENNReal.ofReal_le_ofReal (by linarith)
    have hsec := sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius g
      (by positivity : (0 : ℝ) < 4 * (S * l)) hR4.le
    exact hfinal (Real.exp (1 / 2)) exp_half_lt_two
      (ballVolume_toReal_mul_cube_le_exp_half_of_distanceToBoundary W g q hu huSl hint
        fun y hy => hsec y (hincl2 hy))
  · -- near branch: Q at `q` on `[u, Sl]`
    have hDp : distanceToBoundary W g p ≤ ENNReal.ofReal (S * l + d) := by
      refine (distanceToBoundary_le_add W g p q).trans ?_
      rw [hdeq, ENNReal.ofReal_add hSl0.le hd0]
      exact add_le_add hnearq le_rfl
    have hDp10 : distanceToBoundary W g p ≤ ENNReal.ofReal 10 := by
      by_contra h10
      have h10' : ENNReal.ofReal 10 < distanceToBoundary W g p := lt_of_not_ge h10
      have hfin : distanceToBoundary W g p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDp
      set D := (distanceToBoundary W g p).toReal
      have hDeq : distanceToBoundary W g p = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfin).symm
      have hRp := hR4.trans_le (hfar p)
      rw [hDeq] at h10' hDp hRp
      have hD10 : 10 < D := (ENNReal.ofReal_lt_ofReal_iff'.mp h10').1
      have hDle : D ≤ S * l + d := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hDp
      rw [← ENNReal.ofReal_add (by linarith) (by norm_num)] at hRp
      have h43 : 4 * (S * l) < D + 3 := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hRp
      linarith
    obtain ⟨-, hvolp⟩ := hnear p hDp10
    have ha : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      rw [hadef, div_le_one (by positivity)]
      linarith
    have hrw' : firstVolumeScale g p w' < a :=
      firstVolumeScale_lt_of_ballVolume_le_linear g p ha hw' (hvolp a ha ha1) hδa
    have hlw' : l ≤ firstVolumeScale g p w' := firstVolumeScale_anti_of_le g p hw' hw'w.le
    have hSa : S * a = 1 / 200 := by
      rw [hadef]
      field_simp
      norm_num
    have hSl : S * l ≤ 1 / 100 := by
      nlinarith [mul_lt_mul_of_pos_left (hlw'.trans_lt hrw') hS0]
    have hq : distanceToBoundary W g q ≤ ENNReal.ofReal (1 / 100) :=
      hnearq.trans (ENNReal.ofReal_le_ofReal hSl)
    have hQ := B.collar_comparison hδ0 hδ hq hu huSl hSl
    have hC := cusp_collar_constant_lt hδ0 hδ
    have hq0 : 0 ≤ (1 + δ) / (1 - δ) := div_nonneg (by linarith) (by linarith)
    have hC0 : 0 ≤ Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3 * (S * l) ^ 3 := by
      positivity
    refine hfinal (Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3) (by linarith) ?_
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballVolume_ne_top g q u)) hQ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hu.le 3),
      ENNReal.toReal_ofReal hC0] at hreal

/-- **H (BSA05 envelope at all pairs).** On the uniform tail of the BSA04 sequence,
`r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` for ALL `p, q` (boundary included), `S = 1 + 2/Λ`,
`w' = w/(2S³)`, `a = b₀/(2S)`. The frozen interface, verbatim; `δStar = min δ_G (1/1000)`. -/
theorem H_envelope :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ →
      ∀ {Λ w n : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
        3 ≤ n → 2 * (1 + 2 / Λ) < n → n⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) →
        δ * (16 * n ^ 4) ≤ 1 →
        1000 * δ ^ 2 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 →
        ∀ p q : W.Carrier, firstVolumeScale g p w - Λ / 2 * (riemannianEDistOf g p q).toReal ≤
          firstVolumeScale g q (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  obtain ⟨δG, hδG, hG⟩ := G_consumer_clauses.{u}
  refine ⟨min δG (1 / 1000), lt_min hδG (by norm_num), ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll Λ w n hΛ hw hwc hn hnS hnw hδn hδa p q
  obtain ⟨hnear, hfar⟩ := hG W g K δ hK hδ0 (hδ.trans (min_le_left _ _)) B
  exact B.firstVolumeScale_sub_le hδ0 (hδ.trans (min_le_right _ _)) hcoll hnear
    (fun p => (hfar ‹_› p).2) hΛ hw hwc hn hnS hnw hδn hδa p q

end DifferentialGeometry.Geometry.Collapse
