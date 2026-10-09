import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorLocalModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPairData
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.RankExclusion

/-!
# LC88 / BCP04, packet P5 start: local data at eligible points of the completion (BDRY-3)

Review 45 §3.4 (P5: per-centre kernels on the complete carrier): the per-point local kernels of
the closed producer (LC08/LC09 `exists_uniform_metric_model`, LC18/LC20
`exists_local_rank_exclusion_of_attained_volume`) are statements about ONE complete σ-compact
manifold with an attained volume ratio and a sectional buffer. On the completed interior
`(W°, d_ĝ)` (cut height `4`) they apply at every eligible point `q ∈ U₀ = {D > 5}` once the two
hypotheses are transported from `W` (BCP04.a budgets `16 ≤ n`, `8 L ≤ n`):
* `completion_attained_data_BDRY3`: the attained volume and the sectional buffer of `g` at `q` hold
  for `ĝ`;
* `exists_uniform_metric_model_completion_BDRY3`: the local LC09 ON `(W°, d_ĝ)` (no pull-back);
* `completion_rank_le_two_BDRY3`: LC18/LC20 on `(W°, d_ĝ)` (no `3`-splitting, rank `≤ 2`);
* consumer `scaledSplittingRank_completion_le_two_BDRY3`: for the ORIGINAL scale `ρ` with the LC02
  lower bound (first-hit witness), the scaled splitting rank of `(W°, d_ĝ, ρ ∘ val)` is `≤ 2` at
  every eligible point.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle
open scoped ENNReal Manifold
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Transport of the local hypotheses to the completion.** At `q ∈ W°` with `D(q) > 5` and
BCP04.a (`16 ≤ n`, `8 L ≤ n`): an attained volume ratio `vol_g B(q, r) = w r³` at
`0 < r ≤ 2 ρ(q)` and a sectional bound on `B_g(q, L ρ(q))` hold for `ĝ`. -/
theorem completion_attained_data_BDRY3 (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 5 < distanceToBoundary W g q)
    {w r L : ℝ} (hr : 0 < r) (hr2 : r ≤ 2 * ρ q) (hL : 0 ≤ L) (hn16 : 16 ≤ n) (hnL : 8 * L ≤ n)
    (hvol : ballVolume g q.val r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ y ∈ riemannianBallOf g q.val (L * ρ q),
      SectionalBoundedBelowAt g y (-((L * ρ q) ^ 2)⁻¹)) :
    ballVolume ĝ q r = ENNReal.ofReal (w * r ^ 3) ∧
      ∀ y ∈ riemannianBallOf ĝ q (L * ρ q),
        SectionalBoundedBelowAt ĝ y (-((L * ρ q) ^ 2)⁻¹) := by
  have hdata := completion_cut_local_data_BDRY1 W g ĝ (by norm_num) heq (ρ := 1) one_pos
  have hbudget : ∀ {C : ℝ}, 0 ≤ C → 24 * C ≤ n →
      ENNReal.ofReal (3 * C * ρ q + 4) < distanceToBoundary W g q :=
    fun hC hn => ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp hC hn q hq
  refine ⟨?_, ?_⟩
  · have hb := hbudget (C := 2 / 3) (by norm_num) (by linarith)
    have hrq : ENNReal.ofReal (r * 1 + 4) ≤ distanceToBoundary W g q :=
      (ENNReal.ofReal_le_ofReal (by nlinarith [hρ q])).trans hb.le
    have h := (hdata.2.2 q hr.le hrq).1
    rw [mul_one] at h
    rw [h, hvol]
  · have hb := hbudget (C := L / 3) (by positivity) (by linarith)
    have hr' : 3 * (L / 3) * ρ q = L * ρ q := by ring
    rw [hr'] at hb
    have hball := image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq q
      (mul_nonneg hL (hρ q).le) hb.le
    have hsub := riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g
      (mul_nonneg hL (hρ q).le) (by norm_num) hb.le
    intro y hy
    have hy' : y.val ∈ riemannianBallOf g q.val (L * ρ q) := hball ▸ ⟨y, hy, rfl⟩
    exact ((hdata.1 y (hsub hy') _).1).mpr (hsec _ hy')

/-- **Local LC09 ON the completion.** The constants `w₀, L₀` of LC08 work at every eligible point
`q ∈ U₀` of `(W°, d_ĝ)`: an actual Kleiner–Lott `σ`-map of `(W°, ρ(q)⁻¹ d_ĝ, q)` to a complete
proper model of dimension `≤ 2` with nonnegative four-point comparison and segments. -/
theorem exists_uniform_metric_model_completion_BDRY3 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
        (∀ p, 0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / ρ p) →
        8 * L₀ ≤ n → 16 ≤ n →
        ∀ (q : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g q →
        ∀ {w r : ℝ}, 0 < w → w < w₀ → 0 < r → r ≤ 2 * ρ q →
        ballVolume g q.val r = ENNReal.ofReal (w * r ^ 3) →
        (∀ y ∈ riemannianBallOf g q.val (L₀ * ρ q),
          SectionalBoundedBelowAt g y (-((L₀ * ρ q) ^ 2)⁻¹)) →
        ∃ (Y : Type) (mY : MetricSpace Y),
          letI := mY
          ∃ y : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
            fourPointComparison 0 (univ : Set Y) ∧
            (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
              f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
            Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) Y
              ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) mY q y σ) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hmodel⟩ :=
    exists_uniform_metric_model (I := 𝓡 3) hdim hσ hσ1
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomplete heq ρ hρ n hbcp hnL hn16 q hq w r hw hww hr hr2 hvol hsec
  have hcN := completeSpace_completion_BDRY2 W ĝ hcomplete
  obtain ⟨hvolN, hsecN⟩ := completion_attained_data_BDRY3 W g ĝ heq ρ hρ hbcp q hq hr hr2
    (by linarith) hn16 hnL hvol hsec
  exact @hmodel (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ _ hcN ĝ
    (inducedMetricSpace_hmetric ĝ) q (ρ q) w r (hρ q) hw hww hr hr2 hvolN hsecN

/-- **LC18/LC20 ON the completion.** The constants `w₀, L₀` of the local rank exclusion work at
every eligible point `q ∈ U₀` of `(W°, d_ĝ)`: no `3`-splitting of `(W°, ρ(q)⁻¹ d_ĝ, q)` below LC18's
threshold, hence splitting rank `≤ 2` for every `β` with `β 3` below it. -/
theorem completion_rank_le_two_BDRY3 :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
        (∀ p, 0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / ρ p) →
        8 * L₀ ≤ n → 16 ≤ n →
        ∀ (q : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g q →
        ∀ {w r : ℝ}, 0 < w → w < w₀ → 0 < r → r ≤ 2 * ρ q →
        ballVolume g q.val r = ENNReal.ofReal (w * r ^ 3) →
        (∀ y ∈ riemannianBallOf g q.val (L₀ * ρ q),
          SectionalBoundedBelowAt g y (-((L₀ * ρ q) ^ 2)⁻¹)) →
        (∀ ε : ℝ, ε ≤ threeSplittingExclusionThreshold.{u, 0} →
          ¬ @HasEuclideanSplitting.{u, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 3 ε) ∧
        ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
          @splittingRank.{u, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≤ 2 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hrank⟩ :=
    exists_local_rank_exclusion_of_attained_volume.{u, 0} (I := 𝓡 3) hdim
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomplete heq ρ hρ n hbcp hnL hn16 q hq w r hw hww hr hr2 hvol hsec
  have hcN := completeSpace_completion_BDRY2 W ĝ hcomplete
  obtain ⟨hvolN, hsecN⟩ := completion_attained_data_BDRY3 W g ĝ heq ρ hρ hbcp q hq hr hr2
    (by linarith) hn16 hnL hvol hsec
  exact @hrank (W.pieceInterior ⊤) (inducedMetricSpace ĝ) _ _ _ hcN ĝ
    (inducedMetricSpace_hmetric ĝ) q (ρ q) w r (hρ q) hw hww hr hr2 hvolN hsecN

/-- **Consumer: the scaled rank of the completion is `≤ 2` on `U₀`.** For the ORIGINAL scale `ρ`
of `W` with the LC02 lower bound `r_q(w)/2 < ρ(q)` (first-hit witness), BCP04.a and the sectional
buffer on `B_g(q, L₀ ρ(q))`, the scaled splitting rank of `(W°, d_ĝ, ρ ∘ val)` is at most `2` at
every eligible point. -/
theorem scaledSplittingRank_completion_le_two_BDRY3 :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
        (∀ p, 0 < distanceToBoundary W g p →
          n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
            (distanceToBoundary W g p).toReal / ρ p) →
        8 * L₀ ≤ n → 16 ≤ n →
        ∀ {w : ℝ}, 0 < w → w < w₀ → ∀ (β : ℕ → ℝ),
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
        ∀ (q : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g q →
        firstVolumeScale g q.val w / 2 < ρ q →
        (∀ y ∈ riemannianBallOf g q.val (L₀ * ρ q),
          SectionalBoundedBelowAt g y (-((L₀ * ρ q) ^ 2)⁻¹)) →
        @scaledSplittingRank.{u, 0} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
          (fun x => ρ x) (fun x => hρ x) β q ≤ 2 := by
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hmain⟩ := completion_rank_le_two_BDRY3.{u}
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomplete heq ρ hρ n hbcp hnL hn16 w hw hww β hβ q hq hfirst hsec
  have hd : 0 < distanceToBoundary W g q.val := (zero_le).trans_lt hq
  obtain ⟨hpos, hhit, -⟩ :=
    firstVolumeScale_spec_of_distanceToBoundary_pos W g q.val hd hw (hww.trans hw₀c)
  have hvol : ballVolume g q.val (firstVolumeScale g q.val w) =
      ENNReal.ofReal (w * firstVolumeScale g q.val w ^ 3) := by
    rw [← hhit, ENNReal.ofReal_toReal (ballVolume_ne_top g _ _)]
  exact (hmain W g ĝ hcomplete heq ρ hρ hbcp hnL hn16 q hq hw hww hpos (by linarith) hvol
    hsec).2 β hβ

end DifferentialGeometry.Geometry.Collapse
