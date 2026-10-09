import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorAnalytic
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.UniformMetricModel

/-!
# LC88 / BCP04, packet P2: the local LC09 on the completed interior (lanes BDRY-1, BDRY-2; G9)

Review 45 §1.4–§1.6: the uniform metric model contract LC08 (`exists_uniform_metric_model`, a
threshold kernel for complete σ-compact boundaryless sources) is applied on the completed interior
`(W°, d_ĝ)` (cut height `4`) at an eligible point `q ∈ U₀ = {D > 5}`, with the ORIGINAL metric and
the ORIGINAL scale `ρ` of `W` (never recomputed); the Kleiner–Lott map is pulled back to
`(W, ρ(q)⁻¹ d_g, q)` along the inverse interior inclusion on the protected ball `B_g(q, σ⁻¹ρ(q))`.
Every radius used (`2ρ`, `L₀ρ`, `4σ⁻¹ρ`) is budgeted on the BCP04.a tail (`8 L₀ ≤ n`, `32 σ⁻¹ ≤ n`).
* `exists_uniform_metric_model_boundary_BDRY1`: the local LC09 at an attained volume radius;
* `exists_uniform_metric_model_firstScale_BDRY2` (consumer): the same at the ORIGINAL first volume
  scale `r_q(w)` of `g`, under the LC02 lower bound `r_q(w)/2 < ρ(q)` (the blueprint form).
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

/-- **Local LC09 on a carrier with boundary (P2).** The constants `w₀, L₀` of the uniform metric
model contract (LC08, `exists_uniform_metric_model`) work at every eligible point `q ∈ U₀ = {D > 5}`
of a connected carrier with boundary, for the ORIGINAL metric and scale: given the completion `ĝ`
at cut height `4`, BCP04.a with `8 L₀ ≤ n`, `32 σ⁻¹ ≤ n`, an attained volume ratio
`vol_g B(q, r) = w r³` at `0 < r ≤ 2 ρ(q)` and the sectional buffer on `B_g(q, L₀ ρ(q))`, there is a
complete proper model `Y` of dimension `≤ 2` with nonnegative four-point comparison and segments,
and an actual Kleiner–Lott `σ`-map of `(W, ρ(q)⁻¹ d_g, q)` to it. -/
theorem exists_uniform_metric_model_boundary_BDRY1 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
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
        8 * L₀ ≤ n → 32 * σ⁻¹ ≤ n →
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
            Nonempty (@KleinerLottApprox W.Carrier Y
              ((inducedMetricSpace g).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) mY q.val y σ) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hmodel⟩ :=
    exists_uniform_metric_model (I := 𝓡 3) hdim hσ hσ1
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomplete heq ρ hρ n hbcp hnL hnσ q hq w r hw hww hr hr2 hvol hsec
  have hconn := connectedSpace_pieceInterior_top_BDRY1 W
  let mN := inducedMetricSpace ĝ
  have hmN := inducedMetricSpace_hmetric ĝ
  have hcN : @CompleteSpace (W.pieceInterior ⊤) mN.toUniformSpace := by
    let : RiemannianBundle (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
      ⟨ĝ.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
      ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact hcomplete.complete
  have hdata := completion_cut_local_data_BDRY1 W g ĝ (by norm_num) heq (ρ := 1) one_pos
  obtain ⟨hsrc, hiso⟩ := completion_isometric_cut_BDRY1 W g ĝ heq (a := 4)
  -- budgets
  have hbudget : ∀ {C : ℝ}, 0 ≤ C → 24 * C ≤ n →
      ENNReal.ofReal (3 * C * ρ q + 4) < distanceToBoundary W g q :=
    fun hC hn => ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp hC hn q hq
  -- the volume hypothesis on the completion
  have hvolN : ballVolume ĝ q r = ENNReal.ofReal (w * r ^ 3) := by
    have hb := hbudget (C := 2 / 3) (by norm_num) (by linarith)
    have hrq : ENNReal.ofReal (r * 1 + 4) ≤ distanceToBoundary W g q :=
      (ENNReal.ofReal_le_ofReal (by nlinarith [hρ q])).trans hb.le
    have h := (hdata.2.2 q hr.le hrq).1
    rw [mul_one] at h
    rw [h, hvol]
  -- the sectional hypothesis on the completion
  have hsecN : ∀ y ∈ riemannianBallOf ĝ q (L₀ * ρ q),
      SectionalBoundedBelowAt ĝ y (-((L₀ * ρ q) ^ 2)⁻¹) := by
    have hb := hbudget (C := L₀ / 3) (by positivity) (by linarith)
    have hr' : 3 * (L₀ / 3) * ρ q = L₀ * ρ q := by ring
    rw [hr'] at hb
    have hball := image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq q
      (mul_nonneg (by linarith) (hρ q).le) hb.le
    have hsub := riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g
      (mul_nonneg (by linarith) (hρ q).le) (by norm_num) hb.le
    intro y hy
    have hy' : y.val ∈ riemannianBallOf g q.val (L₀ * ρ q) := hball ▸ ⟨y, hy, rfl⟩
    exact ((hdata.1 y (hsub hy') _).1).mpr (hsec _ hy')
  obtain ⟨Y, mY, y, hYc, hYp, hYd, hYf, hYs, ⟨f⟩⟩ :=
    @hmodel (W.pieceInterior ⊤) mN _ _ _ hcN ĝ hmN q (ρ q) w r (hρ q) hw hww hr hr2 hvolN hsecN
  refine ⟨Y, mY, y, hYc, hYp, hYd, hYf, hYs, ⟨?_⟩⟩
  -- pull the map back along the inverse inclusion on the protected ball `B_g(q, σ⁻¹ρ)`
  set Φ := (interiorInclusion_BDRY1 W).symm with hΦ
  have hb4 := hbudget (C := 4 * σ⁻¹ / 3) (by positivity) (by linarith)
  have hr4 : 3 * (4 * σ⁻¹ / 3) * ρ q = 4 * (σ⁻¹ * ρ q) := by ring
  rw [hr4] at hb4
  have hsub4 : riemannianBallOf g q.val (4 * (σ⁻¹ * ρ q)) ⊆
      ((regionCut_BDRY1 W g 4 : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) :=
    riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g
      (by have := inv_pos.mpr hσ; have := hρ q; positivity) (by norm_num) hb4.le
  have hsub1 : riemannianBallOf g q.val (σ⁻¹ * ρ q) ⊆
      ((regionCut_BDRY1 W g 4 : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) :=
    (riemannianBallOf_mono g q.val (by nlinarith [hρ q, inv_pos.mpr hσ])).trans hsub4
  have hΦq : Φ q.val = q := interiorInclusion_symm_val_BDRY1 W q
  have himage := image_riemannianBallOf_of_isometricOnOpen_BDRY1 g ĝ Φ hsrc hiso hsub1
  rw [hΦq] at himage
  have hballW : @Metric.ball W.Carrier
      ((inducedMetricSpace g).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))).toPseudoMetricSpace q.val σ⁻¹ =
      riemannianBallOf g q.val (σ⁻¹ * ρ q) := by
    rw [rescale_inv_ball_BDRY1 _ (hρ q), inducedMetricSpace_ball]
  have hballN : @Metric.ball (W.pieceInterior ⊤)
      (mN.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))).toPseudoMetricSpace q σ⁻¹ =
      riemannianBallOf ĝ q (σ⁻¹ * ρ q) := by
    rw [rescale_inv_ball_BDRY1 _ (hρ q), inducedMetricSpace_ball]
  refine @KleinerLottApprox.pullback_BDRY1 (W.pieceInterior ⊤) W.Carrier Y
    (mN.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q)))
    ((inducedMetricSpace g).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) mY q y σ f Φ q.val hΦq ?_ ?_
  · intro a ha b hb
    rw [hballW] at ha hb
    have h4 : σ⁻¹ * ρ q = 4 * (σ⁻¹ * ρ q) / 4 := by ring
    rw [h4] at ha hb
    have h := riemannianEDistOf_of_isometricOnOpen_BDRY1 g ĝ Φ hsrc hiso hsub4 ha hb
    change (ρ q)⁻¹ * (riemannianEDistOf ĝ (Φ a) (Φ b)).toReal =
      (ρ q)⁻¹ * (riemannianEDistOf g a b).toReal
    rw [h]
  · rw [hballN, hballW, himage]

/-- **Consumer: the local LC09 at the original first volume scale.** Under the LC02 lower bound
`r_q(w)/2 < ρ(q)` of the ORIGINAL first volume scale of `g` (first-hit witness, BSA03.a), the
radius `r_q(w)` is an admissible attained radius for the local LC09
`exists_uniform_metric_model_boundary_BDRY1`. -/
theorem exists_uniform_metric_model_firstScale_BDRY2 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
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
        8 * L₀ ≤ n → 32 * σ⁻¹ ≤ n →
        ∀ (q : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g q →
        ∀ {w : ℝ}, 0 < w → w < w₀ → firstVolumeScale g q.val w / 2 < ρ q →
        (∀ y ∈ riemannianBallOf g q.val (L₀ * ρ q),
          SectionalBoundedBelowAt g y (-((L₀ * ρ q) ^ 2)⁻¹)) →
        ∃ (Y : Type) (mY : MetricSpace Y),
          letI := mY
          ∃ y : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
            fourPointComparison 0 (univ : Set Y) ∧
            (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
              f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
            Nonempty (@KleinerLottApprox W.Carrier Y
              ((inducedMetricSpace g).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) mY q.val y σ) := by
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hmain⟩ :=
    exists_uniform_metric_model_boundary_BDRY1.{u} hσ hσ1
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomplete heq ρ hρ n hbcp hnL hnσ q hq w hw hww hfirst hsec
  have hd : 0 < distanceToBoundary W g q.val := (zero_le).trans_lt hq
  obtain ⟨hpos, hhit, -⟩ :=
    firstVolumeScale_spec_of_distanceToBoundary_pos W g q.val hd hw (hww.trans hw₀c)
  have hvol : ballVolume g q.val (firstVolumeScale g q.val w) =
      ENNReal.ofReal (w * firstVolumeScale g q.val w ^ 3) := by
    rw [← hhit, ENNReal.ofReal_toReal (ballVolume_ne_top g _ _)]
  exact hmain W g ĝ hcomplete heq ρ hρ hbcp hnL hnσ q hq hw hww hpos (by linarith) hvol hsec

end DifferentialGeometry.Geometry.Collapse
