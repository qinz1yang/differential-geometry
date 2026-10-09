import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPointData
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.VolumeLowerEverywhere
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorOrientation

/-!
# LC88 / BCP04, packet P5 → P6: binding of the shared regionalised kernel to `(W°, d_ĝ)` (BDRY-5)

Review 45 §3.3 (binding route: ONE shared regionalised kernel). The kernel
`exists_regional_chartFamilyEA_BDRY4` (G17) is a statement about an abstract complete, proper,
σ-compact, connected, oriented carrier with explicit local data. This module discharges its
hypotheses on the interior carrier `W° = W.pieceInterior ⊤` (interior atlas, the completed metric
`ĝ = g°` on `{D ≥ 4}`, `ĝ ≥ g°`), with the ORIGINAL scale `ρ ∘ val` of `W` (never recomputed),
the regions `U₁ = {D > 10}`, `U₂ = {D ≥ 20}` and the compact candidate envelope `{D ≥ 10}`; every
radius is budgeted by BCP04.a at one `n` (`8 Lbig ≤ n`):

* `contMDiff_comp_val_BDRY5`, `lipschitzWith_comp_val_completion_BDRY5`: smoothness and the
  Lipschitz bound of `ρ ∘ val` for `d_ĝ` (`d_g ≤ d_ĝ`);
* `ofReal_ten_lt_of_near_BDRY5`, `margin_completion_BDRY5`: the margin of LFR44's witnesses
  (`p ∈ U₂`, `d_ĝ(a, p) < Δρ(a)` ⇒ `a ∈ U₁`, for `13Δ ≤ 10n`);
* `sectional_of_normalized_buffer_BDRY5`, `regional_point_data_BDRY5`: the buffer, the volume of
  the unit ball of `ρ⁻² ĝ` and the derivative bounds at `q ∈ U₁`, from BSA06 at `(q, ρ(q))`
  through G11's pair data;
* `model_completion_BDRY5`: the collapsed model of quality `σ` at `q ∈ U₁` (G15, first-hit
  witness `r = r_q(w) < 2ρ(q)`, the `g`-buffer from BSA06);
* `exists_interior_chartFamilyEA_BDRY5`: the kernel on `(W°, d_ĝ)` — a `ChartFamilyEOn` with
  circle adapted packets, centres in `U₁`, covers of `U₁`/`U₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Binding

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

omit [ConnectedSpace W.Carrier] in
/-- The original scale read on `W°` (interior atlas) is smooth. -/
theorem contMDiff_comp_val_BDRY5 {ρ : W.Carrier → ℝ} (hρ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : W.pieceInterior ⊤ => ρ x) :=
  hρ.comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff

/-- A scale `Λ`-Lipschitz for `d_g` is `Λ`-Lipschitz for `d_ĝ` on `W°` when `ĝ ≥ g°`. -/
theorem lipschitzWith_comp_val_completion_BDRY5
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    {ρ : W.Carrier → ℝ} {Λ : ℝ}
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) :
    @LipschitzWith (W.pieceInterior ⊤) ℝ (inducedMetricSpace ĝ).toPseudoEMetricSpace _
      (Real.toNNReal Λ) (fun x => ρ x) := by
  intro x y
  have : Nonempty (W.pieceInterior ⊤) := ⟨x⟩
  rw [edist_dist, Real.dist_eq]
  exact (hlip x y).trans (mul_le_mul' (le_of_eq rfl)
    (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle x y))

/-- **Margin.** A point `v` of `W°` that is `V ρ_v`-close for `d_ĝ` to a point `z` with
`D(z) ≥ 10 + m` has `D(v) > 10`, by BCP04.a at `v` and `13 V ≤ m n` (`ĝ ≥ g°`). -/
theorem ofReal_ten_lt_of_near_BDRY5
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (v z : W.pieceInterior ⊤) {ρv V m n : ℝ} (hρv : 0 < ρv) (hV : 0 ≤ V) (hm : 0 < m)
    (hVn : 13 * V ≤ m * n)
    (hbcp : n * (distanceToBoundary W g v).toReal / ((distanceToBoundary W g v).toReal + 3) <
      (distanceToBoundary W g v).toReal / ρv)
    (hz : ENNReal.ofReal (10 + m) ≤ distanceToBoundary W g z)
    (hvz : riemannianEDistOf ĝ v z < ENNReal.ofReal (V * ρv)) :
    ENNReal.ofReal 10 < distanceToBoundary W g v := by
  by_contra h10
  have hD10 : distanceToBoundary W g v ≤ ENNReal.ofReal 10 := not_lt.mp h10
  have htop : distanceToBoundary W g v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD10
  set d := (distanceToBoundary W g v).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hd10 : d ≤ 10 := by
    rw [hd, ← ENNReal.ofReal_le_ofReal_iff (by norm_num), ENNReal.ofReal_toReal htop]
    exact hD10
  have hdpos : 0 < d := by
    by_contra hd0'
    have hd00 : d = 0 := le_antisymm (not_lt.mp hd0') hd0
    rw [hd00] at hbcp
    simp at hbcp
  have hnρ : n * ρv < d + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρv] at hbcp
    nlinarith
  have hVρ : V * ρv < m := by
    have h13 : n * ρv < 13 := by linarith
    by_cases hV0 : V = 0
    · rw [hV0, zero_mul]; exact hm
    have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hn : 0 < n := by nlinarith
    nlinarith
  have : Nonempty (W.pieceInterior ⊤) := ⟨v⟩
  have hdist := (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle v z).trans_lt hvz
  have htri := distanceToBoundary_le_add W g z.val v.val
  rw [riemannianEDistOf_comm] at htri
  have hlt : distanceToBoundary W g z < ENNReal.ofReal (10 + m) := by
    calc distanceToBoundary W g z ≤ distanceToBoundary W g v + riemannianEDistOf g v.val z.val :=
          htri
      _ < ENNReal.ofReal 10 + ENNReal.ofReal m := by
          exact ENNReal.add_lt_add_of_le_of_lt htop hD10
            (hdist.trans_le (ENNReal.ofReal_le_ofReal hVρ.le))
      _ = ENNReal.ofReal (10 + m) := by
          rw [← ENNReal.ofReal_add (by norm_num) hm.le]
  exact (lt_irrefl _) (hz.trans_lt hlt)

/-- **The margin of the kernel on `(W°, d_ĝ)`**: `p ∈ U₂ = {D ≥ 20}`, `d_ĝ(a, p) < Δ ρ(a)` ⇒
`a ∈ U₁ = {D > 10}`, for `13 Δ ≤ 10 n` and BCP04.a. -/
theorem margin_completion_BDRY5
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {Δ n : ℝ} (hΔ : 0 ≤ Δ) (hΔn : 13 * Δ ≤ 10 * n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p) :
    letI := inducedMetricSpace ĝ
    ∀ p ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}, ∀ a,
      dist a p < Δ * ρ a →
        a ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} := by
  let _ := inducedMetricSpace ĝ
  intro p hp a hap
  obtain ⟨s, hs, hsD⟩ := exists_pos_ofReal_le_distanceToBoundary_BDRY1 W g a
  have hDa : 0 < distanceToBoundary W g a := (ENNReal.ofReal_pos.mpr hs).trans_le hsD
  have hvz : riemannianEDistOf ĝ a p < ENNReal.ofReal (Δ * ρ a) := by
    rw [inducedMetricSpace_hmetric ĝ a p]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hap
  refine ofReal_ten_lt_of_near_BDRY5 W g ĝ hle a p (hρ a) hΔ (by norm_num : (0 : ℝ) < 10)
    (by linarith) (hbcp a hDa) ?_ hvz
  have h20 : (10 : ℝ) + 10 = 20 := by norm_num
  rw [h20]
  exact hp

omit [ConnectedSpace W.Carrier] in
/-- A buffer of `ρ⁻² g` on the normalized ball of radius `n/4` gives `sec_g ≥ -(Lρ)⁻²` on
`B_g(p, Lρ)` for `0 < L ≤ n/4`. -/
theorem sectional_of_normalized_buffer_BDRY5 {p : W.Carrier} {r n L : ℝ} (hr : 0 < r)
    (hsec : ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p (n / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric g r hr) y (-((n / 4) ^ 2)⁻¹))
    (hL : 0 < L) (hLn : L ≤ n / 4) :
    ∀ y ∈ riemannianBallOf g p (L * r), SectionalBoundedBelowAt g y (-((L * r) ^ 2)⁻¹) := by
  intro y hy
  have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p (n / 4) := by
    rw [normalizedCenterMetric_ball]
    exact riemannianBallOf_mono _ _ (mul_le_mul_of_nonneg_right hLn hr.le) hy
  have h := hsec y hy'
  rw [normalizedCenterMetric_eq_scaleMetric, sectionalBoundedBelowAt_scaleMetric_iff] at h
  refine h.mono ?_
  have hLr : 0 < L * r := mul_pos hL hr
  have hsq : ((n / 4) ^ 2)⁻¹ * r⁻¹ ^ 2 ≤ ((L * r) ^ 2)⁻¹ := by
    have he : ((n / 4) ^ 2)⁻¹ * r⁻¹ ^ 2 = ((n / 4 * r) ^ 2)⁻¹ := by
      rw [mul_pow, mul_inv, inv_pow]
    rw [he]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ hLr.le
    exact mul_le_mul_of_nonneg_right hLn hr.le
  linarith

/-- **Per-point analytic data on the completion.** At `q ∈ W°` with `D(q) > 5`, BCP04.a at
`(q, r)` and BSA06's clauses at `(q, r)` (volume ratio `≥ v`, buffer of `r⁻² g` on the normalized
ball of radius `n/4`, derivative bounds for `2R + 2 < n`), with `8 Lbig ≤ n`, `8 ≤ n`:
the buffer `sec_ĝ ≥ -(Lr)⁻²` on `B_ĝ(q, Lr)` (`0 < L ≤ Lbig`), the volume of the unit ball of
`r⁻² ĝ` is `≥ v`, and the derivative bounds of `r⁻² ĝ` hold for `R ≤ Lbig`. -/
theorem regional_point_data_BDRY5
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 5 < distanceToBoundary W g q)
    {r n v Lbig : ℝ} (hr : 0 < r) {K : ℕ} {Aprof : ℝ → ℝ}
    (hbcp : n * (distanceToBoundary W g q).toReal / ((distanceToBoundary W g q).toReal + 3) <
      (distanceToBoundary W g q).toReal / r)
    (hvol : v ≤ (ballVolume g q.val r).toReal / r ^ 3)
    (hsec : ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) q.val (n / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric g r hr) y (-((n / 4) ^ 2)⁻¹))
    (hder : ∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) q.val R,
        curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤ Aprof R)
    (hL8 : 8 * Lbig ≤ n) (hn8 : 8 ≤ n) :
    (∀ L, 0 < L → L ≤ Lbig →
      ∀ y ∈ @Metric.ball _ (inducedMetricSpace ĝ).toPseudoMetricSpace q (L * r),
        SectionalBoundedBelowAt ĝ y (-((L * r) ^ 2)⁻¹)) ∧
    v ≤ (ballVolume (normalizedCenterMetric ĝ r hr) q 1).toReal ∧
    (∀ R, 0 < R → R ≤ Lbig → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) q R,
        curvatureDerivativeNorm (normalizedCenterMetric ĝ r hr) k y ≤ Aprof R) := by
  have hnpos : 0 < n := by linarith
  refine ⟨fun L hL hLL y hy => ?_, ?_, fun R hR hRL k hk y hy => ?_⟩
  · have hpd := completion_pair_data_BDRY2 W g ĝ heq q hq hr hbcp (R := n / 8) (by positivity)
      (by linarith)
    have hsecN := hpd.2.1 (-((n / 4) ^ 2)⁻¹) (fun y' hy' => hsec y'
      (riemannianBallOf_mono _ _ (by linarith) hy'))
    rw [inducedMetricSpace_ball ĝ q _] at hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) q (n / 8) := by
      rw [normalizedCenterMetric_ball]
      exact riemannianBallOf_mono _ _ (mul_le_mul_of_nonneg_right (by linarith) hr.le) hy
    have h := hsecN y hy'
    rw [normalizedCenterMetric_eq_scaleMetric, sectionalBoundedBelowAt_scaleMetric_iff] at h
    refine h.mono ?_
    have hLr : 0 < L * r := mul_pos hL hr
    have hLn : L ≤ n / 4 := by linarith
    have hsq : ((n / 4) ^ 2)⁻¹ * r⁻¹ ^ 2 ≤ ((L * r) ^ 2)⁻¹ := by
      have he : ((n / 4) ^ 2)⁻¹ * r⁻¹ ^ 2 = ((n / 4 * r) ^ 2)⁻¹ := by
        rw [mul_pow, mul_inv, inv_pow]
      rw [he]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_left₀ hLr.le
      exact mul_le_mul_of_nonneg_right hLn hr.le
    linarith
  · have hpd := completion_pair_data_BDRY2 W g ĝ heq q hq hr hbcp (R := 1) zero_le_one
      (by linarith)
    rw [hpd.2.2.2, ballVolume_normalizedCenterMetric_one_BDRY2 finrank_euclideanSpace_fin g hr]
    exact hvol
  · have hpd := completion_pair_data_BDRY2 W g ĝ heq q hq hr hbcp (R := R) hR.le (by linarith)
    exact hpd.2.2.1 K (Aprof R) (fun k' hk' y' hy' => hder R hR (by linarith) k' hk' y' hy')
      k hk y hy

/-- **The collapsed model at eligible points of the completion** (G15 + first-hit witness + the
BSA06 buffer). For `0 < σ < 1` there are `w₀, L₀` such that, for the ORIGINAL scale `ρ` with the
LC02 lower bound `r_p(w)/2 < ρ(p)` (`w < w₀`), BCP04.a, BSA06's normalized buffer of radius `n/4`
and `8 L₀ ≤ n`, every `q ∈ W°` with `D(q) > 5` carries a Kleiner–Lott `σ`-map of
`(W°, ρ(q)⁻¹ d_ĝ, q)` to a complete proper model of dimension `≤ 2` with nonnegative four-point
comparison and segments. -/
theorem model_completion_BDRY5 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
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
        8 * L₀ ≤ n → 16 ≤ n → ∀ {w : ℝ}, 0 < w → w < w₀ →
        (∀ p, firstVolumeScale g p w / 2 < ρ p) →
        (∀ p : W.Carrier,
          ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
              (-((n / 4) ^ 2)⁻¹)) →
        ∀ (q : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g q →
        ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
          CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
          fourPointComparison 0 (univ : Set C) ∧
          (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
            f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
            ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
          Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) C
            ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) mC q c σ) := by
  obtain ⟨w₀, hw₀, hw₀c, L₀, hL₀, hmodel⟩ := exists_uniform_metric_model_completion_BDRY3.{u} hσ hσ1
  refine ⟨w₀, hw₀, hw₀c, L₀, hL₀, ?_⟩
  intro W _ g ĝ hcomp heq ρ hρ n hbcp hnL hn16 w hw hww hfirst hsecN q hq
  have hd : 0 < distanceToBoundary W g q.val := (zero_le).trans_lt hq
  obtain ⟨hpos, hhit, -⟩ :=
    firstVolumeScale_spec_of_distanceToBoundary_pos W g q.val hd hw (hww.trans hw₀c)
  have hvol : ballVolume g q.val (firstVolumeScale g q.val w) =
      ENNReal.ofReal (w * firstVolumeScale g q.val w ^ 3) := by
    rw [← hhit, ENNReal.ofReal_toReal (ballVolume_ne_top g _ _)]
  have hsec := sectional_of_normalized_buffer_BDRY5 W g (p := q.val) (hρ q) (hsecN q.val)
    (L := L₀) (by linarith) (by linarith)
  obtain ⟨Y, mY, y, h1, h2, h3, h4, h5, h6⟩ := hmodel W g ĝ hcomp heq ρ hρ hbcp hnL hn16 q hq hw
    hww hpos (by linarith [hfirst q.val]) hvol hsec
  exact ⟨Y, mY, y, h1, h2, h3, h4, h5, h6⟩

/-- **Binding of the shared regionalised kernel to `(W°, d_ĝ)` (P5 → P6).** The kernel
`exists_regional_chartFamilyEA_BDRY4` applied to the interior carrier `W° = W.pieceInterior ⊤`
(interior atlas, the metric `ĝ`, complete, `= g°` on `{D ≥ 4}`, `≥ g°`; orientation from
`W.orientation`), the ORIGINAL scale `ρ ∘ val` (smooth, `Λ`-Lipschitz for `g`, LC02 lower bound
`r(w)/2 < ρ`), the regions `U₁ = {D > 10}`, `U₂ = {D ≥ 20}`, the candidate envelope `{D ≥ 10}`,
and BSA06's clauses at one `n` with `8 Lbig ≤ n`, `13 Δ ≤ 10 n`, `16 ≤ n`. Parameter prefix =
the kernel's, with `0 < σ` and `∃ w₀, ∀ w < w₀` (G15's model threshold) in place of `v, A`
(`v = w'/(24 ∫ sinh²)`, `A R = 2^(K+2) C_A(K, 2R+2, w')`, `w' = w/(2(1 + 2/Λ)³)`). -/
theorem exists_interior_chartFamilyEA_BDRY5
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ Lmax : ℝ, ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ Lbig : ℝ, L₀ ≤ Lbig → Lmax ≤ Lbig →
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ →
        (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
        (∀ p, firstVolumeScale g p w / 2 < ρ p) →
      ∀ n : ℝ, 8 * Lbig ≤ n → 13 * Δ ≤ 10 * n → 16 ≤ n →
        (∀ p : W.Carrier,
          w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
              (ballVolume g p (ρ p)).toReal / ρ p ^ 3 ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
              (-((n / 4) ^ 2)⁻¹)) ∧
          (∀ R : ℝ, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρ p)) k y ≤
                (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                  (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          (0 < distanceToBoundary W g p →
            n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
              (distanceToBoundary W g p).toReal / ρ p)) →
      letI := inducedMetricSpace ĝ
      ∃ _ : CompleteSpace (W.pieceInterior ⊤),
      ∃ L : ChartFamilyEOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ
          {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x},
        Nonempty (∀ j (hj : j ∈ L.circle.centres),
          CircleAdaptedCentreOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
            (fun x => ρ x) (fun x => hρ x) β γ
            {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x} L.circle j hj) := by
  obtain ⟨a₂, ha₂, h⟩ := exists_regional_chartFamilyEA_BDRY4 hσs hσs1 K hK
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  have hσ1 : σ < 1 := hση.trans_lt (threeSplittingExclusionThreshold_lt.trans (by norm_num))
  obtain ⟨w₀, hw₀, -, Lm, hLm, hmodel⟩ := model_completion_BDRY5.{0} hσ hσ1
  refine ⟨w₀, hw₀, fun w hw hww b hb hbs hbc hbb₁ hsource => ?_⟩
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  have hv : 0 < w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos hw' (lt_of_lt_of_le (by norm_num) eight_le_twentyFour_mul_integral_sinh_sq)
  obtain ⟨b₀, hb₀, h⟩ := h σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend _ hv
    (fun R => (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
      (w / (2 * (1 + 2 / Λ) ^ 3))) b hb hbs hbc hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ3 Lmax => ?_⟩
  obtain ⟨L₀, hL₀, h⟩ := h β hβ2 hβ1 hβ1b hβ3 Lmax
  refine ⟨max L₀ Lm, lt_max_of_lt_left hL₀, fun Lbig hLbig hLmax W _ g ĝ hcomp heq hle ρ hρ hρsm
    hlip hfirst n hn8 hΔn hn16 hdata => ?_⟩
  let mX : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hcN : CompleteSpace (W.pieceInterior ⊤) := completeSpace_completion_BDRY2 W ĝ hcomp
  have hpN : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete hcomp
  obtain ⟨o⟩ := nonempty_interiorOrientation_BDRY5 W
  have hL₀b : L₀ ≤ Lbig := (le_max_left _ _).trans hLbig
  have hLmb : Lm ≤ Lbig := (le_max_right _ _).trans hLbig
  have hLbig0 : 0 ≤ Lbig := hL₀.le.trans hL₀b
  have hnLm : 8 * Lm ≤ n := by linarith only [hLmb, hn8]
  have hn8' : (8 : ℝ) ≤ n := by linarith only [hn16]
  have hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p := fun p => (hdata p).2.2.2
  have hpos5 : ∀ q : W.pieceInterior ⊤, ENNReal.ofReal 10 < distanceToBoundary W g q →
      ENNReal.ofReal 5 < distanceToBoundary W g q := fun q hq =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 10)).mpr
      (by norm_num : (5 : ℝ) < 10)) hq
  have hpt := fun (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 10 < distanceToBoundary W g q) =>
    regional_point_data_BDRY5 W g ĝ heq q (hpos5 q hq) (hρ q)
      (Aprof := fun R => (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
        (w / (2 * (1 + 2 / Λ) ^ 3)))
      (hbcp q ((zero_le).trans_lt (hpos5 q hq))) (hdata q).1 (hdata q).2.1 (hdata q).2.2.1 hn8 hn8'
  obtain ⟨L, hL⟩ := h Lbig hL₀b hLmax (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) o
    (fun x => ρ x) (fun x => hρ x) (contMDiff_comp_val_BDRY5 W hρsm)
    (lipschitzWith_comp_val_completion_BDRY5 W g ĝ hle hlip)
    {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
    {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
    {x | ENNReal.ofReal 10 ≤ distanceToBoundary W g x}
    (isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num))
    (fun x (hx : ENNReal.ofReal 10 < distanceToBoundary W g x) => show
      ENNReal.ofReal 10 ≤ distanceToBoundary W g x from le_of_lt hx)
    (fun x (hx : ENNReal.ofReal 20 ≤ distanceToBoundary W g x) => show
      ENNReal.ofReal 10 < distanceToBoundary W g x from lt_of_lt_of_le
        ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 20)).mpr
          (by norm_num : (10 : ℝ) < 20)) hx)
    (margin_completion_BDRY5 W g ĝ hle ρ hρ hΔpos.le hΔn hbcp)
    (fun p hp => hmodel W g ĝ hcomp heq ρ hρ hbcp hnLm hn16 hw hww hfirst
      (fun q => (hdata q).2.1) p (hpos5 p hp))
    (fun p hp => (hpt p hp).1) (fun p hp => (hpt p hp).2.1) (fun p hp => (hpt p hp).2.2)
  exact ⟨hcN, L, hL⟩

end Binding

end DifferentialGeometry.Geometry.Collapse
