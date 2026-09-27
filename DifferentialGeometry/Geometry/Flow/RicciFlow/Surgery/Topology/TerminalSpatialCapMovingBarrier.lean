import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSpatialCanonicalAlternatives

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_moving_scalar_range_on_spatial_domains
    (L : G.TerminalLimitMetric) {B : Set G.terminalRegularOpen} (hB : IsCompact B)
    {rmin rmax : ℝ} (hrmin : 0 < rmin)
    (hBscalar : ∀ y ∈ B, rmin ≤ metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ rmax)
    {C1 C2 eps : ℝ} :
    ∀ᶠ t in 𝓝[<] s, ∀ x ∈ B,
      ∀ W : SpatialCanonicalWitness (G.flow.base.metric t) eps C1 C2 x.val,
      ∀ v ∈ W.domain.carrier,
        rmin / (2 * C2) ≤ G.flow.scalar t v ∧ G.flow.scalar t v ≤ C2 * (rmax + 1) := by
  have hclose := L.eventually_scalar_close_on_compact hB (half_pos hrmin)
  have hclose1 := L.eventually_scalar_close_on_compact hB one_pos
  filter_upwards [hclose, hclose1] with t ht ht1
  intro x hx W v hv
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hs := W.scalar_bounds v hv
  have hlo := abs_lt.mp (ht x hx)
  have hhi := abs_lt.mp (ht1 x hx)
  have hxs := hBscalar x hx
  change G.flow.scalar t x.val - metricScalarAt L.metric x ∈ Ioo (-(rmin / 2)) (rmin / 2) at hlo
  have hxlo : rmin / 2 ≤ G.flow.scalar t x.val := by
    have := hlo.1
    linarith [hxs.1]
  have hxhi : G.flow.scalar t x.val ≤ rmax + 1 := by
    change -1 < G.flow.scalar t x.val - metricScalarAt L.metric x ∧
      G.flow.scalar t x.val - metricScalarAt L.metric x < 1 at hhi
    linarith [hxs.2, hhi.2]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hxlo (inv_pos.mpr hC2).le
    have heq : C2⁻¹ * (rmin / 2) = rmin / (2 * C2) := by field_simp
    rw [heq] at hmul
    exact hmul.trans hs.1
  · exact hs.2.trans (mul_le_mul_of_nonneg_left hxhi hC2.le)

theorem TerminalLimitMetric.eventually_moving_spatial_cap_neck_compact_capture
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B) {rmax : ℝ}
    (hBscalar : ∀ y ∈ B, metricScalarAt L.metric y ≤ rmax)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B) {epsCanonical eps C1 C2 : ℝ}
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 (x n).val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical (x n).val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) (x n).val) ≤
        metricDistance (G.flow.base.metric (τ n)) (x n).val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ (v : ℕ → P.Carrier) (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps (v n)),
        (∀ n z, (cap n).tubeMap z = (neck n).map z) ∧
        (∀ n, v n ∈ (cap n).tube) ∧
        ∀ᶠ n in atTop,
          (W n).domain.carrier ∪ (neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆
            Subtype.val '' K := by
  classical
  choose v neck hmap using fun n => hW n (cap n) (depth n) (hcap n)
  have hv (n : ℕ) : v n ∈ (cap n).tube := by
    rw [← (cap n).tube_eq]
    exact ⟨((neck n).center, 0), ⟨mem_univ _, by norm_num⟩,
      (hmap n ((neck n).center, 0)).trans (neck n).center_eq⟩
  have hvW (n : ℕ) : v n ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr (hv n)
  have heps : 0 ≤ eps := (neck 0).eps_pos.le
  have hC2 : 0 ≤ C2 := zero_le_one.trans (W 0).one_le_comparison_constant
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨_, D2, q, _, hD2, hq, hc⟩ := hm epsCan hepsCan le_rfl
  let C : NNReal := ⟨D2, zero_le_one.trans hD2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 :=
    fun y t ht hy => (hc y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  let Bd := (1 + 4323 * eps) * (C2 * (|rmax| + 2))
  obtain ⟨K₀, hK₀, hKreg, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch Bd
  let K : Set G.terminalRegularOpen := Subtype.val ⁻¹' K₀
  have himage : Subtype.val '' K = K₀ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKreg hy⟩, hy, rfl⟩
  have hK : IsCompact K := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hK₀
  have hcenter : ∀ᶠ n in atTop, G.flow.scalar (τ n) (x n).val ≤ |rmax| + 2 := by
    filter_upwards [hτ.eventually (L.eventually_scalar_close_on_compact hB one_pos)] with n hn
    have h := abs_lt.mp (hn (x n) (hxB n))
    change -1 < G.flow.scalar (τ n) (x n).val - metricScalarAt L.metric (x n) ∧
      G.flow.scalar (τ n) (x n).val - metricScalarAt L.metric (x n) < 1 at h
    linarith [hBscalar (x n) (hxB n), le_abs_self rmax]
  have hfac : 1 ≤ 1 + 4323 * eps := by linarith
  refine ⟨K, hK, v, neck, hmap, hv, ?_⟩
  filter_upwards [hτ.eventually (Ioo_mem_nhdsLT hd.2), hcenter] with n hn hR
  have hdom : ∀ y ∈ (W n).domain.carrier,
      G.flow.scalar (τ n) y ≤ C2 * (|rmax| + 2) := fun y hy =>
    (W n).scalar_bounds y hy |>.2.trans (mul_le_mul_of_nonneg_left hR hC2)
  have hCB : C2 * (|rmax| + 2) ≤ Bd :=
    le_mul_of_one_le_left (by positivity) hfac
  rw [himage]
  rintro y (hy | hy)
  · exact hcapture (τ n) hn y ((hdom y hy).trans hCB)
  · apply hcapture (τ n) hn
    have hs := ((neck n).scalar_bounds_on_image_window hy).2
    exact hs.trans (mul_le_mul_of_nonneg_left (hdom (v n) (hvW n)) (by positivity))

theorem TerminalLimitMetric.eventually_normalizedNeck_of_moving_spatial_caps
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B) {rmin rmax : ℝ} (hrmin : 0 < rmin)
    (hBscalar : ∀ y ∈ B, rmin ≤ metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ rmax)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B)
    {epsCanonical eps δ C1 C2 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 (x n).val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical (x n).val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) (x n).val) ≤
        metricDistance (G.flow.base.metric (τ n)) (x n).val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen)
      (nk : SpatialNeck (G.flow.base.metric (τ n)) eps v.val),
      (∀ z, (cap n).tubeMap z = nk.map z) ∧ v.val ∈ (cap n).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
  classical
  obtain ⟨K, hK, v, neck, hmap, hv, hcapture⟩ :=
    L.eventually_moving_spatial_cap_neck_compact_capture hτ hB (fun y hy => (hBscalar y hy).2)
      x hxB W hW cap depth hcap
  have hvW (n : ℕ) : v n ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr (hv n)
  have hC2 : 0 < C2 := zero_lt_one.trans_le (W 0).one_le_comparison_constant
  let qmin := rmin / (2 * C2)
  let qmax := C2 * (rmax + 1)
  have hqmin : 0 < qmin := by dsimp only [qmin]; positivity
  have hrange : ∀ᶠ n in atTop, qmin ≤ G.flow.scalar (τ n) (v n) ∧
      G.flow.scalar (τ n) (v n) ≤ qmax := by
    filter_upwards [hτ.eventually (L.eventually_moving_scalar_range_on_spatial_domains
      hB hrmin hBscalar (C1 := C1) (C2 := C2) (eps := epsCanonical))] with n hn
    exact hn (x n) (hxB n) (W n) (v n) (hvW n)
  have hclose := hτ.eventually (L.eventually_scalar_close_on_compact hK (half_pos hqmin))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hcapture.and (hrange.and hclose))
  have hsub (n : ℕ) := (hn₀ (n + n₀) (by omega)).1
  have hregv (n : ℕ) : v (n + n₀) ∈ G.terminalRegularRegion := by
    obtain ⟨y, hy, he⟩ := hsub n (Or.inl (hvW (n + n₀)))
    exact he ▸ y.property
  let v' : ℕ → G.terminalRegularOpen := fun n => ⟨v (n + n₀), hregv n⟩
  have hvK (n : ℕ) : v' n ∈ K := by
    obtain ⟨y, hy, he⟩ := hsub n (Or.inl (hvW (n + n₀)))
    have he' : y = v' n := Subtype.ext he
    exact he' ▸ hy
  have hpositive (n : ℕ) : 0 < metricScalarAt L.metric (v' n) := by
    have hr := (hn₀ (n + n₀) (by omega)).2.1.1
    have he := abs_lt.mp ((hn₀ (n + n₀) (by omega)).2.2 (v' n) (hvK n))
    change qmin ≤ metricScalarAt (G.flow.base.metric (τ (n + n₀))) (v' n).val at hr
    linarith [he.2]
  have hwindow (n : ℕ) (z : neckBuffer δ) :
      (neck (n + n₀)).map z.val ∈ Subtype.val '' K := by
    apply hsub n
    right
    refine ⟨z.val, ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · have hz := z.property.1
      change -δ⁻¹ - 1 < z.val.2 at hz
      linarith
    · have hz := z.property.2
      change z.val.2 < δ⁻¹ + 1 at hz
      linarith
  have hregular (n : ℕ) (z : neckBuffer δ) :
      (neck (n + n₀)).map z.val ∈ G.terminalRegularRegion := by
    obtain ⟨y, hy, he⟩ := hwindow n z
    exact he ▸ y.property
  have hout := L.eventually_normalizedNeck_of_moving_spatialNecks
    (hτ.comp (tendsto_add_atTop_nat n₀)) v' hpositive hδ hδ1 hepsδ hfit k hk
    (fun n => neck (n + n₀)) hregular hK
    (Eventually.of_forall fun n z _ => hwindow n z) hqmin
    (Eventually.of_forall fun n => (hn₀ (n + n₀) (by omega)).2.1)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hout
  apply eventually_atTop.mpr
  refine ⟨n₀ + n₁, ?_⟩
  intro n hn
  have heq : n - n₀ + n₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨N, hNv, hNmark, hNmap⟩ := hn₁ (n - n₀) (by omega)
  have hresult : ∃ (v : G.terminalRegularOpen)
      (nk : SpatialNeck (G.flow.base.metric (τ (n - n₀ + n₀))) eps v.val),
      (∀ z, (cap (n - n₀ + n₀)).tubeMap z = nk.map z) ∧
      v.val ∈ (cap (n - n₀ + n₀)).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
    exact ⟨v' (n - n₀), neck (n - n₀ + n₀), hmap (n - n₀ + n₀),
      hv (n - n₀ + n₀), N, hNv, hNmark, hNmap⟩
  exact heq ▸ hresult

theorem TerminalLimitMetric.eventually_moving_scalar_bounds_on_spatial_domains
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B) {rmin : ℝ} (hrmin : 0 < rmin)
    (hBscalar : ∀ y ∈ B, rmin ≤ metricScalarAt L.metric y)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B) {eps C1 C2 : ℝ}
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) eps C1 C2 (x n).val)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, (W n).domain.carrier ⊆ Subtype.val '' K) :
    ∀ᶠ n in atTop, ∀ y : G.terminalRegularOpen, y.val ∈ (W n).domain.carrier →
      3 * metricScalarAt L.metric (x n) / (4 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 3 * C2 * metricScalarAt L.metric (x n) / 2 := by
  have hC2 : 1 ≤ C2 := (W 0).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hcenter := hτ.eventually (L.eventually_scalar_close_on_compact hB
    (div_pos hrmin (by norm_num : (0 : ℝ) < 8)))
  have hclose := hτ.eventually (L.eventually_scalar_close_on_compact hK
    (div_pos hrmin (by positivity : 0 < 8 * C2)))
  filter_upwards [hcapture, hcenter, hclose] with n hn hc he
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hn hy
  have hyK : y ∈ K := (Subtype.ext hzy : z = y) ▸ hz
  have hx := hrmin.trans_le (hBscalar (x n) (hxB n))
  have hr8 : rmin / 8 ≤ metricScalarAt L.metric (x n) / 8 := by
    linarith [hBscalar (x n) (hxB n)]
  have hr8C : rmin / (8 * C2) ≤ metricScalarAt L.metric (x n) / (8 * C2) :=
    div_le_div_of_nonneg_right (hBscalar (x n) (hxB n)) (by positivity)
  have hxc := abs_lt.mp ((hc (x n) (hxB n)).trans_le hr8)
  have hyc := abs_lt.mp ((he y hyK).trans_le hr8C)
  change -(metricScalarAt L.metric (x n) / 8) <
      G.flow.scalar (τ n) (x n).val - metricScalarAt L.metric (x n) ∧
    G.flow.scalar (τ n) (x n).val - metricScalarAt L.metric (x n) <
      metricScalarAt L.metric (x n) / 8 at hxc
  change -(metricScalarAt L.metric (x n) / (8 * C2)) <
      G.flow.scalar (τ n) y.val - metricScalarAt L.metric y ∧
    G.flow.scalar (τ n) y.val - metricScalarAt L.metric y <
      metricScalarAt L.metric (x n) / (8 * C2) at hyc
  have hs : C2⁻¹ * G.flow.scalar (τ n) (x n).val ≤ G.flow.scalar (τ n) y.val ∧
      G.flow.scalar (τ n) y.val ≤ C2 * G.flow.scalar (τ n) (x n).val :=
    (W n).scalar_bounds y.val hy
  have hslo : G.flow.scalar (τ n) (x n).val ≤ C2 * G.flow.scalar (τ n) y.val := by
    have hm := mul_le_mul_of_nonneg_left hs.1 hC2pos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul] using hm
  have herr : metricScalarAt L.metric (x n) / (8 * C2) ≤ metricScalarAt L.metric (x n) / 8 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * C2)).mpr
    have hm := mul_lt_mul_of_pos_left hyc.2 hC2pos
    have heq : C2 * (metricScalarAt L.metric (x n) / (8 * C2)) =
        metricScalarAt L.metric (x n) / 8 := by
      field_simp
    rw [heq] at hm
    nlinarith [hxc.1]
  · have hm := mul_lt_mul_of_pos_left hxc.2 hC2pos
    nlinarith [hs.2, hyc.1, hx, hC2]

theorem TerminalLimitMetric.eventually_moving_spatial_cap_midpoint_region
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B) {rmin rmax : ℝ} (hrmin : 0 < rmin)
    (hBscalar : ∀ y ∈ B, rmin ≤ metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ rmax)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (h2k : 2 ≤ k)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 (x n).val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical (x n).val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) (x n).val) ≤
        metricDistance (G.flow.base.metric (τ n)) (x n).val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (N : NormalizedNeck L.metric δ k)
      (K : CompactDomain G.terminalRegularOpen) (e : Sphere 2 → G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x n ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier,
        metricScalarAt L.metric (x n) / (2 * C2) < metricScalarAt L.metric y ∧
          metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric (x n)) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        metricScalarAt L.metric (x n) / (2 * C2) < metricScalarAt L.metric (N.chart z) ∧
          metricScalarAt L.metric (N.chart z) < 2 * C2 * metricScalarAt L.metric (x n)) ∧
      frontier K.carrier = range e ∧ IsSmoothEmbedding I2 I3 ∞ e ∧
      (∀ q, (e q).val = (cap n).tubeMap (q, 1 / 2)) ∧
      (∀ q (hq : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ), e q = N.chart ⟨(q, 1 / 2), hq⟩) ∧
      N.cylindricalChart.metricCloseOn L.metric δ
        {z : N.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ N.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 e,
        c.radius < 1 / 4 ∧
        ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
          (∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
            c.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩) ∧
          (c.toFun q).val = (cap n).tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  obtain ⟨K₀, hK₀, v, neck, _, _, hcapture⟩ :=
    L.eventually_moving_spatial_cap_neck_compact_capture hτ hB (fun y hy => (hBscalar y hy).2)
      x hxB W hW cap depth hcap
  have hnorm := L.eventually_normalizedNeck_of_moving_spatial_caps hτ hB hrmin hBscalar x hxB
    hδ (by linarith) hepsδ hfit k hk W hW cap depth hcap
  have hbound := L.eventually_moving_scalar_bounds_on_spatial_domains hτ hB hrmin
    (fun y hy => (hBscalar y hy).1) x hxB W hK₀
    (hcapture.mono fun n hn => subset_union_left.trans hn)
  filter_upwards [hcapture, hnorm, hbound] with n hcn hnn hbn
  obtain ⟨vn, nk, hmap, hvn, N, hNv, _, hNmap⟩ := hnn
  have hU : (W n).domain.carrier ⊆ G.terminalRegularRegion := by
    intro y hy
    obtain ⟨z, _, he⟩ := hcn (Or.inl hy)
    exact he ▸ z.property
  have hNcap : ∀ z : neckBuffer δ, (N.chart z).val = (cap n).tubeMap z.val :=
    fun z => (hNmap z).trans (hmap z.val).symm
  obtain ⟨K, e, hK, hxK, hKU, hfront, hemb, heold, heN, hscalar, hmetric, hdomain, hc⟩ :=
    L.exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap
      (cap n) hU N (by linarith) h2k hNcap
  have hC2 : 1 ≤ C2 := (W n).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hx : 0 < metricScalarAt L.metric (x n) := hrmin.trans_le (hBscalar (x n) (hxB n)).1
  have hvU : vn.val ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr hvn
  have hNscale : 3 * metricScalarAt L.metric (x n) / (4 * C2) < N.scale ∧
      N.scale < 3 * C2 * metricScalarAt L.metric (x n) / 2 := by
    rw [N.scale_scalar, hNv]
    exact hbn vn hvU
  have hlo : metricScalarAt L.metric (x n) / (2 * C2) <
      3 * metricScalarAt L.metric (x n) / (4 * C2) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * C2) (by positivity : 0 < 4 * C2)).mpr
    nlinarith
  have hhi : 3 * C2 * metricScalarAt L.metric (x n) / 2 <
      2 * C2 * metricScalarAt L.metric (x n) := by nlinarith [mul_pos hC2pos hx]
  refine ⟨N, K, e, hK, hxK, hKU, ?_, ?_, hfront, hemb, heold, heN, hmetric, hdomain, hc⟩
  · intro y hy
    exact ⟨hlo.trans (hbn y (hKU hy)).1, (hbn y (hKU hy)).2.trans hhi⟩
  · intro z hz
    have hs := abs_le.mp (hscalar z hz)
    have hQ := N.scale_pos
    have hsl : (1 - 4323 * δ) * N.scale ≤ metricScalarAt L.metric (N.chart z) := by
      apply (le_div_iff₀ hQ).mp
      linarith [hs.1]
    have hsu : metricScalarAt L.metric (N.chart z) ≤ (1 + 4323 * δ) * N.scale := by
      apply (div_le_iff₀ hQ).mp
      linarith [hs.2]
    have hthree : (3 / 4 : ℝ) * N.scale < metricScalarAt L.metric (N.chart z) := by
      nlinarith
    have hfive : metricScalarAt L.metric (N.chart z) < (5 / 4 : ℝ) * N.scale := by
      nlinarith
    constructor
    · have hlo' := (div_lt_iff₀ (by positivity : 0 < 4 * C2)).mp hNscale.1
      apply (div_lt_iff₀ (by positivity : 0 < 2 * C2)).mpr
      have hm := mul_lt_mul_of_pos_right hthree hC2pos
      nlinarith
    · nlinarith [hNscale.2]

theorem TerminalLimitMetric.eventually_moving_spatial_cap_spherical_barrier
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B)
    (hBpos : ∀ y ∈ B, 0 < metricScalarAt L.metric y)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 (x n).val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, SpatialLocalCap (G.flow.base.metric (τ n)) epsCanonical (x n).val
      (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) (x n).val) ≤
        metricDistance (G.flow.base.metric (τ n)) (x n).val y)
    (hcap : ∀ n, (W n).alternative = SpatialCanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v)
      (K : CompactDomain G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x n ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier,
        metricScalarAt L.metric (x n) / (2 * C2) < metricScalarAt L.metric y ∧
          metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric (x n)) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        metricScalarAt L.metric (x n) / (2 * C2) < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) < 2 * C2 * metricScalarAt L.metric (x n)) ∧
      frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
        c.radius < 1 / 4 ∧ ∀ q,
          c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have hcont : Continuous (metricScalarAt L.metric) := (metricScalar_smooth L.metric).continuous
  obtain ⟨rmin, rmax, hrmin, hBscalar⟩ : ∃ rmin rmax : ℝ, 0 < rmin ∧
      ∀ y ∈ B, rmin ≤ metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ rmax := by
    rcases B.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, 0, one_pos, fun y hy => by simp [hemp] at hy⟩
    obtain ⟨ymin, hymin, hmin⟩ := hB.exists_isMinOn hne hcont.continuousOn
    obtain ⟨ymax, -, hmax⟩ := hB.exists_isMaxOn hne hcont.continuousOn
    exact ⟨metricScalarAt L.metric ymin, metricScalarAt L.metric ymax, hBpos ymin hymin,
      fun y hy => ⟨hmin hy, hmax hy⟩⟩
  have heps : 0 < eps := by
    obtain ⟨v, nk, _⟩ := hW 0 (cap 0) (depth 0) (hcap 0)
    exact nk.eps_pos
  have hδ11 : δ < 1 / 11 := hδsmall.trans (by norm_num)
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ heps hepsδ.le)
  have hlen : (101 : ℝ) < δ⁻¹ :=
    (lt_inv_comm₀ (by norm_num) hδ).mpr (by linarith)
  have h2k : 2 ≤ ⌈δ⁻¹⌉₊ := by
    exact_mod_cast (show (2 : ℝ) ≤ δ⁻¹ by linarith).trans (Nat.le_ceil δ⁻¹)
  have hevent := L.eventually_moving_spatial_cap_midpoint_region hτ hB hrmin hBscalar x hxB
    hδ hδsmall hepsδ hfit ⌈δ⁻¹⌉₊ hk h2k W hW cap depth hcap
  filter_upwards [hevent] with n hn
  obtain ⟨N, K, e, hK, hxK, hKU, hscalarK, hscalarN, hfront, hemb, heold, heN,
    hmetricN, hdomainN, c, hc, hcmap⟩ := hn
  obtain ⟨nk, hmark, hmap⟩ := N.exists_spatialNeck le_rfl hδ11 le_rfl
  have heq : e = (fun q : Sphere 2 => nk.map (q, 1 / 2)) := by
    funext q
    have hz : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ := by constructor <;> linarith
    exact (heN q hz).trans (hmap ⟨(q, 1 / 2), hz⟩).symm
  subst e
  refine ⟨N.center, nk, K, hK, hxK, hKU, hscalarK, ?_, hfront, hemb, ?_, ?_, c, hc, ?_⟩
  · intro z hz
    have hz' : z ∈ neckBuffer δ := by constructor <;> linarith [hz.2.1, hz.2.2]
    rw [hmap ⟨z, hz'⟩]
    exact hscalarN ⟨z, hz'⟩ hz.2
  · intro z _ j hj
    exact nk.cylindricalChart_metricCloseOn z (mem_univ _) j hj
  · intro q z hz
    exact ⟨mem_univ _, by linarith [hz.1], by linarith [hz.2]⟩
  · intro q
    obtain ⟨⟨hz, hqc⟩, _, hmem⟩ := hcmap q
    exact ⟨hqc.trans (hmap ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩).symm, hmem⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
