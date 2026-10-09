import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapTruncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}


theorem TerminalLimitMetric.eventually_scalar_bounds_on_canonical_domains
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Filter.Tendsto τ Filter.atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps C1 C2 : ℝ} (W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n))
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in Filter.atTop, (W n).domain.carrier ⊆ Subtype.val '' K) :
    ∀ᶠ n in Filter.atTop, ∀ y : G.terminalRegularOpen, y.val ∈ (W n).domain.carrier →
      3 * metricScalarAt L.metric x / (4 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 3 * C2 * metricScalarAt L.metric x / 2 := by
  have hC2 : 1 ≤ C2 := (W 0).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hcenter := hτ.eventually (L.eventually_scalar_close_on_compact
    (K := {x}) isCompact_singleton (div_pos hx (by norm_num : (0 : ℝ) < 8)))
  have hclose := hτ.eventually (L.eventually_scalar_close_on_compact hK
    (div_pos hx (by positivity : 0 < 8 * C2)))
  filter_upwards [hcapture, hcenter, hclose] with n hn hc he
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hn hy
  have hyK : y ∈ K := (Subtype.ext hzy : z = y) ▸ hz
  have hxc := abs_lt.mp (hc x (mem_singleton x))
  have hyc := abs_lt.mp (he y hyK)
  change -(metricScalarAt L.metric x / 8) < G.flow.scalar (τ n) x.val - metricScalarAt L.metric x ∧
    G.flow.scalar (τ n) x.val - metricScalarAt L.metric x < metricScalarAt L.metric x / 8 at hxc
  change -(metricScalarAt L.metric x / (8 * C2)) < G.flow.scalar (τ n) y.val - metricScalarAt L.metric y ∧
    G.flow.scalar (τ n) y.val - metricScalarAt L.metric y < metricScalarAt L.metric x / (8 * C2) at hyc
  have hs := (W n).scalar_bounds y.val hy
  have hslo : G.flow.scalar (τ n) x.val ≤ C2 * G.flow.scalar (τ n) y.val := by
    have hm := mul_le_mul_of_nonneg_left hs.1 hC2pos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul] using hm
  have herr : metricScalarAt L.metric x / (8 * C2) ≤ metricScalarAt L.metric x / 8 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 4 * C2)).mpr
    have hm := mul_lt_mul_of_pos_left hyc.2 hC2pos
    have heq : C2 * (metricScalarAt L.metric x / (8 * C2)) = metricScalarAt L.metric x / 8 := by field_simp
    rw [heq] at hm
    nlinarith [hxc.1]
  · have hm := mul_lt_mul_of_pos_left hxc.2 hC2pos
    nlinarith [hs.2, hyc.1, hx, hC2]

set_option backward.isDefEq.respectTransparency false in
theorem TerminalLimitMetric.exists_cap_midpoint_region_of_normalizedNeck
    (L : G.TerminalLimitMetric) {eps t : ℝ} {x : G.terminalRegularOpen} {U : Set P.Carrier}
    (cap : LocalCap G.flow eps x.val t U) (hU : U ⊆ G.terminalRegularRegion)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hδ : δ < 1 / 102) (hk : 2 ≤ k)
    (hmap : ∀ z : neckBuffer δ, (N.chart z).val = cap.tubeMap z.val) :
    ∃ (K : CompactDomain G.terminalRegularOpen) (e : Sphere 2 → G.terminalRegularOpen),
      Subtype.val '' K.carrier = cap.core.carrier ∪
        cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' U ∧
      frontier K.carrier = range e ∧ IsSmoothEmbedding I2 I3 ∞ e ∧
      (∀ q, (e q).val = cap.tubeMap (q, 1 / 2)) ∧
      (∀ q (hq : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ), e q = N.chart ⟨(q, 1 / 2), hq⟩) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        |metricScalarAt L.metric (N.chart z) / N.scale - 1| ≤ 4323 * δ) ∧
      N.cylindricalChart.metricCloseOn L.metric δ
        {z : N.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ N.cylindricalChart.domain) ∧
      ∃ c : SmoothTwoSidedCollar I2 I3 e,
        c.radius < 1 / 4 ∧
        ∀ q : Sphere 2 × symmetricOpenInterval c.radius,
          (∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
            c.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩) ∧
          (c.toFun q).val = cap.tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have hlen : (102 : ℝ) < δ⁻¹ :=
    (lt_inv_comm₀ (by norm_num) N.delta_pos).mpr (by simpa only [one_div] using hδ)
  have hmid (q : Sphere 2) : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ := by
    constructor <;> linarith
  let e : Sphere 2 → G.terminalRegularOpen := fun q =>
    (N.cylindricalChart.chart ⟨(q, 1 / 2), hmid q⟩ : G.terminalRegularOpen)
  have he (q : Sphere 2) : (e q).val = cap.tubeMap (q, 1 / 2) :=
    (congrArg Subtype.val (N.cylindricalChart_chart_apply _)).trans (hmap _)
  obtain ⟨K₀, hK₀, hx₀, hK₀U, hfront₀⟩ :=
    cap.exists_truncated_compactDomain (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  let K := K₀.restrictOpen G.terminalRegularOpen (hK₀U.trans hU)
  have hK : Subtype.val '' K.carrier = cap.core.carrier ∪
      cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) :=
    (K₀.image_restrictOpen_carrier _ _).trans hK₀
  have hxK : x ∈ interior K.carrier := by
    change x ∈ interior (K₀.restrictOpen G.terminalRegularOpen _).carrier
    rw [K₀.interior_restrictOpen_carrier]
    exact hx₀
  have hKU : K.carrier ⊆ Subtype.val ⁻¹' U := fun y hy => hK₀U hy
  have hfront : frontier K.carrier = range e := by
    change frontier (K₀.restrictOpen G.terminalRegularOpen _).carrier = range e
    rw [K₀.frontier_restrictOpen_carrier, hfront₀]
    ext y
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext ((he q).trans hq)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, (he q).symm⟩
  have hgraph : ∀ q : Sphere 2, (q, (1 / 2 : ℝ)) ∈ N.cylindricalChart.domain := hmid
  obtain ⟨c, hc, _, hcoord⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    N.cylindricalChart.domain N.cylindricalChart.target N.cylindricalChart.chart
    (fun _ => (1 / 2 : ℝ)) contMDiff_const hgraph (by norm_num : (0 : ℝ) < 1 / 4)
  let c' : SmoothTwoSidedCollar I2 I3 e := c
  have hcoord' (q : Sphere 2 × symmetricOpenInterval c'.radius) :
      ∃ hz : (q.1, 1 / 2 + (q.2 : ℝ)) ∈ neckBuffer δ,
        c'.toFun q = N.chart ⟨(q.1, 1 / 2 + (q.2 : ℝ)), hz⟩ := by
    obtain ⟨hz, heq⟩ := hcoord q
    exact ⟨hz, heq.trans (N.cylindricalChart_chart_apply _)⟩
  have hEsmooth : IsSmoothEmbedding I2 I3 ∞ e := by
    let f : Sphere 2 → neckBuffer δ := fun q => ⟨(q, 1 / 2), hmid q⟩
    have hf : IsSmoothEmbedding I2 NeckCylinderModel ∞ f := by
      have hfcont : ContMDiff I2 NeckCylinderModel ∞ f :=
        (ContMDiff.subtypeVal_comp_iff (neckBuffer δ) _).mp
          (contMDiff_id.prodMk contMDiff_const)
      have hfst : ContMDiff NeckCylinderModel I2 ∞
          (fun z : neckBuffer δ => z.val.1) := contMDiff_fst.comp contMDiff_subtype_val
      exact (IsSmoothEmbedding.id : IsSmoothEmbedding I2 I2 ∞
        ((fun z : neckBuffer δ => z.val.1) ∘ f)).of_comp
          (J := NeckCylinderModel) (by simp) hfcont hfst
    have hE : e = N.chart ∘ f := funext fun q => N.cylindricalChart_chart_apply _
    rw [hE]
    exact N.chart_smooth.comp hf (by simp)
  refine ⟨K, e, hK, hxK, hKU, hfront, hEsmooth, he, ?_, ?_, ?_, ?_, c', hc, ?_⟩
  · intro q hq
    exact N.cylindricalChart_chart_apply _
  · intro z hz
    have hztest : z ∈ neckClosedTest δ := by
      change -δ⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ δ⁻¹
      constructor <;> linarith [hz.1, hz.2]
    have hy : N.chart z ∈ N.cylindricalChart.region (neckClosedTest δ) := by
      refine ⟨N.cylindricalChart.chart z, ⟨z, hztest, rfl⟩, ?_⟩
      exact N.cylindricalChart_chart_apply z
    exact N.cylindricalChart.scalar_comparison_of_metricCloseOn L.metric δ
      (by linarith) (N.cylindricalChart_metricCloseOn hk) (N.chart z) hy
  · intro z hz j hj
    apply N.cylindricalChart_metricCloseOn hk z ?_ j hj
    change -δ⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ δ⁻¹
    constructor <;> linarith [hz.1, hz.2]
  · intro q z hz
    change -δ⁻¹ - 1 < z ∧ z < δ⁻¹ + 1
    constructor <;> linarith [hz.1, hz.2]
  · intro q
    obtain ⟨hz, hq⟩ := hcoord' q
    have hpoint : (c'.toFun q).val = cap.tubeMap (q.1, 1 / 2 + (q.2 : ℝ)) :=
      (congrArg Subtype.val hq).trans (hmap _)
    refine ⟨⟨hz, hq⟩, hpoint, ?_⟩
    change (c'.toFun q).val ∈ K₀.carrier ↔ _
    rw [hpoint, hK₀]
    have hs : 1 / 2 + (q.2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      have hc' : c'.radius < 1 / 4 := hc
      constructor <;> linarith [q.2.property.1, q.2.property.2]
    rw [cap.mem_truncated_core_on_tube (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) q.1 hs]
    constructor <;> intro h <;> linarith

set_option backward.isDefEq.respectTransparency false in
theorem TerminalLimitMetric.eventually_cap_midpoint_region
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Filter.Tendsto τ Filter.atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (h2k : 2 ≤ k)
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤ metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in Filter.atTop, ∃ (N : NormalizedNeck L.metric δ k)
      (K : CompactDomain G.terminalRegularOpen) (e : Sphere 2 → G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier, metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric x) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric (N.chart z) ∧
          metricScalarAt L.metric (N.chart z) < 2 * C2 * metricScalarAt L.metric x) ∧
      frontier K.carrier = range e ∧ IsSmoothEmbedding I2 I3 ∞ e ∧
      (∀ q, (e q).val = (cap n).tubeMap (q, 1 / 2)) ∧
      (∀ q (hq : (q, (1 / 2 : ℝ)) ∈ neckBuffer δ), e q = N.chart ⟨(q, 1 / 2), hq⟩) ∧
      (∀ z : neckBuffer δ, z.val.2 ∈ Icc (-101 : ℝ) 101 →
        |metricScalarAt L.metric (N.chart z) / N.scale - 1| ≤ 4323 * δ) ∧
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
    L.eventually_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hnorm := L.eventually_normalizedNeck_of_canonical_caps hτ x hx
    hδ (by linarith) hepsδ hfit k hk W hW cap depth hcap
  have hbound := L.eventually_scalar_bounds_on_canonical_domains hτ x hx W hK₀
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
    L.exists_cap_midpoint_region_of_normalizedNeck
      (cap n) hU N (by linarith) h2k hNcap
  have hC2 : 1 ≤ C2 := (W n).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hvU : vn.val ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr hvn
  have hNscale : 3 * metricScalarAt L.metric x / (4 * C2) < N.scale ∧
      N.scale < 3 * C2 * metricScalarAt L.metric x / 2 := by
    rw [N.scale_scalar, hNv]
    exact hbn vn hvU
  have hlo : metricScalarAt L.metric x / (2 * C2) <
      3 * metricScalarAt L.metric x / (4 * C2) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * C2) (by positivity : 0 < 4 * C2)).mpr
    nlinarith
  have hhi : 3 * C2 * metricScalarAt L.metric x / 2 <
      2 * C2 * metricScalarAt L.metric x := by nlinarith [mul_pos hC2pos hx]
  refine ⟨N, K, e, hK, hxK, hKU, ?_, ?_, hfront, hemb, heold, heN,
    hscalar, hmetric, hdomain, hc⟩
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
