import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalNeckNormalization

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_scalar_range_on_canonical_domains
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hx : 0 < metricScalarAt L.metric x) {C1 C2 eps : ℝ} :
    ∀ᶠ t in 𝓝[<] s, ∀ W : CanonicalWitness G.flow eps C1 C2 x.val t,
      ∀ v ∈ W.domain.carrier,
        metricScalarAt L.metric x / (2 * C2) ≤ G.flow.scalar t v ∧
          G.flow.scalar t v ≤ C2 * (metricScalarAt L.metric x + 1) := by
  have hlow := (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds (half_lt_self hx))
  have hhigh := (L.tendsto_metricScalarAt x).eventually_lt_const (lt_add_one _)
  filter_upwards [hlow, hhigh] with t htlo hthi
  intro W v hv
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hs := W.scalar_bounds v hv
  constructor
  · have hmul := mul_le_mul_of_nonneg_left htlo.le (inv_pos.mpr hC2).le
    have heq : C2⁻¹ * (metricScalarAt L.metric x / 2) =
        metricScalarAt L.metric x / (2 * C2) := by field_simp
    rw [heq] at hmul
    exact hmul.trans hs.1
  · exact hs.2.trans (mul_le_mul_of_nonneg_left hthi.le hC2.le)


theorem TerminalLimitMetric.eventually_cap_neck_compact_capture
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen)
    {epsCanonical eps C1 C2 : ℝ}
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤ metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ (v : ℕ → P.Carrier) (neck : ∀ n, StrongNeck G.flow eps (v n) (τ n)),
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
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨D1, D2, q, hD1, hD2, hq, hc⟩ := hm epsCan hepsCan le_rfl
  let C : ℝ≥0 := ⟨D2, zero_le_one.trans hD2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    exact (hc y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨K, hK, d, hd, hcapture⟩ :=
    L.exists_compact_containing_canonical_domains_and_neck_windows
      hq hbound hPhi hpinch x (epsCanonical := epsCanonical) (C1 := C1)
      (neck 0).eps_pos.le (zero_le_one.trans (W 0).one_le_comparison_constant)
  refine ⟨K, hK, v, neck, hmap, hv, ?_⟩
  filter_upwards [hτ.eventually (Ioo_mem_nhdsLT hd.2)] with n hn
  exact union_subset (hcapture (τ n) hn (W n)).1
    ((hcapture (τ n) hn (W n)).2 (v n) (hvW n) (neck n))

theorem TerminalLimitMetric.eventually_normalizedNeck_of_canonical_caps
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤ metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen)
      (nk : StrongNeck G.flow eps v.val (τ n)),
      (∀ z, (cap n).tubeMap z = nk.map z) ∧ v.val ∈ (cap n).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
  classical
  obtain ⟨K, hK, v, neck, hmap, hv, hcapture⟩ :=
    L.eventually_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hvW (n : ℕ) : v n ∈ (W n).domain.carrier := (cap n).union_eq.symm ▸ Or.inr (hv n)
  have hC2 : 0 < C2 := zero_lt_one.trans_le (W 0).one_le_comparison_constant
  let qmin := metricScalarAt L.metric x / (2 * C2)
  let qmax := C2 * (metricScalarAt L.metric x + 1)
  have hqmin : 0 < qmin := by dsimp only [qmin]; positivity
  have hrange : ∀ᶠ n in atTop, qmin ≤ G.flow.scalar (τ n) (v n) ∧
      G.flow.scalar (τ n) (v n) ≤ qmax := by
    filter_upwards [hτ.eventually (L.eventually_scalar_range_on_canonical_domains
      x hx (C1 := C1) (C2 := C2) (eps := epsCanonical))] with n hn
    exact hn (W n) (v n) (hvW n)
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
  have hout := L.eventually_normalizedNeck_of_moving_strongNecks
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
      (nk : StrongNeck G.flow eps v.val (τ (n - n₀ + n₀))),
      (∀ z, (cap (n - n₀ + n₀)).tubeMap z = nk.map z) ∧
      v.val ∈ (cap (n - n₀ + n₀)).tube ∧
      ∃ N : NormalizedNeck L.metric δ k,
        N.center = v ∧ N.sphereMark = nk.center ∧
          ∀ z, (N.chart z).val = nk.map z.val := by
    exact ⟨v' (n - n₀), neck (n - n₀ + n₀), hmap (n - n₀ + n₀),
      hv (n - n₀ + n₀), N, hNv, hNmark, hNmap⟩
  exact heq ▸ hresult

theorem TerminalLimitMetric.eventually_normalizedNeck_of_moving_spatialNecks_of_scalar_comparison
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {Cscalar : ℝ} (hCscalar : 0 < Cscalar)
    (U : ℕ → Set P.Carrier) (v : ℕ → P.Carrier) (hv : ∀ᶠ n in atTop, v n ∈ U n)
    (hU : ∀ᶠ n in atTop, ∀ y ∈ U n,
      Cscalar⁻¹ * G.flow.scalar (τ n) x.val ≤ G.flow.scalar (τ n) y ∧
        G.flow.scalar (τ n) y ≤ Cscalar * G.flow.scalar (τ n) x.val)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps (v n)) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center.val = v n ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).val = (neck n).map z.val := by
  let qmin := metricScalarAt L.metric x / (2 * Cscalar)
  let qmax := Cscalar * (metricScalarAt L.metric x + 1)
  have hqmin : 0 < qmin := by dsimp only [qmin]; positivity
  have hscale : Tendsto (fun n => G.flow.scalar (τ n) x.val) atTop
      (𝓝 (metricScalarAt L.metric x)) := (L.tendsto_metricScalarAt x).comp hτ
  have hlow := hscale.eventually (Ioi_mem_nhds (half_lt_self hx))
  have hhigh := hscale.eventually_lt_const (lt_add_one _)
  have hrange : ∀ᶠ n in atTop, qmin ≤ G.flow.scalar (τ n) (v n) ∧
      G.flow.scalar (τ n) (v n) ≤ qmax := by
    filter_upwards [hU,hv,hlow,hhigh] with n hn hvn hlo hhi
    have hcomp := hn (v n) hvn
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hlo.le (inv_pos.mpr hCscalar).le
      have heq : Cscalar⁻¹ * (metricScalarAt L.metric x / 2) = qmin := by
        dsimp only [qmin]
        field_simp
      rw [heq] at hmul
      exact hmul.trans hcomp.1
    · exact hcomp.2.trans (mul_le_mul_of_nonneg_left hhi.le hCscalar.le)
  exact L.eventually_normalizedNeck_of_moving_spatialNecks_of_scalar_control
    hτ hq hbound v hδ hδ1 hepsδ hfit k hk neck hqmin hrange

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
