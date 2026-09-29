import DifferentialGeometry.Geometry.Neck.SpatialMinimizer
import DifferentialGeometry.Geometry.Metric.Comparison.BoundaryDetour
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Neck.SphericalBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalAlternatives

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_normalizedNeck_of_incoming_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, StrongNeck G.flow eps x.val (τ n)) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center = x ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).val = (neck n).map z.val := by
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨C1, C2, q, _, hC2, hq, hc⟩ := hm epsCan hepsCan le_rfl
  have hcanonical : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      Nonempty (CanonicalWitness G.flow epsCan C1 C2 y t) :=
    fun y t ht hy => hc y t ⟨ht.1.le, ht.2⟩ hy.le
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  exact L.eventually_normalizedNeck_of_canonical_neighborhoods hτ hq hcanonical hPhi hpinch
    x hx hδ hδ1 hepsδ hfit k hk neck

theorem TerminalLimitMetric.eventually_spatialNeck_of_incoming_spatialNecks_of_scalar_derivative_bound
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {q0 : ℝ} {Ctime : ℝ≥0} (hq0 : 0 < q0)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 11) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps x.val) :
    ∀ᶠ n in atTop, ∃ nk : SpatialNeck L.metric δ x,
      nk.center = (neck n).center ∧
        ∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val := by
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ (neck 0).eps_pos hepsδ.le)
  have hevent := L.eventually_normalizedNeck_of_spatialNecks_of_scalar_control
    hτ hq0 hbound x hx hδ
    (hδsmall.trans (by norm_num)) hepsδ hfit ⌈δ⁻¹⌉₊ hk neck
  filter_upwards [hevent] with n hn
  obtain ⟨N, hN, hmark, hmap⟩ := hn
  obtain ⟨nk, hnkmark, hnkmap⟩ := N.exists_spatialNeck le_rfl hδsmall le_rfl
  let nk' : SpatialNeck L.metric δ x := hN ▸ nk
  have hcenter : nk'.center = (neck n).center := by
    cases hN
    exact hnkmark.trans hmark
  have hvalues : ∀ z : neckBuffer δ, (nk'.map z.val).val = (neck n).map z.val := by
    cases hN
    intro z
    exact (congrArg Subtype.val (hnkmap z)).trans (hmap z)
  exact ⟨nk', hcenter, hvalues⟩

theorem TerminalLimitMetric.eventually_spatialNeck_of_incoming_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 11) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, StrongNeck G.flow eps x.val (τ n)) :
    ∀ᶠ n in atTop, ∃ nk : SpatialNeck L.metric δ x,
      nk.center = (neck n).center ∧
        ∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val := by
  obtain ⟨epsCan, hepsCan, hm⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨C1, C2, q0, _, hC2, hq0, hc⟩ := hm epsCan hepsCan le_rfl
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
        (⟨C2, zero_le_one.trans hC2⟩ : ℝ≥0) * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    exact (hc y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  exact L.eventually_spatialNeck_of_incoming_spatialNecks_of_scalar_derivative_bound hτ hq0 hbound x hx hδ
    hδsmall hepsδ hfit (fun n => (neck n).toSpatialNeck)

theorem TerminalLimitMetric.exists_neck_spherical_barrier_of_incoming_spatialNecks_of_scalar_derivative_bound
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {q0 : ℝ} {Ctime : ℝ≥0} (hq0 : 0 < q0)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2)
    (x : G.terminalRegularOpen) {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8646)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, SpatialNeck (G.flow.base.metric (τ n)) eps x.val)
    (A C2 : ℝ) (hA : 0 < A) (hC2 : 1 ≤ C2)
    (hscale : metricScalarAt L.metric x = 4 * C2 * A) :
    ∃ (n : ℕ) (nk : SpatialNeck L.metric δ x) (K : CompactDomain G.terminalRegularOpen),
      (∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val) ∧
      K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧ x ∈ interior K.carrier ∧
      frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, -3)) ∪
        range (fun y : Sphere 2 => nk.map (y, 3)) ∧
      Disjoint (range (fun y : Sphere 2 => nk.map (y, -3)))
        (range (fun y : Sphere 2 => nk.map (y, 3))) ∧
      (∀ t ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, t))) ∧
      (∀ y ∈ K.carrier, 2 * A < metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ 8 * C2 ^ 2 * A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ nk.cylindricalChart.domain) ∧
      ∃ (cneg : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, -3)))
        (cpos : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, 3))),
        cneg.radius < 1 ∧ cpos.radius < 1 ∧
        (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
          (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
        (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
          (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) := by
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  obtain ⟨n, nk, _, hmap⟩ :=
    (L.eventually_spatialNeck_of_incoming_spatialNecks_of_scalar_derivative_bound hτ hq0 hbound x hx hδ
      (hδsmall.trans (by norm_num)) hepsδ hfit neck).exists
  obtain ⟨K, hK⟩ := nk.exists_short_spherical_barrier hδsmall A C2 hA hC2 hscale
  exact ⟨n, nk, K, hmap, hK⟩

theorem TerminalLimitMetric.exists_neck_spherical_barrier_of_incoming_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8646)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, StrongNeck G.flow eps x.val (τ n))
    (A C2 : ℝ) (hA : 0 < A) (hC2 : 1 ≤ C2)
    (hscale : metricScalarAt L.metric x = 4 * C2 * A) :
    ∃ (n : ℕ) (nk : SpatialNeck L.metric δ x) (K : CompactDomain G.terminalRegularOpen),
      (∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val) ∧
      K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧ x ∈ interior K.carrier ∧
      frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, -3)) ∪
        range (fun y : Sphere 2 => nk.map (y, 3)) ∧
      Disjoint (range (fun y : Sphere 2 => nk.map (y, -3)))
        (range (fun y : Sphere 2 => nk.map (y, 3))) ∧
      (∀ t ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, t))) ∧
      (∀ y ∈ K.carrier, 2 * A < metricScalarAt L.metric y ∧ metricScalarAt L.metric y ≤ 8 * C2 ^ 2 * A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ nk.cylindricalChart.domain) ∧
      ∃ (cneg : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, -3)))
        (cpos : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3 (fun y : Sphere 2 => nk.map (y, 3))),
        cneg.radius < 1 ∧ cpos.radius < 1 ∧
        (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
          (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
        (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
          (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) := by
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  obtain ⟨n, nk, _, hmap⟩ :=
    (L.eventually_spatialNeck_of_incoming_strongNecks hτ x hx hδ
      (hδsmall.trans (by norm_num)) hepsδ hfit neck).exists
  obtain ⟨K, hK⟩ := nk.exists_short_spherical_barrier hδsmall A C2 hA hC2 hscale
  exact ⟨n, nk, K, hmap, hK⟩

theorem TerminalLimitMetric.eventually_spatialNeck_of_canonical_caps
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 11)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤ metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v),
      v.val ∈ (cap n).tube ∧
        ∀ z : neckBuffer δ, (nk.map z.val).val = (cap n).tubeMap z.val := by
  have heps : 0 < eps := by
    obtain ⟨v, nk, hmap⟩ := hW 0 (cap 0) (depth 0) (hcap 0)
    exact nk.eps_pos
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ heps hepsδ.le)
  have hevent := L.eventually_normalizedNeck_of_canonical_caps hτ x hx hδ
    (hδsmall.trans (by norm_num)) hepsδ hfit ⌈δ⁻¹⌉₊ hk W hW cap depth hcap
  filter_upwards [hevent] with n hn
  obtain ⟨v, source, hsource, hv, N, hNv, _, hNmap⟩ := hn
  obtain ⟨nk, _, hnkmap⟩ := N.exists_spatialNeck le_rfl hδsmall le_rfl
  let nk' : SpatialNeck L.metric δ v := hNv ▸ nk
  have hm : ∀ z : neckBuffer δ, (nk'.map z.val).val = (cap n).tubeMap z.val := by
    cases hNv
    intro z
    exact (congrArg Subtype.val (hnkmap z)).trans ((hNmap z).trans (hsource z.val).symm)
  exact ⟨v, nk', hv, hm⟩

set_option backward.isDefEq.respectTransparency false in
theorem TerminalLimitMetric.eventually_cap_spherical_barrier
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤ metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v)
      (K : CompactDomain G.terminalRegularOpen),
      Subtype.val '' K.carrier = (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      x ∈ interior K.carrier ∧ K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier ∧
      (∀ y ∈ K.carrier, metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 2 * C2 * metricScalarAt L.metric x) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) < 2 * C2 * metricScalarAt L.metric x) ∧
      frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
        (fun q : Sphere 2 => nk.map (q, 1 / 2)),
        c.radius < 1 / 4 ∧ ∀ q,
          c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
            (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0) := by
  have heps : 0 < eps := by
    obtain ⟨v, nk, _⟩ := hW 0 (cap 0) (depth 0) (hcap 0)
    exact nk.eps_pos
  have hδ11 : δ < 1 / 11 := hδsmall.trans (by norm_num)
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ heps hepsδ.le)
  have hlen : (101 : ℝ) < δ⁻¹ :=
    (lt_inv_comm₀ (by norm_num) hδ).mpr (by linarith)
  have h2k : 2 ≤ ⌈δ⁻¹⌉₊ := by exact_mod_cast (show (2 : ℝ) ≤ δ⁻¹ by linarith).trans (Nat.le_ceil δ⁻¹)
  have hevent := L.eventually_cap_midpoint_region hτ x hx hδ hδsmall hepsδ hfit
    ⌈δ⁻¹⌉₊ hk h2k W hW cap depth hcap
  filter_upwards [hevent] with n hn
  obtain ⟨N, K, e, hK, hxK, hKU, hscalarK, hscalarN, hfront, hemb, heold, heN,
    hrelative, hmetricN, hdomainN, c, hc, hcmap⟩ := hn
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


private theorem neck_half_slice_edist_le
    (L : G.TerminalLimitMetric) {δ : ℝ} {v : G.terminalRegularOpen}
    (nk : SpatialNeck L.metric δ v) (p q : Sphere 2) :
    riemannianEDistOf L.metric (nk.map (p, 1 / 2)) (nk.map (q, 1 / 2)) ≤
      ENNReal.ofReal (28 / Real.sqrt (metricScalarAt L.metric v)) := by
  have hlen : (1 : ℝ) < δ⁻¹ := by
    apply (lt_inv_comm₀ zero_lt_one nk.eps_pos).mpr
    simpa using nk.eps_small.trans (by norm_num : (1 : ℝ) / 11 < 1)
  have hroot : 0 < Real.sqrt (metricScalarAt L.metric v) := Real.sqrt_pos.mpr nk.Q_pos
  have hsqrt : Real.sqrt (1 + δ) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith [nk.eps_small]
  have hb (z : Sphere 2) : riemannianEDistOf L.metric v (nk.map (z, 1 / 2)) ≤
      ENNReal.ofReal (14 / Real.sqrt (metricScalarAt L.metric v)) := by
    have h := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 1) hlen
      ⟨(z, 1 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ hroot.le
    norm_num
    linarith
  calc
    _ ≤ riemannianEDistOf L.metric (nk.map (p, 1 / 2)) v +
        riemannianEDistOf L.metric v (nk.map (q, 1 / 2)) :=
      riemannianEDistOf_triangle L.metric _ _ _
    _ ≤ ENNReal.ofReal (14 / Real.sqrt (metricScalarAt L.metric v)) +
        ENNReal.ofReal (14 / Real.sqrt (metricScalarAt L.metric v)) := by
      rw [riemannianEDistOf_comm L.metric (nk.map (p, 1 / 2)) v]
      exact add_le_add (hb p) (hb q)
    _ = ENNReal.ofReal (28 / Real.sqrt (metricScalarAt L.metric v)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem neck_boundary_edist_le_of_scalar_comparison
    (L : G.TerminalLimitMetric) {δ C Q : ℝ} (hC : 1 ≤ C) (hQ : 0 < Q)
    {v : G.terminalRegularOpen} (nk : SpatialNeck L.metric δ v)
    (hscalar : Q / (2 * C) < metricScalarAt L.metric v)
    (K : CompactDomain G.terminalRegularOpen)
    (hfront : frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, 1 / 2))) :
    ∀ y ∈ frontier K.carrier, ∀ z ∈ frontier K.carrier,
      riemannianEDistOf L.metric y z ≤ ENNReal.ofReal (56 * C / Real.sqrt Q) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hRv := nk.Q_pos
  have hrootQ := Real.sqrt_pos.mpr hQ
  have hrootV := Real.sqrt_pos.mpr hRv
  have hQR : Q < 2 * C * metricScalarAt L.metric v :=
    by
      simpa only [mul_comm] using
        (div_lt_iff₀ (show 0 < 2 * C by positivity)).mp hscalar
  have hproduct : 2 * C * metricScalarAt L.metric v ≤
      (2 * C) ^ 2 * metricScalarAt L.metric v := by
    apply mul_le_mul_of_nonneg_right _ hRv.le
    nlinarith
  have hroot : Real.sqrt Q ≤ 2 * C * Real.sqrt (metricScalarAt L.metric v) := by
    calc
      _ ≤ Real.sqrt ((2 * C) ^ 2 * metricScalarAt L.metric v) :=
        Real.sqrt_le_sqrt (hQR.le.trans hproduct)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  intro y hy z hz
  rw [hfront] at hy hz
  obtain ⟨p, rfl⟩ := hy
  obtain ⟨q, rfl⟩ := hz
  refine (neck_half_slice_edist_le L nk p q).trans (ENNReal.ofReal_le_ofReal ?_)
  apply (div_le_div_iff₀ hrootV hrootQ).mpr
  nlinarith


private theorem canonical_domain_edist_lt
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps C1 C2 : ℝ} (W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n)) :
    ∀ᶠ n in atTop, ∀ y ∈ (W n).domain.carrier,
      riemannianEDistOf (G.flow.base.metric (τ n)) x.val y <
        ENNReal.ofReal (4 * C1 / Real.sqrt (metricScalarAt L.metric x)) := by
  have hlower := hτ.eventually ((L.tendsto_metricScalarAt x).eventually
    (Ioi_mem_nhds (show metricScalarAt L.metric x / 4 < metricScalarAt L.metric x by linarith)))
  filter_upwards [hlower] with n hn
  change metricScalarAt L.metric x / 4 < G.flow.scalar (τ n) x.val at hn
  have hroot := Real.sqrt_pos.mpr hx
  have hrootn := Real.sqrt_pos.mpr (W n).Q_pos
  have hrootle : Real.sqrt (metricScalarAt L.metric x) ≤
      2 * Real.sqrt (G.flow.scalar (τ n) x.val) := by
    nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt (W n).Q_pos.le,
      Real.sqrt_nonneg (G.flow.scalar (τ n) x.val)]
  have hC1 : 0 < C1 := by
    have hr := (inv_pos.mpr hrootn).trans_le (W n).radius_lower
    have hpos := hr.trans_le (W n).radius_upper
    exact ((div_pos_iff.mp hpos).resolve_right (fun h => hrootn.not_gt h.2)).1
  intro y hy
  apply ((W n).inside_ball hy).trans_le
  apply ENNReal.ofReal_le_ofReal
  calc
    2 * (W n).radius ≤ 2 * (C1 / Real.sqrt (G.flow.scalar (τ n) x.val)) := by
      linarith [(W n).radius_upper]
    _ ≤ 4 * C1 / Real.sqrt (metricScalarAt L.metric x) := by
      apply (le_div_iff₀ hroot).mpr
      calc
        _ = (2 * C1 * Real.sqrt (metricScalarAt L.metric x)) /
            Real.sqrt (G.flow.scalar (τ n) x.val) := by ring
        _ ≤ 4 * C1 := (div_le_iff₀ hrootn).mpr (by nlinarith)

private theorem eventually_canonical_domain_metric_lower
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {K : Set G.terminalRegularOpen} (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ∀ v : TangentSpace ThreeModel y,
      L.metric.inner y v v ≤ (2 : ℝ) ^ 2 * (G.flow.base.metric (τ n)).inner y.val v v := by
  obtain ⟨d, hd, hclose⟩ := L.converges K hK 0 (1 / 2) (by norm_num)
  filter_upwards [hτ.eventually (Ioo_mem_nhdsLT hd.2)] with n hn
  intro y hy v
  have hb := (DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le L.metric
    ((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen) y (hclose (τ n) hn y hy).le v).1
  have hnonneg := DifferentialGeometry.metric_inner_self_nonneg L.metric y v
  change (1 - 1 / 2 : ℝ) * L.metric.inner y v v ≤
    (G.flow.base.metric (τ n)).inner y.val v v at hb
  nlinarith


private theorem eventually_canonical_region_subset_ball_of_neck_boundary
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps C1 C2 : ℝ} (W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n))
    {K₀ : Set G.terminalRegularOpen} (hK₀ : IsCompact K₀)
    (hcapture : ∀ᶠ n in atTop, (W n).domain.carrier ⊆ Subtype.val '' K₀) :
    ∀ᶠ n in atTop, ∀ {δ : ℝ} {v : G.terminalRegularOpen}
      (nk : SpatialNeck L.metric δ v) (K : CompactDomain G.terminalRegularOpen),
      x ∈ K.carrier → K.carrier ⊆ Subtype.val ⁻¹' (W n).domain.carrier →
      metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric v →
      frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, 1 / 2)) →
      K.carrier ⊆ riemannianBallOf L.metric x
        ((8 * C1 + 56 * C2) / Real.sqrt (metricScalarAt L.metric x)) := by
  have hdist := canonical_domain_edist_lt L hτ x hx W
  have hmetric := eventually_canonical_domain_metric_lower L hτ hK₀
  filter_upwards [hcapture, hdist, hmetric] with n hcap hd hm
  intro δ v nk K hxK hKW hscalar hfront
  have hKsub : K.carrier ⊆ K₀ := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hcap (hKW hz)
    exact (Subtype.ext hwz : w = z) ▸ hw
  have hC2 := (W n).one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hroot := Real.sqrt_pos.mpr hx
  have hfrontbound := neck_boundary_edist_le_of_scalar_comparison L hC2 hx nk hscalar K hfront
  intro y hy
  have hbound := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_subtype_le_mul_add_of_frontier_bound
    (G.flow.base.metric (τ n)) G.terminalRegularOpen L.metric K.compact
    (by norm_num : (0 : ℝ) < 2)
    (ENNReal.ofReal (56 * C2 / Real.sqrt (metricScalarAt L.metric x)))
    (fun z hz => hm z (hKsub hz)) hfrontbound hxK hy
  change riemannianEDistOf L.metric x y < _
  apply hbound.trans_lt
  calc
    _ < ENNReal.ofReal 2 * ENNReal.ofReal (4 * C1 / Real.sqrt (metricScalarAt L.metric x)) +
        ENNReal.ofReal (56 * C2 / Real.sqrt (metricScalarAt L.metric x)) :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
        (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
          ENNReal.ofReal_ne_top (hd y.val (hKW hy)))
    _ = ENNReal.ofReal ((8 * C1 + 56 * C2) / Real.sqrt (metricScalarAt L.metric x)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_add]
      · congr 1
        ring
      · have hRn := Real.sqrt_pos.mpr (W n).Q_pos
        have hC1 : 0 ≤ C1 := by
          have hh := (W n).radius_lower.trans (W n).radius_upper
          have hposit : 0 < C1 / Real.sqrt (G.flow.scalar (τ n) x.val) :=
            (inv_pos.mpr hRn).trans_le hh
          exact ((div_pos_iff.mp hposit).resolve_right (fun h => hRn.not_gt h.2)).1.le
        positivity
      · positivity


theorem TerminalLimitMetric.spatial_neck_or_cap_of_canonical_neighborhoods
    (L : G.TerminalLimitMetric) {eps δ q C1 C2 : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (hq : 0 < q)
    (x y : G.terminalRegularOpen)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : CanonicalWitness G.flow eps C1 C2 x.val t, W.capTubeHasNeckChart eps)
    (hx : q < metricScalarAt L.metric x)
    (hy : y.val ∈ connectedComponent x.val)
    (hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x) :
    Nonempty (SpatialNeck L.metric δ x) ∨
      ∃ (v : G.terminalRegularOpen) (nk : SpatialNeck L.metric δ v)
        (K : CompactDomain G.terminalRegularOpen),
        Nonempty (CapCore K.carrier) ∧ x ∈ interior K.carrier ∧
        riemannianBallOf L.metric x (1000 / Real.sqrt (metricScalarAt L.metric x)) ⊆
          interior K.carrier ∧
        K.carrier ⊆ riemannianBallOf L.metric x
          ((8 * C1 + 56 * C2) / Real.sqrt (metricScalarAt L.metric x)) ∧
        (∀ w ∈ K.carrier,
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
            metricScalarAt L.metric w < 2 * C2 * metricScalarAt L.metric x) ∧
        (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric (nk.map z) ∧
            metricScalarAt L.metric (nk.map z) < 2 * C2 * metricScalarAt L.metric x) ∧
        frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, 1 / 2)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => nk.map (z, 1 / 2)) ∧
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
          (fun z : Sphere 2 => nk.map (z, 1 / 2)),
          c.radius < 1 / 4 ∧ ∀ z,
            c.toFun z = nk.map (z.1, 1 / 2 + (z.2 : ℝ)) ∧
              (c.toFun z ∈ K.carrier ↔ (z.2 : ℝ) ≤ 0) := by
  have hxpos := hq.trans hx
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have hbranch := L.eventually_canonical_neck_or_cap x y hy (eps := eps) (C1 := C1) hscalar
  obtain ⟨τ, _, _, hτ, W, hW, halt⟩ :=
    exists_canonical_neck_or_cap_sequence_of_eventually hcanonical hhigh hbranch
  rcases halt with hn | hc
  · obtain ⟨neck, _⟩ := hn
    obtain ⟨n, nk, _, _⟩ := (L.eventually_spatialNeck_of_incoming_strongNecks hτ x hxpos
      hδ (hδsmall.trans (by norm_num)) hepsδ hfit (fun n => (neck n).strong)).exists
    exact Or.inl ⟨nk⟩
  · obtain ⟨cap, depth, hcap⟩ := hc
    obtain ⟨K₀, hK₀, _, _, _, _, hcapture⟩ :=
      L.eventually_cap_neck_compact_capture hτ x W hW cap depth hcap
    have hupper := eventually_canonical_region_subset_ball_of_neck_boundary L hτ x hxpos W hK₀
      (hcapture.mono fun n hn => subset_union_left.trans hn)
    obtain ⟨n, ⟨⟨v, nk, K, hK, hxK, hKW, hscalarK, hscalarN, hfront, hemb, _, _, c, hc, hcollar⟩,
        hball⟩, hupper⟩ :=
      (((L.eventually_cap_spherical_barrier hτ x hxpos hδ hδsmall hepsδ hfit
        W hW cap depth hcap).and
          (L.eventually_ball_subset_canonical_cap_core hτ x hxpos W cap depth)).and hupper).exists
    have hsubset : (cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ G.terminalRegularOpen := by
      rw [← hK]
      rintro z ⟨w, _, rfl⟩
      exact w.property
    have hpreimage : Subtype.val ⁻¹' ((cap n).core.carrier ∪
        (cap n).tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2))) = K.carrier := by
      rw [← hK, preimage_image_eq _ Subtype.val_injective]
    have hmodel := (cap n).nonempty_capCore_truncated_core
      (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    have hmodel' := hmodel.some.nonempty_preimage_open G.terminalRegularOpen hsubset
    rw [hpreimage] at hmodel'
    have hcore : (Subtype.val ⁻¹' (cap n).core.carrier : Set G.terminalRegularOpen) ⊆
        K.carrier := by
      intro z hz
      rw [← hpreimage]
      exact Or.inl hz
    have hballK : riemannianBallOf L.metric x
        (1000 / Real.sqrt (metricScalarAt L.metric x)) ⊆ interior K.carrier := by
      refine hball.trans ?_
      apply Subset.trans ?_ (interior_mono hcore)
      exact preimage_interior_subset_interior_preimage continuous_subtype_val
    have hscalarV : metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric v := by
      have h := (hscalarN (nk.center, 0) ⟨mem_univ _, by norm_num⟩).1
      simpa only [nk.center_eq] using h
    have hupperK := hupper nk K (interior_subset hxK) hKW hscalarV hfront
    exact Or.inr ⟨v, nk, K, hmodel', hxK, hballK, hupperK, hscalarK, hscalarN, hfront, hemb, c, hc, hcollar⟩

theorem TerminalLimitMetric.exists_spherical_barrier_at_level_of_canonical
    (L : G.TerminalLimitMetric) {δ C1 C2 q A : ℝ}
    (hδsmall : δ < 1 / 20000) (hA : 0 < A)
    (hqA : q < 4 * C2 * A)
    {x y : G.terminalRegularOpen}
    (hscale : metricScalarAt L.metric x = 4 * C2 * A)
    (hy : y.val ∈ connectedComponent x.val)
    (hyA : metricScalarAt L.metric y ≤ A)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x.val t,
        W.capTubeHasNeckChart (δ / 4)) :
    ∃ (K : CompactDomain G.terminalRegularOpen) (v : G.terminalRegularOpen)
      (nk : SpatialNeck L.metric δ v),
      x ∈ interior K.carrier ∧
      (∀ z ∈ K.carrier, 2 * A < metricScalarAt L.metric z ∧
        metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
      (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
        2 * A < metricScalarAt L.metric (nk.map z) ∧
          metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
      nk.cylindricalChart.metricCloseOn L.metric δ
        {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
      (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
      ((K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
          range (fun q : Sphere 2 => nk.map (q, 3)) ∧
        Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
          (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
        (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞
          (fun q : Sphere 2 => nk.map (q, b))) ∧
        ∃ (cneg : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, -3)))
          (cpos : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, 3))),
          cneg.radius < 1 ∧ cpos.radius < 1 ∧
          (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
            (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
          (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
            (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
      (frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
        ∃ c : SmoothTwoSidedCollar I2 I3
            (fun q : Sphere 2 => nk.map (q, 1 / 2)),
          c.radius < 1 / 4 ∧ ∀ q,
            c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
              (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) := by
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds (hscale.symm ▸ hqA))
  have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s := Ioo_mem_nhdsLT G.lt
  obtain ⟨t, ht, hqt⟩ := (htime.and hhigh).exists
  obtain ⟨W₀, _⟩ := hcanonical t ht hqt
  have hδ : 0 < δ := by linarith [W₀.eps_pos]
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  let eps := δ / 4
  have hepsδ : eps < δ := by dsimp [eps]; linarith
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by
    have hδ1 : δ < 1 := hδsmall.trans (by norm_num)
    have hdiv : δ⁻¹ + 1 ≤ (δ / 4)⁻¹ := by
      rw [inv_div]
      apply (le_div_iff₀ hδ).mpr
      field_simp
      linarith
    exact hdiv
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  have hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x := by
    rw [hscale]
    have hm := mul_le_mul_of_nonneg_left hyA (zero_le_one.trans hC2)
    nlinarith
  have hbranch := L.eventually_canonical_neck_or_cap x y hy (eps := eps)
    (C1 := C1) (C2 := C2) hscalar
  obtain ⟨τ, _, _, hτ, W, hW, hcases⟩ :=
    exists_canonical_neck_or_cap_sequence_of_eventually
      (fun t ht hxq => by
        obtain ⟨w, hw⟩ := hcanonical t ht hxq
        exact ⟨w, by simpa [eps] using hw⟩)
      hhigh hbranch
  rcases hcases with ⟨neck, hneck⟩ | ⟨cap, depth, hcap⟩
  · obtain ⟨n, nk, K, _, hK, hxK, hfront, hdisj, hemb, hband, hfull, hmetric, hdom, hcollar⟩ :=
      L.exists_neck_spherical_barrier_of_incoming_strongNecks hτ x hδ
        (hδsmall.trans (by norm_num)) hepsδ hfit
        (fun n => (neck n).strong) A C2 hA hC2 hscale
    exact ⟨K, x, nk, hxK, hband, hfull, hmetric, hdom,
      Or.inl ⟨hK, hfront, hdisj, hemb, hcollar⟩⟩
  · obtain ⟨n, v, nk, K, hK, hxK, hKU, hband, hfull, hfront, hemb, hmetric, hdom, hcollar⟩ :=
      (L.eventually_cap_spherical_barrier hτ x hx hδ hδsmall hepsδ hfit W hW cap depth hcap).exists
    have hlow : metricScalarAt L.metric x / (2 * C2) = 2 * A := by
      rw [hscale]
      field_simp
      ring
    have hhigh' : 2 * C2 * metricScalarAt L.metric x = 8 * C2 ^ 2 * A := by
      rw [hscale]
      ring
    refine ⟨K, v, nk, hxK, ?_, ?_, hmetric, hdom, ?_⟩
    · intro z hz
      simpa only [hlow, hhigh'] using And.intro (hband z hz).1 (hband z hz).2.le
    · intro z hz
      simpa only [hlow, hhigh'] using And.intro (hfull z hz).1 (hfull z hz).2.le
    · exact Or.inr ⟨hfront, hemb, hcollar⟩


theorem exists_uniform_spherical_barrier_at_level
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (A : ℝ) (x y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric x = 4 * C2 * A →
        y.val ∈ connectedComponent x.val → metricScalarAt L.metric y ≤ A →
        ∃ (K : CompactDomain G.terminalRegularOpen) (v : G.terminalRegularOpen)
          (nk : SpatialNeck L.metric δ v),
          x ∈ interior K.carrier ∧
          (∀ z ∈ K.carrier, 2 * A < metricScalarAt L.metric z ∧ metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
          nk.cylindricalChart.metricCloseOn L.metric δ
            {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
          ((K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
            frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
              range (fun q : Sphere 2 => nk.map (q, 3)) ∧
            Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
              (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
            (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, b))) ∧
            ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, -3)))
              (cpos : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 3))),
              cneg.radius < 1 ∧ cpos.radius < 1 ∧
              (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
                (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
              (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
                (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
          (frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
              c.radius < 1 / 4 ∧ ∀ q,
                c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
                  (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) := by
  have heps : 0 < δ / 4 := by positivity
  have hepsSmall : δ / 4 < 1 / 11 := by linarith
  obtain ⟨C2, hC2, hmain⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hepsSmall
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L A x y hA hqA hscale hy hyA
  exact L.exists_spherical_barrier_at_level_of_canonical hδsmall hA hqA
    hscale hy hyA (fun t ht hx => hcanonical x.val t ⟨ht.1.le, ht.2⟩ hx.le)


theorem TerminalLimitMetric.exists_spherical_barrier_at_level
    (L : G.TerminalLimitMetric) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000) :
    ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
      ∀ (A : ℝ) (x y : G.terminalRegularOpen), 0 < A → q < 4 * C2 * A →
        metricScalarAt L.metric x = 4 * C2 * A →
        y.val ∈ connectedComponent x.val → metricScalarAt L.metric y ≤ A →
        ∃ (K : CompactDomain G.terminalRegularOpen) (v : G.terminalRegularOpen)
          (nk : SpatialNeck L.metric δ v),
          x ∈ interior K.carrier ∧
          (∀ z ∈ K.carrier, 2 * A < metricScalarAt L.metric z ∧ metricScalarAt L.metric z ≤ 8 * C2 ^ 2 * A) ∧
          (∀ z ∈ (univ ×ˢ Icc (-101 : ℝ) 101 : Set Cylinder),
            2 * A < metricScalarAt L.metric (nk.map z) ∧ metricScalarAt L.metric (nk.map z) ≤ 8 * C2 ^ 2 * A) ∧
          nk.cylindricalChart.metricCloseOn L.metric δ
            {z : nk.cylindricalChart.domain | z.val.2 ∈ Icc (-101 : ℝ) 101} ∧
          (∀ q z, z ∈ Icc (-101 : ℝ) 101 → (q, z) ∈ nk.cylindricalChart.domain) ∧
          ((K.carrier = nk.map '' (univ ×ˢ Icc (-3 : ℝ) 3) ∧
            frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, -3)) ∪
              range (fun q : Sphere 2 => nk.map (q, 3)) ∧
            Disjoint (range (fun q : Sphere 2 => nk.map (q, -3)))
              (range (fun q : Sphere 2 => nk.map (q, 3))) ∧
            (∀ b ∈ ({-3, 3} : Set ℝ), IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, b))) ∧
            ∃ (cneg : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, -3)))
              (cpos : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 3))),
              cneg.radius < 1 ∧ cpos.radius < 1 ∧
              (∀ q, cneg.toFun q = nk.map (q.1, -3 - (q.2 : ℝ)) ∧
                (cneg.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0)) ∧
              (∀ q, cpos.toFun q = nk.map (q.1, 3 + (q.2 : ℝ)) ∧
                (cpos.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) ∨
          (frontier K.carrier = range (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, 1 / 2)) ∧
            ∃ c : SmoothTwoSidedCollar I2 I3 (fun q : Sphere 2 => nk.map (q, 1 / 2)),
              c.radius < 1 / 4 ∧ ∀ q,
                c.toFun q = nk.map (q.1, 1 / 2 + (q.2 : ℝ)) ∧
                  (c.toFun q ∈ K.carrier ↔ (q.2 : ℝ) ≤ 0))) := by
  obtain ⟨C2, hC2, hmain⟩ := exists_uniform_spherical_barrier_at_level.{u} hδ hδsmall
  obtain ⟨q, hq, hbarrier⟩ := hmain P a s G
  exact ⟨C2, q, hC2, hq, hbarrier L⟩


theorem TerminalLimitMetric.nonempty_spatialNeck_of_canonical_along_minimizer
    (L : G.TerminalLimitMetric) {eps δ α q C1 C2 : ℝ}
    (hδ : 0 < δ)
    (hα : α < 1 / 11) (hreserve : 13000 * δ ≤ α)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (hq : 0 < q) (hC2 : 0 < C2)
    {γ : ℝ → G.terminalRegularOpen} {l t r : ℝ} (hlt : l < t) (htr : t < r)
    (hmin : ∀ u ∈ Icc l r, ∀ v ∈ Icc l r,
      riemannianEDistOf L.metric (γ u) (γ v) = ENNReal.ofReal |u - v|)
    (hcanonical : ∀ u ∈ Ioo a s, q < G.flow.scalar u (γ t).val →
      ∃ W : CanonicalWitness G.flow eps C1 C2 (γ t).val u, W.capTubeHasNeckChart eps)
    (hx : q < metricScalarAt L.metric (γ t))
    (hleft : 2 * C2 * metricScalarAt L.metric (γ l) < metricScalarAt L.metric (γ t))
    (hright : 2 * C2 * metricScalarAt L.metric (γ t) ≤ metricScalarAt L.metric (γ r)) :
    Nonempty (SpatialNeck L.metric α (γ t)) := by
  have hδsmall : δ < 1 / 20000 := by linarith
  have hxpos : 0 < metricScalarAt L.metric (γ t) := hq.trans hx
  have hy : (γ l).val ∈ connectedComponent (γ t).val := by
    have hfinite : riemannianEDistOf L.metric (γ t) (γ l) ≠ ⊤ := by
      rw [hmin t ⟨hlt.le, htr.le⟩ l ⟨le_rfl, hlt.le.trans htr.le⟩]
      exact ENNReal.ofReal_ne_top
    have hmem : γ l ∈ connectedComponent (γ t) := by
      have hball : γ l ∈ riemannianBallOf L.metric (γ t)
          ((riemannianEDistOf L.metric (γ t) (γ l)).toReal + 1) := by
        apply (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
        exact lt_add_one _
      exact Geometry.Metric.edistOf_ball_subset_connCompOpen L.metric (γ t) _ hball
    exact continuous_subtype_val.mapsTo_connectedComponent (γ t) hmem
  have hscalar : C2 * metricScalarAt L.metric (γ l) < metricScalarAt L.metric (γ t) := by
    by_cases hnonneg : 0 ≤ metricScalarAt L.metric (γ l)
    · nlinarith
    · exact (mul_neg_of_pos_of_neg hC2 (lt_of_not_ge hnonneg)).trans hxpos
  rcases L.spatial_neck_or_cap_of_canonical_neighborhoods hδ hδsmall hepsδ hfit hq
      (γ t) (γ l) hcanonical hx hy hscalar with hneck | hcap
  · obtain ⟨N⟩ := hneck
    exact ⟨N.mono (by linarith) hα⟩
  · obtain ⟨v, nk, K, hK, hxK, hball, hupper, hscalarK, hscalarN, hfront, hemb, hcollar⟩ := hcap
    apply nk.exists_at_minimizing_point_of_frontier_eq_slice hα hreserve hfront hlt htr hmin
    · intro hlK
      have hh := (hscalarK (γ l) (interior_subset hlK)).1
      have hcontra : metricScalarAt L.metric (γ l) <
          metricScalarAt L.metric (γ t) / (2 * C2) := by
        apply (lt_div_iff₀ (by positivity : 0 < 2 * C2)).mpr
        nlinarith
      exact (not_lt_of_ge hcontra.le) hh
    · intro hrK
      exact (not_lt_of_ge hright) (hscalarK (γ r) (interior_subset hrK)).2
    · exact hxK


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
