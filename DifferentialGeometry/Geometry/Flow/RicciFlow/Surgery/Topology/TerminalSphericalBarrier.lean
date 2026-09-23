import DifferentialGeometry.Geometry.Neck.SphericalBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalAlternatives

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

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

theorem TerminalLimitMetric.eventually_spatialNeck_of_incoming_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 11) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (neck : ∀ n, StrongNeck G.flow eps x.val (τ n)) :
    ∀ᶠ n in atTop, ∃ nk : SpatialNeck L.metric δ x,
      nk.center = (neck n).center ∧
        ∀ z : neckBuffer δ, (nk.map z.val).val = (neck n).map z.val := by
  have hk : ⌈δ⁻¹⌉₊ ≤ ⌈eps⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ (neck 0).eps_pos hepsδ.le)
  have hevent := L.eventually_normalizedNeck_of_incoming_strongNecks hτ x hx hδ
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
        ∀ z : neckBuffer δ, (nk.map z.val).val = (cap n).tube_map z.val := by
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
  have hm : ∀ z : neckBuffer δ, (nk'.map z.val).val = (cap n).tube_map z.val := by
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
        (cap n).tube_map '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
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


set_option backward.isDefEq.respectTransparency false in
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
  let eps := δ / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsδ : eps < δ := by dsimp [eps]; linarith
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by
    have hδ1 : δ < 1 := hδsmall.trans (by norm_num)
    have hepsquarter : eps ≤ δ / 4 := le_rfl
    have hdiv : δ⁻¹ + 1 ≤ (δ / 4)⁻¹ := by
      rw [inv_div]
      apply (le_div_iff₀ hδ).mpr
      field_simp
      linarith
    exact hdiv.trans (inv_anti₀ heps hepsquarter)
  obtain ⟨C2, hC2, hsequence⟩ := exists_uniform_canonical_neck_or_cap_sequence.{u} heps
    (hepsδ.trans (hδsmall.trans (by norm_num)))
  refine ⟨C2, hC2, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hseq⟩ := hsequence P a s G
  refine ⟨q, hq, ?_⟩
  intro L A x y hA hqA hscale hy hyA
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hx : 0 < metricScalarAt L.metric x := by rw [hscale]; positivity
  have hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x := by
    rw [hscale]
    have hm := mul_le_mul_of_nonneg_left hyA hC2pos.le
    nlinarith
  obtain ⟨τ, _, _, hτ, W, hW, hcases⟩ := hseq L x y (hscale ▸ hqA) hy hscalar
  rcases hcases with ⟨neck, hneck⟩ | ⟨cap, depth, hcap⟩
  · obtain ⟨n, nk, K, _, hK, hxK, hfront, hdisj, hemb, hband, hfull, hmetric, hdom, hcollar⟩ :=
      L.exists_neck_spherical_barrier_of_incoming_strongNecks hτ x hδ
        (hδsmall.trans (by norm_num)) hepsδ hfit (fun n => (neck n).strong) A C2 hA hC2 hscale
    exact ⟨K, x, nk, hxK, hband, hfull, hmetric, hdom, Or.inl ⟨hK, hfront, hdisj, hemb, hcollar⟩⟩
  · obtain ⟨n, v, nk, K, hK, hxK, hKU, hband, hfull, hfront, hemb, hmetric, hdom, hcollar⟩ :=
      (L.eventually_cap_spherical_barrier hτ x hx hδ hδsmall hepsδ hfit W hW cap depth hcap).exists
    have hlow : metricScalarAt L.metric x / (2 * C2) = 2 * A := by rw [hscale]; field_simp; ring
    have hhigh : 2 * C2 * metricScalarAt L.metric x = 8 * C2 ^ 2 * A := by rw [hscale]; ring
    refine ⟨K, v, nk, hxK, ?_, ?_, hmetric, hdom, Or.inr ⟨hfront, hemb, hcollar⟩⟩
    · intro z hz
      simpa only [hlow, hhigh] using And.intro (hband z hz).1 (hband z hz).2.le
    · intro z hz
      simpa only [hlow, hhigh] using And.intro (hfull z hz).1 (hfull z hz).2.le

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
