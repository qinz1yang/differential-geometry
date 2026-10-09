import DifferentialGeometry.Geometry.Metric.LocalMetricBallContainment
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Neck.SpatialChart

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem TerminalLimitMetric.exists_compact_containing_spatial_neck_windows_of_pinching
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) {eps C2 : ℝ} (heps : 0 ≤ eps) (hC2 : 0 ≤ C2) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        ∀ U : Set P.Carrier,
          (∀ y ∈ U, G.flow.scalar t y ≤ C2 * G.flow.scalar t x.val) →
          U ⊆ Subtype.val '' K ∧
          ∀ v ∈ U, ∀ nk : SpatialNeck (G.flow.base.metric t) eps v,
            nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ Subtype.val '' K := by
  let B := (1 + 4323 * eps) * (C2 * (|metricScalarAt L.metric x| + 1))
  obtain ⟨K₀, hK₀, hKreg, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch B
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
  have hcenter : ∀ᶠ t in 𝓝[<] s,
      G.flow.scalar t x.val < |metricScalarAt L.metric x| + 1 :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (by linarith [le_abs_self (metricScalarAt L.metric x)])
  obtain ⟨d', hd', hcenter'⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hcenter
  refine ⟨K, hK, max d d', ⟨hd.1.trans (le_max_left _ _), max_lt hd.2 hd'.2⟩, ?_⟩
  intro t ht U hU
  have ht₀ : t ∈ Ioo d s := ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
  have ht₁ : t ∈ Ioo d' s := ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩
  have hR : G.flow.scalar t x.val ≤ |metricScalarAt L.metric x| + 1 := (hcenter' ht₁).le
  have hfac : 1 ≤ 1 + 4323 * eps := by linarith
  have hCB : C2 * (|metricScalarAt L.metric x| + 1) ≤ B :=
    le_mul_of_one_le_left (by positivity) hfac
  constructor
  · intro y hy
    rw [himage]
    apply hcapture t ht₀
    exact ((hU y hy).trans (mul_le_mul_of_nonneg_left hR hC2)).trans hCB
  · intro v hv nk y hy
    rw [himage]
    apply hcapture t ht₀
    have hs := (nk.scalar_bounds_on_image_window hy).2
    exact hs.trans (mul_le_mul_of_nonneg_left
      ((hU v hv).trans (mul_le_mul_of_nonneg_left hR hC2)) (by positivity))

theorem TerminalLimitMetric.exists_compact_containing_spatial_neck_windows
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    (x : G.terminalRegularOpen) {eps C2 : ℝ} (heps : 0 ≤ eps) (hC2 : 0 ≤ C2) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        ∀ U : Set P.Carrier,
          (∀ y ∈ U, G.flow.scalar t y ≤ C2 * G.flow.scalar t x.val) →
          U ⊆ Subtype.val '' K ∧
          ∀ v ∈ U, ∀ nk : SpatialNeck (G.flow.base.metric t) eps v,
            nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ Subtype.val '' K := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  exact L.exists_compact_containing_spatial_neck_windows_of_pinching hq hbound hPhi hpinch x heps hC2

theorem TerminalLimitMetric.exists_compact_containing_canonical_domains_and_neck_windows
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) {epsCanonical eps C1 C2 : ℝ} (heps : 0 ≤ eps) (hC2 : 0 ≤ C2) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        ∀ W : CanonicalWitness G.flow epsCanonical C1 C2 x.val t,
          W.domain.carrier ⊆ Subtype.val '' K ∧
          ∀ v ∈ W.domain.carrier, ∀ nk : StrongNeck G.flow eps v t,
            nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ Subtype.val '' K := by
  obtain ⟨K, hK, d, hd, hcapture⟩ :=
    L.exists_compact_containing_spatial_neck_windows_of_pinching hq hbound hPhi hpinch x heps hC2
  refine ⟨K, hK, d, hd, ?_⟩
  intro t ht W
  have h := hcapture t ht W.domain.carrier (fun y hy => (W.scalar_bounds y hy).2)
  exact ⟨h.1, fun v hv nk => h.2 v hv nk.toSpatialNeck⟩

theorem TerminalLimitMetric.exists_compact_containing_cap_neck_windows
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) {epsCanonical eps C1 C2 : ℝ}
    (heps : 0 ≤ eps) (hC2 : 0 ≤ C2) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        ∀ W : CanonicalWitness G.flow epsCanonical C1 C2 x.val t,
          W.capTubeHasNeckChart eps →
          ∀ (cap : LocalCap G.flow epsCanonical x.val t W.domain.carrier) (depth),
            W.alternative = CanonicalAlternative.cap cap depth →
            ∃ (v : P.Carrier) (nk : StrongNeck G.flow eps v t),
              (∀ z, cap.tubeMap z = nk.map z) ∧ v ∈ cap.tube ∧
              W.domain.carrier ∪ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆
                Subtype.val '' K := by
  obtain ⟨K, hK, d, hd, hcapture⟩ :=
    L.exists_compact_containing_canonical_domains_and_neck_windows
      hq hbound hPhi hpinch x (epsCanonical := epsCanonical) (C1 := C1) heps hC2
  refine ⟨K, hK, d, hd, ?_⟩
  intro t ht W hW cap depth hcap
  obtain ⟨v, nk, hmap⟩ := hW cap depth hcap
  have hv : v ∈ cap.tube := by
    rw [← cap.tube_eq]
    exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩,
      (hmap (nk.center, 0)).trans nk.center_eq⟩
  have hvW : v ∈ W.domain.carrier := cap.union_eq.symm ▸ Or.inr hv
  exact ⟨v, nk, hmap, hv, union_subset (hcapture t ht W).1
    ((hcapture t ht W).2 v hvW nk)⟩

theorem TerminalLimitMetric.exists_uniform_scalar_comparison_on_cap_neck_windows
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) {epsCanonical eps C1 C2 : ℝ}
    (heps : 0 ≤ eps) (hC2 : 0 ≤ C2) :
    ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
      ∀ eta : ℝ, 0 < eta → ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
        ∀ W : CanonicalWitness G.flow epsCanonical C1 C2 x.val t,
          W.capTubeHasNeckChart eps →
          ∀ (cap : LocalCap G.flow epsCanonical x.val t W.domain.carrier) (depth),
            W.alternative = CanonicalAlternative.cap cap depth →
            ∃ (v : P.Carrier) (nk : StrongNeck G.flow eps v t),
              (∀ z, cap.tubeMap z = nk.map z) ∧ v ∈ cap.tube ∧
              W.domain.carrier ∪ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆
                Subtype.val '' K ∧
              ∀ y : G.terminalRegularOpen,
                y.val ∈ W.domain.carrier ∪ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) →
                  |G.flow.scalar t y.val - metricScalarAt L.metric y| < eta := by
  obtain ⟨K, hK, d₀, hd₀, hcapture⟩ := L.exists_compact_containing_cap_neck_windows
    hq hbound hPhi hpinch x (epsCanonical := epsCanonical) (C1 := C1) heps hC2
  refine ⟨K, hK, ?_⟩
  intro eta heta
  obtain ⟨d₁, hd₁, hclose⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp
    (L.eventually_scalar_close_on_compact hK heta)
  refine ⟨max d₀ d₁, ⟨hd₀.1.trans (le_max_left _ _), max_lt hd₀.2 hd₁.2⟩, ?_⟩
  intro t ht W hW cap depth hcap
  obtain ⟨v, nk, hmap, hv, hsub⟩ := hcapture t
    ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩ W hW cap depth hcap
  refine ⟨v, nk, hmap, hv, hsub, ?_⟩
  intro y hy
  obtain ⟨z, hz, he⟩ := hsub hy
  have hzy : z = y := Subtype.ext he
  exact hclose (⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩) y (hzy ▸ hz)

theorem TerminalLimitMetric.exists_canonical_cap_neck_scalar_comparison
    (L : G.TerminalLimitMetric) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 q : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < q ∧
        ∀ x : G.terminalRegularOpen, q < metricScalarAt L.metric x →
          ∃ K : Set G.terminalRegularOpen, IsCompact K ∧
            ∀ eta : ℝ, 0 < eta → ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
              ∃ W : CanonicalWitness G.flow eps C1 C2 x.val t,
                W.capTubeHasNeckChart eps ∧
                ∀ (cap : LocalCap G.flow eps x.val t W.domain.carrier) (depth),
                  W.alternative = CanonicalAlternative.cap cap depth →
                  ∃ (v : P.Carrier) (nk : StrongNeck G.flow eps v t),
                    (∀ z, cap.tubeMap z = nk.map z) ∧ v ∈ cap.tube ∧
                    W.domain.carrier ∪ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆
                      Subtype.val '' K ∧
                    (∀ y : G.terminalRegularOpen,
                      y.val ∈ W.domain.carrier ∪ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) →
                        |G.flow.scalar t y.val - metricScalarAt L.metric y| < eta) ∧
                    (∀ y : G.terminalRegularOpen, y.val ∈ W.domain.carrier →
                      C2⁻¹ * G.flow.scalar t x.val - eta < metricScalarAt L.metric y ∧
                        metricScalarAt L.metric y < C2 * G.flow.scalar t x.val + eta) ∧
                    ∀ y : G.terminalRegularOpen,
                      y.val ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) →
                        (1 - 4323 * eps) * G.flow.scalar t v - eta < metricScalarAt L.metric y ∧
                          metricScalarAt L.metric y < (1 + 4323 * eps) * G.flow.scalar t v + eta := by
  obtain ⟨epsCan, hepsCan, hmain⟩ := G.exists_all_point_canonical_neighborhoods_with_cap_neck_charts
  refine ⟨epsCan, hepsCan, ?_⟩
  intro eps heps hsmall
  obtain ⟨C1, C2, q, hC1, hC2, hq, hcanonical⟩ := hmain eps heps hsmall
  refine ⟨C1, C2, q, hC1, hC2, hq, ?_⟩
  intro x hx
  let C : ℝ≥0 := ⟨C2, zero_le_one.trans hC2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    obtain ⟨W, _⟩ := hcanonical y t ⟨ht.1.le, ht.2⟩ hy.le
    exact W.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨K, hK, hcompare⟩ := L.exists_uniform_scalar_comparison_on_cap_neck_windows
    hq hbound hPhi hpinch x (epsCanonical := eps) (C1 := C1) heps.le (zero_le_one.trans hC2)
  refine ⟨K, hK, ?_⟩
  intro eta heta
  obtain ⟨d₀, hd₀, hclose⟩ := hcompare eta heta
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  obtain ⟨d₁, hd₁, hR⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp hhigh
  refine ⟨max d₀ d₁, ⟨hd₀.1.trans (le_max_left _ _), max_lt hd₀.2 hd₁.2⟩, ?_⟩
  intro t ht
  have ht₀ : t ∈ Ioo d₀ s := ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
  have ht₁ : t ∈ Ioo d₁ s := ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩
  obtain ⟨W, hW⟩ := hcanonical x.val t ⟨hd₀.1.trans ht₀.1.le, ht.2⟩ (hR ht₁).le
  refine ⟨W, hW, ?_⟩
  intro cap depth hcap
  obtain ⟨v, nk, hmap, hv, hsub, herr⟩ := hclose t ht₀ W hW cap depth hcap
  refine ⟨v, nk, hmap, hv, hsub, herr, ?_, ?_⟩
  · intro y hy
    have hs := W.scalar_bounds y.val hy
    have he := abs_lt.mp (herr y (Or.inl hy))
    constructor <;> linarith [hs.1, hs.2, he.1, he.2]
  · intro y hy
    have hs := nk.toSpatialNeck.scalar_bounds_on_image_window hy
    have he := abs_lt.mp (herr y (Or.inr hy))
    change (1 - 4323 * eps) * G.flow.scalar t v ≤ G.flow.scalar t y.val ∧
      G.flow.scalar t y.val ≤ (1 + 4323 * eps) * G.flow.scalar t v at hs
    constructor <;> linarith [hs.1, hs.2, he.1, he.2]

theorem TerminalLimitMetric.eventually_ball_subset_cap_core_of_compact_capture
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps : ℝ} {U : ℕ → Set P.Carrier}
    (cap : ∀ n, LocalCap G.flow eps x.val (τ n) (U n))
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, (cap n).core.carrier ⊆ Subtype.val '' K) :
    ∀ᶠ n in atTop,
      riemannianBallOf L.metric x (1000 / Real.sqrt (metricScalarAt L.metric x)) ⊆
        Subtype.val ⁻¹' interior (cap n).core.carrier := by
  obtain ⟨d, hd, hclose⟩ := L.converges K hK 0 1 zero_lt_one
  have htime := hτ.eventually (Ioo_mem_nhdsLT hd.2)
  have hscalar := hτ.eventually ((L.tendsto_metricScalarAt x).eventually_lt_const
    (show metricScalarAt L.metric x < 4 * metricScalarAt L.metric x by linarith))
  have hpositive := hτ.eventually ((L.tendsto_metricScalarAt x).eventually
    (Ioi_mem_nhds hx))
  filter_upwards [hcapture, htime, hscalar, hpositive] with n hcn hn hsn hRn
  change 0 < G.flow.scalar (τ n) x.val at hRn
  change G.flow.scalar (τ n) x.val < 4 * metricScalarAt L.metric x at hsn
  let Q := metricScalarAt L.metric x
  have hQ : 0 < Q := hx
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let gt := (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
  let r : ℝ := 4000 / Real.sqrt Q
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrootn : Real.sqrt (G.flow.scalar (τ n) x.val) ≤ 2 * Real.sqrt Q := by
    have hsn' : G.flow.scalar (τ n) x.val < 4 * Q := hsn
    nlinarith [Real.sq_sqrt hRn.le, Real.sq_sqrt hQ.le,
      Real.sqrt_nonneg (G.flow.scalar (τ n) x.val)]
  have hrsource : r ≤ 10000 / Real.sqrt (G.flow.scalar (τ n) x.val) := by
    dsimp only [r]
    apply (div_le_div_iff₀ hroot (Real.sqrt_pos.mpr hRn)).mpr
    nlinarith
  have hcapBall := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (G.flow.base.metric (τ n)) (cap n).center_inside
    (r := ENNReal.ofReal (10000 / Real.sqrt (G.flow.scalar (τ n) x.val))) (by
      intro y hy
      have hytube : y ∈ (cap n).tube := ((cap n).overlap_eq.symm ▸ hy).2
      exact (ENNReal.ofReal_le_ofReal (depth n y hytube)).trans ENNReal.ofReal_toReal_le)
  have hcore (y : G.terminalRegularOpen)
      (hy : riemannianEDistOf gt x y < ENNReal.ofReal r) :
      y.val ∈ interior (cap n).core.carrier := by
    apply hcapBall
    exact ((riemannianEDistOf_le_restrictOpen (G.flow.base.metric (τ n))
      G.terminalRegularOpen x y).trans_lt hy).trans_le (ENNReal.ofReal_le_ofReal hrsource)
  have hupper (y : G.terminalRegularOpen)
      (hy : riemannianEDistOf gt x y < ENNReal.ofReal r)
      (v : TangentSpace ThreeModel y) : gt.inner y v v ≤ (4 : ℝ) * L.metric.inner y v v := by
    obtain ⟨z, hz, hzy⟩ := hcn (interior_subset (hcore y hy))
    have hyK : y ∈ K := (Subtype.ext hzy : z = y) ▸ hz
    have hb := (DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      L.metric gt y (hclose (τ n) hn y hyK).le v).2
    have hnonneg := DifferentialGeometry.metric_inner_self_nonneg L.metric y v
    nlinarith
  have hball := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_local_quad
    gt L.metric x x hr (by norm_num : (0 : ℝ) < 4)
    (by rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr (half_pos hr)) hupper
  intro y hy
  apply hcore y
  apply hball
  change riemannianEDistOf L.metric x y < ENNReal.ofReal (r / (2 * Real.sqrt 4))
  have hradius : r / (2 * Real.sqrt 4) = 1000 / Real.sqrt Q := by
    dsimp only [r]
    norm_num
    ring
  rw [hradius]
  exact hy


theorem TerminalLimitMetric.eventually_ball_subset_canonical_cap_core
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps C1 C2 : ℝ}
    (W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n))
    (cap : ∀ n, LocalCap G.flow eps x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y) :
    ∀ᶠ n in atTop,
      riemannianBallOf L.metric x (1000 / Real.sqrt (metricScalarAt L.metric x)) ⊆
        Subtype.val ⁻¹' interior (cap n).core.carrier := by
  obtain ⟨epsCan, hepsCan, hcan⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨D1, D2, q, _, hD2, hq, hmodels⟩ := hcan epsCan hepsCan le_rfl
  let C : ℝ≥0 := ⟨D2, zero_lt_one.le.trans hD2⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    exact (hmodels y t ⟨ht.1.le, ht.2⟩ hy.le).some.time_derivative
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨K, hK, hregular, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch (C2 * (metricScalarAt L.metric x + 1))
  let K' : Set G.terminalRegularOpen := Subtype.val ⁻¹' K
  have himage : Subtype.val '' K' = K := by
    ext y
    exact ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, hregular hy⟩, hy, rfl⟩⟩
  have hK' : IsCompact K' := by
    rw [_root_.Topology.IsEmbedding.subtypeVal.isCompact_iff]
    exact himage ▸ hK
  have htime := hτ.eventually (Ioo_mem_nhdsLT hd.2)
  have hscalar := hτ.eventually ((L.tendsto_metricScalarAt x).eventually_lt_const
    (lt_add_one (metricScalarAt L.metric x)))
  apply L.eventually_ball_subset_cap_core_of_compact_capture hτ x hx cap depth hK'
  filter_upwards [htime, hscalar] with n hn hsn
  intro y hy
  rw [himage]
  apply hcapture (τ n) hn y
  have hC2 : 0 ≤ C2 := zero_le_one.trans (W n).one_le_comparison_constant
  exact ((W n).scalar_bounds y (interior_subset ((cap n).core_inside hy))).2.trans
    (mul_le_mul_of_nonneg_left hsn.le hC2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
