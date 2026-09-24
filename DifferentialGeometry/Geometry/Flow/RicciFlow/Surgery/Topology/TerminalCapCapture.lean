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
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

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
  intro t ht W
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
    exact ((W.scalar_bounds y hy).2.trans (mul_le_mul_of_nonneg_left hR hC2)).trans hCB
  · intro v hv nk y hy
    rw [himage]
    apply hcapture t ht₀
    have hs := (nk.toSpatialNeck.scalar_bounds_on_image_window hy).2
    exact hs.trans (mul_le_mul_of_nonneg_left
      ((W.scalar_bounds v hv).2.trans (mul_le_mul_of_nonneg_left hR hC2)) (by positivity))

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
              (∀ z, cap.tube_map z = nk.map z) ∧ v ∈ cap.tube ∧
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
              (∀ z, cap.tube_map z = nk.map z) ∧ v ∈ cap.tube ∧
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
                    (∀ z, cap.tube_map z = nk.map z) ∧ v ∈ cap.tube ∧
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
