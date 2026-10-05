import DifferentialGeometry.Geometry.Fibration.ActualStageChainEReplacement
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualReplacementEdgeBall

/-!
# FDC03's chain clauses: vertical set, `E`-fibre constancy, the open edge candidate and coverage

Blueprint `master207B.tex`, FDC03 (`thm:fibration-actual-circle-remainder`, B:7285–7365), the
clauses that read the final map `E` of ONE chain, and the EDP02 inputs they use (B:6748–6835:
"on the full preimage … `X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`", "the original closed smaller sets
`{|η_i| ≤ 3.5Δ, t ≤ 3.5Δ}` lie in the ambient interior of `X₂`", "`B₂` is open … each patch has
`v_i = R_i`"), with `W₂` dropped. Conventions of lane C14-EDP-E (`A`, `s`, `T = A/s`, `V`); the
EDGE CANDIDATE is `X₂° = {T < 4Δ} ∩ {x | ∃ k, v_k(E x) = R_k, |u_k(E x)| < 4ΔR_k}`.

* `fdc03_height_numbers_FDC` (numbers); `Gaf02Chain.height_lt_of_low_FDC` (`t ≤ 3.6Δ ⇒ T < 4Δ`,
  with the chain's `c₀, c₃ ≤ 1/512` only); `Gaf02Chain.vertical_eq_FDC` (`V = {T ≤ 4Δ}` on all of
  `X`, no extra numeric hypothesis); `Gaf02Chain.fibre_constancy_FDC` (`E p = E p'` ⇒ equal `s`,
  `T`, `V`-membership and witnessed-base membership: the inputs of
  `EdgeDisk.relativeRemoval_saturated`); `Gaf02Chain.edge_vector_lt_FDC` (`ζ_j = 1` in `U_j` ⇒
  `|u_j(E q)| < (|η_j(q)| + 1.0001/512)R_j`).
* On `Gaf02ChainE`: `isOpen_edgeCandidate_FDC` (`X₂°` is OPEN: at a point, FDC02's limit-point
  lemma localizes in `U_k`, and GAF05's plateau clause keeps the marker exact on the open plateau);
  `smaller_set_interior_FDC` (`{|η_k| ≤ 3.5Δ, t ≤ 3.5Δ} ∩ U_k ⊆ int X₂°`); `fdc03_coverage_FDC`
  (every point is zero-stratum, in a circle ball `B(j, 2ρ_j)`, in a slim ball `B(j, 2Δρ_j)`, or in
  `int X₂°`: FDC03's coverage "any nonslim one-stratum point … EDP02 puts a full ambient
  neighborhood of that point in `X₂`", with the family's exhaustion `fdc03_edge_alternative_FDC1`).

NOT here: `int Z`, `int_{M₁} M^slim` (ZSP02, GAF07), `X₁` (GAF07), `W₂` (BASES), the converse
"relative interior ⇒ `T < 4Δ`" (EDP05's face charts), the circle-bundle structure of `M₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The low height numbers of EDP02: `F ≤ aΔr` (`a ≤ 3.6`), `A < F + c₂r`, `s > (1 − c₀)r`,
`c₀, c₂ ≤ 1/512`, `Δ ≥ 1` give `A < 4Δs`. -/
theorem fdc03_height_numbers_FDC {Δ r F A s c₀ c₂ a : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (ha : a ≤ 36 / 10) (hF : F ≤ a * Δ * r)
    (hA : A < F + c₂ * r) (hs : (1 - c₀) * r < s) : A < 4 * Δ * s := by
  have h1 : 4 * Δ * ((1 - c₀) * r) ≤ 4 * Δ * s := mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : a * (Δ * r) ≤ 36 / 10 * (Δ * r) := mul_le_mul_of_nonneg_right ha (by positivity)
  nlinarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **EDP02's low inequality on the chain**: `t(p) ≤ 3.6Δ` gives `T(p) < 4Δ` (only the chain's
`c₀, c₃ ≤ 1/512`, `Δ ≥ 1`). -/
theorem height_lt_of_low_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {p : X}
    (ht : P.edge.smoothing p / ρ p ≤ 36 / 10 * Δ) :
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
      C.scale p < 4 * Δ := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨-, -, hc0, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hrp := hρ p
  have hsp := (C.scale_pos p).2
  have hs : (1 - c 0) * ρ p < C.scale p := by
    have := (abs_lt.mp (C.scale_pos p).1).1
    linarith
  rw [div_lt_iff₀ hsp]
  have hF : P.edge.smoothing p ≤ 36 / 10 * Δ * ρ p := by
    rwa [div_le_iff₀ hrp] at ht
  exact fdc03_height_numbers_FDC hΔ hrp hc0 hc2 le_rfl hF (C.heightAxis_value_EDPE p).2 hs

/-- **The vertical set of (ED) is `{T ≤ 4Δ}`** on all of `X` (EDP02's set equality, here without
any numeric hypothesis beyond the chain's own). -/
theorem vertical_eq_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} =
    {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} := by
  obtain ⟨-, hΔ, -⟩ := C.std
  ext p
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact (C.height_lt_of_low_FDC (by linarith)).le
    · exact h.2
  · exact fun h => Or.inr ⟨(C.scale_pos p).2, h⟩

/-- **`E`-fibre constancy** (FDC03, B:7337–7346): `E p = E p'` gives equal `s`, equal `T`, equal
`V`-membership and equal witnessed-base membership (`∃ k, v_k(E·) = R_k, |u_k(E·)| < 4ΔR_k`). -/
theorem fibre_constancy_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {p p' : X}
    (h : C.E p = C.E p') :
    C.scale p = C.scale p' ∧
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p =
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p')) /
        C.scale p' ∧
    (p ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} ↔
      p' ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) ∧
    ((∃ k : P.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E p) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E p)‖ < 4 * Δ * ρ k.1) ↔
      ∃ k : P.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E p') = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.E p')‖ < 4 * Δ * ρ k.1) := by
  have hs : C.scale p = C.scale p' := by
    change gafScaleMarker P.toLocalChartFamily P.zero (C.E p) =
      gafScaleMarker P.toLocalChartFamily P.zero (C.E p')
    rw [h]
  have hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p =
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p')) /
        C.scale p' := by
    rw [h, hs]
  refine ⟨hs, hT, ?_, by rw [h]⟩
  rw [C.vertical_eq_FDC]
  simp only [mem_ofPred_eq]
  rw [hT]

/-- **The final edge vector at a full original cutoff** in `U_j`:
`|u_j(E q)| < (|η_j(q)| + 1.0001/512)R_j`. -/
theorem edge_vector_lt_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X} (hball : q ∈ ball j.1 (100 * Δ * ρ j.1))
    (hζ : P.edge.cutoff j.1 q = 1) :
    ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ < (|P.edge.coord j.1 q| + 10001 / 5120000) * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hc2pos : 0 < c 2 := by
    obtain ⟨h0, h1, h2⟩ := C.accuracy_order_EDPE
    linarith
  have hrj := hρ j.1
  have hρq : ρ q ≤ (1 + 1 / 10000) * ρ j.1 := by
    have h1 := (abs_le.mp (scale_ratio_ball_EDPE P hΛ hball)).2
    have h2 : 100 * Δ * Λ ≤ 1 / 10000 := by nlinarith
    have h4 : ρ q / ρ j.1 ≤ 1 + 1 / 10000 := by linarith
    rwa [div_le_iff₀ hrj] at h4
  have hk : c 2 * ρ q ≤ 10001 / 5120000 * ρ j.1 := by
    have h1 := mul_le_mul_of_nonneg_left hρq hc2pos.le
    have h2 : c 2 * ((1 + 1 / 10000) * ρ j.1) ≤ 1 / 512 * ((1 + 1 / 10000) * ρ j.1) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    linarith
  have herr := C.stage_error_lt.2.2 q
  have hblk := cgpGlobalMap_edgeBlock P.toLocalChartFamily P.zero j q
  have hv0 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ =
        |P.edge.coord j.1 q| * ρ j.1 := by
    rw [blockVectorCLM_apply]
    change ‖(cgpGlobalMap P.toLocalChartFamily P.zero q
      (cgpEdgeBlockTag P.toLocalChartFamily P.zero j)).fst‖ = _
    rw [hblk.1, hζ, mul_one, norm_smul, norm_planeAxis, Real.norm_eq_abs, abs_of_pos hrj, mul_comm]
  have hvd : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) - blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ ≤
      ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ := by
    rw [← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_blockVectorCLM_le _) (norm_nonneg _))
  have htri := norm_le_insert' (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
    ℝ²) (.inr (.inr (.inl j))) (C.E q)) (blockVectorCLM (V := fun _ : CGPTag
      P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j)))
        (cgpGlobalMap P.toLocalChartFamily P.zero q))
  rw [hv0] at htri
  linarith

end Gaf02Chain

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The edge candidate `X₂°` is open** (EDP02's openness of the base patches, `W₂` dropped). -/
theorem isOpen_edgeCandidate_FDC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    IsOpen ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
        (C.toChain.E x)) / C.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  have hTc := C.toChain.final_smooth_EDPE.2.2.2.1.continuous
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hxT, k, hv, hu⟩
  have hxT' : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
      (C.toChain.E x)) / C.toChain.scale x < 4 * Δ := hxT
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  obtain ⟨hball, hη, ht, -⟩ := C.toChain.fdc02_limit_point_FDC k hv hu.le
    (Or.inr ⟨(C.toChain.scale_pos x).2, hxT'.le⟩)
  obtain ⟨-, hΔ, -⟩ := C.toChain.std
  refine ⟨{y | y ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |P.edge.coord k.1 y| < 6 * Δ ∧
      -1 < P.edge.smoothing y / ρ y ∧ P.edge.smoothing y / ρ y < 6 * Δ} ∩
    {y | ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E y)‖ < 4 * Δ * ρ k.1} ∩
    {y | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
        (C.toChain.E y)) / C.toChain.scale y < 4 * Δ}, ?_, ?_, ?_⟩
  · rintro y ⟨⟨⟨hyb, hyη, -, hyt⟩, hyu⟩, hyT⟩
    exact ⟨hyT, k, C.gaf05_edge_plateau_G47 k hyb hyη hyt, hyu⟩
  · exact (((isOpen_edgeBand_EDPE P.toLocalChartPackets hk (6 * Δ) (-1) (6 * Δ)).inter
      (isOpen_lt (C.toChain.continuous_edgeVector_FDC k) continuous_const)).inter
      (isOpen_lt hTc continuous_const))
  · refine ⟨⟨⟨hball, by linarith, ?_, by linarith⟩, hu⟩, hxT⟩
    have := cgpHeight_nonneg P.toLocalChartFamily x
    change -1 < cgpHeight P.toLocalChartFamily x
    linarith

/-- **EDP02's interior clause, `W₂` dropped**: `{|η_k| ≤ 3.5Δ, t ≤ 3.5Δ} ∩ U_k ⊆ int X₂°`. -/
theorem smaller_set_interior_FDC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (k : P.toLocalChartFamily.edge.finite_centres.toFinset) {x : X}
    (hball : x ∈ ball k.1 (100 * Δ * ρ k.1)) (hη : |P.edge.coord k.1 x| ≤ 35 / 10 * Δ)
    (ht : P.edge.smoothing x / ρ x ≤ 35 / 10 * Δ) :
    x ∈ interior ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (C.toChain.E x)) / C.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  obtain ⟨-, hΔ, -⟩ := C.toChain.std
  have hΔ0 : 0 < Δ := by linarith
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  rw [C.isOpen_edgeCandidate_FDC.interior_eq]
  have hζ := edge_cutoff_eq_one_EDPE P.toLocalChartPackets hΔ0 hk hball (by linarith)
    (by linarith)
  have hu := C.toChain.edge_vector_lt_FDC k hball hζ
  have hrk := hρ k.1
  refine ⟨C.toChain.height_lt_of_low_FDC (by linarith), k,
    C.gaf05_edge_plateau_G47 k hball (by linarith)
      (by change P.edge.smoothing x / ρ x < 6 * Δ; linarith), ?_⟩
  have h1 : (|P.edge.coord k.1 x| + 10001 / 5120000) * ρ k.1 ≤ 4 * Δ * ρ k.1 :=
    mul_le_mul_of_nonneg_right (by linarith) hrk.le
  linarith

/-- **FDC03's coverage on the chain** (B:7322–7335, `W₂` dropped): every point is zero-stratum, in
a circle ball `B(j, 2ρ_j)`, in a slim ball `B(j, 2Δρ_j)`, or in the interior of `X₂°`. -/
theorem fdc03_coverage_FDC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hσc : σc ≤ 1 / 2) (x : X) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
      (∃ j ∈ P.circle.centres, x ∈ ball j (2 * ρ j)) ∨
      (∃ j ∈ P.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
      x ∈ interior ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (C.toChain.E x)) / C.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  obtain ⟨hΛ, hΔ, hμ, -, hLΛ, -⟩ := C.toChain.std
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  rcases fdc03_edge_alternative_FDC1 P.toLocalChartFamily hΔ0 hσc hμ hΛ hΔΛ x with
    h | h | h | ⟨j, hj, hd, hη, ht, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hball : x ∈ ball j (100 * Δ * ρ j) := by
      rw [mem_ball]
      have := hρ j
      nlinarith
    exact C.smaller_set_interior_FDC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ hball
      (by linarith) (by change cgpHeight P.toLocalChartFamily x ≤ 35 / 10 * Δ; linarith)

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
