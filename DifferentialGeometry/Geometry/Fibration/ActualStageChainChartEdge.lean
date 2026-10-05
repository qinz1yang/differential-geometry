import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartTools
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches
import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# GAF02 BASES on the chain: CGP06 and CGP07 for the edge charts (stage two)

Blueprint `master207B.tex`, CGP06 (B:4130–4174), CGP07 (B:4176–4247); external draft 59 §4, third
to fifth steps (D59-5); review 66 §5.4 (D66-7); review 71 D71-2 (one rough-graph choice), D71-4
(the edge stage's own one-dimensional adapter and its four bindings). Indexed by ONE chain
`C : Gaf02Chain P.toLocalChartPackets …` and its rough data `R`. Edge retained coordinates are the
ACTUAL one-dimensional axis coordinate `u_j = axisCoordCLM_BAS ∘ gafEdgeVector j`.

* One-dimensional adapters (D71-4): `exists_bounded_preimage_line_BAS` (unit witness ⇒ bounded
  preimages + homogeneous normal error) and `retained_coordinate_of_unit_pp_BAS` (the unit-vector
  (PP) + rough-graph error at the same preimage ⇒ CGP06's `‖v‖ ≤ 2Ω‖π v‖` on the line).
* Generic: `cgp07_of_cfs15_BAS` (CGP07 for any CFS15 stage output with its own local graphs).
* `edge_section_BAS` (CGP03's edge inner section, extended to `ℝ`).
* Given ONE rough graph `(sgn, cc)` with EGP06's clause: `Gaf02Chain.cgp06_edge_of_graph_BAS`,
  `Gaf02Chain.cgp07_edge_of_graph_BAS` (with the input lemmas `edge_chart_inputs_BAS`,
  `edge_section_inputs_BAS`, `edge_assemble_BAS`); from `R` alone: `Gaf02Chain.cgp06_edge_BAS`,
  `Gaf02Chain.cgp07_edge_BAS` (`R_j⁻¹u_j : V_j⁰ → (-5.5Δ, 5.5Δ)` bijective, exhaustion by the
  ORIGINAL threshold-6 plateau `|η_j| < 6Δ`, `t < 6Δ`, smooth inverse chart, compact preimages).

D71-4 bindings: (i) (PP) and the rough graph are used at the SAME preimage `q`
(`cgp06_edge_of_graph_BAS`: `C.test1`'s clause at `q` and `hcl q`); (ii) the reference scales
`ρ_i`, `ρ_j` are unified by rescaling the unit vector (`hD`, `hwu` there); (iii) `π T = id` by the
chain rule on the rough graph (`clm_fderiv_of_left_inverse_BAS` + `egp06_model`'s own block);
(iv) `‖T‖ ≤ egpGraphConst ≤ Ω` at every point and the error at every point of the thickened chart
domain `B(c_j, 100Δρ_j) ∩ {|η_j| ≤ 8Δ, t ≤ 8Δ}`, applied at every section point
(`edge_chart_inputs_BAS`).
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

/-- **CGP06 for a line from the unit-vector (PP)** (the edge stage's form): `L` one-dimensional,
`d₀ = D w` for a unit vector with `‖π_L d₀‖ ≥ 1/2` and normal error `< e`, the rough graph's error
`‖d₀ − T y₀‖ < e` (`y₀ = Dη w`), `pr T = I`, `‖T‖ ≤ Ω`, `8e(1+Ω) ≤ 1` ⇒ `‖v‖ ≤ 2Ω‖pr v‖` on `L`. -/
theorem retained_coordinate_of_unit_pp_BAS {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℝ H)
    [L.HasOrthogonalProjection] (hL : Module.finrank ℝ L = 1) (pr : H →L[ℝ] E) (hpr : ‖pr‖ ≤ 1)
    (Tm : E →L[ℝ] H) (hprT : ∀ y, pr (Tm y) = y) {e Ω : ℝ} (hT : ∀ y, ‖Tm y‖ ≤ Ω * ‖y‖)
    (d0 : H) (y0 : E) (hv : 1 / 2 ≤ ‖L.starProjection d0‖)
    (hclose : ‖d0 - L.starProjection d0‖ < e) (hrough : ‖d0 - Tm y0‖ < e) (hΩ : 1 ≤ Ω)
    (hsmall : 8 * e * (1 + Ω) ≤ 1) :
    ∀ v ∈ L, ‖v‖ ≤ 2 * Ω * ‖pr v‖ := by
  set v₀ := L.starProjection d0 with hv₀
  have hv₀L : v₀ ∈ L := Submodule.starProjection_apply_mem L d0
  have he : 0 < e := lt_of_le_of_lt (norm_nonneg _) hclose
  -- the bound at `v₀`
  have hclose2 : ‖v₀ - Tm y0‖ < 2 * e := by
    have h := norm_sub_le (d0 - Tm y0) (d0 - v₀)
    rw [show d0 - Tm y0 - (d0 - v₀) = v₀ - Tm y0 by abel] at h
    linarith
  have hpr0 : ‖y0‖ - 2 * e ≤ ‖pr v₀‖ := by
    have h1 : pr v₀ = y0 + pr (v₀ - Tm y0) := by rw [map_sub, hprT]; abel
    have h2 : ‖pr (v₀ - Tm y0)‖ ≤ 2 * e :=
      (pr.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hpr).trans hclose2.le)
    have h3 : ‖y0‖ ≤ ‖pr v₀‖ + ‖pr (v₀ - Tm y0)‖ := by
      have := norm_sub_le (pr v₀) (pr (v₀ - Tm y0))
      rwa [show pr v₀ - pr (v₀ - Tm y0) = y0 by rw [h1]; abel] at this
    linarith
  have hv₀up : ‖v₀‖ ≤ Ω * ‖y0‖ + 2 * e := by
    have h := norm_add_le (Tm y0) (v₀ - Tm y0)
    rw [add_sub_cancel] at h
    linarith [hT y0]
  have hΩ0 : 0 < Ω := by linarith
  have key : ‖v₀‖ ≤ 2 * Ω * ‖pr v₀‖ := by
    have h1 : Ω * (‖y0‖ - 2 * e) ≤ Ω * ‖pr v₀‖ := mul_le_mul_of_nonneg_left hpr0 hΩ0.le
    nlinarith
  -- every vector of the line is a multiple of `v₀`
  have hne : (⟨v₀, hv₀L⟩ : L) ≠ 0 := by
    intro h
    have h' : v₀ = 0 := congrArg Subtype.val h
    rw [h', norm_zero] at hv
    linarith
  intro v hv
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v₀, hv₀L⟩ : L) hne).mp hL ⟨v, hv⟩
  have hvt : v = t • v₀ := (congrArg Subtype.val ht).symm
  rw [hvt, norm_smul, map_smul, norm_smul]
  have := norm_nonneg t
  nlinarith

/-- **The one-dimensional (PP) adapter** (review 71 D71-4, edge stage): `L` one-dimensional,
`P_m : V → L` linear, a unit vector `w₀` (`N w₀ = 1`, `N` absolutely homogeneous) with
`‖P_m w₀‖ ≥ 1/2` and normal error `‖D w₀ − P_m w₀‖ ≤ e` ⟹ every `v ∈ L` has a preimage `w`
(a multiple of `w₀`) with `N w ≤ 2‖v‖`, and the normal error extends by homogeneity:
`‖D w − P_m w‖ ≤ e N(w)`. -/
theorem exists_bounded_preimage_line_BAS {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : Submodule ℝ H) (hL : Module.finrank ℝ L = 1)
    (Pm D : V →ₗ[ℝ] H) (hPL : ∀ w, Pm w ∈ L) (N : V → ℝ) (hN : ∀ (t : ℝ) w, N (t • w) = |t| * N w)
    {e : ℝ} (w₀ : V) (hN₀ : N w₀ = 1) (hP₀ : 1 / 2 ≤ ‖Pm w₀‖) (hD₀ : ‖D w₀ - Pm w₀‖ ≤ e) :
    ∀ v ∈ L, ∃ w, Pm w = v ∧ N w ≤ 2 * ‖v‖ ∧ ‖D w - Pm w‖ ≤ e * N w := by
  have hne : (⟨Pm w₀, hPL w₀⟩ : L) ≠ 0 := by
    intro h
    have h' : Pm w₀ = 0 := congrArg Subtype.val h
    rw [h', norm_zero] at hP₀
    linarith
  intro v hv
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (⟨Pm w₀, hPL w₀⟩ : L) hne).mp hL ⟨v, hv⟩
  have hvt : t • Pm w₀ = v := congrArg Subtype.val ht
  refine ⟨t • w₀, by rw [map_smul, hvt], ?_, ?_⟩
  · rw [hN, hN₀, mul_one, ← hvt, norm_smul, Real.norm_eq_abs]
    have := abs_nonneg t
    nlinarith
  · rw [map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, hN, hN₀, mul_one]
    have := abs_nonneg t
    nlinarith

/-- Numeric helper (CGP07's `r_x ≥ (9/20)ΣR`): `3ρ_q/5 ≤ ρ_s`, `3ρ_j/4 ≤ ρ_q`, `0 ≤ Σ`. -/
theorem nine_twenty_le_BAS {Sg ρj ρq ρs : ℝ} (hS : 0 ≤ Sg) (h1 : 3 / 5 * ρq ≤ ρs)
    (h2 : 3 / 4 * ρj ≤ ρq) : 9 / 20 * Sg * ρj ≤ Sg * ρs := by
  have h : 9 / 20 * ρj ≤ ρs := by linarith
  calc 9 / 20 * Sg * ρj = Sg * (9 / 20 * ρj) := by ring
    _ ≤ Sg * ρs := mul_le_mul_of_nonneg_left h hS

/-- Numeric helper (CGP07's `r_x/4 ≤ ρ`): `0 < Ξ ≤ 1/10`, `0 ≤ x` ⇒ `x/4 ≤ 3Ξ⁻¹x`. -/
theorem quarter_le_three_inv_mul_BAS {Ξ x : ℝ} (hΞ : 0 < Ξ) (hΞ1 : Ξ ≤ 1 / 10) (hx : 0 ≤ x) :
    x / 4 ≤ 3 * Ξ⁻¹ * x := by
  have hinv : 10 ≤ Ξ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hΞ]
    linarith
  nlinarith

/-- Numeric helper (CGP06 ⇒ the lower bound `m = 1/(2Ω)`). -/
theorem inv_two_mul_le_of_le_BAS {Ω x y : ℝ} (hΩ : 0 < Ω) (h : x ≤ 2 * Ω * y) :
    1 / (2 * Ω) * x ≤ y := by
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- The closed `1/100`-balls about the targets of `(-5.5Δ, 5.5Δ)` stay in `|y| < 6Δ`, `|y| ≤ 8Δ`
and in the edge section's domain `(-17Δ/2, 17Δ/2)` (`Δ ≥ 1`). -/
theorem edge_ball_sub_BAS {Δ : ℝ} (hΔ : 1 ≤ Δ) : ∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
    ∀ y ∈ closedBall a (1 / 100),
      |y| < 6 * Δ ∧ |y| ≤ 8 * Δ ∧ y ∈ Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) := by
  intro a ha y hy
  rw [mem_ball_zero_iff, Real.norm_eq_abs] at ha
  rw [mem_closedBall, Real.dist_eq] at hy
  have h1 : |y| ≤ |y - a| + |a| := by
    have := abs_sub_abs_le_abs_sub y a
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_lt] at ha
  rw [abs_le] at hy
  constructor <;> linarith

/-- A continuous map on a set, extended to the whole space (`dite`), continuous on the set. -/
theorem exists_set_extension_BAS {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {U : Set E} (y₀ : Y) (sec : U → Y) (hsec : Continuous sec) :
    ∃ secE : E → Y, ContinuousOn secE U ∧ ∀ b (hb : b ∈ U), secE b = sec ⟨b, hb⟩ := by
  classical
  refine ⟨fun b => if hb : b ∈ U then sec ⟨b, hb⟩ else y₀, ?_, fun b hb => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hsec using 1
    funext b
    exact dite_eq_left b.2
  · exact dite_eq_left hb

/-- **CGP07 for a CFS15 stage output** (`cgp07_one_sheet_BPRE` with `Z = O.Z` and the output's
own local graphs at the centres `x a ∈ S`, radius `3ε⁻¹r_{x a}`): the retained-coordinate lower
bound `1/(2Ω)` on the planes `P (x a)` (CGP06) above the native slope `ε/3`, `dim P (x a) = dim E`,
the rough graph `Φ` (slope `≤ Ω`), (OS), the centres' value error and `r_{x a} ≥ (9/20)ΣR`,
(MW), and the inner-section data give CGP07's conclusions on `V = markedPatch O.Z u v R ℓ`. -/
theorem cgp07_of_cfs15_BAS {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} {k K : ℕ} {ε cw : ℝ} {Sc T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}
    (O : Cfs15StageOutput k K ε cw Sc T r P) (u : H →L[ℝ] E) (hu : ‖u‖ ≤ 1) (v : H →L[ℝ] ℝ)
    (hv : ‖v‖ ≤ 1) {R ℓ Ω e Sg c : ℝ} (hR : 0 < R) (hΩ : 1 ≤ Ω) (hS : 0 < Sg)
    (he : e ≤ Sg / 1000) (hε : ε ≤ 1 / (1000 * (Ω + 1))) (hεm : ε / 3 < 1 / (2 * Ω))
    (Φ : E → H) (hΦd : ∀ b, DifferentiableAt ℝ Φ b) (hΦb : ∀ b, ‖fderiv ℝ Φ b‖ ≤ Ω)
    (x : E → H) (hxS : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), x a ∈ Sc)
    (hxv : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ‖R⁻¹ • x a - Φ a‖ ≤ e)
    (hxr : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), 9 / 20 * Sg * R ≤ r (x a))
    (hm : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ w ∈ P (x a), 1 / (2 * Ω) * ‖w‖ ≤ ‖u w‖)
    (hdim : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), Module.finrank ℝ (P (x a)) = Module.finrank ℝ E)
    (hMW : ∀ w ∈ markedPatch_BPRE O.Z u v R ℓ, ∃ (y : H) (sw : E),
      ‖R⁻¹ • y - Φ sw‖ ≤ e ∧ u y = R • sw ∧ ‖w - y‖ ≤ 25 / 12 * ε * Sg * R)
    (f F' : M → H) (sec : E → M) (ρM : M → ℝ) (B6 : Set M) (hc : 0 ≤ c)
    (hsmall : 5 / 4 * c ≤ 1 / 100) (hsmall' : 5 / 4 * c < 1 / 10)
    (hcont : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ),
      ContinuousOn (fun b => f (sec b)) (closedBall a (1 / 100)))
    (hsec : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a (1 / 100),
      u (F' (sec b)) = R • b ∧ v (F' (sec b)) = R)
    (herr : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a (1 / 100),
      ‖f (sec b) - F' (sec b)‖ ≤ c * ρM (sec b))
    (hρ : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a (1 / 100), ρM (sec b) ≤ 5 / 4 * R)
    (hplat : ∀ a ∈ ball (0 : E) (11 / 2 * ℓ), ∀ b ∈ closedBall a (1 / 100),
      sec b ∈ B6 ∧ f (sec b) ∈ O.Z) :
    BijOn (R⁻¹ • u) (markedPatch_BPRE O.Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
    (∀ w ∈ markedPatch_BPRE O.Z u v R ℓ, ∃ p ∈ B6, f p = w) ∧
    ∃ φ : E → H, ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * ℓ)) ∧
      InvOn φ (R⁻¹ • u) (markedPatch_BPRE O.Z u v R ℓ) (ball 0 (11 / 2 * ℓ)) ∧
      MapsTo φ (ball 0 (11 / 2 * ℓ)) (markedPatch_BPRE O.Z u v R ℓ) ∧
      ∀ K ⊆ ball (0 : E) (11 / 2 * ℓ), IsCompact K →
        IsCompact (markedPatch_BPRE O.Z u v R ℓ ∩ (R⁻¹ • u) ⁻¹' K) := by
  have hε0 : 0 ≤ ε := O.eps_pos.le
  have hinv : 10 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) O.eps_pos]
    linarith [O.eps_le]
  refine cgp07_one_sheet_BPRE O.Z u hu v hv hR hΩ hS he hε0 hε Φ convex_univ (fun b _ => hΦd b)
    (fun b _ => hΦb b) x (fun a => r (x a)) (fun a => 3 * ε⁻¹ * r (x a)) (fun a ha => ?_)
    (fun a ha => cfs15_hgraph_BAS O u ⟨x a, hxS a ha⟩ (hm a ha) hεm (hdim a ha))
    (fun w hw => ?_) f F' sec ρM B6 hc hsmall hsmall' hcont hsec herr hρ hplat
  · have hr : 0 ≤ r (x a) := (O.radius_pos _ (hxS a ha)).le
    refine ⟨mem_univ a, hxv a ha, hxr a ha, ?_⟩
    nlinarith
  · obtain ⟨y, sw, h1, h2, h3⟩ := hMW w hw
    exact ⟨y, sw, mem_univ sw, h1, h2, h3⟩

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The edge inner section, extended to `ℝ`** (`edge_section_FAM` + CGP03's edge point): on
`|b| ≤ 8Δ`: `η_j(s b) = b`, `t(s b) < Δ/100`, `s b ∈ B(c_j, 100Δρ_j)`, `ζ_j(s b) = 1`,
`ρ(s b) ∈ [3ρ_j/4, 5ρ_j/4]`; continuous on `(-17Δ/2, 17Δ/2)`. -/
theorem edge_section_BAS (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hbud : Λ * (10 * Δ) ≤ 1 / 4)
    (j : P.edge.finite_centres.toFinset) :
    ∃ secE : ℝ → X, ContinuousOn secE (Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ)) ∧ ∀ y : ℝ,
      |y| ≤ 8 * Δ → P.edge.coord j.1 (secE y) = y ∧
        cgpHeight P.toLocalChartFamily (secE y) < Δ / 100 ∧
        secE y ∈ ball j.1 (100 * Δ * ρ j.1) ∧ P.edge.cutoff j.1 (secE y) = 1 ∧
        3 / 4 * ρ j.1 ≤ ρ (secE y) ∧ ρ (secE y) ≤ 5 / 4 * ρ j.1 := by
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨sec, hsc, hs⟩ := P.edge_section_FAM hj
  obtain ⟨secE, hcont, heq⟩ := exists_set_extension_BAS j.1 sec hsc
  refine ⟨secE, hcont, fun y hy => ?_⟩
  have hmem : y ∈ Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) := by
    rw [abs_le] at hy
    constructor <;> linarith
  rw [heq y hmem]
  obtain ⟨hco, -, hht, hd⟩ := hs ⟨y, hmem⟩
  have hpt := cgp03_edge_point P.toLocalChartFamily hΔ hΛ hbud hj (x := sec ⟨y, hmem⟩)
    (by rw [hco]; exact hy) (by linarith) hd
  exact ⟨hco, hht, hpt⟩

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **CGP06 on the chain, edge stage, for ONE chosen rough graph** (review 71 D71-2: the edge
rough graph `(sgn, cc)` and its EGP06 clause are inputs, so CGP06 and CGP07 use the same choice): at a point `x` of the edge cloud and a preimage `q`
(`π₂𝓔⁰ q = x`) in the edge chart `j` with `|η_j(q)| ≤ 8Δ` and `t(q) ≤ 8Δ`, every vector of the
chain's (one-dimensional) plane `L_x` has `‖v‖ ≤ 2Ω|u_j v|` (`u_j` = the ACTUAL axis coordinate of
the edge block). Inputs: `C.test1`'s unit-vector (PP) at `q`, EGP06's rough graph (`R.edge`, the
model's own block and slope from `egp06_model`), `R.os 1`. -/
theorem cgp06_edge_of_graph_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (sgn cc : CGPTag P.toLocalChartFamily P.zero → ℝ) (hsgn : ∀ t, |sgn t| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (100 * Δ * ρ j.1), |P.edge.coord j.1 x| ≤ 8 * Δ →
      cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) x -
          egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc (P.edge.coord j.1 x)‖ < eg 1 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j.1)⁻¹ ^ 2 * g.inner x w w = 1 →
          ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
            fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc)
              (P.edge.coord j.1 x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) x w)‖ < eg 1)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x)
    (hqj : q ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 q| ≤ 8 * Δ)
    (ht : cgpHeight P.toLocalChartFamily q ≤ 8 * Δ) :
    ∀ v ∈ C.plane 1 x, ‖v‖ ≤ 2 * gafGraphOmega_BAS *
      ‖axisCoordCLM_BAS (gafEdgeVector P.toLocalChartFamily P.zero j v)‖ := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, hT, -⟩ := C.std
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨-, hrough⟩ := hcl q hqj hη ht
  obtain ⟨hΦs, hΦown, -, hΦbd⟩ := egp06_model P.toLocalChartPacketsR hΛ hΔ hLΛ hμ hτ he hT hj sgn cc
    hsgn
  obtain ⟨i, -, hPP⟩ := C.test1.2.2.1 x hx
  obtain ⟨hnormal, -, ⟨w₀, hw₀u, hw₀⟩, -⟩ := hPP q hq
  have hρi := hρ i
  have hρj := hρ j.1
  -- the unit vector rescaled from the reference `i` to the chart `j`
  have hD : (ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ2Tags P.toLocalChartFamily P.zero)) q ((ρ j.1 / ρ i) • w₀) =
      (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀ := by
    rw [map_smul, smul_smul]
    congr 1
    field_simp
  have hwu : (ρ j.1)⁻¹ ^ 2 * g.inner q ((ρ j.1 / ρ i) • w₀) ((ρ j.1 / ρ i) • w₀) = 1 := by
    have hg : g.inner q ((ρ j.1 / ρ i) • w₀) ((ρ j.1 / ρ i) • w₀) =
        (ρ j.1 / ρ i) ^ 2 * g.inner q w₀ w₀ := by
      simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hg, ← hw₀u]
    field_simp
  have hr := hrough _ hwu
  rw [hD] at hr
  have hown : ∀ a, (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc a) = a := by
    intro a
    rw [ContinuousLinearMap.comp_apply, gafEdgeVector, blockVectorCLM_apply, hΦown j rfl a]
    exact axisCoordCLM_planeAxis_BAS a
  have hpr : ‖axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)‖ ≤ 1 := by
    have h1 := norm_axisCoordCLM_le_BAS
    have h2 := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      change ‖axisCoordCLM_BAS‖ * ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)‖ ≤ 1
      nlinarith [norm_nonneg axisCoordCLM_BAS, norm_nonneg (blockVectorCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero))])
  have hL : Module.finrank ℝ (C.plane 1 x) = 1 := (C.test1.1 x hx).1
  exact retained_coordinate_of_unit_pp_BAS (C.plane 1 x) hL _ hpr _
    (clm_fderiv_of_left_inverse_BAS _ ((hΦs.differentiable (by simp)) _) hown)
    (fun y => ((fderiv ℝ _ _).le_opNorm y).trans (mul_le_mul_of_nonneg_right
      ((hΦbd _).1.trans egpGraphConst_le_gafGraphOmega_BAS) (norm_nonneg y)))
    _ _ hw₀ (hnormal w₀ hw₀u) hr one_le_gafGraphOmega_BAS (os_small_BAS R 1)

/-- **CGP06 on the chain, edge stage**: at a point `x` of the edge cloud and a preimage `q`
(`π₂𝓔⁰ q = x`) in the edge chart `j` with `|η_j(q)| ≤ 8Δ` and `t(q) ≤ 8Δ`, every vector of the
chain's (one-dimensional) plane `L_x` has `‖v‖ ≤ 2Ω|u_j v|` (EGP06's graph from `R.edge`). -/
theorem cgp06_edge_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x)
    (hqj : q ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 q| ≤ 8 * Δ)
    (ht : cgpHeight P.toLocalChartFamily q ≤ 8 * Δ) :
    ∀ v ∈ C.plane 1 x, ‖v‖ ≤ 2 * gafGraphOmega_BAS *
      ‖axisCoordCLM_BAS (gafEdgeVector P.toLocalChartFamily P.zero j v)‖ := by
  obtain ⟨sgn, cc, hsgn, hcl⟩ := R.edge j.1 ((Set.Finite.mem_toFinset _).mp j.2)
  exact C.cgp06_edge_of_graph_BAS R j sgn cc hsgn hcl hx hq hqj hη ht

/-- `π_{Q₂}𝓔⁰ = π₂𝓔⁰` in the `cgpQ2Tags` form. -/
theorem gafStageQ_one_globalMap_BAS (p : X) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) =
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p :=
  gafStageQ_starProjection_globalMap _ _ 1 p

/-- FC01's edge block formula in `π₂𝓔⁰` form at a point of full marker:
`u_j(π₂𝓔⁰ p) = R_j η_j(p)` (axis coordinate) and `v_j(π₂𝓔⁰ p) = R_j`. -/
theorem edge_block_of_cutoff_BAS (j : P.edge.finite_centres.toFinset) {p : X} (hcut : P.edge.cutoff j.1 p = 1) :
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p) =
      ρ j.1 • P.edge.coord j.1 p ∧
    gafEdgeMarker P.toLocalChartFamily P.zero j
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p) =
      ρ j.1 := by
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 1 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈
      cgpQ2Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inr j)) p = 1 := hcut
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS p
  rw [hcut', mul_one, gafStageQ_one_globalMap_BAS] at hb
  refine ⟨?_, hb.2⟩
  calc _ = ρ j.1 • axisCoordCLM_BAS (cgpCoord P.toLocalChartFamily P.zero
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j))) p) := hb.1
    _ = _ := by
      change ρ j.1 • axisCoordCLM_BAS (planeAxis (P.edge.coord j.1 p)) = _
      rw [axisCoordCLM_planeAxis_BAS]

/-- `‖u_j‖ ≤ 1` for the edge axis coordinate. -/
theorem norm_edgeAxis_le_BAS (j : P.edge.finite_centres.toFinset) :
    ‖axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)‖ ≤ 1 := by
  have h1 := norm_axisCoordCLM_le_BAS
  have h2 := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    change ‖axisCoordCLM_BAS‖ * ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²) (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)‖ ≤ 1
    nlinarith [norm_nonneg axisCoordCLM_BAS, norm_nonneg (blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero))])

/-- The edge section's points over `(-5.5Δ, 5.5Δ)` are edge-cloud points. -/
theorem edge_section_cloud_BAS (hΔ : 1 ≤ Δ) (j : P.edge.finite_centres.toFinset) (secE : ℝ → X)
    (hsec : ∀ y : ℝ, |y| ≤ 8 * Δ → P.edge.coord j.1 (secE y) = y ∧
      cgpHeight P.toLocalChartFamily (secE y) < Δ / 100 ∧ secE y ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      P.edge.cutoff j.1 (secE y) = 1 ∧ 3 / 4 * ρ j.1 ≤ ρ (secE y) ∧ ρ (secE y) ≤ 5 / 4 * ρ j.1) :
    ∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a) ∈
        gafCloud P.toLocalChartFamily P.zero 1 := by
  intro a ha
  have hΔ0 : 0 < Δ := by linarith
  have h6 := edge_ball_sub_BAS hΔ a ha a (mem_closedBall_self (by norm_num))
  have hh := hsec a h6.2.1
  refine ⟨secE a, ⟨j, hh.2.2.1, ?_, ?_⟩, rfl⟩
  · rw [hh.1]
    linarith only [h6.1, hΔ0]
  · linarith only [hh.2.1, hΔ0]

/-- CGP07's section-side inputs on the edge chart `j` (continuity, block formula, cumulative
error, scale, (PLAT)) for an active stage-two slot `O`. -/
theorem edge_section_inputs_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) (secE : ℝ → X)
    (hsecC : ContinuousOn secE (Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ)))
    (hsec : ∀ y : ℝ, |y| ≤ 8 * Δ → P.edge.coord j.1 (secE y) = y ∧
      cgpHeight P.toLocalChartFamily (secE y) < Δ / 100 ∧ secE y ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      P.edge.cutoff j.1 (secE y) = 1 ∧ 3 / 4 * ρ j.1 ≤ ρ (secE y) ∧ ρ (secE y) ≤ 5 / 4 * ρ j.1)
    {O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1)}
    (hO : C.slot 1 = .active O) :
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      ContinuousOn (fun y => C.stageMap_BAS 1 (secE y)) (closedBall a (1 / 100))) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
            (secE y)) = ρ j.1 • y ∧
      gafEdgeMarker P.toLocalChartFamily P.zero j
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
            (secE y)) = ρ j.1) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      ‖C.stageMap_BAS 1 (secE y) - cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) (secE y)‖ ≤ c 1 * ρ (secE y)) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      ρ (secE y) ≤ 5 / 4 * ρ j.1) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      secE y ∈ {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 p| < 6 * Δ ∧
        cgpHeight P.toLocalChartFamily p < 6 * Δ} ∧ C.stageMap_BAS 1 (secE y) ∈ O.Z) := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hsub := edge_ball_sub_BAS hΔ
  refine ⟨fun a ha => (C.stageMap_contMDiff_BAS 1).continuous.comp_continuousOn
      (hsecC.mono fun y hy => (hsub a ha y hy).2.2), fun a ha y hy => ?_, fun a ha y hy => ?_,
    fun a ha y hy => (hsec y (hsub a ha y hy).2.1).2.2.2.2.2, fun a ha y hy => ?_⟩
  · have hh := hsec y (hsub a ha y hy).2.1
    have hb := edge_block_of_cutoff_BAS j hh.2.2.2.1
    rw [hh.1] at hb
    exact hb
  · have h := C.stageMap_error_BAS 1 (secE y)
    rw [gafStageQ_one_globalMap_BAS] at h
    exact h.le
  · have hh := hsec y (hsub a ha y hy).2.1
    have h6 : |P.edge.coord j.1 (secE y)| < 6 * Δ := by
      rw [hh.1]
      exact (hsub a ha y hy).1
    have ht6 : cgpHeight P.toLocalChartFamily (secE y) < 6 * Δ := by
      linarith only [hh.2.1, hΔ0]
    exact ⟨⟨hh.2.2.1, h6, ht6⟩, (C.plat_BAS hO (p := secE y) ⟨j, hh.2.2.1, h6, ht6⟩).2.2⟩

/-- CGP07's rough-graph-side inputs on the edge chart `j` for ONE chosen rough graph `(sgn, cc)`:
the centres `x a = π₂𝓔⁰(s_j a)` with value error, radius `r_x ≥ (9/20)ΣR` and `r_x/4 ≤ ρ_a`;
the coframe bound `m = 1/(2Ω)` (CGP06) and the dimension; (MW) with the graph's value error. -/
theorem edge_chart_inputs_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (sgn cc : CGPTag P.toLocalChartFamily P.zero → ℝ) (hsgn : ∀ t, |sgn t| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (100 * Δ * ρ j.1), |P.edge.coord j.1 x| ≤ 8 * Δ →
      cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) x -
          egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc (P.edge.coord j.1 x)‖ < eg 1 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j.1)⁻¹ ^ 2 * g.inner x w w = 1 →
          ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
            fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc)
              (P.edge.coord j.1 x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) x w)‖ < eg 1) (secE : ℝ → X)
    (hsec : ∀ y : ℝ, |y| ≤ 8 * Δ → P.edge.coord j.1 (secE y) = y ∧
      cgpHeight P.toLocalChartFamily (secE y) < Δ / 100 ∧ secE y ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      P.edge.cutoff j.1 (secE y) = 1 ∧ 3 / 4 * ρ j.1 ≤ ρ (secE y) ∧ ρ (secE y) ≤ 5 / 4 * ρ j.1)
    {O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1)}
    (hO : C.slot 1 = .active O) :
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), a ∈ (univ : Set ℝ) ∧
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
          (secE a) - egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc a‖ ≤ eg 1 ∧
      9 / 20 * S 1 * ρ j.1 ≤ S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) ∧
      S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) / 4 ≤
        3 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))))) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      ∀ v ∈ C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a)),
        1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
          ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) v‖) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      Module.finrank ℝ (C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) = Module.finrank ℝ ℝ) ∧
    (∀ w ∈ markedPatch_BPRE O.Z
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ, ∃ (y : BlockSpace (fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²)) (sw : ℝ), sw ∈ (univ : Set ℝ) ∧
      ‖(ρ j.1)⁻¹ • y - egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc sw‖ ≤ eg 1 ∧
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y = ρ j.1 • sw ∧
      ‖w - y‖ ≤ 25 / 12 * Ξ 1 * S 1 * ρ j.1) := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hΩ := one_le_gafGraphOmega_BAS
  obtain ⟨hΞ0, hS0, -⟩ := C.numbers.1 1
  have hΞle : Ξ 1 ≤ 1 / 10 := O.eps_le
  have hsub := edge_ball_sub_BAS hΔ
  have hcloud := edge_section_cloud_BAS hΔ j secE hsec
  have hpatch : C.edgePatch_BAS j = markedPatch_BPRE O.Z
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ := by
    unfold edgePatch_BAS
    rw [hO]
    rfl
  have hm : ∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      ∀ v ∈ C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a)),
        1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
          ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) v‖ := by
    intro a ha v hv
    have h8 := (hsub a ha a (mem_closedBall_self (by norm_num))).2.1
    have hh := hsec a h8
    have h1 : |P.edge.coord j.1 (secE a)| ≤ 8 * Δ := by
      rw [hh.1]
      exact h8
    exact inv_two_mul_le_of_le_BAS (by linarith only [hΩ])
      (C.cgp06_edge_of_graph_BAS R j sgn cc hsgn hcl (hcloud a ha) rfl hh.2.2.1 h1
        (by linarith only [hh.2.1, hΔ0]) v hv)
  have hdim : ∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      Module.finrank ℝ (C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) = Module.finrank ℝ ℝ := by
    intro a ha
    rw [(C.test1.1 _ (hcloud a ha)).1, Module.finrank_self]
    rfl
  refine ⟨fun a ha => ?_, hm, hdim, fun w hw => ?_⟩
  · have h8 := (hsub a ha a (mem_closedBall_self (by norm_num))).2.1
    have hh := hsec a h8
    have h1 : |P.edge.coord j.1 (secE a)| ≤ 8 * Δ := by
      rw [hh.1]
      exact h8
    have hval := (hcl (secE a) hh.2.2.1 h1 (by linarith only [hh.2.1, hΔ0])).1
    rw [hh.1] at hval
    have hxe := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le 1 (hcloud a ha)
    have hrat := gafCloudEnlarged_preimage_ratio_BAS P.toLocalChartFamily P.zero hΔ hΛ C.small_BAS 1
      (C.sel 1) (C.hsel 1) _ hxe (secE a) (gafStageQ_one_globalMap_BAS _)
    exact ⟨mem_univ a, hval.le, nine_twenty_le_BAS hS0.le hrat.1 hh.2.2.2.2.1,
      quarter_le_three_inv_mul_BAS hΞ0 hΞle (mul_pos hS0 (hρ _)).le⟩
  · rw [← hpatch] at hw
    have hwit := C.edgePatch_witness_BAS j w hw
    obtain ⟨q, -, hr⟩ := hwit
    have hmw := hr.2.2.2.2.2.2.2.2
    rw [gafStageQ_one_globalMap_BAS] at hmw
    have hval := (hcl q hr.1 (by linarith only [hr.2.2.2.1, hΔ0]) hr.2.1).1
    exact ⟨_, P.edge.coord j.1 q, mem_univ _, hval.le, (edge_block_of_cutoff_BAS j hr.2.2.1).1,
      hmw.le⟩

/-- The edge chart's CGP07 assembly from its prepared inputs (`edge_chart_inputs_BAS`,
`edge_section_inputs_BAS`) for one chosen rough graph. -/
theorem edge_assemble_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (sgn cc : CGPTag P.toLocalChartFamily P.zero → ℝ)
    (hΦd : ∀ y, DifferentiableAt ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc) y)
    (hΦb : ∀ y, ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc) y‖ ≤
      gafGraphOmega_BAS) (secE : ℝ → X)
    (hcloud : ∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a) ∈
        gafCloud P.toLocalChartFamily P.zero 1)
    {O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1)}
    (hin :
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), a ∈ (univ : Set ℝ) ∧
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
          (secE a) - egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc a‖ ≤ eg 1 ∧
      9 / 20 * S 1 * ρ j.1 ≤ S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) ∧
      S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) / 4 ≤
        3 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))))) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      ∀ v ∈ C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a)),
        1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
          ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) v‖) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      Module.finrank ℝ (C.plane 1 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))) = Module.finrank ℝ ℝ) ∧
    (∀ w ∈ markedPatch_BPRE O.Z
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ, ∃ (y : BlockSpace (fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²)) (sw : ℝ), sw ∈ (univ : Set ℝ) ∧
      ‖(ρ j.1)⁻¹ • y - egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc sw‖ ≤ eg 1 ∧
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y = ρ j.1 • sw ∧
      ‖w - y‖ ≤ 25 / 12 * Ξ 1 * S 1 * ρ j.1))
    (hsi :
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ),
      ContinuousOn (fun y => C.stageMap_BAS 1 (secE y)) (closedBall a (1 / 100))) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
            (secE y)) = ρ j.1 • y ∧
      gafEdgeMarker P.toLocalChartFamily P.zero j
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
            (secE y)) = ρ j.1) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      ‖C.stageMap_BAS 1 (secE y) - cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero) (secE y)‖ ≤ c 1 * ρ (secE y)) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      ρ (secE y) ≤ 5 / 4 * ρ j.1) ∧
    (∀ a ∈ ball (0 : ℝ) (11 / 2 * Δ), ∀ y ∈ closedBall a (1 / 100),
      secE y ∈ {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 p| < 6 * Δ ∧
        cgpHeight P.toLocalChartFamily p < 6 * Δ} ∧ C.stageMap_BAS 1 (secE y) ∈ O.Z)) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
      (∀ w ∈ markedPatch_BPRE O.Z
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ,
        ∃ p ∈ {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 p| < 6 * Δ ∧
          cgpHeight P.toLocalChartFamily p < 6 * Δ}, C.stageMap_BAS 1 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * Δ)) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
            (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ) (ball 0 (11 / 2 * Δ)) ∧
        MapsTo φ (ball 0 (11 / 2 * Δ))
          (markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
            (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * Δ), IsCompact K →
          IsCompact (markedPatch_BPRE O.Z
            (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
            (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) := by
  have hxC := hin.1
  have hm := hin.2.1
  have hdim := hin.2.2.1
  have hMW := hin.2.2.2
  have hcont := hsi.1
  have hsecv := hsi.2.1
  have herr := hsi.2.2.1
  have hρs := hsi.2.2.2.1
  have hplat := hsi.2.2.2.2
  obtain ⟨-, hS0, -⟩ := C.numbers.1 1
  obtain ⟨hεos, heos, -⟩ := R.os 1
  have hc1 := C.c_le_BAS 1
  exact cgp07_of_cfs15_BAS (ℓ := Δ) (M := X) O (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (norm_edgeAxis_le_BAS j) (gafEdgeMarker P.toLocalChartFamily P.zero j) (norm_blockMarkerCLM_le _)
    (hρ j.1) one_le_gafGraphOmega_BAS hS0 heos.le hεos.le (R.eps_lt_margin_BAS 1).2
    (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc) hΦd hΦb
    (fun a => cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) (secE a))
    hcloud (fun a ha => (hxC a ha).2.1) (fun a ha => (hxC a ha).2.2.1) hm hdim
    (fun w hw => by
      obtain ⟨y, sw, -, h1, h2, h3⟩ := hMW w hw
      exact ⟨y, sw, h1, h2, h3⟩)
    (C.stageMap_BAS 1) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero))
    secE ρ {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |P.edge.coord j.1 p| < 6 * Δ ∧
        cgpHeight P.toLocalChartFamily p < 6 * Δ} (C.c_pos_BAS 1).le
    (by linarith only [hc1]) (by linarith only [hc1]) hcont hsecv
    (fun a ha y hy => by convert herr a ha y hy using 3) hρs hplat


/-- **CGP07 on the chain, edge stage, for ONE chosen rough graph** (`cgp07_one_sheet_BPRE`
instantiated): see `cgp07_edge_BAS`. -/
theorem cgp07_edge_of_graph_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (sgn cc : CGPTag P.toLocalChartFamily P.zero → ℝ) (hsgn : ∀ t, |sgn t| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (100 * Δ * ρ j.1), |P.edge.coord j.1 x| ≤ 8 * Δ →
      cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) x -
          egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc (P.edge.coord j.1 x)‖ < eg 1 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j.1)⁻¹ ^ 2 * g.inner x w w = 1 →
          ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
            fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero j.1 sgn cc)
              (P.edge.coord j.1 x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) x w)‖ < eg 1) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
      (∀ w ∈ C.edgePatch_BAS j, ∃ p, (p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) ∧
        C.stageMap_BAS 1 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * Δ)) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
        MapsTo φ (ball 0 (11 / 2 * Δ)) (C.edgePatch_BAS j) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * Δ), IsCompact K →
          IsCompact (C.edgePatch_BAS j ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, hT, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hbud : Λ * (10 * Δ) ≤ 1 / 4 := by
    have h := C.small_BAS
    nlinarith
  obtain ⟨hΦs, -, -, hΦbd⟩ := egp06_model P.toLocalChartPacketsR hΛ hΔ hLΛ hμ hτ he hT hj sgn cc
    hsgn
  obtain ⟨secE, hsecC, hsec⟩ := edge_section_BAS P hΔ0 hΛ hbud j
  cases hO : C.slot 1 with
  | inactive h =>
    exfalso
    have h' : P.edge.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  | active O =>
  have hpatch : C.edgePatch_BAS j = markedPatch_BPRE O.Z
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ := by
    unfold edgePatch_BAS
    rw [hO]
    rfl
  rw [hpatch]
  exact C.edge_assemble_BAS R j sgn cc (fun y => (hΦs.differentiable (by simp)) y)
    (fun y => (hΦbd y).1.trans egpGraphConst_le_gafGraphOmega_BAS) secE
    (edge_section_cloud_BAS hΔ j secE hsec)
    (C.edge_chart_inputs_BAS R j sgn cc hsgn hcl secE hsec hO)
    (C.edge_section_inputs_BAS j secE hsecC hsec hO)

/-- **CGP07 on the chain, edge stage** (only `(C, R)`): the ACTUAL one-dimensional retained
coordinate `R_j⁻¹u_j` is a bijection of the edge patch `V_j⁰` onto `(-5.5Δ, 5.5Δ)`; every point of
`V_j⁰` is `f₂(p)` for a `p` of the chart's ORIGINAL threshold-6 plateau (`|η_j| < 6Δ`, `t < 6Δ`);
the inverse chart is smooth on the interval, inverts the coordinate and lands in `V_j⁰`; compact
subsets have compact preimages in `V_j⁰`. -/
theorem cgp07_edge_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
      (∀ w ∈ C.edgePatch_BAS j, ∃ p, (p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) ∧
        C.stageMap_BAS 1 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * Δ)) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (C.edgePatch_BAS j) (ball 0 (11 / 2 * Δ)) ∧
        MapsTo φ (ball 0 (11 / 2 * Δ)) (C.edgePatch_BAS j) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * Δ), IsCompact K →
          IsCompact (C.edgePatch_BAS j ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) := by
  obtain ⟨sgn, cc, hsgn, hcl⟩ := R.edge j.1 ((Set.Finite.mem_toFinset _).mp j.2)
  exact C.cgp07_edge_of_graph_BAS R j sgn cc hsgn hcl

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
