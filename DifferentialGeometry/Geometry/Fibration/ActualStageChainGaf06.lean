import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# GAF06 on the chain object: whole-preimage localization along `[𝓔⁰, C.E]`

Blueprint `master207B.tex`, GAF06 (`lem:fibration-whole-ratio-preimage-localization`,
B:6008–6047); external draft 59 §5 ("GAF06 reads `C.E`, the global segment, segment (AM0), the
strict final error and the original block formula; this route does not need BASES"). Everything is
about ONE chain `C : Gaf02Chain P …`: `H_τ = (1 − τ)𝓔⁰ + τ C.E`, its (AM0) is `C.segment_am0`, its
error is `C.stage_error_lt` (`|C.E − 𝓔⁰| < c₃ρ`), with GAF01's (JA) clause `c₃ = c 2 < 1/1000` on
the chain's own parameter (blueprint: `δ = (5/4)c₃ < 1/800`).

* `Gaf02Chain.segment_am0_param_G47`: (AM0) at `H_τ p`, `τ ∈ [0, 1]`.
* `Gaf02Chain.gaf06_G47`: for EVERY retained index `i` (circle, slim, edge), every `ℓ ≥ 1`, every
  `p` and `τ`: (RP) `v_i(H_τ p) > .9R_i`, `|u_i(H_τ p)| ≤ 4ℓ v_i(H_τ p)` ⇒ the original cutoff is
  positive, `p` lies in the chart domain (the coordinate is defined) and `|η_i(p)| < 4.01ℓ`.
* `Gaf02Chain.gaf06_circle_G47` (`ℓ = 1`), `Gaf02Chain.gaf06_slim_G47` (`ℓ = 10⁵Δ`): the original
  cutoff is ONE. `Gaf02Chain.gaf06_edge_G47` (`ℓ = Δ`): positive cutoff and the TANGENTIAL bound
  `|η_i| < 4.01Δ` only (no height claim, blueprint B:6022–6023).
* Consumer `gaf06_final_family_G47`: the three chart cases for a chain on the final family
  `LocalChartPacketsC14Z` (projection `toLocalChartPackets`), at the end point `τ = 1` (`H₁ = C.E`).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The packet range `Λ · 10⁶Δ ≤ 1/4` read off the chain's packet hypotheses. -/
theorem small_range_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : Λ * (1000000 * Δ) ≤ 1 / 4 := by
  obtain ⟨-, -, -, -, hLΛ, -⟩ := C.std
  have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
  linarith

/-- **(AM0) at the points `H_τ p = (1 − τ)𝓔⁰ p + τ C.E p`** of the chain's global segment. -/
theorem segment_am0_param_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : CGPMarkerIndex P.toLocalChartFamily) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1, cgpMarkerCutoff P.toLocalChartFamily i p = 0 →
      |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily i) / 32 := by
  intro p t ht hp
  exact C.segment_am0 i p hp _ ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩

/-- **GAF06 on the chain object** (B:6008): with GAF01's `c₃ = c 2 < 1/1000`, for EVERY retained
index `i`, every `ℓ ≥ 1`, every `p` and every `τ ∈ [0, 1]`, (RP) at `H_τ p = (1 − τ)𝓔⁰ p + τ C.E p`
(`v_i > .9R_i`, `|u_i| ≤ 4ℓ v_i`) forces a positive original cutoff, `p` in the chart domain (the
original coordinate is defined) and `|η_i(p)| < 4.01ℓ`. -/
theorem gaf06_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000) {ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (i : CGPMarkerIndex P.toLocalChartFamily) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      0 < cgpMarkerCutoff P.toLocalChartFamily i p ∧
        p ∈ ball (cgpMarkerCentre P.toLocalChartFamily i)
          (cgpMarkerDomain P.toLocalChartFamily i * ρ (cgpMarkerCentre P.toLocalChartFamily i)) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) p‖ <
          401 / 100 * ℓ := by
  intro p t ht hmark hratio
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -, -, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hpos, hη⟩ := gaf06_segment_localization P.toLocalChartFamilyQ P.zero hΔ hσs hσs1 hΛ
    C.small_range_G47 C.E hc hℓ i (C.segment_am0_param_G47 i) C.stage_error_lt.2.2 p t ht hmark
    hratio
  exact ⟨hpos, cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 i p hpos.ne', hη⟩

/-- **GAF06, circle charts, on the chain** (`ℓ = 1`): (RP) at `H_τ p` puts `p` in
`B(c_j, 200ρ(c_j))` with `‖η_j(p)‖ < 4.01`, and the original circle cutoff is ONE. -/
theorem gaf06_circle_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.circle.finite_centres.toFinset) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl j) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      p ∈ ball j.1 (200 * ρ j.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 401 / 100 ∧
        P.circle.cutoff j.1 p = 1 := by
  intro p t ht hmark hratio
  obtain ⟨-, hdom, hη⟩ := C.gaf06_G47 hc le_rfl (.inl j) p t ht hmark
    (by rw [mul_one]; exact hratio)
  have hp : p ∈ ball j.1 (200 * ρ j.1) := hdom
  have hη' : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 401 / 100 := by
    have h1 : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 401 / 100 * 1 := hη
    linarith
  exact ⟨hp, hη', circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyQ P.zero j hp
    (by linarith)⟩

/-- **GAF06, slim charts, on the chain** (`ℓ = 10⁵Δ`): (RP) at `H_τ p` puts `p` in
`B(c_j, 10⁶Δρ(c_j))` with `|η_j(p)| < 4.01·10⁵Δ`, and the original slim cutoff is ONE. -/
theorem gaf06_slim_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.slim.finite_centres.toFinset) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff j.1 p = 1 := by
  intro p t ht hmark hratio
  obtain ⟨-, hΔ, -⟩ := C.std
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨-, hdom, hη⟩ := C.gaf06_G47 hc hℓ (.inr (.inl j)) p t ht hmark hratio
  have hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1) := hdom
  change ‖planeAxis ((P.slim.centre j.1 hj).coord p)‖ < 401 / 100 * (10 ^ 5 * Δ) at hη
  rw [norm_planeAxis] at hη
  refine ⟨hp, hη, ?_⟩
  rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
  refine (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le ?_ ?_
  · convert hp using 2
    norm_num
  · nlinarith

/-- **GAF06, edge charts, on the chain** (`ℓ = Δ`): (RP) at `H_τ p` gives a positive original edge
cutoff, `p ∈ B(c_j, 100Δρ(c_j))` and the TANGENTIAL bound `|η_j(p)| < 4.01Δ`; no height bound is
claimed (blueprint B:6022–6023). -/
theorem gaf06_edge_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.edge.finite_centres.toFinset) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p +
            t • C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j)))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p +
            t • C.E p) →
      0 < P.edge.cutoff j.1 p ∧ p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 401 / 100 * Δ := by
  intro p t ht hmark hratio
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨hpos, hdom, hη⟩ := C.gaf06_G47 hc hΔ (.inr (.inr j)) p t ht hmark hratio
  change ‖planeAxis (P.edge.coord j.1 p)‖ < 401 / 100 * Δ at hη
  rw [norm_planeAxis] at hη
  exact ⟨hpos, hdom, hη⟩

end Gaf02Chain

/-- **Consumer: GAF06 for a chain on the final family** `LocalChartPacketsC14Z` (through its
projection `toLocalChartPackets`), at the end point `τ = 1` of the segment (`H₁ = C.E`): (RP) at
`C.E p` for a circle / slim index makes the original cutoff one, for an edge index gives the
tangential bound. -/
theorem gaf06_final_family_G47 {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000) (p : X) :
    (∀ j : P.circle.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl j) (C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          (C.E p)‖ ≤
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          (C.E p) →
      P.circle.cutoff j.1 p = 1) ∧
    (∀ j : P.slim.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) (C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl j))
          (C.E p)‖ ≤
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) (C.E p) →
      P.slim.cutoff j.1 p = 1) ∧
    ∀ j : P.edge.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.E p)‖ ≤
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.E p) →
      |P.edge.coord j.1 p| < 401 / 100 * Δ := by
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.E p =
      C.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨fun j hm hr => ?_, fun j hm hr => ?_, fun j hm hr => ?_⟩
  · exact (C.gaf06_circle_G47 hc j p 1 ht (by rw [h1]; exact hm) (by rw [h1]; exact hr)).2.2
  · exact (C.gaf06_slim_G47 hc j p 1 ht (by rw [h1]; exact hm) (by rw [h1]; exact hr)).2.2
  · exact (C.gaf06_edge_G47 hc j p 1 ht (by rw [h1]; exact hm) (by rw [h1]; exact hr)).2.2

end DifferentialGeometry.Geometry.Collapse
