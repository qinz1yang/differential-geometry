import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff

/-!
# EDP02's height-factor estimate (EZ) on the original map `𝓔⁰`

Blueprint `master207B.tex`, EDP02 (`lem:fibration-actual-edge-height-localization`, B:6797–6825),
the part of the proof that involves only the original map: "Since the final marker is exactly
`R_i`, `ζ_i > 1 − d`, `d = 5c₃/4`. The tangential cutoff equals one, so `ζ_i = g(t/Δ)` and
`t < 9Δ`. Put `Z₀ = χ_{1/2,1}(Σ_{j∈I_e} ζ_j)`. … Its actual profile derivative bound gives
`Z₀ ≥ 1 − 2P₀d`, since the sum is at least `1 − d`. Thus `g(t/Δ)Z₀ > 1 − β`, `β = (1 + 2P₀)d`
(EZ). If `t ≥ .3Δ`, the original weak-edge vector is `ρ t g(t/Δ) Z₀`." (also used by FDC02).

* `le_cgpEdgeSum_GAFS`: every edge cutoff is at most the edge sum `Σ_{I_e} ζ_j`.
* `edgeSumRamp_ge_GAFS`: `χ_{1/2,1}(s) ≥ 1 − 2P₀d` for `s ≥ 1 − d` (`P₀ = cgpProfileBound`).
* `edp02_ez_GAFS`: for an edge index `i`, a point `p` of its chart ball with `|η_i(p)| < 8Δ` and
  `ζ_i(p) > 1 − d` (`0 ≤ d`, `2P₀d < 1`): `t(p) < 9Δ`, `Z₀(p) ≥ 1 − 2P₀d`,
  `g(t/Δ)Z₀ > 1 − (1 + 2P₀)d`, and for `t ≥ .3Δ` the `E'` marker of `𝓔⁰` is `z₀ = g(t/Δ)Z₀`.
The inequality `ζ_i > 1 − d` itself comes from the adjusted map (GAF06 and the exact final marker).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- CGP01's sum profile `χ_{1/2,1}` is at least `1 − 2P₀d` on `[1 − d, ∞)` (`0 ≤ d`). -/
theorem edgeSumRamp_ge_GAFS {d s : ℝ} (hd : 0 ≤ d) (hs : 1 - d ≤ s) :
    1 - 2 * cgpProfileBound * d ≤ cfsRamp lc87EdgeTransition (1 / 2) 1 s := by
  have hP := cgpProfileBound_spec.1
  by_cases hs1 : 1 ≤ s
  · rw [cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hs1]
    nlinarith
  · have h := abs_cfsRamp_sub_le lc87EdgeTransition_contDiff abs_deriv_lc87EdgeTransition_le_cgp
      (by norm_num : (1 / 2 : ℝ) < 1) s 1
    rw [cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) le_rfl] at h
    have habs : |s - 1| = 1 - s := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [habs] at h
    have h2 : cgpProfileBound / (1 - 1 / 2) * (1 - s) ≤ 2 * cgpProfileBound * d := by
      have : cgpProfileBound / (1 - 1 / 2) = 2 * cgpProfileBound := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := (abs_le.mp h).1
    linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- Each actual edge cutoff is at most the edge sum `Σ_{I_e} ζ_j` (all cutoffs are nonnegative). -/
theorem le_cgpEdgeSum_GAFS (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (i : L.edge.finite_centres.toFinset) (p : X) :
    L.edge.cutoff i.1 p ≤ cgpEdgeSum L p := by
  unfold cgpEdgeSum
  exact Finset.single_le_sum (f := fun j : L.edge.finite_centres.toFinset => L.edge.cutoff j.1 p)
    (fun j _ => (cgpEdgeCutoff_mem_Icc L hΔ j.1 p).1) (Finset.mem_univ i)

/-- **EDP02 (EZ) on `𝓔⁰`**: for an edge index `i` and `p ∈ B(c_i, 100Δρ(c_i))` with
`|η_i(p)| < 8Δ` and `ζ_i(p) > 1 − d` (`0 ≤ d`, `2P₀d < 1`): `t(p) < 9Δ`, `Z₀(p) ≥ 1 − 2P₀d`,
`g(t/Δ)Z₀(p) > 1 − (1 + 2P₀)d` (`g = 1 − χ_{8,9}`), and if `t ≥ .3Δ` the `E'` marker of `𝓔⁰` at `p`
is `g(t/Δ)Z₀(p)`. -/
theorem edp02_ez_GAFS (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) (i : L.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hη : |L.edge.coord i.1 p| < 8 * Δ) {d : ℝ}
    (hd : 0 ≤ d) (hdP : 2 * cgpProfileBound * d < 1) (hζ : 1 - d < L.edge.cutoff i.1 p) :
    cgpHeight L p < 9 * Δ ∧
      1 - 2 * cgpProfileBound * d ≤ cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L p) ∧
      1 - (1 + 2 * cgpProfileBound) * d <
        (1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ)) *
          cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L p) ∧
      (3 / 10 * Δ ≤ cgpHeight L p → cgpEdgeMarker L p =
        (1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ)) *
          cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L p)) := by
  have hP := cgpProfileBound_spec.1
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hid := cgp01_edge_identity L hi hp hη hΔ
  rw [hid] at hζ
  set G := 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ) with hG
  set Z₀ := cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L p) with hZ
  have hsum : 1 - d ≤ cgpEdgeSum L p := by
    have h := le_cgpEdgeSum_GAFS L hΔ i p
    rw [hid] at h
    linarith
  have hZ₀ : 1 - 2 * cgpProfileBound * d ≤ Z₀ := edgeSumRamp_ge_GAFS hd hsum
  have hd1 : d < 1 / 2 := by nlinarith
  -- `t < 9Δ`: otherwise `g(t/Δ) = 0`
  have ht : cgpHeight L p < 9 * Δ := by
    by_contra hcon
    have h9 : 9 ≤ cgpHeight L p / Δ := by
      rw [le_div_iff₀ hΔ]
      linarith
    have h1 : cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ) = 1 :=
      cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) h9
    rw [hG, h1] at hζ
    linarith
  refine ⟨ht, hZ₀, ?_, fun h3 => ?_⟩
  · have hZpos : 0 < Z₀ := by linarith
    calc 1 - (1 + 2 * cgpProfileBound) * d ≤ (1 - d) * (1 - 2 * cgpProfileBound * d) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * cgpProfileBound) hd) hd]
      _ ≤ (1 - d) * Z₀ := mul_le_mul_of_nonneg_left hZ₀ (by linarith)
      _ < G * Z₀ := mul_lt_mul_of_pos_right hζ hZpos
  · have hu : 3 / 10 ≤ cgpHeight L p / Δ := by
      rw [le_div_iff₀ hΔ]
      linarith
    rw [cgpEdgeMarker, cgpEdgeH_eq_of_le hu]

end DifferentialGeometry.Geometry.Collapse
