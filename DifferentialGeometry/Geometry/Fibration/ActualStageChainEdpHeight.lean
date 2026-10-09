import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp01
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBufferCollar
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.HeightQuotient
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FaceIndependence
import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools

/-!
# EDP03–EDP06 on the chain object: (EH), EDP04's homotopy, its whole trace and the rim rank

Lane C14-EDP-E. Blueprint `master207B.tex`, EDP03 (EH) (B:6861–6862, proof B:6912–6937), EDP04
(EI) (B:6974–7013), EDP05's face independence (B:7080–7084) and EDP06's band (B:7103–7105), for a
chain `C : Gaf02Chain L.toLocalChartPackets …` on `L : LocalChartPacketsC14` (EDP01 is proved there,
`Gaf02Chain.edp01_GAF8`). Conventions as in `ActualStageChainEdpBlocks`:
`A = proj₀(gafHeightVector E)`, `s = C.scale`, `T = A/s`, `g = proj₀(gafEdgeVector j E)/R_j`,
`t = P/ρ`, `H₀ = Δψ(t/Δ)`, blueprint
`c₃` = chain `c 2`; EDP01's `κ = C_ρΛ` with `C_ρ = 100(L₀ + 1)(1 + b_cut + c_w(1)/Σ₁)` and
`h_* = 50(c₃ + κΔ)`. Numerical hypotheses (parameters only): EDP01's `0 ≤ c_w(1)`, `Σ₁ ≤ Ξ₁/10⁴`;
(SE) `c₃ < 10⁻⁵`, `κΔ < 10⁻⁶`; `0 ≤ ε < 1` (`‖dP‖ ≤ 1 + ε < 2`); EDP03's collar `0 < γc ≤ 1/100`,
`βc ≤ 10⁻⁵` for the co-norm.

* `Gaf02Chain.edge_height_EH_EDPE` ((EH)): `h_* < 1/1000`; `|T − t| < h_*` on `Y_j ∩ {.3Δ ≤ t}`;
  `|dT(W) − dt(W)| < h_*` for `R_j⁻²g`-unit `W` on `Y_j ∩ {.3Δ < t}` (EDP01 + the FULL quotient
  rule, kernels `EdgeDisk.edgeHeight_quotient_value_lt` / `_deriv_lt`).
* `norm_le_abs_add_abs_EDPE`, `mvfderiv_homotopyPair_EDPE` (`DH_τ = (1 − τ)D(f₁,f₂) + τD(h₁,h₂)`).
* `Gaf02Chain.edge_homotopy_conorm_EDPE` ((EI) transversality): on `Y_j`'s collar `3.9Δ < t < 4.1Δ`,
  for every `τ ∈ [0, 1]`, `H_τ = ((1 − τ)η + τg, (1 − τ)H₀ + τT)` has co-norm `> .9 − (c₃ + h_*)`
  for `R_j⁻²g`, and `c₃ + h_* < 1/500`.
* `Gaf02Chain.edge_trace_EDPE` ((EI) localization): every point of the time trace of
  `X_a = {a} × (−∞, 4Δ]`, `|a| < 4Δ`, in `Y_j` has `|η| < 4.01Δ`, `t < 4.01Δ`; the trace of `∂X_a`
  lies in `|t − 4Δ| < h_*` (inside the collar).
* `Gaf02Chain.edge_vertical_rank_EDPE` (EDP04's final-time rank, EDP05 face independence, EDP06
  band): at `p ∈ Y_j` with `|g| < 4Δ`, `T = 4Δ`: `|η| < 4.01Δ`, `|t − 4Δ| < h_* < 1/1000`,
  `D(g, T)` onto, and `(d(b ∘ g), dT)` onto whenever `b'(g(p)) ≠ 0`
  (`EdgeDisk.pair_surjective_smul_left`).

Not here (state-C14-EDP-E.md): FC34's transport of the initial fibre, the final fibre
`= f₂⁻¹(w) ∩ X₂`, properness and bundle charts of `f₂`, (ELoc), GAF05's patch, X₁ / B₁ (GAF07).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_EDPEh
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_EDPEh
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_EDPEh
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **(EH) of EDP03 on the chain object** (B:6861–6862 and B:6912–6937): with EDP01's
`κ = C_ρΛ` (`C_ρ = 100(L₀ + 1)(1 + b_cut + c_w(1)/Σ₁)`) and `h_* = 50(c₃ + κΔ)`: `h_* < 1/1000`;
on the band `.3Δ ≤ t < 5Δ` of `Y_j`, `|T − t| < h_*`; on the open band `.3Δ < t < 5Δ`,
`|dT(W) − dt(W)| < h_*` for every `R_j⁻²g`-unit `W` (the FULL quotient rule). -/
theorem Gaf02Chain.edge_height_EH_EDPE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) {j : X} (hj : j ∈ L.edge.centres) :
    let κ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    50 * (c 2 + κ * Δ) < 1 / 1000 ∧
    (∀ p ∈ ball j (100 * Δ * ρ j), |L.edge.coord j p| < 5 * Δ → 3 / 10 * Δ ≤ t p →
      t p < 5 * Δ → |Tq p - t p| < 50 * (c 2 + κ * Δ)) ∧
    ∀ p ∈ ball j (100 * Δ * ρ j), |L.edge.coord j p| < 5 * Δ → 3 / 10 * Δ < t p →
      t p < 5 * Δ → ∀ W : TangentSpace 𝓘(ℝ, E3) p, (ρ j)⁻¹ ^ 2 * g.inner p W W = 1 →
        |mvfderiv 𝓘(ℝ, E3) Tq p W - mvfderiv 𝓘(ℝ, E3) t p W| < 50 * (c 2 + κ * Δ) := by
  intro κ t A Tq
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hc0, hc01, hc12⟩ := C.accuracy_order_EDPE
  obtain ⟨hnum, -⟩ := C.numbers
  have hS0 : 0 < S 0 := (hnum 0).2.1
  obtain ⟨hC100, hsd⟩ := C.edp01_GAF8 hcw hSΞ
  have hκ : 0 ≤ κ := by
    have : 0 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) := by
      linarith
    exact mul_nonneg this hΛ
  have hΛκ : Λ ≤ κ := by
    have h := mul_le_mul_of_nonneg_right hC100 hΛ
    change Λ ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ
    linarith
  have hrj := hρ j
  -- the normalized inputs at a band point
  have inputs : ∀ p ∈ ball j (100 * Δ * ρ j), |L.edge.coord j p| < 5 * Δ → 3 / 10 * Δ ≤ t p →
      t p < 5 * Δ →
      99 / 100 < ρ p / ρ j ∧ |C.scale p / ρ j - ρ p / ρ j| ≤ κ * (ρ p / ρ j) ∧
        |A p / ρ j - L.edge.smoothing p / ρ j| < c 2 * (ρ p / ρ j) ∧
        0 ≤ L.edge.smoothing p / ρ j / (ρ p / ρ j) ∧
        L.edge.smoothing p / ρ j / (ρ p / ρ j) < 5 * Δ ∧
        A p / ρ j / (C.scale p / ρ j) = Tq p ∧
        L.edge.smoothing p / ρ j / (ρ p / ρ j) = t p := by
    intro p hp hη ht3 ht5
    have hrp := hρ p
    have hsp := (C.scale_pos p).2
    have hq := scale_ratio_ball_EDPE L.toLocalChartPackets hΛ hp
    have hz := edgeMarker_eq_one_EDPE L.toLocalChartPackets hΔ0 hj hp (by linarith) ht3
      (by linarith)
    have hAv := (C.heightAxis_value_EDPE p).1
    rw [hz, one_mul] at hAv
    have htp : t p = L.edge.smoothing p / ρ p := rfl
    have hFt : L.edge.smoothing p / ρ j / (ρ p / ρ j) = t p := by
      rw [htp]
      field_simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hFt⟩
    · have := (abs_le.mp hq).1
      nlinarith
    · have h := (hsd p).2.1
      rw [← sub_div, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
      calc |C.scale p - ρ p| ≤ κ * ρ p := h
        _ = κ * (ρ p / ρ j) * ρ j := by field_simp
    · rw [← sub_div, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
      calc |A p - L.edge.smoothing p| < c 2 * ρ p := hAv
        _ = c 2 * (ρ p / ρ j) * ρ j := by field_simp
    · rw [hFt, htp]
      exact div_nonneg (L.edge.smoothing_nonneg p) hrp.le
    · rw [hFt]
      exact ht5
    · change A p / ρ j / (C.scale p / ρ j) = A p / C.scale p
      field_simp
  have hϑ' : κ * Δ < 1 / 1000000 := hϑ
  refine ⟨by linarith, fun p hp hη ht3 ht5 => ?_, fun p hp hη ht3 ht5 W hW => ?_⟩
  · obtain ⟨hq, hS, hB, ht0, ht, hT, hFt⟩ := inputs p hp hη ht3 ht5
    have h := EdgeDisk.edgeHeight_quotient_value_lt hq hS hB ht0 ht hΔ hκ hϑ'
    rw [hT, hFt] at h
    have : 0 ≤ κ * Δ := mul_nonneg hκ hΔ0.le
    linarith
  · obtain ⟨hq, hS, hB, ht0, ht, hT, hFt⟩ := inputs p hp hη ht3.le ht5
    have hrp := hρ p
    have hsp := (C.scale_pos p).2
    obtain ⟨hAsm, hssm, -, -, -⟩ := C.final_smooth_EDPE
    obtain ⟨Hd, hHd, -, -, hband, -⟩ := C.final_derivative_EDPE
    have hgW : g.inner p W W = ρ j ^ 2 := by
      have hr2 : 0 < ρ j ^ 2 := by positivity
      field_simp at hW
      linarith
    have hsqrt : Real.sqrt (g.inner p W W) = ρ j := by rw [hgW, Real.sqrt_sq hrj.le]
    have hAd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) A p := (hAsm p).mdifferentiableAt (by simp)
    have hsd' : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p :=
      (hssm p).mdifferentiableAt (by simp)
    have htd : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t p :=
      L.edge.contMDiffAt_height_of_collar hj hp (by linarith) (by linarith) (by linarith)
    have hρd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ρ p :=
      (L.contMDiff_scale p).mdifferentiableAt (by simp)
    have hFfun : L.edge.smoothing = fun y => t y * ρ y := funext fun y => by
      have := hρ y
      change L.edge.smoothing y = L.edge.smoothing y / ρ y * ρ y
      field_simp
    have hFd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) L.edge.smoothing p := by
      rw [hFfun]
      exact (htd.mdifferentiableAt (by simp)).mul hρd
    have hdT : mvfderiv 𝓘(ℝ, E3) Tq p W = (C.scale p)⁻¹ * mvfderiv 𝓘(ℝ, E3) A p W -
        A p * (C.scale p ^ 2)⁻¹ * mvfderiv 𝓘(ℝ, E3) C.scale p W :=
      mvfderiv_div_apply hAd hsd' hsp.ne' W
    have hdt : mvfderiv 𝓘(ℝ, E3) t p W = (ρ p)⁻¹ * mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W -
        L.edge.smoothing p * (ρ p ^ 2)⁻¹ * mvfderiv 𝓘(ℝ, E3) ρ p W :=
      mvfderiv_div_apply hFd hρd hrp.ne' W
    have b1 : |mvfderiv 𝓘(ℝ, E3) C.scale p W| ≤ κ * ρ j := by
      have h := (hsd p).2.2.1 W
      rw [hsqrt] at h
      exact h
    have b2 : |mvfderiv 𝓘(ℝ, E3) ρ p W| ≤ Λ * ρ j := by
      have h := abs_mvfderiv_scale_le_GAFS L.toLocalChartPackets hΛ p W
      rw [hsqrt] at h
      exact h
    have hjF : j ∈ L.edge.finite_centres.toFinset := (Set.Finite.mem_toFinset _).mpr hj
    have b3 : |mvfderiv 𝓘(ℝ, E3) A p W - mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W| ≤
        Hd * ρ j := by
      have h := hband ⟨j, hjF⟩ p hp (by linarith) ht3 (by linarith) W
      rw [hsqrt] at h
      exact h
    have b4 : |mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W| ≤ (1 + ε) * ρ j := by
      have h := Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf g hmetric
        (by linarith) L.edge.lipschitz_smoothing hFd W
      rw [hsqrt] at h
      exact h
    have k := EdgeDisk.edgeHeight_quotient_deriv_lt (V := ℝ)
      (dp := mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W / ρ j)
      (dq := mvfderiv 𝓘(ℝ, E3) ρ p W / ρ j) (dS := mvfderiv 𝓘(ℝ, E3) C.scale p W / ρ j)
      (dB := mvfderiv 𝓘(ℝ, E3) A p W / ρ j) hq hS hB ht0 ht hΔ hκ hϑ' hc ?_ ?_ ?_ ?_
    · rw [Real.norm_eq_abs] at k
      have heq : (C.scale p / ρ j)⁻¹ * (mvfderiv 𝓘(ℝ, E3) A p W / ρ j -
          mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W / ρ j) +
          ((C.scale p / ρ j)⁻¹ - (ρ p / ρ j)⁻¹) * (mvfderiv 𝓘(ℝ, E3) L.edge.smoothing p W / ρ j) -
          (A p / ρ j / (C.scale p / ρ j) / (C.scale p / ρ j)) *
            (mvfderiv 𝓘(ℝ, E3) C.scale p W / ρ j) +
          (L.edge.smoothing p / ρ j / (ρ p / ρ j) / (ρ p / ρ j)) *
            (mvfderiv 𝓘(ℝ, E3) ρ p W / ρ j) =
          mvfderiv 𝓘(ℝ, E3) Tq p W - mvfderiv 𝓘(ℝ, E3) t p W := by
        rw [hdT, hdt]
        field_simp
        ring
      simp only [smul_eq_mul] at k
      rw [heq] at k
      have : 0 ≤ κ * Δ := mul_nonneg hκ hΔ0.le
      linarith
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
      exact b1
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
      exact b2.trans (mul_le_mul_of_nonneg_right hΛκ hrj.le)
    · rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
      exact lt_of_le_of_lt b3 (mul_lt_mul_of_pos_right hHd hrj)
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
      exact lt_of_le_of_lt b4 (mul_lt_mul_of_pos_right (by linarith) hrj)


/-- A vector of `ℝ²` is bounded by the sum of its two coordinates. -/
theorem norm_le_abs_add_abs_EDPE (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]
  have h : (v 0) ^ 2 + (v 1) ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1)]
  calc Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) ≤ Real.sqrt ((|v 0| + |v 1|) ^ 2) := Real.sqrt_le_sqrt h
    _ = |v 0| + |v 1| := Real.sqrt_sq (by positivity)

section Pair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The differential of the homotopy pair `((1 − τ)f₁ + τh₁, (1 − τ)f₂ + τh₂)` is
`(1 − τ) D(f₁, f₂) + τ D(h₁, h₂)`. -/
theorem mvfderiv_homotopyPair_EDPE {f₁ f₂ h₁ h₂ : M → ℝ} {x : M} (τ : ℝ)
    (hf₁ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f₁ x) (hf₂ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f₂ x)
    (hh₁ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h₁ x) (hh₂ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h₂ x)
    (W : TangentSpace I x) :
    mvfderiv I (edgeReferenceCoordinates ![fun z => (1 - τ) * f₁ z + τ * h₁ z,
        fun z => (1 - τ) * f₂ z + τ * h₂ z]) x W =
      (1 - τ) • mvfderiv I (edgeReferenceCoordinates ![f₁, f₂]) x W +
        τ • mvfderiv I (edgeReferenceCoordinates ![h₁, h₂]) x W := by
  have hc : ∀ (f h : M → ℝ), ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x → ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z => (1 - τ) * f z + τ * h z) x := fun f h hf hh =>
    (contMDiffAt_const.mul hf).add (contMDiffAt_const.mul hh)
  have hd : ∀ (f h : M → ℝ), ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x → ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x →
      mvfderiv I (fun z => (1 - τ) * f z + τ * h z) x W =
        (1 - τ) * mvfderiv I f x W + τ * mvfderiv I h x W := fun f h hf hh => by
    have hf' := hf.mdifferentiableAt (by simp)
    have hh' := hh.mdifferentiableAt (by simp)
    have hf'' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => (1 - τ) * f z) x :=
      (contMDiffAt_const.mul hf).mdifferentiableAt (by simp)
    have hh'' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => τ * h z) x :=
      (contMDiffAt_const.mul hh).mdifferentiableAt (by simp)
    rw [mvfderiv_fun_add hf'' hh'', add_apply, mvfderiv_const_mul _ _ hf',
      mvfderiv_const_mul _ _ hh']
    rfl
  have hA : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![fun z => (1 - τ) * f₁ z + τ * h₁ z,
      fun z => (1 - τ) * f₂ z + τ * h₂ z] k) x := fun k => by
    fin_cases k
    · exact hc f₁ h₁ hf₁ hh₁
    · exact hc f₂ h₂ hf₂ hh₂
  have hF : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![f₁, f₂] k) x := fun k => by
    fin_cases k
    · exact hf₁
    · exact hf₂
  have hH : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![h₁, h₂] k) x := fun k => by
    fin_cases k
    · exact hh₁
    · exact hh₂
  ext k
  rw [edgeReferenceCoordinates_derivative hA W k, PiLp.add_apply, PiLp.smul_apply,
    PiLp.smul_apply, edgeReferenceCoordinates_derivative hF W k,
    edgeReferenceCoordinates_derivative hH W k]
  fin_cases k
  · exact hd f₁ h₁ hf₁ hh₁
  · exact hd f₂ h₂ hf₂ hh₂

end Pair


/-- **EDP04's homotopy (EI) on the chain object: the co-norm on the collar** (B:7005–7013): with
`h_* = 50(c₃ + κΔ)` (`κ = C_ρΛ`), at every point of `Y_j`'s collar `3.9Δ < t < 4.1Δ` and every
`τ ∈ [0, 1]`, the pair `H_τ = ((1 − τ)η + τg, (1 − τ)H₀ + τT)` has, for every unit `ξ ∈ ℝ²`, an
`R_j⁻²g`-unit `W` (`g(W, W) = R_j²`) with `⟪DH_τ(W), ξ⟫ > .9 − (c₃ + h_*)`; and
`c₃ + h_* < 1/500`. -/
theorem Gaf02Chain.edge_homotopy_conorm_EDPE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ L.edge.centres) :
    let κ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight Δ L.edge.smoothing ρ
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    c 2 + 50 * (c 2 + κ * Δ) < 1 / 500 ∧
    ∀ p ∈ ball j (100 * Δ * ρ j), |η p| < 5 * Δ → 39 / 10 * Δ < t p → t p < 41 / 10 * Δ →
      ∀ θ ∈ Icc (0 : ℝ) 1, ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
        ∃ W : TangentSpace 𝓘(ℝ, E3) p, g.inner p W W = ρ j ^ 2 ∧
          9 / 10 - (c 2 + 50 * (c 2 + κ * Δ)) < inner ℝ (mvfderiv 𝓘(ℝ, E3)
            (edgeReferenceCoordinates ![fun z => (1 - θ) * η z + θ * gq z,
              fun z => (1 - θ) * H₀ z + θ * Tq z]) p W) ξ := by
  intro κ jF η t H₀ A Tq gq
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hEH := C.edge_height_EH_EDPE hcw hSΞ hc hϑ hε0 hε hj
  obtain ⟨hhs, -, hEHd⟩ := hEH
  refine ⟨by linarith, fun p hp hη ht1 ht2 θ hθ ξ hξ => ?_⟩
  have hrj := hρ j
  obtain ⟨-, hco⟩ := L.edge.collar_conorm_phys_EDP3 hγc hγc1 hβc1 hΔ0 hj hp hη ht1 ht2
  obtain ⟨hev, hD, -, -⟩ := L.edge.collar_height_conorm_EDP3 hγc hγc1 hβc1 hΔ0 hj hp hη ht1 ht2
  obtain ⟨-, -, -, hT, hg⟩ := C.final_smooth_EDPE
  obtain ⟨Hd, hHd, -, -, -, hedge⟩ := C.final_derivative_EDPE
  have hηc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ η p :=
    (L.edge.contMDiffOn_coord hj).contMDiffAt (isOpen_ball.mem_nhds hp)
  have htc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ t p :=
    L.edge.contMDiffAt_height_of_collar hj hp (by linarith) (by linarith) (by linarith)
  have hHc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H₀ p := htc.congr_of_eventuallyEq hev
  have hgc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ gq p := hg jF p
  have hTc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ Tq p := hT p
  have hpair : ∀ W : TangentSpace 𝓘(ℝ, E3) p,
      mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![fun z => (1 - θ) * η z + θ * gq z,
        fun z => (1 - θ) * H₀ z + θ * Tq z]) p W =
      (1 - θ) • mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W +
        θ • mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p W := fun W => by
    rw [mvfderiv_homotopyPair_EDPE θ hηc hHc hgc hTc W]
    change _ = (1 - θ) • mvfderiv 𝓘(ℝ, E3)
      (edgeReferenceCoordinates ![L.edge.coord j, fun z => L.edge.smoothing z / ρ z]) p W + _
    rw [← hD]
  have hFc : ∀ k, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (![η, t] k) p := fun k => by
    fin_cases k
    · exact hηc
    · exact htc
  have hGc : ∀ k, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (![gq, Tq] k) p := fun k => by
    fin_cases k
    · exact hgc
    · exact hTc
  have hab : ∀ W ∈ {W : TangentSpace 𝓘(ℝ, E3) p | g.inner p W W = ρ j ^ 2},
      ‖mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p W -
        mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W‖ ≤
        c 2 + 50 * (c 2 + κ * Δ) := by
    intro W hW
    have hW' : g.inner p W W = ρ j ^ 2 := hW
    have hunit : (ρ j)⁻¹ ^ 2 * g.inner p W W = 1 := by
      rw [hW']
      field_simp
    refine (norm_le_abs_add_abs_EDPE _).trans ?_
    rw [PiLp.sub_apply, PiLp.sub_apply, edgeReferenceCoordinates_derivative hGc W 0,
      edgeReferenceCoordinates_derivative hFc W 0, edgeReferenceCoordinates_derivative hGc W 1,
      edgeReferenceCoordinates_derivative hFc W 1]
    have h0 := hedge jF p hp (by linarith) (by linarith) W
    rw [hunit, Real.sqrt_one, mul_one] at h0
    have h1 := hEHd p hp hη (by linarith) (by linarith) W hunit
    change |mvfderiv 𝓘(ℝ, E3) gq p W - mvfderiv 𝓘(ℝ, E3) η p W| +
      |mvfderiv 𝓘(ℝ, E3) Tq p W - mvfderiv 𝓘(ℝ, E3) t p W| ≤ c 2 + 50 * (c 2 + κ * Δ)
    linarith
  have ha : ∀ ξ' : EuclideanSpace ℝ (Fin 2), ‖ξ'‖ = 1 →
      ∃ W ∈ {W : TangentSpace 𝓘(ℝ, E3) p | g.inner p W W = ρ j ^ 2},
        9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![η, t]) p W) ξ' :=
    fun ξ' hξ' => by
      obtain ⟨W, hW, -, h9⟩ := hco ξ' hξ'
      exact ⟨W, hW, h9⟩
  obtain ⟨W, hW, hlt⟩ := conorm_homotopy_EDP3 _ _ _ ha hab hθ.1 hθ.2 ξ hξ
  exact ⟨W, hW, by rw [hpair W]; exact hlt⟩


/-- **EDP04's whole time trace and its rim, on the chain object** (B:6974–6985, B:6989–6993): for
`τ ∈ [0, 1]`, `|a| < 4Δ` and `p ∈ Y_j` with `(1 − τ)η + τg = a` and `(1 − τ)H₀ + τT ≤ 4Δ`:
`|η| < 4.01Δ` and `t < 4.01Δ` (so `p` lies in EDP03's (EBuf) set, inside `int Q_j`); and if
`(1 − τ)H₀ + τT = 4Δ` (the inverse image of `∂X_a`), then `|t − 4Δ| < h_*`, `3.9Δ < t < 4.1Δ`. -/
theorem Gaf02Chain.edge_trace_EDPE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) {j : X} (hj : j ∈ L.edge.centres) :
    let κ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight Δ L.edge.smoothing ρ
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    ∀ θ ∈ Icc (0 : ℝ) 1, ∀ p ∈ ball j (100 * Δ * ρ j), |η p| < 5 * Δ → t p < 5 * Δ →
      ∀ a : ℝ, |a| < 4 * Δ → (1 - θ) * η p + θ * gq p = a →
        (1 - θ) * H₀ p + θ * Tq p ≤ 4 * Δ →
        |η p| < 401 / 100 * Δ ∧ t p < 401 / 100 * Δ ∧
          ((1 - θ) * H₀ p + θ * Tq p = 4 * Δ →
            |t p - 4 * Δ| < 50 * (c 2 + κ * Δ) ∧ 39 / 10 * Δ < t p ∧ t p < 41 / 10 * Δ) := by
  intro κ jF η t H₀ A Tq gq θ hθ p hp hη ht5 a ha hfib hH
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hhs, hEHv, -⟩ := C.edge_height_EH_EDPE hcw hSΞ hc hϑ hε0 hε hj
  obtain ⟨-, hlow, -⟩ := C.low_branch_EDPE hc
  obtain ⟨hc0, hc01, hc12⟩ := C.accuracy_order_EDPE
  have hκ0 : 0 ≤ κ * Δ := by
    have hκ : 0 ≤ κ := by
      obtain ⟨hnum, -⟩ := C.numbers
      have hS0 : 0 < S 0 := (hnum 0).2.1
      have h1 := one_le_gafDerivativeBound
      have h2 := gafCutoffConstant_nonneg
      have h3 : 0 ≤ 1 * cw 0 / S 0 := div_nonneg (by linarith) hS0.le
      have : 0 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) := by
        positivity
      exact mul_nonneg this hΛ
    exact mul_nonneg hκ hΔ0.le
  have hgη := ((C.edgeAxis_value_EDPE jF p).2 hp (by linarith) (by linarith)).2
  change |gq p - η p| < 5 / 4 * c 2 at hgη
  have hθ0 := hθ.1
  have hθ1 := hθ.2
  -- the coordinate
  have hηa : η p - a = θ * (η p - gq p) := by rw [← hfib]; ring
  have hηa' : |η p - a| ≤ |gq p - η p| := by
    rw [hηa, abs_mul, abs_of_nonneg hθ0, abs_sub_comm]
    calc θ * |gq p - η p| ≤ 1 * |gq p - η p| :=
          mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
      _ = |gq p - η p| := one_mul _
  have hη401 : |η p| < 401 / 100 * Δ := by
    have := abs_sub_abs_le_abs_sub (η p) a
    linarith
  have ht0 : 0 ≤ t p := div_nonneg (L.edge.smoothing_nonneg p) (hρ p).le
  -- the height, by cases
  have hlowT : t p ≤ 2 * Δ → Tq p < 2 * Δ + 50 * (c 2 + κ * Δ) := fun h2 => by
    rcases lt_or_ge (t p) (3 / 10 * Δ) with h3 | h3
    · have := hlow p h3
      linarith
    · have := hEHv p hp hη h3 ht5
      have := (abs_lt.mp this).2
      linarith
  have hH₀2 : t p ≤ 2 * Δ → H₀ p ≤ 2 * Δ := fun h2 => edgeRowHeight_le_two_EDP3 hΔ0 h2
  have hH₀t : 2 * Δ ≤ t p → H₀ p = t p := fun h2 => edgeRowHeight_eq_self_EDP3 hΔ0 h2
  have hhigh : 2 * Δ < t p → |Tq p - t p| < 50 * (c 2 + κ * Δ) := fun h2 =>
    hEHv p hp hη (by linarith) ht5
  refine ⟨hη401, ?_, fun hrim => ?_⟩
  · rcases le_or_gt (t p) (2 * Δ) with h2 | h2
    · linarith
    · have hE := hhigh h2
      rw [hH₀t h2.le] at hH
      have hle : t p - 4 * Δ ≤ θ * (t p - Tq p) := by nlinarith
      have hθT : θ * (t p - Tq p) ≤ |Tq p - t p| := by
        rw [← abs_sub_comm]
        calc θ * (t p - Tq p) ≤ θ * |t p - Tq p| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hθ0
          _ ≤ 1 * |t p - Tq p| := mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
          _ = |t p - Tq p| := one_mul _
      linarith
  · have h2 : 2 * Δ < t p := by
      by_contra hcon
      rw [not_lt] at hcon
      have hA := hH₀2 hcon
      have hB := hlowT hcon
      have hsum : (1 - θ) * H₀ p + θ * Tq p < 4 * Δ := by
        have e1 : (1 - θ) * H₀ p ≤ (1 - θ) * (2 * Δ) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have e2 : θ * Tq p ≤ θ * (2 * Δ + 50 * (c 2 + κ * Δ)) :=
          mul_le_mul_of_nonneg_left hB.le hθ0
        nlinarith
      linarith
    have hE := hhigh h2
    rw [hH₀t h2.le] at hrim
    have heq : t p - 4 * Δ = θ * (t p - Tq p) := by linarith
    have hθT : |θ * (t p - Tq p)| ≤ |Tq p - t p| := by
      rw [abs_mul, abs_of_nonneg hθ0, abs_sub_comm]
      calc θ * |Tq p - t p| ≤ 1 * |Tq p - t p| :=
            mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
        _ = |Tq p - t p| := one_mul _
    have hfin : |t p - 4 * Δ| < 50 * (c 2 + κ * Δ) := by
      rw [heq]
      exact lt_of_le_of_lt hθT hE
    refine ⟨hfin, ?_, ?_⟩
    · have := (abs_lt.mp hfin).1
      linarith
    · have := (abs_lt.mp hfin).2
      linarith


/-- **EDP04–EDP06's final-time rank along the rim, on the chain object** (EDP04 B:7010–7012,
EDP05 B:7080–7084, EDP06 B:7103–7105): at a point of `Y_j` with `|g| < 4Δ` and `T = 4Δ`:
`|η| < 4.01Δ`, `|t − 4Δ| < h_* < 1/1000` (EDP06's band), `D(g, T)` is onto, and for every `b` with
`b'(g(p)) ≠ 0` the pair `(d(b ∘ g), dT)` is onto (EDP05's face independence `H ∩ V_e`). -/
theorem Gaf02Chain.edge_vertical_rank_EDPE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ L.edge.centres) :
    let κ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    ∀ p ∈ ball j (100 * Δ * ρ j), |η p| < 5 * Δ → t p < 5 * Δ → |gq p| < 4 * Δ →
      Tq p = 4 * Δ →
      |η p| < 401 / 100 * Δ ∧ |t p - 4 * Δ| < 50 * (c 2 + κ * Δ) ∧
        50 * (c 2 + κ * Δ) < 1 / 1000 ∧
        Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p) ∧
        ∀ (bf : ℝ → ℝ) (bd : ℝ), HasDerivAt bf bd (gq p) → bd ≠ 0 →
          Function.Surjective (fun W : TangentSpace 𝓘(ℝ, E3) p =>
            (mvfderiv 𝓘(ℝ, E3) (fun z => bf (gq z)) p W, mvfderiv 𝓘(ℝ, E3) Tq p W)) := by
  intro κ jF η t A Tq gq p hp hη ht5 hga hT4
  have htr := C.edge_trace_EDPE hcw hSΞ hc hϑ hε0 hε hj 1 ⟨zero_le_one, le_rfl⟩ p hp hη ht5
    (gq p) hga (by ring) (by rw [sub_self, zero_mul, zero_add, one_mul]; exact le_of_eq hT4)
  obtain ⟨hη401, -, hrim⟩ := htr
  obtain ⟨hband, ht1, ht2⟩ := hrim (by rw [sub_self, zero_mul, zero_add, one_mul]; exact hT4)
  obtain ⟨hhs, -, -⟩ := C.edge_height_EH_EDPE hcw hSΞ hc hϑ hε0 hε hj
  obtain ⟨hsmall, hco⟩ := C.edge_homotopy_conorm_EDPE hcw hSΞ hc hϑ hε0 hε hγc hγc1 hβc1 hj
  have hco1 := hco p hp hη ht1 ht2 1 ⟨zero_le_one, le_rfl⟩
  have hfun : edgeReferenceCoordinates ![fun z => (1 - 1) * η z + 1 * gq z,
      fun z => (1 - 1) * edgeRowHeight Δ L.edge.smoothing ρ z + 1 * Tq z] =
      edgeReferenceCoordinates ![gq, Tq] := by
    congr 1
    funext k
    fin_cases k <;> funext z <;> simp
  rw [hfun] at hco1
  have hsurj : Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p) := by
    refine surjective_of_conorm_pos_EDP6
      (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p).toLinearMap (fun ξ hξ => ?_)
    obtain ⟨W, -, hW⟩ := hco1 ξ hξ
    refine ⟨W, ?_⟩
    change 0 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![gq, Tq]) p W) ξ
    linarith
  obtain ⟨-, -, -, hT, hg⟩ := C.final_smooth_EDPE
  have hGc : ∀ k, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (![gq, Tq] k) p := fun k => by
    fin_cases k
    · exact hg jF p
    · exact hT p
  have hpair : Function.Surjective (fun W : TangentSpace 𝓘(ℝ, E3) p =>
      (mvfderiv 𝓘(ℝ, E3) gq p W, mvfderiv 𝓘(ℝ, E3) Tq p W)) := by
    intro y
    obtain ⟨W, hW⟩ := hsurj (WithLp.toLp 2 ![y.1, y.2])
    refine ⟨W, ?_⟩
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hW
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hW
    simp only at h0 h1
    rw [edgeReferenceCoordinates_derivative hGc W 0] at h0
    rw [edgeReferenceCoordinates_derivative hGc W 1] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  refine ⟨hη401, hband, hhs, hsurj, fun bf bd hbf hbd => ?_⟩
  have hgd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) gq p := (hg jF p).mdifferentiableAt (by simp)
  have hs := EdgeDisk.pair_surjective_smul_left (mvfderiv 𝓘(ℝ, E3) gq p).toLinearMap
    (mvfderiv 𝓘(ℝ, E3) Tq p).toLinearMap hbd hpair
  intro y
  obtain ⟨W, hW⟩ := hs y
  refine ⟨W, ?_⟩
  change (mvfderiv 𝓘(ℝ, E3) (fun z => bf (gq z)) p W, mvfderiv 𝓘(ℝ, E3) Tq p W) = y
  rw [mvfderiv_comp_hasDerivAt hgd hbf W]
  exact hW

end DifferentialGeometry.Geometry.Collapse
