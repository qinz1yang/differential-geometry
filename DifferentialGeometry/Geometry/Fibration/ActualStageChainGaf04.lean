import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneFullMarkerApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# GAF04 on the chain object, as a consumer of the same-plane (FM\*) certificate

Blueprint `master207B.tex`, GAF04 (`lem:fibration-actual-full-marker-contributors`, B:5896–5970);
external review 66, disposition D66-8: "GAF04 as a consumer of `C` + a same-plane FM certificate
(FM\* source = ChainE)". The certificate is the enhanced planes object `A` of the stage (lane
C14-PLANES: `FirstStagePlanes_PLN`, `EdgeStagePlanes_PLN`, `SlimStagePlanes_PLN`) together with the
two binding equations of the chain to it, `C.sel st = A.rsel x₀` and `C.plane st = A.plane` —
exactly
the fields `planes_st`, `x₀`, `sel_eq`, `plane_eq` of the forthcoming `Gaf02ChainE` (state-C14-GAF8,
G7 design), so `Ĉ : Gaf02ChainE` instantiates these theorems with `C := Ĉ.toChain`. Nothing about
the plane is assumed: (FM) is PROVED from `A`'s fields by (FM\*) (`*.full_marker`).

For stage `st`, a marked chart `i` of the stage, a threshold-`7` core point `p` (edges also
`t(p) ≤ 7Δ`), `x = π_st𝓔⁰(p)`, `b = Ξ_st⁻¹`, `r = Σ_stρ(C.sel st ·)` and GAF04's own hypothesis
`Σ_st ≤ Ξ_st/10000`:

* (FM) for EVERY selected smoothing centre `y ∈ S_st` whose closed `80br_y` support meets
  `B(x, 8br_x)`: `v_i(y) = R_i` and `C.plane st y ≤ ker v_i`;
* "consequently GAF03 applies with `J = v_i`, `c = R_i`": the chain's own slot map satisfies
  `v_i(a_st z) = R_i` on the whole ball `B(x, r_x)` (slot locality, `Gaf02StageSlot.bounds`).

`Gaf02Chain.gaf04_first_G47`, `gaf04_edge_G47`, `gaf04_slim_G47`; helpers
`Gaf02Chain.eg_bounds_G47` (`0 ≤ e_j < 1/100` from the chain's CHOICE numbers),
`marker_starProjection_orth_ker_G47`. Consumer `gaf04_final_family_slot_marker_G47` (a chain on
`LocalChartPacketsC14Z` with its three enhanced planes).
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

/-- A scalar functional is unchanged by the projection onto the orthogonal complement of its
kernel: `v((ker v)ᗮ.starProjection w) = v(w)`. -/
theorem marker_starProjection_orth_ker_G47 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (v : H →L[ℝ] ℝ) (w : H) :
    v ((LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w) = v w := by
  have h : w - (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w ∈
      (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal w
  rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker, map_sub] at h
  have h' : v w - v ((LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w) = 0 := h
  linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

/-- The chain's CHOICE numbers give `0 ≤ e_j < 1/100` at every stage (`e_j < c_j ≤ 1/512`). -/
theorem eg_bounds_G47 {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : ∀ j, 0 ≤ eg j ∧ eg j < 1 / 100 := by
  obtain ⟨hnum, h0, hc0, hd0, -, -, a1, hc1, hd1, -, -, -, hc2, hd2⟩ := C.numbers
  have hb := gafCutoffConstant_nonneg
  have hL := one_le_gafDerivativeBound
  have hpos : ∀ j, 0 < Ξ j ∧ 0 < S j := fun j => ⟨(hnum j).1, (hnum j).2.1⟩
  have hc0p : 0 < c 0 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hpos 0).1) (hpos 0).2
    linarith
  have hc1p : 0 < c 1 := by
    have u1 := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hpos 1).1) (hpos 1).2
    have u2 : 0 ≤ (1 + Ξ 1) * c 0 := mul_nonneg (by linarith [(hpos 1).1]) hc0p.le
    linarith
  intro j
  refine ⟨(hnum j).2.2.2, ?_⟩
  fin_cases j
  · have t1 : 0 ≤ 5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hpos 0).1.le) (hpos 0).2.le) hb)
        (by linarith)
    have t2 : 0 ≤ Ξ 0 * gafDerivativeBound := mul_nonneg (hpos 0).1.le (by linarith)
    simp only [Fin.zero_eta, Fin.isValue]
    linarith
  · have t0 : 0 ≤ 5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hpos 1).1.le) (hpos 1).2.le)
        (mul_nonneg (by linarith [(hpos 1).1]) hc0p.le)
    have t1 : 0 ≤ (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant *
        (gafDerivativeBound + c 0) :=
      mul_nonneg (mul_nonneg t0 hb) (by linarith)
    have t2 : 0 ≤ Ξ 1 * (gafDerivativeBound + c 0) := mul_nonneg (hpos 1).1.le (by linarith)
    simp only [Fin.mk_one, Fin.isValue]
    linarith
  · have t0 : 0 ≤ 5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hpos 2).1.le) (hpos 2).2.le)
        (mul_nonneg (by linarith [(hpos 2).1]) hc1p.le)
    have t1 : 0 ≤ (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant *
        (gafDerivativeBound + c 1) :=
      mul_nonneg (mul_nonneg t0 hb) (by linarith)
    have t2 : 0 ≤ Ξ 2 * (gafDerivativeBound + c 1) := mul_nonneg (hpos 2).1.le (by linarith)
    simp only [Fin.reduceFinMk, Fin.isValue]
    linarith

/-- **GAF04 on the chain, circle (first) stage: `p ∈ B(c_i, 200ρ(c_i))`, `‖η_i(p)‖ ≤ 7`** (B:5896),
as a consumer of the
same-plane (FM\*) certificate `A` (`C.sel 0 = A.rsel x₀`, `C.plane 0 = A.plane`; the fields of
`Gaf02ChainE`): with `Σ ≤ Ξ/10000`, every centre `y ∈ S_0` whose closed `80Ξ⁻¹r_y` support meets
`B(x, 8Ξ⁻¹r_x)`, `x = π𝓔⁰(p)`, `r = Σρ(C.sel 0 ·)`, has `v_i(y) = R_i` and `C.plane 0 y ≤ ker v_i`
(FM); consequently (GAF03, `J = v_i`, `c = R_i`) the chain's slot map has `v_i(a z) = R_i` on
`B(x, r_x)`. -/
theorem gaf04_first_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0)) (x₀ : X) (hsel : C.sel 0 = A.rsel x₀)
    (hplane : C.plane 0 = A.plane) (hSΞ : S 0 ≤ Ξ 0 / 10000)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hηp : ‖cgpCircleCoord P.toLocalChartFamily i.1 ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall y (80 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p)
          (8 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 0) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) y = ρ i.1 ∧
        C.plane 0 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        p)
        (S 0 * ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 0) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) ((C.slot 0).map z) = ρ i.1 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  obtain ⟨heg0, heg⟩ := C.eg_bounds_G47 0
  obtain ⟨hnum, -⟩ := C.numbers
  have hε : 0 < Ξ 0 := (hnum 0).1
  have hS : 0 < S 0 := (hnum 0).2.1
  have hFM : ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall y (80 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p)
          (8 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 0) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) y = ρ i.1 ∧
        C.plane 0 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
    intro y hy hmeet
    rw [hsel] at hmeet
    rw [hplane]
    exact A.full_marker hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp rfl hy hmeet
  refine ⟨hFM, fun z hz => ?_⟩
  have hx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p ∈
      gafCloud P.toLocalChartFamily P.zero 0 :=
    ⟨p, (show p ∈ fc04Set P.toLocalChartFamily P.zero 7 from ⟨i, hpi, hηp⟩), rfl⟩
  have hloc := ((C.slot 0).bounds _ hx z hz).2.2.2
    (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ
    ((LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection
              (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
                  p))
    (fun y hy hmeet => by
      rw [hsel] at hmeet
      rw [hplane]
      exact A.gaf03_input hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp rfl y hy hmeet)
  have hr : 0 < ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
      P.toLocalChartFamily P.zero 0) p)) := hρ _
  have hself := hFM _ hx ⟨_, mem_closedBall_self (by positivity), mem_ball_self (by positivity)⟩
  rw [← marker_starProjection_orth_ker_G47, hloc, marker_starProjection_orth_ker_G47]
  exact hself.1

/-- **GAF04 on the chain, edge stage: `p ∈ B(c_i, 100Δρ(c_i))`, `|η_i(p)| ≤ 7Δ`, `t(p) ≤ 7Δ`**
(B:5896), as a consumer of the
same-plane (FM\*) certificate `A` (`C.sel 1 = A.rsel x₀`, `C.plane 1 = A.plane`; the fields of
`Gaf02ChainE`): with `Σ ≤ Ξ/10000`, every centre `y ∈ S_1` whose closed `80Ξ⁻¹r_y` support meets
`B(x, 8Ξ⁻¹r_x)`, `x = π𝓔⁰(p)`, `r = Σρ(C.sel 1 ·)`, has `v_i(y) = R_i` and `C.plane 1 y ≤ ker v_i`
(FM); consequently (GAF03, `J = v_i`, `c = R_i`) the chain's slot map has `v_i(a z) = R_i` on
`B(x, r_x)`. -/
theorem gaf04_edge_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (x₀ : X) (hsel : C.sel 1 = A.rsel x₀)
    (hplane : C.plane 1 = A.plane) (hSΞ : S 1 ≤ Ξ 1 / 10000)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hηp : |P.edge.coord i.1 p| ≤ 7 * Δ)
    (htp : cgpHeight P.toLocalChartFamily p ≤ 7 * Δ) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      (closedBall y (80 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p)
          (8 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 1) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) y = ρ i.1 ∧
        C.plane 1 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        p)
        (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 1) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) ((C.slot 1).map z) = ρ i.1 :=
              by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  obtain ⟨heg0, heg⟩ := C.eg_bounds_G47 1
  obtain ⟨hnum, -⟩ := C.numbers
  have hε : 0 < Ξ 1 := (hnum 1).1
  have hS : 0 < S 1 := (hnum 1).2.1
  have hFM : ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      (closedBall y (80 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p)
          (8 * (Ξ 1)⁻¹ * (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 1) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) y = ρ i.1 ∧
        C.plane 1 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
    intro y hy hmeet
    rw [hsel] at hmeet
    rw [hplane]
    exact A.full_marker hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp htp rfl hy hmeet
  refine ⟨hFM, fun z hz => ?_⟩
  have hx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p ∈
      gafCloud P.toLocalChartFamily P.zero 1 :=
    ⟨p, (show p ∈ fc27EdgeSet P.toLocalChartFamily 7 from ⟨i, hpi, hηp, htp⟩), rfl⟩
  have hloc := ((C.slot 1).bounds _ hx z hz).2.2.2
    (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ
    ((LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection
              (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
                  p))
    (fun y hy hmeet => by
      rw [hsel] at hmeet
      rw [hplane]
      exact A.gaf03_input hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp htp rfl y hy hmeet)
  have hr : 0 < ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
      P.toLocalChartFamily P.zero 1) p)) := hρ _
  have hself := hFM _ hx ⟨_, mem_closedBall_self (by positivity), mem_ball_self (by positivity)⟩
  rw [← marker_starProjection_orth_ker_G47, hloc, marker_starProjection_orth_ker_G47]
  exact hself.1

/-- **GAF04 on the chain, slim stage: `p ∈ B(c_i, 10⁶Δρ(c_i))`, `|η_i(p)| ≤ 7·10⁵Δ`** (B:5896), as
a consumer of the
same-plane (FM\*) certificate `A` (`C.sel 2 = A.rsel x₀`, `C.plane 2 = A.plane`; the fields of
`Gaf02ChainE`): with `Σ ≤ Ξ/10000`, every centre `y ∈ S_2` whose closed `80Ξ⁻¹r_y` support meets
`B(x, 8Ξ⁻¹r_x)`, `x = π𝓔⁰(p)`, `r = Σρ(C.sel 2 ·)`, has `v_i(y) = R_i` and `C.plane 2 y ≤ ker v_i`
(FM); consequently (GAF03, `J = v_i`, `c = R_i`) the chain's slot map has `v_i(a z) = R_i` on
`B(x, r_x)`. -/
theorem gaf04_slim_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2)) (x₀ : X) (hsel : C.sel 2 = A.rsel x₀)
    (hplane : C.plane 2 = A.plane) (hSΞ : S 2 ≤ Ξ 2 / 10000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηp : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ)) :
    (∀ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      (closedBall y (80 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p)
          (8 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 2) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) y = ρ i.1 ∧
        C.plane 2 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        p)
        (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
            P.toLocalChartFamily P.zero 2) p))),
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) ((C.slot 2).map z) = ρ i.1 :=
              by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  obtain ⟨heg0, heg⟩ := C.eg_bounds_G47 2
  obtain ⟨hnum, -⟩ := C.numbers
  have hε : 0 < Ξ 2 := (hnum 2).1
  have hS : 0 < S 2 := (hnum 2).2.1
  have hFM : ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      (closedBall y (80 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 y))) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p)
          (8 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 2) p))))).Nonempty →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) y = ρ i.1 ∧
        C.plane 2 y ≤ LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
            P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
    intro y hy hmeet
    rw [hsel] at hmeet
    rw [hplane]
    exact A.full_marker hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp rfl hy hmeet
  refine ⟨hFM, fun z hz => ?_⟩
  have hx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p ∈
      gafCloud P.toLocalChartFamily P.zero 2 :=
    ⟨p, (show p ∈ fc27SlimSet P.toLocalChartFamily 7 from ⟨i, hpi, by linarith⟩), rfl⟩
  have hloc := ((C.slot 2).bounds _ hx z hz).2.2.2
    (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ
    ((LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ.starProjection
              (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
                  p))
    (fun y hy hmeet => by
      rw [hsel] at hmeet
      rw [hplane]
      exact A.gaf03_input hΔ hΛ hLΛ heg0 heg hε hS.le hSΞ x₀ i hpi hηp rfl y hy hmeet)
  have hr : 0 < ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
      P.toLocalChartFamily P.zero 2) p)) := hρ _
  have hself := hFM _ hx ⟨_, mem_closedBall_self (by positivity), mem_ball_self (by positivity)⟩
  rw [← marker_starProjection_orth_ker_G47, hloc, marker_starProjection_orth_ker_G47]
  exact hself.1

end Gaf02Chain

/-- **Consumer: GAF04 ⇒ GAF03 on a chain over the final family** `LocalChartPacketsC14Z` bound to
its three enhanced stage planes (the data of `Gaf02ChainE`): at a threshold-`7` core point of a
marked edge chart (resp. slim chart) the stage-two (resp. stage-three) slot map has the exact
marker `R_i` on the whole tube ball `B(π𝓔⁰ p, Σρ(sel(π𝓔⁰ p)))`. -/
theorem gaf04_final_family_slot_marker_G47 {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (x₀ : X)
    (A₁ : EdgeStagePlanes_PLN P.toLocalChartPacketsC14 (Γ 1) (S 1) (eg 1))
    (A₂ : SlimStagePlanes_PLN P.toLocalChartPacketsC14 (Γ 2) (S 2) (eg 2))
    (hsel₁ : C.sel 1 = A₁.rsel x₀) (hplane₁ : C.plane 1 = A₁.plane)
    (hsel₂ : C.sel 2 = A₂.rsel x₀) (hplane₂ : C.plane 2 = A₂.plane)
    (hSΞ₁ : S 1 ≤ Ξ 1 / 10000) (hSΞ₂ : S 2 ≤ Ξ 2 / 10000) {p : X} :
    (∀ i : P.toLocalChartFamily.edge.finite_centres.toFinset,
      p ∈ ball i.1 (100 * Δ * ρ i.1) → |P.edge.coord i.1 p| ≤ 7 * Δ →
      cgpHeight P.toLocalChartFamily p ≤ 7 * Δ →
      ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero
          1) p) (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 1) p))),
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl
            i))) ((C.slot 1).map z) = ρ i.1) ∧
    ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 * (10 ^ 5 * Δ) →
      ∀ z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero
          2) p) (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 2) p))),
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
            ((C.slot 2).map z) = ρ i.1 :=
  ⟨fun i hpi hηp htp => (Gaf02Chain.gaf04_edge_G47 (P := P.toLocalChartPacketsC14) C A₁ x₀ hsel₁
      hplane₁ hSΞ₁ i hpi hηp htp).2,
    fun i hpi hηp => (Gaf02Chain.gaf04_slim_G47 (P := P.toLocalChartPacketsC14) C A₂ x₀ hsel₂
      hplane₂ hSΞ₂ i hpi hηp).2⟩

end DifferentialGeometry.Geometry.Collapse
