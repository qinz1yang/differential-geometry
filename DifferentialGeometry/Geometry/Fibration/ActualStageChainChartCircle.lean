import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartTools
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches
import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# GAF02 BASES on the chain: CGP06 and CGP07 for the circle charts (stage one)

Blueprint `master207B.tex`, CGP06 (B:4130–4174), CGP07 (B:4176–4247); external draft 59 §4, third
to fifth steps (D59-5); review 66 §5.4 steps 3–5 (D66-7). Indexed by ONE chain
`C : Gaf02Chain P.toLocalChartPackets …` and its rough data `R : Gaf02RoughData C`; no further
hypothesis.

* `circle_section_BAS`: CGP03's circle inner section extended to `ℝ²`.
* `Gaf02Chain.cgp06_circle_BAS`: at a first-cloud point `x` and a preimage `q` in chart `j`
  (`‖η_j(q)‖ ≤ 8`), `‖v‖ ≤ 2Ω‖u_j v‖` on the chain's plane `L_x` (the plane's (PP) at `q` from
  `C.test0`, TCP05's graph from `R.circle`, (OS) from `R.os`; deviation: no right inverse of `Dη_j`,
  see G4).
* `Gaf02Chain.cgp07_circle_BAS`: `R_j⁻¹u_j : V_j⁰ → B(0, 5.5)` bijective, `V_j⁰ ⊆ f₁(B⁶_j)`
  (ORIGINAL threshold-6 plateau of the chart), smooth inverse chart landing in `V_j⁰`, compact
  preimages — on the native zero set of the chain's own stage output, with (MW) from CGP05, (SN)
  from (OS), the section's Brouwer step and (PLAT).
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **CGP03's circle section, extended to `ℝ²`** (`exists_ball_extension_BAS`): continuous on
`B(0, 23/4)`, there `η_j(s b) = b`, `s b ∈ B(c_j, 200ρ_j)`, `ζ_j(s b) = 1`,
`ρ(s b) ∈ [3ρ_j/4, 5ρ_j/4]`. -/
theorem circle_section_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (hΛ : 0 ≤ Λ) (hbud : Λ * 102 ≤ 1 / 4)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ secE : ℝ² → X, ContinuousOn secE (ball 0 (23 / 4)) ∧ ∀ b ∈ ball (0 : ℝ²) (23 / 4),
      cgpCoord P.toLocalChartFamily P.zero (.inl j) (secE b) = b ∧
      secE b ∈ ball j.1 (200 * ρ j.1) ∧ P.circle.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1 := by
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨sec, hsc, hs⟩ := cgp03_circle_section P.toLocalChartFamily hΛ hbud hj
  obtain ⟨secE, hcont, heq⟩ := exists_ball_extension_BAS j.1 sec hsc
  refine ⟨secE, hcont, fun b hb => ?_⟩
  rw [heq b hb]
  exact hs ⟨b, hb⟩


namespace Gaf02Chain


variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **CGP06 on the chain, circle stage** (draft 59 §4 third step, review 66 §5.4 step 3): at a
point `x` of the first cloud and a preimage `q` of `x` in the circle chart `j` with `‖η_j(q)‖ ≤ 8`,
every vector of the chain's plane `L_x` has `‖v‖ ≤ 2Ω‖u_j v‖`. Inputs: the plane's (PP) data at `q`
(`C.test0`, any reference), TCP05's rough graph `Φ_j` at `q` (`R.circle`) and GAF01's (OS)
(`R.os`). -/
theorem cgp06_circle_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0) {q : X}
    (hq : cgpGlobalMap P.toLocalChartFamily P.zero q = x) (hqj : q ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ ≤ 8) :
    ∀ v ∈ C.plane 0 x,
      ‖v‖ ≤ 2 * gafGraphOmega_BAS * ‖gafCircleVector P.toLocalChartPackets j v‖ := by
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨Φ, hΦs, hΦown, hΦbd, hΦcl⟩ := R.circle j.1 hj
  obtain ⟨-, hrough⟩ := hΦcl q hqj hη
  obtain ⟨i, hPP⟩ := C.test0.2.2.1 x hx
  obtain ⟨hsurj, hnorm, hlow, -⟩ := hPP q hq
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) q) := inferInstanceAs (FiniteDimensional ℝ E3)
  have hρi := hρ i.1
  have hρj := hρ j.1
  have hown : ∀ a, gafCircleVector P.toLocalChartPackets j (Φ a) = a := by
    intro a
    rw [gafCircleVector, blockVectorCLM_apply, hΦown j rfl a]
    rfl
  have hπT : ∀ y, gafCircleVector P.toLocalChartPackets j
      (fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily j.1 hj q) y) = y :=
    clm_fderiv_of_left_inverse_BAS _ ((hΦs.differentiable (by simp)) _) hown
  have hT : ∀ y, ‖fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily j.1 hj q) y‖ ≤
      gafGraphOmega_BAS * ‖y‖ := fun y =>
    ((fderiv ℝ Φ _).le_opNorm y).trans (mul_le_mul_of_nonneg_right
      ((hΦbd _).1.trans tcpGraphConst_le_gafGraphOmega_BAS) (norm_nonneg y))
  exact retained_coordinate_of_pp_rescaled_BAS (V := TangentSpace 𝓘(ℝ, E3) q)
    (H := BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (E := ℝ²)
    (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q)
    (ContinuousLinearMap.toLinearMap₁₂ (g.inner q)) (fun w hw => by simpa using g.pos q w hw)
    (C.plane 0 x) hρi hρj (C.numbers.1 0).2.2.2 hsurj hnorm
    (fun w hw => hlow w (fun k hk => by simpa using hw k hk))
    (gafCircleVector P.toLocalChartPackets j) (norm_blockVectorCLM_le _) _ hπT hT _ hrough
    one_le_gafGraphOmega_BAS (os_small_BAS R 0)


/-- **CGP07 on the chain, circle stage** (draft 59 §4 fourth–fifth steps; `cgp07_one_sheet_BPRE`
instantiated on `(C, R)`): the retained coordinate `R_j⁻¹u_j` is a bijection of the circle patch
`V_j⁰` (`v_j > .9R_j` only, no GAF05 marker) onto `B(0, 5.5)`; every point of `V_j⁰` is `f₁(p)`
for a `p` of the chart's ORIGINAL threshold-6 plateau; the inverse chart `φ_j` is smooth on the
ball, inverts the coordinate and lands in `V_j⁰`; compact subsets of the ball have compact
preimages in `V_j⁰`. -/
theorem cgp07_circle_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    BijOn ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.circlePatch_BAS j)
        (ball 0 (11 / 2 * 1)) ∧
      (∀ w ∈ C.circlePatch_BAS j, ∃ p, (p ∈ ball j.1 (200 * ρ j.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) ∧ C.stageMap_BAS 0 p = w) ∧
      ∃ φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * 1)) ∧
        InvOn φ ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.circlePatch_BAS j)
          (ball 0 (11 / 2 * 1)) ∧
        MapsTo φ (ball 0 (11 / 2 * 1)) (C.circlePatch_BAS j) ∧
        ∀ K ⊆ ball (0 : ℝ²) (11 / 2 * 1), IsCompact K →
          IsCompact (C.circlePatch_BAS j ∩
            ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) ⁻¹' K) := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hρj := hρ j.1
  have hbud : Λ * 102 ≤ 1 / 4 := by
    have h := C.small_BAS
    nlinarith
  obtain ⟨Φ, hΦs, -, hΦbd, hΦcl⟩ := R.circle j.1 hj
  obtain ⟨secE, hsecC, hsec⟩ := circle_section_BAS P.toLocalChartPackets hΛ hbud j
  have hΩ := one_le_gafGraphOmega_BAS
  obtain ⟨hΞ0, hS0, -, he0⟩ := C.numbers.1 0
  obtain ⟨hεos, heos, -⟩ := R.os 0
  have hc0 := C.c_pos_BAS 0
  have hc1 := C.c_le_BAS 0
  -- the inner section stays in the section's ball
  have hsub : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), closedBall a (1 / 100) ⊆ ball (0 : ℝ²) (23 / 4) := by
    intro a ha b hb
    rw [mem_ball_zero_iff] at ha ⊢
    rw [mem_closedBall, dist_eq_norm] at hb
    have h2 : ‖b‖ ≤ ‖b - a‖ + ‖a‖ := by
      have := norm_sub_le (b - a) (-a)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
      linarith
    linarith
  have hsub6 : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), ∀ b ∈ closedBall a (1 / 100), ‖b‖ < 6 := by
    intro a ha b hb
    rw [mem_ball_zero_iff] at ha
    rw [mem_closedBall, dist_eq_norm] at hb
    have h2 : ‖b‖ ≤ ‖b - a‖ + ‖a‖ := by
      have := norm_sub_le (b - a) (-a)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
      linarith
    linarith
  cases hO : C.slot 0 with
  | inactive h =>
    exfalso
    have h' : P.circle.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  | active O =>
  have hpatch : C.circlePatch_BAS j = markedPatch_BPRE O.Z (gafCircleVector P.toLocalChartPackets j)
      (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 := by
    unfold circlePatch_BAS
    rw [hO]
    rfl
  -- block formula on the section
  have hblock : ∀ b ∈ ball (0 : ℝ²) (23 / 4),
      gafCircleVector P.toLocalChartPackets j (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) =
        ρ j.1 • b ∧
      gafCircleMarker P.toLocalChartPackets j (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) =
        ρ j.1 := by
    intro b hb
    obtain ⟨hη, -, hcut, -⟩ := hsec b hb
    have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inl j) (secE b) = 1 := hcut
    have hbl := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inl j) (secE b)
    rw [hcut', mul_one] at hbl
    refine ⟨?_, ?_⟩
    · change blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j))
          (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) = _
      rw [hbl.1]
      change ρ j.1 • cgpCoord P.toLocalChartFamily P.zero (.inl j) (secE b) = _
      rw [hη]
    · change blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j))
          (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) = _
      rw [hbl.2]
      rfl
  -- the section points are cloud points
  have hcloud : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1),
      cgpGlobalMap P.toLocalChartFamily P.zero (secE a) ∈ gafCloud P.toLocalChartFamily P.zero 0 := by
    intro a ha
    have ha' : a ∈ ball (0 : ℝ²) (23 / 4) := hsub a ha (mem_closedBall_self (by norm_num))
    obtain ⟨hη, hball, -⟩ := hsec a ha'
    rw [gafCloud_zero_GAF4]
    refine ⟨secE a, ⟨j, hball, ?_⟩, rfl⟩
    rw [hη]
    rw [mem_ball_zero_iff] at ha
    linarith
  have hxC : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), a ∈ (univ : Set ℝ²) ∧
      ‖(ρ j.1)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero (secE a) - Φ a‖ ≤ eg 0 ∧
      9 / 20 * S 0 * ρ j.1 ≤ S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a))) ∧
      S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a))) / 4 ≤
        3 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a)))) := by
    intro a ha
    have ha' : a ∈ ball (0 : ℝ²) (23 / 4) := hsub a ha (mem_closedBall_self (by norm_num))
    obtain ⟨hη, hball, -, hsc1, -⟩ := hsec a ha'
    have hη' : cgpCircleCoord P.toLocalChartFamily j.1 hj (secE a) = a := hη
    have hval := (hΦcl (secE a) hball (by
      rw [hη']
      rw [mem_ball_zero_iff] at ha
      linarith)).1
    rw [hη'] at hval
    have hxe : cgpGlobalMap P.toLocalChartFamily P.zero (secE a) ∈
        gafCloudEnlarged P.toLocalChartFamily P.zero 0 :=
      gafCloud_subset_enlarged P.toLocalChartFamily P.zero (by linarith) 0 (hcloud a ha)
    have hrat := gafCloudEnlarged_preimage_ratio_BAS P.toLocalChartFamily P.zero hΔ hΛ C.small_BAS 0
      (C.sel 0) (C.hsel 0) _ hxe (secE a) (gafStageQ_zero_starProjection_BAS _ _)
    have hsel0 := hρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a)))
    have hΞle : Ξ 0 ≤ 1 / 10 := O.eps_le
    have hinv : 10 ≤ (Ξ 0)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hΞ0]
      linarith
    refine ⟨mem_univ a, hval.le, ?_, ?_⟩
    · nlinarith [hrat.1]
    · have hr : 0 ≤ S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a))) := by
        positivity
      nlinarith
  -- the local graphs (CGP06 + the output's graph)
  have hm : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1),
      ∀ v ∈ C.plane 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a)),
        1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤ ‖gafCircleVector P.toLocalChartPackets j v‖ := by
    intro a ha v hv
    have ha' : a ∈ ball (0 : ℝ²) (23 / 4) := hsub a ha (mem_closedBall_self (by norm_num))
    have hη := (hsec a ha').1
    have hball := (hsec a ha').2.1
    have h06 := C.cgp06_circle_BAS R j (hcloud a ha) rfl hball (by
      rw [hη]
      rw [mem_ball_zero_iff] at ha
      linarith) v hv
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hdim : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1),
      Module.finrank ℝ (C.plane 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a))) =
        Module.finrank ℝ ℝ² := by
    intro a ha
    rw [(C.test0.1 _ (hcloud a ha)).1, finrank_euclideanSpace_fin]
    rfl
  have hgraph := fun a (ha : a ∈ ball (0 : ℝ²) (11 / 2 * 1)) =>
    cfs15_hgraph_BAS O (gafCircleVector P.toLocalChartPackets j) ⟨_, hcloud a ha⟩ (hm a ha)
      (R.eps_lt_margin_BAS 0).2 (hdim a ha)
  -- (MW) on the patch, with TCP05's value error at the witness
  have hMW : ∀ w ∈ markedPatch_BPRE O.Z (gafCircleVector P.toLocalChartPackets j)
      (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1, ∃ (y : BlockSpace (fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²)) (sw : ℝ²), sw ∈ (univ : Set ℝ²) ∧
      ‖(ρ j.1)⁻¹ • y - Φ sw‖ ≤ eg 0 ∧ gafCircleVector P.toLocalChartPackets j y = ρ j.1 • sw ∧
      ‖w - y‖ ≤ 25 / 12 * Ξ 0 * S 0 * ρ j.1 := by
    intro w hw
    rw [← hpatch] at hw
    obtain ⟨q, -, hqb, -, hηq, -, -, hu, -, hmw⟩ := C.circlePatch_witness_BAS j w hw
    have hηq' : ‖cgpCircleCoord P.toLocalChartFamily j.1 hj q‖ ≤ 8 := by
      have h : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ < 31 / 5 := hηq
      exact (le_of_lt h).trans (by norm_num)
    exact ⟨cgpGlobalMap P.toLocalChartFamily P.zero q, cgpCoord P.toLocalChartFamily P.zero (.inl j) q,
      mem_univ _, (hΦcl q hqb hηq').1.le, hu, hmw.le⟩
  -- the inner-section data on the closed balls `B̄(a, 1/100)`
  have hcont : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1),
      ContinuousOn (fun b => C.stageMap_BAS 0 (secE b)) (closedBall a (1 / 100)) := fun a ha =>
    (C.stageMap_contMDiff_BAS 0).continuous.comp_continuousOn (hsecC.mono (hsub a ha))
  have hsecv : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), ∀ b ∈ closedBall a (1 / 100),
      gafCircleVector P.toLocalChartPackets j (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) =
        ρ j.1 • b ∧
      gafCircleMarker P.toLocalChartPackets j (cgpGlobalMap P.toLocalChartFamily P.zero (secE b)) =
        ρ j.1 := fun a ha b hb => hblock b (hsub a ha hb)
  have herr : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), ∀ b ∈ closedBall a (1 / 100),
      ‖C.stageMap_BAS 0 (secE b) - cgpGlobalMap P.toLocalChartFamily P.zero (secE b)‖ ≤
        c 0 * ρ (secE b) := by
    intro a ha b hb
    have h := C.stageMap_error_BAS 0 (secE b)
    rw [gafStageQ_zero_starProjection_BAS] at h
    exact h.le
  have hρs : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), ∀ b ∈ closedBall a (1 / 100),
      ρ (secE b) ≤ 5 / 4 * ρ j.1 := fun a ha b hb => (hsec b (hsub a ha hb)).2.2.2.2
  have hplat : ∀ a ∈ ball (0 : ℝ²) (11 / 2 * 1), ∀ b ∈ closedBall a (1 / 100),
      secE b ∈ {p | p ∈ ball j.1 (200 * ρ j.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6} ∧ C.stageMap_BAS 0 (secE b) ∈ O.Z := by
    intro a ha b hb
    obtain ⟨hη, hball, -⟩ := hsec b (hsub a ha hb)
    have h6 : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) (secE b)‖ < 6 := by
      rw [hη]
      exact hsub6 a ha b hb
    exact ⟨⟨hball, h6⟩, (C.plat_BAS hO (p := secE b) ⟨j, hball, h6⟩).2.2⟩
  rw [hpatch]
  exact cgp07_one_sheet_BPRE O.Z (gafCircleVector P.toLocalChartPackets j)
    (norm_blockVectorCLM_le _) (gafCircleMarker P.toLocalChartPackets j) (norm_blockMarkerCLM_le _)
    hρj hΩ hS0 heos.le hΞ0.le hεos.le Φ convex_univ
    (fun b _ => (hΦs.differentiable (by simp)) b)
    (fun b _ => (hΦbd b).1.trans tcpGraphConst_le_gafGraphOmega_BAS)
    (fun a => cgpGlobalMap P.toLocalChartFamily P.zero (secE a))
    (fun a => S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a))))
    (fun a => 3 * (Ξ 0)⁻¹ * (S 0 * ρ (C.sel 0 (cgpGlobalMap P.toLocalChartFamily P.zero (secE a)))))
    hxC hgraph hMW (C.stageMap_BAS 0) (cgpGlobalMap P.toLocalChartFamily P.zero) secE ρ _ hc0.le
    (by linarith) (by linarith) hcont hsecv herr hρs hplat

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
