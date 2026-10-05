import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartTools
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches
import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# GAF02 BASES on the chain: CGP06 and CGP07 for the slim charts (stage three)

Blueprint `master207B.tex`, CGP06 (B:4130–4174), CGP07 (B:4176–4247); external draft 59 §4, third
to fifth steps (D59-5); review 66 §5.4 steps 3–5 (D66-7). Indexed by ONE chain
`C : Gaf02Chain P.toLocalChartPackets …` and its rough data `R : Gaf02RoughData C`; no further
hypothesis. Mirror of the circle charts (`ActualStageChainChartCircle`), with the ONE-dimensional
retained coordinate `u_j = axisCoord ∘ (slim block vector)`, `ℓ = 10⁵Δ`, the projected original map
`π₃𝓔⁰` and SGP04's full slim graph `Φ_j = sgpFullGraph` (`R.slim`).

* `sgpFullGraph_slope_le_BASP`: SGP04's slope `‖DΦ_j‖ ≤ C_* ≤ Ω` on the chain's family (SGP01's
  zero clauses from the chain's standing hypotheses).
* `Gaf02Chain.cgp06_slim_BAS`: at a slim-cloud point `x` and a preimage `q` in chart `j`
  (`|η_j(q)| ≤ 8·10⁵Δ`), `‖v‖ ≤ 2Ω|u_j v|` on the chain's plane `L_x` (the plane's (PP) at `q` from
  `C.test2`, SGP04's graph from `R.slim`, (OS) from `R.os`).
* `Gaf02Chain.cgp07_slim_BAS`: `R_j⁻¹u_j : V_j⁰ → B(0, 5.5·10⁵Δ)` bijective, `V_j⁰ ⊆ f₃(B⁶_j)`
  (ORIGINAL threshold-6 plateau of the chart), smooth inverse chart landing in `V_j⁰`, compact
  preimages — on the native zero set of the chain's own stage output, with (MW) from CGP05, (SN)
  from (OS), CGP03's slim section and (PLAT).
* Helpers (`_BASP`): the slim block of `π₃𝓔⁰` at a full marker, slim-cloud membership, the scale
  ratio, the local graph in CGP07's form, (MW) with SGP04's value error, the section's balls.
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

/-- The numerics of the slim inner section: for `a ∈ B(0, 5.5ℓ)` (`ℓ = 10⁵Δ`, `Δ ≥ 1`) and
`b ∈ B̄(a, 1/100)`, `b ∈ B(0, 23ℓ/4)` and `|b| < 6ℓ`; and `|a| ≤ 7·10⁵Δ`. -/
theorem slim_section_balls_BASP {Δ : ℝ} (hΔ : 1 ≤ Δ) {a : ℝ}
    (ha : a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ))) :
    |a| ≤ 7 * 10 ^ 5 * Δ ∧ ∀ b ∈ closedBall a (1 / 100),
      b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)) ∧ |b| < 6 * (10 ^ 5 * Δ) := by
  rw [mem_ball_zero_iff, Real.norm_eq_abs] at ha
  refine ⟨by linarith, fun b hb => ?_⟩
  rw [mem_closedBall, Real.dist_eq] at hb
  have h := abs_sub_abs_le_abs_sub b a
  rw [mem_ball_zero_iff, Real.norm_eq_abs]
  constructor <;> linarith

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

section Slim

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The retained slim coordinate `axisCoord ∘ u_j` has norm at most one. -/
theorem norm_slimCoord_le_BASP (j : P.slim.finite_centres.toFinset) :
    ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)‖ ≤ 1 := by
  have h1 := norm_axisCoordCLM_le_BAS
  have h2 := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    change ‖axisCoordCLM_BAS‖ * ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²) (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero)‖ ≤ 1
    nlinarith [norm_nonneg axisCoordCLM_BAS, norm_nonneg (blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero))])

/-- The own block of SGP04's graph: `axisCoord (u_j (Φ_j a)) = a`. -/
theorem slimCoord_sgpFullGraph_BASP (j : P.slim.finite_centres.toFinset)
    (sgn cc zsgn zc : X → ℝ) (a : ℝ) :
    axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)
      (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc a) = a := by
  rw [ContinuousLinearMap.comp_apply, gafSlimVector, blockVectorCLM_apply, sgpFullGraph_own]
  exact axisCoordCLM_planeAxis_BAS a

/-- The slim block of `π₃𝓔⁰` at a point with a full `j` marker: `u_j = R_jη_j`, `v_j = R_j`. -/
theorem slimBlock_of_cutoff_BASP (j : P.slim.finite_centres.toFinset) {p : X}
    (hcut : P.slim.cutoff j.1 p = 1) :
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p)) =
      ρ j.1 • (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p ∧
    gafSlimMarker P.toLocalChartFamily P.zero j
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p)) = ρ j.1 := by
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 2 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈
      cgpQ3Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inl j)) p = 1 := hcut
  have hbl := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS p
  rw [hcut', mul_one] at hbl
  refine ⟨?_, hbl.2⟩
  calc _ = ρ j.1 • axisCoordCLM_BAS (cgpCoord P.toLocalChartFamily P.zero
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j))) p) := hbl.1
    _ = _ := by
      change ρ j.1 • axisCoordCLM_BAS (planeAxis ((P.slim.centre j.1
        ((Set.Finite.mem_toFinset _).mp j.2)).coord p)) = _
      rw [axisCoordCLM_planeAxis_BAS]

/-- A point of the slim chart `j` with `|η_j| ≤ 7·10⁵Δ` projects into the slim cloud `S₃`. -/
theorem slimCloud_mem_BASP (j : P.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 7 * 10 ^ 5 * Δ) :
    cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p ∈
      gafCloud P.toLocalChartFamily P.zero 2 := by
  have hmem : p ∈ fc27SlimSet P.toLocalChartFamily 7 := ⟨j, hp, hη⟩
  exact ⟨p, hmem, rfl⟩

end Slim

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- SGP04's slim graph slope on the chain's family: `‖DΦ_i‖ ≤ C_* ≤ Ω` for signs of size at most
one (SGP01's zero clauses from the chain's standing hypotheses). -/
theorem sgpFullGraph_slope_le_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (i : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1)
    (hzsgn : ∀ k, |zsgn k| ≤ 1) (a : ℝ) :
    ‖fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn cc zsgn zc) a‖ ≤
      gafGraphOmega_BAS := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, he, hT, hσs, hσs1, -⟩ := C.std
  have hi : i.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp i.2
  have hs01 := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs hσs1 hi
  have hs0 : ∀ k (hk : k ∈ P.zero.centres), sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (P.zero.zero k hk).radius / ρ i.1 :=
    fun k hk hmt => (one_le_div_twenty_SGP4 hΔ hT).trans ((hs01.2.2.2.2.1 k hk hmt).1)
  exact ((sgp04_full_model_bounds P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn cc zsgn zc hsgn
    hzsgn hs0 hs01.2.2.2.1 a).1).trans sgpGraphBound_le_gafGraphOmega_BAS

/-- **CGP06 on the chain, slim stage, for a GIVEN rough graph** (review 71, D71-2: the BASES
assembly chooses SGP04's graph `Φ_j = sgpFullGraph … sgn cc zsgn zc` ONCE and passes it here; the
clause `hcl` is SGP04's conclusion at `j` for that graph). At a slim-cloud point `x` and a preimage
`q` (`π₃𝓔⁰ q = x`) in chart `j` with `|η_j(q)| ≤ 8·10⁵Δ`, every `v ∈ L_x` has `‖v‖ ≤ 2Ω|u_j v|`.
D71-4: the plane's (PP) is used at the SAME preimage `q` as the graph's derivative error; the two
reference scales `ρ_i`, `ρ_j` are unified by `retained_coordinate_of_pp_rescaled_BAS`; `π DΦ = id`
by the chain rule (`clm_fderiv_of_left_inverse_BAS`); `‖DΦ_j‖ ≤ Ω` everywhere
(`sgpFullGraph_slope_le_BASP`) and the error on the whole chart domain (`hcl`). -/
theorem cgp06_slim_of_graph_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x)
    (hqj : q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| ≤ 8 * 10 ^ 5 * Δ) :
    ∀ v ∈ C.plane 2 x, ‖v‖ ≤ 2 * gafGraphOmega_BAS *
      ‖axisCoordCLM_BAS (gafSlimVector P.toLocalChartFamily P.zero j v)‖ := by
  have hrough := (hcl q hqj hη).2
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) q) := inferInstanceAs (FiniteDimensional ℝ E3)
  have hπT : ∀ y, axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)
      (fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
        ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q) y) = y :=
    clm_fderiv_of_left_inverse_BAS _ ((contDiff_sgpFullGraph P.toLocalChartFamily P.zero j sgn cc
      zsgn zc).differentiable (by simp) _) (slimCoord_sgpFullGraph_BASP j sgn cc zsgn zc)
  have hT : ∀ y, ‖fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
      ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q) y‖ ≤
      gafGraphOmega_BAS * ‖y‖ := fun y =>
    ((fderiv ℝ _ _).le_opNorm y).trans (mul_le_mul_of_nonneg_right
      (C.sgpFullGraph_slope_le_BASP j sgn cc zsgn zc hsgn hzsgn _) (norm_nonneg y))
  obtain ⟨i, hPP⟩ := C.test2.2.2.1 x hx
  have hPPq := hPP q hq
  intro v hv
  exact retained_coordinate_of_pp_rescaled_BAS (V := TangentSpace 𝓘(ℝ, E3) q)
    (H := BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (E := ℝ)
    (mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
    (ContinuousLinearMap.toLinearMap₁₂ (g.inner q)) (fun w hw => by simpa using g.pos q w hw)
    (C.plane 2 x) (hρ i.1) (hρ j.1) (C.numbers.1 2).2.2.2 hPPq.1 hPPq.2.1
    (fun w hw => hPPq.2.2.1 w (fun k hk => by simpa using hw k hk))
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (norm_slimCoord_le_BASP j) _ hπT hT _ hrough one_le_gafGraphOmega_BAS (C.os_small_BAS R 2) v hv

/-- **CGP06 on the chain, slim stage** (frozen statement): at a point `x` of the slim cloud and a
preimage `q` (`π₃𝓔⁰ q = x`) in the slim chart `j` with `|η_j(q)| ≤ 8·10⁵Δ`, every vector of the
chain's plane `L_x` has `‖v‖ ≤ 2Ω|u_j v|` (`u_j` = the ACTUAL one-dimensional axis coordinate of the
slim block). Corollary of `cgp06_slim_of_graph_BASP` at a graph of `R.slim`. -/
theorem cgp06_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x)
    (hqj : q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| ≤ 8 * 10 ^ 5 * Δ) :
    ∀ v ∈ C.plane 2 x, ‖v‖ ≤ 2 * gafGraphOmega_BAS *
      ‖axisCoordCLM_BAS (gafSlimVector P.toLocalChartFamily P.zero j v)‖ :=
  Exists.elim (R.slim j) fun sgn h1 => Exists.elim h1 fun cc h2 => Exists.elim h2 fun zsgn h3 =>
    Exists.elim h3 fun zc h4 =>
      C.cgp06_slim_of_graph_BASP R j sgn cc zsgn zc h4.1 h4.2.1 h4.2.2 hx hq hqj hη

/-- **CGP03's slim section, extended to `ℝ`** (`exists_ball_extension_BAS`): continuous on
`B(0, 23·10⁵Δ/4)`, there `η_j(s b) = b`, `s b ∈ B(c_j, 10⁶Δρ_j)`, `ζ_j(s b) = 1`,
`ρ(s b) ∈ [3ρ_j/4, 5ρ_j/4]`. -/
theorem slim_section_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    ∃ secE : ℝ → X, ContinuousOn secE (ball 0 (23 / 4 * (10 ^ 5 * Δ))) ∧
      ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
        (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
        secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
        3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hj : j.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hbud : Λ * (10 ^ 6 * Δ) ≤ 1 / 4 := by
    have h := C.small_BAS
    norm_num at h ⊢
    linarith
  obtain ⟨sec, hsc, hs⟩ := cgp03_slim_section P.toLocalChartFamily (by linarith) hΛ hbud hj
  obtain ⟨secE, hcont, heq⟩ := exists_ball_extension_BAS j.1 sec hsc
  refine ⟨secE, hcont, fun b hb => ?_⟩
  rw [heq b hb]
  exact hs ⟨b, hb⟩

/-- The scale clauses of CGP07's `hxC` at a slim-cloud point `π₃𝓔⁰ p`: with `ρ(p) ≥ 3r/4`,
`r_x = Σ₃ρ(sel₃ x) ≥ (9/20)Σ₃r`, and `r_x/4 ≤ 3Ξ₃⁻¹r_x` for `Ξ₃ ≤ 1/10`. -/
theorem slim_scale_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) {p : X} {r : ℝ}
    (hx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p ∈
      gafCloud P.toLocalChartFamily P.zero 2) (hr : 3 / 4 * r ≤ ρ p) (hΞ : Ξ 2 ≤ 1 / 10) :
    9 / 20 * S 2 * r ≤ S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) p)) ∧
      S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) p)) / 4 ≤
        3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) p))) := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  obtain ⟨hΞ2, hS2, -, -⟩ := C.numbers.1 2
  have hxe := gafCloud_subset_enlarged P.toLocalChartFamily P.zero (by linarith) 2 hx
  have hQ3 : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero p) =
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p :=
    gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 2 p
  have hrat := gafCloudEnlarged_preimage_ratio_BAS P.toLocalChartFamily P.zero hΔ hΛ C.small_BAS 2
    (C.sel 2) (C.hsel 2) _ hxe p hQ3
  have hsel0 := hρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
    (cgpQ3Tags P.toLocalChartFamily P.zero) p))
  have hinv : 10 ≤ (Ξ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hΞ2]
    linarith
  refine ⟨?_, ?_⟩
  · nlinarith [hrat.1]
  · have hr0 : 0 ≤ S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) p)) := by
      positivity
    nlinarith

/-- **The local graph of the slim stage output in CGP07's `hgraph` form** at `x = π₃𝓔⁰ p` for a
point `p` of chart `j` with `|η_j(p)| ≤ 7·10⁵Δ` (CGP06 at `p` for the given graph + the output's
graph). -/
theorem slim_hgraph_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2))
    {p : X} (hp : p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 7 * 10 ^ 5 * Δ) :
    ∃ (R₀ m sl : ℝ) (L : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
      (gr : L → Lᗮ), (∀ v' ∈ L, m * ‖v'‖ ≤
          ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j) v'‖) ∧
      sl < m ∧ Module.finrank ℝ L = Module.finrank ℝ ℝ ∧ ContDiffOn ℝ ∞ gr (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ gr t‖ ≤ sl) ∧
      O.Z ∩ ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p)
          (3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) p)))) =
        {z | ∃ t ∈ ball (0 : L) R₀, z = cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) p + orthogonalCoordinateSum L (t, gr t)} ∩
          ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p)
            (3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ3Tags P.toLocalChartFamily P.zero) p)))) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hcl7 := slimCloud_mem_BASP j hp hη
  have hΩ := one_le_gafGraphOmega_BAS
  have hm : ∀ v ∈ C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) p),
      1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
        ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j) v‖ := by
    intro v hv
    have h06 := C.cgp06_slim_of_graph_BASP R j sgn cc zsgn zc hsgn hzsgn hcl hcl7 rfl hp
      (by linarith) v hv
    rw [ContinuousLinearMap.comp_apply, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hdim : Module.finrank ℝ (C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) p)) = Module.finrank ℝ ℝ := by
    rw [(C.test2.1 _ hcl7).1, Module.finrank_self]
    rfl
  exact cfs15_hgraph_BAS O (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    ⟨_, hcl7⟩ hm (R.eps_lt_margin_BAS 2).2 hdim

/-- **(MW) on the slim patch with SGP04's value error** at the witness: every `w ∈ V_j⁰` has a
`y = π₃𝓔⁰ q` with `‖R_j⁻¹y − Φ(η_j q)‖ ≤ e₃`, `u_j y = R_jη_j(q)`, `‖w − y‖ ≤ (25/12)Ξ₃Σ₃R_j`, for any
`Φ` with SGP04's value clause. -/
theorem slim_hMW_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hval : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        Φ ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2) :
    ∀ w ∈ C.slimPatch_BAS j,
      ∃ (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (sw : ℝ),
        sw ∈ (univ : Set ℝ) ∧ ‖(ρ j.1)⁻¹ • y - Φ sw‖ ≤ eg 2 ∧
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y = ρ j.1 • sw ∧
        ‖w - y‖ ≤ 25 / 12 * Ξ 2 * S 2 * ρ j.1 := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  intro w hw
  obtain ⟨q, -, hqb, -, hηq, -, -, hu, -, hmw⟩ := C.slimPatch_witness_BAS j w hw
  have hqb' : q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) := by
    norm_num
    exact hqb
  have hηq' : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| ≤
      8 * 10 ^ 5 * Δ := by linarith
  have hv := hval q hqb' hηq'
  have hQ3 : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q) =
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q :=
    gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 2 q
  refine ⟨cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q,
    (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q, mem_univ _, hv.le, ?_, ?_⟩
  · rw [← hQ3, smul_eq_mul]
    exact hu
  · rw [← hQ3]
    exact hmw.le

/-- A point of the slim section over `B(0, 5.5ℓ)` lies in the chart ball with `|η_j| ≤ 7·10⁵Δ`. -/
theorem slim_section_point_BASP (j : P.slim.finite_centres.toFinset) (hΔ : 1 ≤ Δ) (secE : ℝ → X)
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1)
    {a : ℝ} (ha : a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ))) :
    secE a ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE a)| ≤
        7 * 10 ^ 5 * Δ ∧ 3 / 4 * ρ j.1 ≤ ρ (secE a) := by
  have ha' := ((slim_section_balls_BASP hΔ ha).2 a (mem_closedBall_self (by norm_num))).1
  have hs := hsec a ha'
  refine ⟨hs.2.1, ?_, hs.2.2.2.1⟩
  rw [hs.1]
  exact (slim_section_balls_BASP hΔ ha).1

/-- CGP07's `hxC` on the slim section `s_j`: the target lies in `C = ℝ`, SGP04's value error at
`s_j a` (`η_j(s_j a) = a`), and the scale clauses (`slim_scale_BASP`). -/
theorem slim_hxC_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hval : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        Φ ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2)
    (hΞ : Ξ 2 ≤ 1 / 10) (secE : ℝ → X)
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1) :
    ∀ a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), a ∈ (univ : Set ℝ) ∧
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
          (secE a) - Φ a‖ ≤ eg 2 ∧
      9 / 20 * S 2 * ρ j.1 ≤ S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a))) ∧
      S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a))) / 4 ≤
        3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a)))) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  intro a ha
  have hpt := slim_section_point_BASP j hΔ secE hsec ha
  have hη : (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE a) = a :=
    (hsec a ((slim_section_balls_BASP hΔ ha).2 a (mem_closedBall_self (by norm_num))).1).1
  have hv := hval (secE a) hpt.1 (by linarith [hpt.2.1])
  rw [hη] at hv
  exact ⟨mem_univ a, hv.le, C.slim_scale_BASP (slimCloud_mem_BASP j hpt.1 hpt.2.1) hpt.2.2 hΞ⟩

/-- CGP07's `hplat` on the slim section: `s_j b` lies in the chart's ORIGINAL threshold-6 plateau
and `f₃(s_j b) ∈ Z₃` (PLAT). -/
theorem slim_hplat_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O) (secE : ℝ → X)
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1) :
    ∀ a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), ∀ b ∈ closedBall a (1 / 100),
      secE b ∈ {p | p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)} ∧
      C.stageMap_BAS 2 (secE b) ∈ O.Z := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  intro a ha b hb
  have hb' := (slim_section_balls_BASP hΔ ha).2 b hb
  have hs := hsec b hb'.1
  have hball' : secE b ∈ ball j.1 (1000000 * Δ * ρ j.1) := by
    have h := hs.2.1
    norm_num at h ⊢
    exact h
  have h6 : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b)| <
      6 * (10 ^ 5 * Δ) := by
    rw [hs.1]
    exact hb'.2
  exact ⟨⟨hball', h6⟩, (C.plat_BAS hO (p := secE b) ⟨j, hball', h6⟩).2.2⟩

/-- CGP07's `hsec` on the slim section: `u_j(π₃𝓔⁰(s_j b)) = R_j b`, `v_j(π₃𝓔⁰(s_j b)) = R_j`. -/
theorem slim_hsecv_BASP (j : P.slim.finite_centres.toFinset) (hΔ : 1 ≤ Δ) (secE : ℝ → X)
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1) :
    ∀ a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), ∀ b ∈ closedBall a (1 / 100),
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero (secE b))) = ρ j.1 • b ∧
      gafSlimMarker P.toLocalChartFamily P.zero j
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero (secE b))) = ρ j.1 := by
  intro a ha b hb
  have hs := hsec b ((slim_section_balls_BASP hΔ ha).2 b hb).1
  have h := slimBlock_of_cutoff_BASP j hs.2.2.1
  rw [hs.1] at h
  exact h

/-- CGP07's `hgraph` on the slim section (`slim_hgraph_BASP` at `s_j a`). -/
theorem slim_hgraph_section_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)) (secE : ℝ → X)
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1) :
    ∀ a ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
    ∃ (R₀ m sl : ℝ) (L : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
      (gr : L → Lᗮ), (∀ v' ∈ L, m * ‖v'‖ ≤
          ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j) v'‖) ∧
      sl < m ∧ Module.finrank ℝ L = Module.finrank ℝ ℝ ∧ ContDiffOn ℝ ∞ gr (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ gr t‖ ≤ sl) ∧
      O.Z ∩ ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
          (secE a)) (3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a))))) =
        {z | ∃ t ∈ ball (0 : L) R₀, z = cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a) + orthogonalCoordinateSum L (t, gr t)} ∩
          ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
            (secE a)) (3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a))))) := fun _ ha =>
  C.slim_hgraph_BASP R j sgn cc zsgn zc hsgn hzsgn hcl O
    (slim_section_point_BASP j C.std.2.1 secE hsec ha).1
    (slim_section_point_BASP j C.std.2.1 secE hsec ha).2.1

/-- The slim patch of the chain is the marked patch of the slot's output `O` (slot `= .active O`). -/
theorem slimPatch_eq_of_active_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O) :
    C.slimPatch_BAS j = markedPatch_BPRE O.Z
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) := by
  unfold slimPatch_BAS
  rw [hO]
  rfl

/-- (MW) of `slim_hMW_BASP` on the marked patch of the slot's output. -/
theorem slim_hMW_active_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O)
    (Φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hval : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        Φ ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2) :
    ∀ w ∈ markedPatch_BPRE O.Z
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
      ∃ (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (sw : ℝ),
        sw ∈ (univ : Set ℝ) ∧ ‖(ρ j.1)⁻¹ • y - Φ sw‖ ≤ eg 2 ∧
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y = ρ j.1 • sw ∧
        ‖w - y‖ ≤ 25 / 12 * Ξ 2 * S 2 * ρ j.1 := fun w hw =>
  C.slim_hMW_BASP j Φ hval w ((Set.ext_iff.mp (C.slimPatch_eq_of_active_BASP j hO) w).mpr hw)

/-- **The stage-three slot is active as soon as a slim centre exists** (indexing by the ACTUAL
centre `j`, review 71 D71-11: no consumer branches on the slot's constructor). -/
theorem slot_two_active_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    ∃ O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2),
      C.slot 2 = .active O := by
  have hj : j.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  cases hO : C.slot 2 with
  | active O => exact ⟨O, rfl⟩
  | inactive h =>
    exfalso
    have h' : P.slim.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj

/-- **CGP07 on the chain, slim stage, for a given output, section and rough graph** (the assembly
of `cgp07_one_sheet_BPRE`): `O` the stage output in the slot, `secE` CGP03's slim section, SGP04's
graph `Φ_j` with its clauses. -/
theorem cgp07_slim_core_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O) (secE : ℝ → X)
    (hsecC : ContinuousOn secE (ball 0 (23 / 4 * (10 ^ 5 * Δ))))
    (hsec : ∀ b ∈ ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)),
      (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord (secE b) = b ∧
      secE b ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 (secE b) = 1 ∧
      3 / 4 * ρ j.1 ≤ ρ (secE b) ∧ ρ (secE b) ≤ 5 / 4 * ρ j.1) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ))
        (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ w ∈ markedPatch_BPRE O.Z
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
        ∃ p ∈ {p | p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)},
          C.stageMap_BAS 2 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily
            P.zero j)) (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ))
          (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        MapsTo φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (markedPatch_BPRE O.Z
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ)) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), IsCompact K →
          IsCompact (markedPatch_BPRE O.Z
            (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
            (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hc0 := C.c_pos_BAS 2
  have hc1 := C.c_le_BAS 2
  have hxC := C.slim_hxC_BASP j (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
    (fun x hx hη => (hcl x hx hη).1) O.eps_le secE hsec
  refine cgp07_one_sheet_BPRE O.Z (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily
      P.zero j)) (norm_slimCoord_le_BASP j) (gafSlimMarker P.toLocalChartFamily P.zero j)
    (norm_blockMarkerCLM_le _) (hρ j.1) one_le_gafGraphOmega_BAS (C.numbers.1 2).2.1
    (R.os 2).2.1.le (C.numbers.1 2).1.le (R.os 2).1.le
    (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc) convex_univ
    (fun b _ => (contDiff_sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc).differentiable
      (by simp) b)
    (fun b _ => C.sgpFullGraph_slope_le_BASP j sgn cc zsgn zc hsgn hzsgn b)
    (fun a => cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
      (secE a))
    (fun a => S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a))))
    (fun a => 3 * (Ξ 2)⁻¹ * (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) (secE a)))))
    ?_
    (C.slim_hgraph_section_BASP R j sgn cc zsgn zc hsgn hzsgn hcl O secE hsec)
    (C.slim_hMW_active_BASP j hO (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
      (fun x hx hη => (hcl x hx hη).1)) (C.stageMap_BAS 2)
    (fun q => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q)) secE ρ
    {p | p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)}
    (r₀ := 1 / 100) hc0.le (by linarith) (by linarith)
    (fun a ha => (C.stageMap_contMDiff_BAS 2).continuous.comp_continuousOn
      (hsecC.mono fun b hb => ((slim_section_balls_BASP hΔ ha).2 b hb).1))
    (slim_hsecv_BASP j hΔ secE hsec)
    (fun _ _ b _ => (C.stageMap_error_BAS 2 (secE b)).le)
    (fun a ha b hb => (hsec b ((slim_section_balls_BASP hΔ ha).2 b hb).1).2.2.2.2)
    (C.slim_hplat_BASP j hO secE hsec)
  -- `hxC` (the norm clause by `convert`: the instance paths of `•` differ only up to unfolding)
  intro a ha
  refine ⟨(hxC a ha).1, ?_, (hxC a ha).2.2.1, (hxC a ha).2.2.2⟩
  convert (hxC a ha).2.1 using 3

/-- **CGP07 on the chain, slim stage, for a GIVEN rough graph** (review 71, D71-2: the BASES
assembly chooses SGP04's graph ONCE and passes it here). Conclusion = the frozen `cgp07_slim_BAS`. -/
theorem cgp07_slim_of_graph_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) (sgn cc zsgn zc : X → ℝ)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hcl : ∀ x ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1),
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ j.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc
          ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)‖ < eg 2 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero j sgn cc zsgn zc)
            ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j.1
              ((Set.Finite.mem_toFinset _).mp j.2)).coord x w)‖ ≤
          eg 2 * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w)) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.slimPatch_BAS j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ w ∈ C.slimPatch_BAS j, ∃ p, (p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) ∧
        C.stageMap_BAS 2 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (C.slimPatch_BAS j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        MapsTo φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.slimPatch_BAS j) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), IsCompact K →
          IsCompact (C.slimPatch_BAS j ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) :=
  Exists.elim (C.slot_two_active_BASP j) fun O hO =>
    Exists.elim (C.slim_section_BASP j) fun secE hs => by
      rw [C.slimPatch_eq_of_active_BASP j hO]
      exact C.cgp07_slim_core_BASP R j sgn cc zsgn zc hsgn hzsgn hcl hO secE hs.1 hs.2

/-- **CGP07 on the chain, slim stage** (frozen statement; `cgp07_one_sheet_BPRE` instantiated):
the retained coordinate `R_j⁻¹u_j` is a bijection of the slim patch `V_j⁰` onto `B(0, 5.5·10⁵Δ)`;
every point of `V_j⁰` is `f₃(p)` for some `p` of the chart's ORIGINAL threshold-6 plateau; the
inverse chart is smooth on the ball, inverts the coordinate, lands in `V_j⁰`; compact sets of the
ball have compact preimages in `V_j⁰`. Corollary of `cgp07_slim_of_graph_BASP` at a graph of
`R.slim`. -/
theorem cgp07_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) :
    BijOn ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.slimPatch_BAS j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ w ∈ C.slimPatch_BAS j, ∃ p, (p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) ∧
        C.stageMap_BAS 2 p = w) ∧
      ∃ φ : ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        InvOn φ ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (C.slimPatch_BAS j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
        MapsTo φ (ball 0 (11 / 2 * (10 ^ 5 * Δ))) (C.slimPatch_BAS j) ∧
        ∀ K ⊆ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), IsCompact K →
          IsCompact (C.slimPatch_BAS j ∩
            ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹'
              K) :=
  Exists.elim (R.slim j) fun sgn h1 => Exists.elim h1 fun cc h2 => Exists.elim h2 fun zsgn h3 =>
    Exists.elim h3 fun zc h4 =>
      C.cgp07_slim_of_graph_BASP R j sgn cc zsgn zc h4.1 h4.2.1 h4.2.2

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
