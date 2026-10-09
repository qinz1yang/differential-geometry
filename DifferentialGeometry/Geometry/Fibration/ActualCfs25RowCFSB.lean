import DifferentialGeometry.Geometry.Fibration.ActualCfs2223RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater

/-!
# CFS25 on the actual data: the uniform cutoff consumer at the chain's stages two and three

Blueprint `master207B.tex`, CFS25 (`cor:fibration-uniform-cutoff-consumer`, B:3522–3568). On the
chain `C : Gaf02Chain P …` (actual packets, actual clouds, CFS15 native outputs, the actual
cutoffs; `F = 𝓔⁰`), the row's premises are produced, not assumed:

* the actual PRECEDING adjustments supply (ZM) for the next edge / slim family and have cumulative
  value error at most `4κ/5` and at most `3Σ_j/10` (`Gaf02Chain.prior_contract_CFSB`, `C.numbers`);
* the auxiliary cutoffs are CFS23 (`ψ₂`, edge) and CFS22 (`ψ₃`, slim) — `cfs23_row_CFSB`,
  `cfs22_row_CFSB` give their support, exact plateau and derivative requirements with
  `C = 10⁴(N+1)²P⁴`, fixed before `Δ`;

and the row's conclusions: the closed support localizes the ORIGINAL point to the stage core and
CFS16 puts the perturbed projected input in the half-tube of the original centre
(`C.stage_input_mem_tube`); CFS18 gives a smooth open neighbourhood of each actual image on which
the stage map is smooth (`stage_neighborhood_CFSB`); the slim adjustment factors over `Q₂`; the
derivative budget of every stage uses `b_j = C` (`C.numbers`).

Main theorem: `Gaf02Chain.cfs25_row_CFSB`.
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

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **CFS18 at a stage of the chain**: if a preceding map `f` has its values in an open `O` on
which the cutoff `ψ` is smooth, and the closed support of `ψ` along `f` localizes to the native
tube of stage `st` (`π_st F p ∈ S_st`, `π_st f p ∈ B(π_st F p, Σ_st ρ(sel_st(π_st F p)))`), then
the stage adjustment `adjustmentMap Q_st (π_st ∘ a_st) ψ` is smooth on an open `V` with
`f(M) ⊆ V ⊆ O`. -/
theorem stage_neighborhood_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hO : IsOpen O)
    (hfO : ∀ p, f p ∈ O) (hψ : ContDiffOn ℝ ∞ ψ O)
    (hloc : ∀ p, f p ∈ tsupport ψ →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p) ∈
          ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))
            (S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero p))))) :
    ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range f ⊆ W ∧ W ⊆ O ∧
      ContDiffOn ℝ ∞ (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y))
        ψ) W := by
  classical
  have hh : ContDiffOn ℝ ∞ (fun z => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      ((C.slot st).map ((gafStageQ P.toLocalChartFamily P.zero st).starProjection z)) -
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection z)
      (O ∩ cfsProjectedTube (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero)
        {p | (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st}
        (fun p => S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p))))) := by
    intro z hz
    obtain ⟨p, hpA, hpz⟩ := hz.2
    have hmap : ContDiffAt ℝ ∞ (C.slot st).map
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection z) :=
      C.slot_contDiffAt_BAS st hpA hpz
    have hπ : ContDiffAt ℝ ∞
        (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection y) z :=
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection.contDiff.contDiffAt
    exact (((gafStageQ P.toLocalChartFamily P.zero st).starProjection.contDiff.contDiffAt.comp z
      (hmap.comp z hπ)).sub hπ).contDiffWithinAt
  obtain ⟨W, hW, hKW, hWO, -, hsmooth, hzero, -⟩ :=
    cfs25_closedSupport_neighborhood (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero) f _ _ hO hfO hψ (fun p hp => hloc p hp) hh
  refine ⟨W, hW, hKW, hWO, hsmooth.congr fun z hz => ?_⟩
  unfold Set.piecewise
  split_ifs with hzt
  · rfl
  · rw [adjustmentMap_apply, hzero z hz hzt, zero_smul, add_zero, id]

/-- CFS25, the preceding errors and (ZM) at the chain's preceding maps. -/
theorem cfs25_prior_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q ∧
      ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 3 * S 1 / 10 * ρ q) ∧
    (∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q ∧
      ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 3 * S 2 / 10 * ρ q) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (C.g₁ p)| ≤ ρ j.1 / 32) ∧
    ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (C.g₂ p)| ≤ ρ j.1 / 32 := by
  obtain ⟨-, -, -, -, hc₀κ, hc₀s, -, -, -, hc₁κ, hc₁s, -, -, -⟩ := C.numbers
  have k4 := C.stage_error_lt.1
  have k5 := C.stage_error_lt.2.1
  obtain ⟨-, -, hZM₁, hZM₂⟩ := C.prior_contract_CFSB
  exact ⟨fun q => ⟨(k4 q).le.trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le),
      (k4 q).le.trans (mul_le_mul_of_nonneg_right hc₀s (hρ q).le)⟩,
    fun q => ⟨(k5 q).le.trans (mul_le_mul_of_nonneg_right hc₁κ (hρ q).le),
      (k5 q).le.trans (mul_le_mul_of_nonneg_right hc₁s (hρ q).le)⟩, hZM₁, hZM₂⟩

/-- CFS25, CFS16 at the closed supports: the stage-two / stage-three closed supports localize the
original point and put the projected perturbed input in the half-tube of the original centre. -/
theorem cfs25_tube_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ p, C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
      (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
            p))
        (S 1 * ρ (C.sel 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) ∧
    ∀ p, C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
      (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          7 * (10 ^ 5 * Δ)) ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 2 ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
            p))
        (S 2 * ρ (C.sel 2 ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p)))) := by
  have e4 := C.cutoff_bindings.2.1.2.2.2.1
  have s4 := C.cutoff_bindings.2.2.2.2.2.1
  exact ⟨fun p hp => ⟨e4 p hp, (C.stage_input_mem_tube p).2.1 hp⟩,
    fun p hp => ⟨s4 p hp, (C.stage_input_mem_tube p).2.2 hp⟩⟩

/-- CFS25, CFS18 and FC32: the stage maps `Ψ₂`, `Ψ₃` are smooth on open neighbourhoods of the
actual preceding images, and `Ψ₃` commutes with `π_{Q₂}`. -/
theorem cfs25_smooth_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.g₁ ⊆ W ∧ W ⊆ {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      ContDiffOn ℝ ∞ C.Ψ₂ W) ∧
    (∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.g₂ ⊆ W ∧ ContDiffOn ℝ ∞ C.Ψ₃ W) ∧
    ∀ z, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.Ψ₃ z) =
      C.Ψ₃ ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) := by
  have e1 := C.cutoff_bindings.2.1.1
  have e5 := C.cutoff_bindings.2.1.2.2.2.2
  have s1 := C.cutoff_bindings.2.2.1
  have hopen : IsOpen {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
      0 < gafScaleMarker P.toLocalChartFamily P.zero z} :=
    isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous
  have hscale : ∀ p, C.g₁ p ∈ {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} := by
    intro p
    have h := (e5 p 1 (by norm_num)).1
    simpa using h
  obtain ⟨W₂, hW₂, hK₂, hWO₂, hs₂⟩ := C.stage_neighborhood_CFSB 1 _ C.g₁ hopen hscale e1
    fun p hp => (C.stage_input_mem_tube p).2.1 hp
  obtain ⟨W₃, hW₃, hK₃, -, hs₃⟩ := C.stage_neighborhood_CFSB 2 _ C.g₂ isOpen_univ
    (fun _ => mem_univ _) s1.contDiffOn fun p hp => (C.stage_input_mem_tube p).2.2 hp
  refine ⟨⟨W₂, hW₂, hK₂, hWO₂, hs₂⟩, ⟨W₃, hW₃, hK₃, hs₃⟩, fun z => ?_⟩
  exact starProjection_adjustmentMap_comm_BPRE (gafStageQ P.toLocalChartFamily P.zero 1)
    (gafStageQ P.toLocalChartFamily P.zero 2) (gafStageQ_two_le_one_BAS P)
    (fun z => Submodule.starProjection_apply_mem _ _)
    (gafStageThreeCutoff_starProjection_BAS P) z

/-- **CFS25** (`cor:fibration-uniform-cutoff-consumer`) on the actual data of the chain. The actual
preceding adjustments `g₁`, `g₂` have cumulative value errors at most `4κ/5` and at most
`3Σ_j/10` (`j` = the next stage) and supply (ZM) for the next edge / slim family; the auxiliary
cutoffs are CFS23 (`ψ₂`) and CFS22 (`ψ₃`) with their support, exact plateau and derivative bound
`C/ρ`, `C = 10⁴(N+1)²P⁴` fixed before `Δ`; their closed supports localize the original point and
CFS16 puts `π_j g_{j−1} p` in the half-tube of the original centre; CFS18: each stage map is
smooth on an open neighbourhood of the actual preceding image; the slim adjustment factors over
`Q₂`; every stage derivative budget is the one with `b_j = C`. -/
theorem cfs25_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q ∧
      ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 3 * S 1 / 10 * ρ q) ∧
    (∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q ∧
      ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 3 * S 2 / 10 * ρ q) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (C.g₁ p)| ≤ ρ j.1 / 32) ∧
    (∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (C.g₂ p)| ≤ ρ j.1 / 32) ∧
    (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1) ∧
    (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1) ∧
    (∀ p, C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
      (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
            p))
        (S 1 * ρ (C.sel 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) ∧
    (∀ p, C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
      (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          7 * (10 ^ 5 * Δ)) ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 2 ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
            p))
        (S 2 * ρ (C.sel 2 ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) ∧
    (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
          P.toLocalChartFamily P.zero p + t • C.g₁ p)‖ ≤ gafCutoffConstant / ρ p ∧
      ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
          P.toLocalChartFamily P.zero p + t • C.g₂ p)‖ ≤ gafCutoffConstant / ρ p) ∧
    (∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.g₁ ⊆ W ∧ W ⊆ {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      ContDiffOn ℝ ∞ C.Ψ₂ W) ∧
    (∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.g₂ ⊆ W ∧ ContDiffOn ℝ ∞ C.Ψ₃ W) ∧
    (∀ z, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.Ψ₃ z) =
      C.Ψ₃ ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z)) ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2 ∧
    gafCutoffConstant = 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, hd₂, -, -, -, -, hd₃⟩ := C.numbers
  have a := C.cfs25_prior_CFSB
  have t := C.cfs25_tube_CFSB
  have sm := C.cfs25_smooth_CFSB
  have e3 := C.cutoff_bindings.2.1.2.2.1
  have e5 := C.cutoff_bindings.2.1.2.2.2.2
  have s3 := C.cutoff_bindings.2.2.2.2.1
  have s5 := C.cutoff_bindings.2.2.2.2.2.2
  exact ⟨a.1, a.2.1, a.2.2.1, a.2.2.2, e3, s3, t.1, t.2, fun p t ht => ⟨(e5 p t ht).2, s5 p t ht⟩,
    sm.1, sm.2.1, sm.2.2, hd₂, hd₃, rfl⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
