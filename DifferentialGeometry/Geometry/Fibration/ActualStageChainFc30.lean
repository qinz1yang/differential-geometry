import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# FC30 (buffered ambient cutoffs) on the chain object: the chain-dependent clauses

Blueprint `master207B.tex`, FC30 (`found:fibration-ambient-cutoffs`, B:2779–2806). The E-free
clauses are `fc30_row_FCF` (lane FC-FOUND, `FoundationBufferedCutoffs.lean`); the two clauses that
need the chain are proved here on ONE chain `C : Gaf02Chain P …`:

* the cutoffs at the chain's OWN previous images `𝓔⁰`, `g₁ = C.g₁`, `g₂ = C.g₂` (CFS31's
  closeness is the chain's own strict error and (ZM), `C.cutoff_bindings`): smooth on an OPEN
  neighbourhood of the image (`ψ₁`, `ψ₃` everywhere; `ψ₂` on the open set `{x_ρ > 0}`, which
  contains `g₁(M)` and every segment `[𝓔⁰ p, g₁ p]`), values in `[0, 1]`, plateau one on the
  thresholds `6`, `6Δ` (height `< 6Δ`), `6·10⁵Δ`, closed support only over the threshold-`7`
  cores (stage one `13/2`), `‖dψ_j‖ ≤ b_cut/ρ(p)` at `g_{j−1} p`;
* "closed supports lie in the open domain of `P_jπ_j`": if `g_{j−1} p ∈ tsupport ψ_j` then
  `π_j g_{j−1} p` lies in the OPEN tube `Ω_j = ⋃_{x ∈ S_j} B(x, Σ_jρ(sel_j x))`
  (`C.stage_input_mem_tube`), on which the slot map `a_j` (hence `P_j = π_j ∘ a_j`) is smooth
  (`Gaf02StageSlot.smooth`).

`Gaf02Chain.fc30_row_chain_G47` is the whole row on the chain; consumer
`fc30_final_family_chain_G47` (a chain on `LocalChartPacketsC14Z`).
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

/-- The stage tube `Ω_st = ⋃_{x ∈ S_st} B(x, Σ_st ρ(sel_st x))` of a chain is open and its slot
map is smooth on it. -/
theorem tube_open_smooth_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    IsOpen (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (S st * ρ (C.sel st x))) ∧
      ContDiffOn ℝ ∞ (C.slot st).map
        (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (S st * ρ (C.sel st x))) :=
  ⟨isOpen_biUnion fun _ _ => isOpen_ball, (C.slot st).smooth⟩

/-- **FC30 on the chain object** (B:2779): the three actual cutoffs at the chain's own previous
images `𝓔⁰`, `g₁`, `g₂` — smooth on an open neighbourhood of the image, `[0, 1]`-valued, plateau
one on the thresholds `6`, `6Δ` (height `< 6Δ`), `6·10⁵Δ`, closed support only over the cores
`13/2`, `7Δ` (height `< 7Δ`), `7·10⁵Δ`, `‖dψ_j(g_{j−1} p)‖ ≤ b_cut/ρ(p)` — and their closed supports
lie in the open domain of `P_jπ_j`: `g_{j−1} p ∈ tsupport ψ_j ⇒ π_j g_{j−1} p ∈ Ω_j`, an open
tube on which the slot map is smooth. -/
theorem fc30_row_chain_G47 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (ContDiff ℝ ∞ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P) (gafCircleMarker P)) ∧
      (∀ z, (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
          p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) →
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1) ∧
      (∀ p, cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport (markerLocalitySourceCutoff
          lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P) (gafCircleMarker P)) →
        (∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
          p ∈ ball j.1 (200 * ρ j.1) ∧
            ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ ≤ 13 / 2) ∧
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈
          ⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ball x (S 0 * ρ (C.sel 0 x))) ∧
      (∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
          (gafCircleVector P) (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ ≤
        gafCutoffConstant / ρ p)) ∧
    (IsOpen {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      ContDiffOn ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      (∀ z, (gafStageTwoCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1) ∧
      (∀ p, C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
        (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈
          ⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ball x (S 1 * ρ (C.sel 1 x))) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < gafScaleMarker P.toLocalChartFamily P.zero ((1 - t) • cgpGlobalMap P.toLocalChartFamily
            P.zero p + t • C.g₁ p) ∧
        ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
            P.toLocalChartFamily P.zero p + t • C.g₁ p)‖ ≤ gafCutoffConstant / ρ p) ∧
    (ContDiff ℝ ∞ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
      (∀ z, (gafStageThreeCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
        (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1) ∧
      (∀ p, C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
            7 * (10 ^ 5 * Δ)) ∧
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈
          ⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ball x (S 2 * ρ (C.sel 2 x))) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
            P.toLocalChartFamily P.zero p + t • C.g₂ p)‖ ≤ gafCutoffConstant / ρ p) ∧
    ∀ st, IsOpen (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (S st * ρ (C.sel st x))) ∧
      ContDiffOn ℝ ∞ (C.slot st).map
        (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (S st * ρ (C.sel st x))) := by
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩, c1, c2, c3, c4, c5⟩ := C.cutoff_bindings
  refine ⟨⟨a1, a2, a3, fun p hp => ⟨a4 p hp, ?_⟩, a5⟩,
    ⟨isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous, b1, b2,
      b3, fun p hp => ⟨b4 p hp, ?_⟩, b5⟩,
    ⟨c1, c2, c3, fun p hp => ⟨c4 p hp, ?_⟩, c5⟩, C.tube_open_smooth_G47⟩
  · obtain ⟨hx, hb⟩ := (C.stage_input_mem_tube p).1 hp
    exact mem_biUnion hx hb
  · obtain ⟨hx, hb⟩ := (C.stage_input_mem_tube p).2.1 hp
    exact mem_biUnion hx hb
  · obtain ⟨hx, hb⟩ := (C.stage_input_mem_tube p).2.2 hp
    exact mem_biUnion hx hb

end Gaf02Chain

/-- **Consumer: FC30's chain clauses for a chain on the final family** `LocalChartPacketsC14Z`
(projection `toLocalChartPackets`): at every point the derivative bounds of `ψ₂`, `ψ₃` hold AT the
previous images `g₁ p`, `g₂ p` themselves, and image points in the closed supports of `ψ₂`, `ψ₃`
project into the open tubes where the slot maps are smooth. -/
theorem fc30_final_family_chain_G47 {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (p : X) :
    ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p)‖ ≤ gafCutoffConstant / ρ p ∧
      ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p)‖ ≤
        gafCutoffConstant / ρ p ∧
      (C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
        ∃ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
          (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈
            ball x (S 1 * ρ (C.sel 1 x))) ∧
      (C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        ∃ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
          (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈
            ball x (S 2 * ρ (C.sel 2 x))) := by
  obtain ⟨-, ⟨-, -, -, -, h2, h2d⟩, ⟨-, -, -, h3, h3d⟩, -⟩ := C.fc30_row_chain_G47
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.g₁ p =
      C.g₁ p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  have e2 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.g₂ p =
      C.g₂ p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  refine ⟨?_, ?_, fun hp => ?_, fun hp => ?_⟩
  · have h := (h2d p 1 ht).2
    rwa [e1] at h
  · have h := h3d p 1 ht
    rwa [e2] at h
  · simpa only [mem_iUnion, exists_prop] using (h2 p hp).2
  · simpa only [mem_iUnion, exists_prop] using (h3 p hp).2

end DifferentialGeometry.Geometry.Collapse
