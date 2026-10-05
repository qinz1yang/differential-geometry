import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Bases

/-!
# GAF07 as ONE row on the chain with (JA), on BASES' open bases

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6049–6165). For
`j = 1, 3`: `B_j = ⋃_i {w ∈ W_j : v_i(w) > .9R_i, |u_i(w)|/v_i(w) < 4ℓ_i}`, `X_j = (π_jE)⁻¹(B_j)`;
`⋃_i {|η_i| ≤ 3.5ℓ_i} ⊂ X_j ⊂ U_j`; `π_jE : X_j → B_j` is a proper onto smooth bundle with connected
fibres, smooth circles (`j = 1`) or smooth `S²` / `T²` (`j = 3`); each WHOLE fibre is isotopic, in
its original buffered chart, to a fibre of the same `η_i`; the whole stage-`j` fibre equals the
whole final fibre.

On ONE chain `C : Gaf02ChainEJA` (`c₃ < 1/1000` = `C.c_two_lt`) with BASES' final bases
`W₁ = C.toChain.finalBase_BAS 0`, `W₃ = C.toChain.finalBase_BAS 2` and its open bases
`B₁ = circleBase_BAS` (full `ℝ²` ratio), `B₃ = slimBase_BAS` (AXIS ratio — the real `u_i` of a
one-dimensional chart):

* `Gaf02ChainEJA.gaf07_circle_row_GAFD (C) hβ hd` — `j = 1`; numerical hypotheses: the packet's
  TCP01 range `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10` (the right inverse of `Dη_i`,
  `tcp01_gram_right_inverse_FAM2`).
* `Gaf02ChainEJA.gaf07_slim_row_GAFD (C) hK oM` — `j = 3`; inputs of the standard smooth type
  (review 70, lane C14-SLIM-STD): packet jet order `K ≥ 5` and a manifold orientation `oM` of `M`.
* `Gaf02ChainEJA.gaf07_row_GAFD` — both.

Clause by clause (each part, in this order): (1) `B_j = W_j ∩ O_j` with `O_j` open (relatively open
in the embedded `W_j`; chart form `circleBase_chart_BAS` / `slimBase_chart_BAS` of BASES); (2) first
inclusion `{|η_i| ≤ 3.5ℓ_i} ⊂ X_j`; (3) `X_j ⊂ U_j` (cutoff one, `|η_i| < 4.01ℓ_i < 5ℓ_i`);
(4) properness of `π_jE : X_j → B_j`; (5) onto; (6) submersion in the base chart: at every
`p ∈ X_j` and every ratio index `i` of `π_jE(p)`, `p ∈ Y_i` and `g_i = R_i⁻¹u_i ∘ π_jE` has
surjective differential; (7) WHOLE fibres over `B_j`: `a = R_i⁻¹u_i(w)` is in the `4ℓ_i` ball, the
whole fibre equals the whole adjusted level `{p ∈ Y_i | g_i(p) = a}`, is homeomorphic to the
original fibre `{p ∈ Y_i | η_i(p) = a}` (FC34a transport), is connected, is the image of a smooth
embedding of `Circle` (`j = 1`) or of the standard `ClosureSphere` / `Torus` (`j = 3`), and the
whole trace `{h_τ = a}`, `h_τ = (1 − τ)η_i + τg_i`, `τ ∈ [0, 1]`, stays in `{|η_i| < 4.01ℓ_i}`
(inside the buffered chart `Y_i`); (8) whole stage fibre = whole final fibre
(`f_j⁻¹(Θ_j⁻¹w) = (π_jE)⁻¹(w)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

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

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **GAF07, `j = 1` (circles), the whole row part** on BASES' `B₁ = circleBase_BAS`, for a chain
with (JA) and the packet's TCP01 range: (1) `B₁` relatively open in `W₁`; (2) `{‖η_i‖ ≤ 3.5} ⊂ X₁`;
(3) `X₁ ⊂ U₁`; (4) proper; (5) onto; (6) submersion in the base chart; (7) every WHOLE fibre is the
whole adjusted level, `≃ₜ` the original fibre, connected, a SMOOTH circle, with its whole trace in
`{‖η_i‖ < 4.01}`; (8) whole stage fibre = whole final fibre. -/
theorem gaf07_circle_row_GAFD (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    (C.toChain.circleBase_BAS = C.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 P.toLocalChartPackets ∧
      IsOpen (gaf07CircleRatio_G47 P.toLocalChartPackets)) ∧
    (∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X),
      p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2 →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        C.toChain.circleBase_BAS) ∧
    (∀ p : X, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        C.toChain.circleBase_BAS →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 ∧
        P.toLocalChartFamily.circle.cutoff i.1 p = 1) ∧
    IsProperMap (C.toChain.circleBase_BAS.restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))) ∧
    (∀ w ∈ C.toChain.circleBase_BAS,
      ∃ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w) ∧
    (∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X),
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) →
      p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) p)) ∧
    (∀ w ∈ C.toChain.finalBase_BAS 0, ∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) w →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w →
      ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl i) w‖ < 4 ∧
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
            {w} =
          {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
            C.toChain.gaf07CircleCoord_GAFC i p = (ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w} ∧
        Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (C.toChain.E p)) ⁻¹' {w} ≃ₜ
          {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
            cgpCoord P.toLocalChartFamily P.zero (.inl i) p = (ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inl i) w}) ∧
        IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (C.toChain.E p)) ⁻¹' {w}) ∧
        (∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
          range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (C.toChain.E p)) ⁻¹' {w}) ∧
        ∀ p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i, ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) • cgpCoord P.toLocalChartFamily P.zero (.inl i) p +
              t • C.toChain.gaf07CircleCoord_GAFC i p =
            (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inl i) w →
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100) ∧
    ∀ w ∈ C.toChain.finalBase_BAS 0, ∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) w →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w →
      ∃ w₀ ∈ C.toChain.circlePatch_BAS i, C.toChain.Θ_BAS 0 w₀ = w ∧
        C.toChain.stageMap_BAS 0 ⁻¹' {w₀} =
          (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
            {w} := by
  have hc := C.c_two_lt
  refine ⟨C.toGaf02ChainE.circleBase_relOpen_GAFD,
    fun i p hp hη => C.toGaf02ChainE.gaf07_circle_first_inclusion_base_GAFD hc i hp hη,
    fun p hp => C.toGaf02ChainE.gaf07_circle_total_subset_base_GAFD hc p hp,
    (C.toChain.gaf07_proper_G47 0 _).1,
    fun w hw => C.toGaf02ChainE.gaf07_circle_onto_GAFC w hw.1,
    fun i p hm hr => C.toGaf02ChainE.gaf07_circle_submersion_GAFC hc hβ hd i p hm hr,
    fun w hW i hm hr => ?_,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_circle_stage_fibre_GAFC hc w hW i hm hr⟩
  obtain ⟨ha, heq, hhom, hconn⟩ :=
    C.toGaf02ChainE.gaf07_circle_whole_fibre_GAFC hc hβ hd w hW i hm hr
  refine ⟨ha, heq, hhom, hconn,
    C.toGaf02ChainE.gaf07_circle_whole_fibre_smooth_GAFD hc hβ hd w hW i hm hr,
    fun p hp t ht hlev => ?_⟩
  exact (C.toChain.gaf07_circle_coordinate_G47 hc i hp.1 hp.2).2 t ht _ ha hlev

/-- **GAF07, `j = 3` (slim charts), the whole row part** on BASES' AXIS base `B₃ = slimBase_BAS`,
for a chain with (JA), packet jet order `K ≥ 5` and a manifold orientation `oM`: (1) `B₃` relatively
open in `W₃`; (2) `{|η_i| ≤ 3.5·10⁵Δ} ⊂ X₃`; (3) `X₃ ⊂ U₃`; (4) proper; (5) onto; (6) submersion in
the base chart; (7) every WHOLE fibre is the whole adjusted level, `≃ₜ` the original fibre,
connected, the image of a smooth embedding of the standard `ClosureSphere` or `Torus`, with its
whole trace in `{|η_i| < 4.01·10⁵Δ}`; (8) whole stage fibre = whole final fibre. -/
theorem gaf07_slim_row_GAFD (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hK : 5 ≤ K)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3) :
    (∃ O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen O ∧
      C.toChain.slimBase_BAS = C.toChain.finalBase_BAS 2 ∩ O) ∧
    (∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X),
      p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
        7 / 2 * (10 ^ 5 * Δ) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        C.toChain.slimBase_BAS) ∧
    (∀ p : X, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        C.toChain.slimBase_BAS →
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
        |(P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.toLocalChartFamily.slim.cutoff i.1 p = 1) ∧
    IsProperMap (C.toChain.slimBase_BAS.restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) ∧
    (∀ w ∈ C.toChain.slimBase_BAS,
      ∃ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w) ∧
    (∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X),
      9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) →
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) →
      p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.toChain.gaf07SlimCoord_GAFC i) p)) ∧
    (∀ w ∈ C.toChain.finalBase_BAS 2, ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w →
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w →
      |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
          blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
            w)| < 4 * (10 ^ 5 * Δ) ∧
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
            {w} =
          {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
            C.toChain.gaf07SlimCoord_GAFC i p = EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inl i)) w)} ∧
        Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (C.toChain.E p)) ⁻¹' {w} ≃ₜ
          {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
            (P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p =
              EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
                blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                  (.inr (.inl i)) w)}) ∧
        IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (C.toChain.E p)) ⁻¹' {w}) ∧
        ((∃ f : ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
            range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
              (C.toChain.E p)) ⁻¹' {w}) ∨
          (∃ f : Torus → X, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
            range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
              (C.toChain.E p)) ⁻¹' {w})) ∧
        ∀ p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i, ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) * (P.toLocalChartFamily.slim.centre i.1
              ((Set.Finite.mem_toFinset _).mp i.2)).coord p +
              t * C.toChain.gaf07SlimCoord_GAFC i p =
            EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inl i)) w) →
          |(P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
            401 / 100 * (10 ^ 5 * Δ)) ∧
    ∀ w ∈ C.toChain.finalBase_BAS 2, ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w →
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w →
      ∃ w₀ ∈ C.toChain.slimPatch_BAS i, C.toChain.Θ_BAS 2 w₀ = w ∧
        C.toChain.stageMap_BAS 2 ⁻¹' {w₀} =
          (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
            {w} := by
  have hc := C.c_two_lt
  refine ⟨C.toGaf02ChainE.slimBase_relOpen_GAFD,
    fun i p hp hη => C.toGaf02ChainE.gaf07_slim_first_inclusion_base_GAFD hc i hp hη,
    fun p hp => C.toGaf02ChainE.gaf07_slim_total_subset_base_GAFD hc p hp,
    (C.toChain.gaf07_proper_G47 2 _).1,
    fun w hw => C.toGaf02ChainE.gaf07_slim_onto_GAFC w hw.1,
    fun i p hm hr => ?_,
    fun w hW i hm hr => ?_,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_slim_stage_fibre_GAFD hc w hW i hm hr⟩
  · have hY := C.toGaf02ChainE.gaf07_slim_fibre_mem_Y_axis_GAFD hc _ i hm hr p rfl
    exact ⟨hY, C.toChain.gaf07_slim_submersion_of_mem_GAFD hc i hY⟩
  · obtain ⟨-, hΔ1, -⟩ := C.toChain.std
    have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
    obtain ⟨ha, heq, hhom, hconn⟩ :=
      C.toGaf02ChainE.gaf07_slim_whole_fibre_axis_GAFD hc w hW i hm hr
    refine ⟨ha, heq, hhom, hconn, ?_, fun p hp t ht hlev => ?_⟩
    · rw [heq]
      exact C.toChain.gaf07_slim_level_standard_GAFC hc hK oM i ha
    · have hv : |C.toChain.gaf07SlimCoord_GAFC i p -
          (P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
          1 / 800 := C.toChain.gaf07_slim_axis_value_GAFC hc i hp.1 hp.2
      have h := norm_lt_of_level_of_straight_line (V := ℝ) ht hℓ
        (by rw [Real.norm_eq_abs]; exact ha) (by rw [Real.norm_eq_abs]; exact hv)
        (by simpa only [smul_eq_mul] using hlev)
      rwa [Real.norm_eq_abs] at h

/-- **GAF07, the whole row** (`j = 1` and `j = 3`) on a chain with (JA): the circle part with the
packet's TCP01 range, the slim part with `K ≥ 5` and a manifold orientation `oM`. -/
theorem gaf07_row_GAFD (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3) :
    type_of% (C.gaf07_circle_row_GAFD hβ hd) ∧ type_of% (C.gaf07_slim_row_GAFD hK oM) :=
  ⟨C.gaf07_circle_row_GAFD hβ hd, C.gaf07_slim_row_GAFD hK oM⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
