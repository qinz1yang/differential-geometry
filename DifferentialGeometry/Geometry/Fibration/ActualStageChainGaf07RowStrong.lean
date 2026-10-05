import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Trivial

/-!
# GAF07, the STRONG row: local trivializations (D1), whole-fibre isotopy (D2)

Blueprint `master207B.tex`, GAF07 (B:6049–6165). `Gaf02ChainEJA.gaf07_row_GAFD` (C14-GAF-D G3,
accepted "done except D1 / D2") plus:

* D1, smooth bundle: for every chart index `i` of the stage, (a) the whole preimage of the base
  piece `B_j^i` is `{p ∈ Y_i | |g_i(p)| < 4ℓ_i}` and BASES' base chart `κ_i` maps `B_j^i`
  bijectively onto the ball `B(0, 4ℓ_i)`; (b) `g_i = κ_i ∘ π_jE` from that open set onto the ball
  is a smooth PROPER SURJECTIVE SUBMERSION of manifolds; (c) local trivializations over every
  point of the ball (Ehresmann, `ehresmann_local_triviality`): `Θ : g_i⁻¹(y) × Q ≃ₘ g_i⁻¹(Q)`
  over `Q`.
* D2, isotopy: every WHOLE fibre `(π_jE)⁻¹(w)` over `B_j` and the original fibre `{p ∈ Y_i |
  η_i(p) = a}` of the SAME coordinate are the images of two smooth embeddings of ONE manifold `S`
  (FC34a's diffeomorphism of the regular levels, transported along the whole trace inside `Y_i`):
  `Gaf02ChainE.gaf07_circle_isotopy_GAFD`, `Gaf02ChainE.gaf07_slim_isotopy_GAFD`.

`Gaf02ChainEJA.gaf07_row_strong_GAFD` — the accepted row and all of the above.
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

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, `j = 1`: every WHOLE fibre is isotopic (FC34a) in its buffered chart to an original
fibre of the same `η_i`** (D2): for `w ∈ W₁` in the ratio piece of `i`, `a = R_i⁻¹u_i(w)`, there are
a manifold `S` and smooth embeddings `ι₀, ι₁ : S → M` onto the original fibre
`{p ∈ Y_i | η_i(p) = a}` and onto the WHOLE fibre `(π₁E)⁻¹(w)`. -/
theorem gaf07_circle_isotopy_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    ∃ (S : Type) (_ : TopologicalSpace S)
      (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) S)
      (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) ∞ S)
      (ι₀ ι₁ : S → X),
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) 𝓘(ℝ, E3) ∞ ι₀ ∧
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ²) → ℝ) 𝓘(ℝ, E3) ∞ ι₁ ∧
      range ι₀ = {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        cgpCoord P.toLocalChartFamily P.zero (.inl i) p = (ρ i.1)⁻¹ •
          blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w} ∧
      range ι₁ = (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w} := by
  obtain ⟨ha, heq, -, -⟩ := C.gaf07_circle_whole_fibre_GAFC hc hβ hd w hW i hm hr
  rw [heq]
  exact C.toChain.gaf07_circle_level_pair_GAFD hc hβ hd i ha

/-- **GAF07, `j = 3`: every WHOLE fibre over the axis base is isotopic (FC34a) in its buffered
chart to an original fibre of the same `η_i`** (D2): for `w ∈ W₃` in the axis ratio piece of `i`,
`a = proj₀(R_i⁻¹u_i(w))`, there are a manifold `S` and smooth embeddings `ι₀, ι₁ : S → M` onto
`{p ∈ Y_i | η_i(p) = a}` and onto the WHOLE fibre `(π₃E)⁻¹(w)`. -/
theorem gaf07_slim_isotopy_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 2)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w)
    (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
      4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w) :
    ∃ (S : Type) (_ : TopologicalSpace S)
      (_ : ChartedSpace (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) S)
      (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) ∞ S)
      (ι₀ ι₁ : S → X),
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ∞ ι₀ ∧
      IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ∞ ι₁ ∧
      range ι₀ = {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
        (P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p =
          EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inr (.inl i)) w)} ∧
      range ι₁ = (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.toChain.E p)) ⁻¹' {w} := by
  obtain ⟨ha, heq, -, -⟩ := C.gaf07_slim_whole_fibre_axis_GAFD hc w hW i hm hr
  rw [heq]
  exact C.toChain.gaf07_slim_level_pair_GAFD hc i ha

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **GAF07, the STRONG row** on a chain with (JA) (TCP01 range of the packet; `K ≥ 5` and an
orientation for the standard slim type): the accepted row `gaf07_row_GAFD` and, for `j = 1, 3`,
(D1) for every chart index the base piece in BASES' chart with its whole preimage, the base-chart
map as a smooth proper surjective submersion of manifolds, and its local trivializations; (D2) at
every whole fibre over `B_j`, one manifold embedded smoothly onto the whole fibre and onto the
original fibre of the same `η_i`. -/
theorem gaf07_row_strong_GAFD (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3) :
    type_of% (C.gaf07_row_GAFD hβ hd hK oM) ∧
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      type_of% (C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i)) ∧
    (∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      type_of% (C.toGaf02ChainE.gaf07_slim_piece_GAFD C.c_two_lt i) ∧
      type_of% (C.toChain.gaf07_slim_chart_map_GAFD C.c_two_lt i) ∧
      type_of% (C.toChain.gaf07_slim_local_trivial_GAFD C.c_two_lt i)) ∧
    (∀ w (hW : w ∈ C.toChain.finalBase_BAS 0)
      (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
      (hm : 9 / 10 * ρ i.1 < blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w)
      (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w),
      type_of% (C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr)) ∧
    ∀ w (hW : w ∈ C.toChain.finalBase_BAS 2) (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
      (hm : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w)
      (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w),
      type_of% (C.toGaf02ChainE.gaf07_slim_isotopy_GAFD C.c_two_lt w hW i hm hr) :=
  ⟨C.gaf07_row_GAFD hβ hd hK oM,
    fun i => ⟨C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i⟩,
    fun i => ⟨C.toGaf02ChainE.gaf07_slim_piece_GAFD C.c_two_lt i,
      C.toChain.gaf07_slim_chart_map_GAFD C.c_two_lt i,
      C.toChain.gaf07_slim_local_trivial_GAFD C.c_two_lt i⟩,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_slim_isotopy_GAFD C.c_two_lt w hW i hm hr⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
