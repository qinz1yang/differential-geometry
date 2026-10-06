import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowStrongApplications
import DifferentialGeometry.Topology.Ehresmann.CircleBundleTrivializationEFE

/-!
# FDC03's circle bundle: local trivializations with the circle as fibre, in the GAF07 base chart

Lane S-EDP-FDC, group G6 (partial; draft 74 D74-13). On a chain `C : Gaf02ChainEJA P …` and a circle
chart index `i`, GAF07's strong row (`ActualStageChainGaf07RowStrong`/`Trivial`) gives the base
piece `B₁^i = W₁ ∩ {v_i > .9R_i, ‖u_i‖ < 4v_i}` (`gaf07_circle_piece_GAFD`: `κ_i = R_i⁻¹u_i` maps it
bijectively onto `B(0, 4)`), the base-chart map `g_i = κ_i ∘ π₁E : {p ∈ Y_i | ‖g_i p‖ < 4} → B(0, 4)`
as a smooth proper surjective submersion (`gaf07_circle_chart_map_GAFD`) and the connected whole
fibres (row item (7), `gaf07_circle_row_GAFD`).

* **`Gaf02ChainEJA.gaf07_circle_trivial_circle_EFE`**: over every `y ∈ B(0, 4)` an open `Q ∋ y` of
  the base ball and a diffeomorphism `g_i⁻¹(Q) ≃ₘ Q × Circle` (models `𝓘(ℝ, E3)` and
  `(𝓡 2).prod (𝓡 1)`) whose first coordinate is `g_i` — the `CircleBundle.trivialization` /
  `projection_trivialization` clauses in the chart `κ_i` of the base. Kernel:
  `exists_circle_trivialization_of_proper_submersion_EFE` (`CircleBundleTrivializationEFE`).
* `gaf07_circle_trivial_circle_C14Z_EFE`: the statement on the final closed family.
* `Gaf02Chain.circle_cbase_isCompact_EFE`: `π₁E(M₃)` is compact for every closed `M₃` (`cbase_compact`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Ehresmann

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

theorem gaf07_circle_trivial_circle_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ hmaps : ∀ p ∈ {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4},
        C.toChain.gaf07CircleCoord_GAFC i p ∈ ball (0 : ℝ²) 4,
      let fW : (⟨_, C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) →
          (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²) :=
        fun x => ⟨C.toChain.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩
      ∀ y, ∃ (Q : TopologicalSpace.Opens (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ :
          TopologicalSpace.Opens ℝ²)) (hQ : IsOpen (fW ⁻¹' Q)), y ∈ Q ∧
        ∃ Ψ : Diffeomorph 𝓘(ℝ, E3) ((𝓡 2).prod (𝓡 1))
          (⟨fW ⁻¹' Q, hQ⟩ : TopologicalSpace.Opens (⟨_, C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩
            : TopologicalSpace.Opens X)) (Q × Circle) ∞,
        ∀ x, (Ψ x).1.1 = fW x.1 := by
  obtain ⟨hmaps, hsm, hpr, hsurj, hreg⟩ := C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i
  refine ⟨hmaps, fun y => ?_⟩
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  have hpiece := C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i
  have hconn : ∀ y' : (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²),
      IsConnected {x : (⟨_, C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩ :
        TopologicalSpace.Opens X) | (⟨C.toChain.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
          (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²)) = y'} := by
    intro y'
    obtain ⟨w, hw, hwy⟩ := hpiece.2.surjOn (mem_ball_zero_iff.mpr (mem_ball_zero_iff.mp y'.2))
    have hw1 : w ∈ C.toChain.finalBase_BAS 0 := hw.1
    obtain ⟨-, hfib, -, hcon, -⟩ := h7 w hw1 i hw.2.1 hw.2.2
    have himg : Subtype.val '' {x : (⟨_, C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩ :
        TopologicalSpace.Opens X) | (⟨C.toChain.gaf07CircleCoord_GAFC i x, hmaps x x.2⟩ :
          (⟨ball (0 : ℝ²) 4, isOpen_ball⟩ : TopologicalSpace.Opens ℝ²)) = y'} =
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
          {w} := by
      rw [hfib]
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hgx : C.toChain.gaf07CircleCoord_GAFC i x.1 = y'.1 := congrArg Subtype.val hx
        exact ⟨x.2.1, by rw [hgx, ← hwy]; rfl⟩
      · rintro ⟨hY, hg⟩
        have hg' : C.toChain.gaf07CircleCoord_GAFC i p = y'.1 := by rw [hg, ← hwy]; rfl
        have hn : ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4 := by
          rw [hg']
          exact mem_ball_zero_iff.mp y'.2
        exact ⟨⟨p, hY, hn⟩, Subtype.ext hg', rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp⟩ := hcon.nonempty
      rw [← himg] at hp
      obtain ⟨x, hx, -⟩ := hp
      exact ⟨x, hx⟩
    · exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mp (himg ▸ hcon.isPreconnected)
  have : LocallyCompactSpace
      (⟨_, C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩ : TopologicalSpace.Opens X) :=
    (C.toChain.isOpen_gaf07CircleChartSource_GAFD i).locallyCompactSpace
  have hdim : Module.finrank ℝ E3 = Module.finrank ℝ ℝ² + 1 := by
    simp only [finrank_euclideanSpace_fin]
  obtain ⟨Q, hy, Ψ, hΨ⟩ := exists_circle_trivialization_of_proper_submersion_EFE _ hsm hpr hreg
    hdim hconn y
  exact ⟨Q, Q.isOpen.preimage hsm.continuous, hy, Ψ, hΨ⟩

end Gaf02ChainEJA

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
    e T V} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **`CircleBundle.cbase_compact`**: the image `C₁ = π₁E(M₃)` of a closed set (the actual `M₃` is
closed in the compact `X`) is compact. -/
theorem circle_cbase_isCompact_EFE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {M₃ : Set X}
    (hM₃ : IsClosed M₃) :
    IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) '' M₃) :=
  (hM₃.isCompact).image ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection.continuous.comp
    C.stage_smooth.2.2.continuous)

end Gaf02Chain

namespace Gaf02ChainEJA

/-- **The circle trivializations on the final closed family** (`LocalChartPacketsC14Z`). -/
theorem gaf07_circle_trivial_circle_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : PZ.toLocalChartFamily.circle.finite_centres.toFinset) :
    type_of% (Gaf02ChainEJA.gaf07_circle_trivial_circle_EFE C hβ hd i) :=
  by exact C.gaf07_circle_trivial_circle_EFE hβ hd i

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
