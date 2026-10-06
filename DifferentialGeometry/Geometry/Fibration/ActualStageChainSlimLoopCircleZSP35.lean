import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimBundleEFE
import DifferentialGeometry.Topology.Ehresmann.LoopCircleSubmersionZSP35

/-!
# ZSP04, closed side: the circle branch of the slim bundle (S1) on the chain

Lane S-ZSP04, group G18 (draft 74 D74-10 / S1, ZSP04 B:6531–6595: "on a circle component it gives
the actual surface mapping torus"). Kernel: `Topology/Ehresmann/LoopCircleSubmersionZSP35.lean`
(`exists_loop_circle_submersion_ZSP35`). The model is the tree's `SlimModel.overCircle`: a smooth
submersion `p` to `S¹` with an actual embedded standard surface as the fibre over `1` on a piece
without boundary (monodromy kept; no product is asserted).

* `Gaf02ChainEJA.slim_loop_circle_ZSP35` (final family, `K ≥ 5`): for ANY smooth compact
  one-dimensional domain `D` of the slim base `Bs` and every loop `j` of `D`, the preimage
  `O_j = f₃⁻¹(range (loop j))` is open and compact in `M`, and there is `p : M → S¹` smooth on
  `O_j` with onto differential, recording the base position (`p x = e^{2π i t} ↔ f₃ x = loop j t`),
  whose fibre over `1` is the range of a standard `ClosureSphere` or `Torus` whole fibre.

Consumer: `slim_loop_circle_C14Z_ZSP35`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim circle branch (S1) on the final family**: over every loop `j` of a smooth compact
one-dimensional domain `D ⊆ Bs`, the whole preimage `O_j = f₃⁻¹(range (loop j))` is open and
compact, and a circle-valued map `p`, smooth with onto differential on `O_j`, records the position
over the loop; the fibre over `1` is a standard whole `S²` or `T²`. -/
theorem slim_loop_circle_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) (D : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (j : Fin D.l) :
    IsOpen (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
      IsCompact (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
      ∃ p : X → Circle,
        ContMDiffOn 𝓘(ℝ, E3) (𝓡 1) ∞ p (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
        (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j),
          Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) p x)) ∧
        (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j), ∀ t : ℝ,
          p x = Circle.exp (2 * Real.pi * t) ↔ C.slimMap_ZSP35 x = D.loop j t) ∧
        ((∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            (D.loop j 0),
          range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j) ∧ p x = 1}) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
            (D.loop j 0),
          range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j) ∧ p x = 1})) := by
  obtain ⟨hOo, hOc, p, hp, hsub, hiff⟩ := exists_loop_circle_submersion_ZSP35
    (P := C.slimSubmersion_EFE) (D.loop_smooth j) (D.loop_periodic j) (D.loop_injOn j)
    (D.loop_deriv j) (D.loop_relOpen j)
  have hw : D.loop j 0 ∈ C.slimBs_ZSP35 :=
    D.subset_base (by
      rw [D.carrier_eq]
      exact Or.inr (mem_iUnion.mpr ⟨j, mem_range_self 0⟩))
  have hfib : ∀ {F₀range : Set X}, F₀range = C.slimMap_ZSP35 ⁻¹' {D.loop j 0} →
      F₀range = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j) ∧ p x = 1} := by
    intro F₀range h
    rw [h]
    ext x
    constructor
    · intro hx
      have hxO : x ∈ C.slimMap_ZSP35 ⁻¹' range (D.loop j) := ⟨0, hx.symm⟩
      refine ⟨hxO, ?_⟩
      have := (hiff x hxO 0).mpr hx
      simpa using this
    · rintro ⟨hxO, hx1⟩
      refine (hiff x hxO 0).mp ?_
      simpa using hx1
  refine ⟨hOo, hOc, p, hp, hsub, hiff, ?_⟩
  rcases C.standard_whole_fibre_EFE hK hw with h | h
  · obtain ⟨F₀⟩ := h
    exact Or.inl ⟨F₀, hfib F₀.range_eq⟩
  · obtain ⟨F₀⟩ := h
    exact Or.inr ⟨F₀, hfib F₀.range_eq⟩

end Final

end Gaf02ChainEJA

section Consumer

/-- **Consumer: the circle branch over the loops of ZSP04's `D₃`** on the final family: for the
`K₃, D₃ = K₃ ∩ C₃` of `zsp04_D3_ZSP35`, over every loop `j` of `D₃` the whole preimage is an open
compact set carrying a circle-valued map, smooth with onto differential. -/
theorem slim_loop_circle_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      ∀ j : Fin D₃.l, IsOpen (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        ∃ p : X → Circle,
          ContMDiffOn 𝓘(ℝ, E3) (𝓡 1) ∞ p (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
          ∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j),
            Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) p x) := by
  obtain ⟨K₃, D₃, hD, -⟩ := C.zsp04_D3_ZSP35 hεr
  refine ⟨K₃, D₃, hD, fun j => ?_⟩
  obtain ⟨hOo, hOc, p, hp, hsub, -⟩ := C.slim_loop_circle_ZSP35 hK D₃ j
  exact ⟨hOo, hOc, p, hp, hsub⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
