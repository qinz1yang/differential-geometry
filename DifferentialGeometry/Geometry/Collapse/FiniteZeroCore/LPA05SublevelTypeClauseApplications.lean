import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause

/-!
# LPA05's sublevel types: the typed sublevels are compact (consumer)

* `isCompact_of_partialDiffeomorph_image`: a set inside the source of a partial diffeomorphism
  whose image is compact is compact.
* `isCompact_of_sublevel_types`: a set of a compact source with one of the five types of
  `lpa05_selected_sublevel_types_withCarrier` (the whole source, or carried onto a disc core of a
  soul bundle over `Fin 0 → ℝ`, `AddCircle 1` or a compact surface) is compact.
* `lpa05_selected_sublevels_typed_and_compact`: in LPA05's selection, every actual sublevel
  `{η_c ≤ ρ}`, `ρ ∈ [1/5, 2]`, of every selected zero-model ball is compact AND has one of LFR54's
  types (the compact model with LFR53's type of the oriented source; `D³`; `S¹ × D²`;
  `ℝP³ ∖ int D³`; `D(o(K))`), on the same selection.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **Compact images pull back along partial diffeomorphisms.** A set `A ⊆ dom Ψ` whose image
`Ψ '' A` is compact is compact (it is the image of `Ψ '' A` under the continuous inverse). -/
theorem isCompact_of_partialDiffeomorph_image {M N : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [TopologicalSpace N] [ChartedSpace E3 N]
    (Ψ : PartialDiffeomorph I3 I3 M N ∞) {A : Set M} (hA : A ⊆ Ψ.source)
    (hK : IsCompact (Ψ '' A)) : IsCompact A := by
  have htgt : Ψ '' A ⊆ Ψ.target :=
    Ψ.toPartialEquiv.image_source_eq_target ▸ image_mono hA
  have hsymm : Ψ.symm '' (Ψ '' A) = A := by
    rw [← image_comp]
    exact (image_congr fun y hy => Ψ.toPartialEquiv.left_inv (hA hy)).trans (image_id _)
  rw [← hsymm]
  exact hK.image_of_continuousOn (Ψ.symm.contMDiffOn.continuousOn.mono htgt)

/-- **The five sublevel types are compact.** In a compact source, a set that is the whole source
or is carried by an ambient partial diffeomorphism onto a disc core of a soul bundle over
`Fin 0 → ℝ`, `AddCircle 1` or a compact surface is compact. -/
theorem isCompact_of_sublevel_types {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] [CompactSpace M] {oM : ManifoldOrientation I3 M 3} {Nc : Type}
    [TopologicalSpace Nc] [ChartedSpace E3 Nc] {A : Set M}
    (h : CompactModelSublevel oM Nc A ∨ PointSoulCoreSublevel Nc A ∨ CircleSoulCoreSublevel Nc A ∨
      ProjectiveSoulCoreSublevel Nc A ∨ KleinSoulCoreSublevel Nc A) : IsCompact A := by
  rcases h with ⟨hA, -⟩ | ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hAs, hΨA, -⟩ |
      ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hAs, hΨA, -⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hAs,
        hΨA, -⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hAs,
        hΨA, -⟩
  · rw [hA]
    exact isCompact_univ
  · exact isCompact_of_partialDiffeomorph_image Ψ hAs (hΨA ▸ isCompact_discCore D T₀)
  · exact isCompact_of_partialDiffeomorph_image Ψ hAs (hΨA ▸ isCompact_discCore D T₀)
  · exact isCompact_of_partialDiffeomorph_image Ψ hAs (hΨA ▸ isCompact_discCore D T₀)
  · exact isCompact_of_partialDiffeomorph_image Ψ hAs (hΨA ▸ isCompact_discCore D T₀)

/-- **The selected sublevels are typed and compact.** In LPA05's selection with the carrier and
the compact metric, for oriented sources, every actual sublevel `{η_c ≤ ρ}`, `ρ ∈ [1/5, 2]`, of
every selected zero-model ball is compact and has one of LFR54's types. -/
theorem lpa05_selected_sublevels_typed_and_compact
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
      [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (_ : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ oX : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∃ (N C : X i → Type) (_ : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (_ : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          ∀ c (hc : c ∈ Z.centres), ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            IsCompact {x | (Z.zero c hc).radial x ≤ ρ'} ∧
            (CompactModelSublevel (oX i) (N (Z.zero c hc).model)
                {x | (Z.zero c hc).radial x ≤ ρ'} ∨
              PointSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
              CircleSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'} ∨
              ProjectiveSoulCoreSublevel (N (Z.zero c hc).model)
                {x | (Z.zero c hc).radial x ≤ ρ'} ∨
              KleinSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ ρ'}) := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    lpa05_selected_sublevel_types_withCarrier hβ hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder oX Λ w hΛ hw hwc
  obtain ⟨V₀, hTV, δ₀, hδ0, hδδ', hW⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand K hK A hA
    hder oX Λ w hΛ hw hwc
  refine ⟨V₀, hTV, δ₀, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi ρ hρ hρc hρw
  obtain ⟨N, C, mN, cN, hMN, mC, o, Z, hZ⟩ := hi ρ hρ hρc hρw
  exact ⟨N, C, mN, cN, hMN, mC, o, Z, fun c hc ρ' hρ' =>
    ⟨isCompact_of_sublevel_types (hZ c hc ρ' hρ'), hZ c hc ρ' hρ'⟩⟩

end DifferentialGeometry.Geometry.Collapse
