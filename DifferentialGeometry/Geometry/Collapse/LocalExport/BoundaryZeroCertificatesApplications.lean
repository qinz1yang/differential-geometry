import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroCertificates

/-!
# Consumers of the regional zero certificates (lane BZ-1, G1)

* `ZeroModelFamilyOn.shell_rank_BZ1`: the regional X82 certificate gives, at every point of every
  closed zero shell, `HasEuclideanSplitting q 1 β₁` in `ρ(q)⁻¹ d` and `splittingRank β 3 ≠ 0` (the
  raw shell clause of LPA05, on a complete carrier);
* `ZeroModelFamilyOn.adapted_value_BZ1`: the regional LC73 certificate gives, on the unit test
  ball, `|λ (η_c x − η_c q)| ≤ (1 + ζ) d_λ(x, q)` for the STORED radial function.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **Consumer of the regional X82 certificate.** Constants first; under the hypotheses of
`ZeroModelFamilyOn.shell_split_BZ1`, every point `q` of every closed zero shell of `F` has a
`(1, β₁)`-splitting in `ρ(q)⁻¹ d` and nonzero splitting rank (so the shells miss the zero
stratum). -/
theorem ZeroModelFamilyOn.shell_rank_BZ1 {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I3 M),
      RiemannianMetricComplete (I := I3) g →
      letI mM := inducedMetricSpace g
      ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) {ι : Type} {N C : ι → Type} [∀ a, MetricSpace (N a)]
        [∀ a, ChartedSpace E3 (N a)] [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
        {δ εr e T V : ℝ} {U₁ U₂ : Set M}
        (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂),
      δ < δ' →
      (∀ c (hc : c ∈ F.centres), Nonempty (RadialConeData (o (F.zero c hc).model))) →
      (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) →
      (∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
        Λ' ≤ (F.zero c hc).radius / ρ q) →
      ∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
        dist c q ≤ 10 * (F.zero c hc).radius →
        @HasEuclideanSplitting.{0, 0} M (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1 (β 1) ∧
          @splittingRank.{0, 0} M (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≠ 0 := by
  obtain ⟨δ', Λ', hδ', hΛ', h⟩ := ZeroModelFamilyOn.shell_split_BZ1 hβ hβone
  refine ⟨δ', Λ', hδ', hΛ', ?_⟩
  intro M _ _ _ _ _ _ g hg ρ hρ ι N C _ _ _ o δ εr e T V U₁ U₂ F hδ hcone hbuf hloc c hc q hq1 hq2
  let mM := inducedMetricSpace g
  obtain ⟨Zf, mZ, z, Fk, -⟩ := h M g hg ρ hρ F hδ hcone hbuf hloc c hc q hq1 hq2
  have hs : @HasEuclideanSplitting.{0, 0} M (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1 (β 1) :=
    ⟨Zf, mZ, z, ⟨Fk⟩⟩
  refine ⟨hs, ?_⟩
  have h1 := @le_splittingRank.{0, 0} M (mM.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 1
    (by norm_num) hs
  omega

/-- **Consumer of the regional LC73 certificate.** Constants first; under the hypotheses of
`ZeroModelFamilyOn.adapted_BZ1`, at every closed-shell point `q` and every ratio `λ ≥ Λ'`, the
prescribed function `ψ = λ (η_c − η_c(q))` of the STORED radial function satisfies
`|ψ x| ≤ (1 + ζ) d(x, q)` on the unit test ball of `(M, λ r_c⁻¹ d)`. -/
theorem ZeroModelFamilyOn.adapted_value_BZ1 {β : ℕ → ℝ} (hβ : 0 < β 1) {ζ : ℝ}
    (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I3 M),
      RiemannianMetricComplete (I := I3) g →
      letI mM := inducedMetricSpace g
      ∀ (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) {ι : Type} {N C : ι → Type} [∀ a, MetricSpace (N a)]
        [∀ a, ChartedSpace E3 (N a)] [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
        {δ εr e T V : ℝ} {U₁ U₂ : Set M}
        (F : ZeroModelFamilyOn I3 M g ρ hρ β N C o δ εr e T V U₁ U₂),
      δ < δ' → εr ≤ ε →
      (∀ c (hc : c ∈ F.centres), Nonempty (RadialConeData (o (F.zero c hc).model))) →
      (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) →
      ∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
        dist c q ≤ 10 * (F.zero c hc).radius →
        ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
        ∀ x ∈ @ball M ((mM.rescale ((F.zero c hc).radius)⁻¹
            (inv_pos.mpr (F.zero c hc).radius_pos)).rescale lam hlam).toPseudoMetricSpace q 1,
          |lam * ((F.zero c hc).radial x - (F.zero c hc).radial q)| ≤
            (1 + ζ) * @dist M ((mM.rescale ((F.zero c hc).radius)⁻¹
              (inv_pos.mpr (F.zero c hc).radius_pos)).rescale lam hlam).toDist x q := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ := ZeroModelFamilyOn.adapted_BZ1 hβ hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro M _ _ _ _ _ _ g hg ρ hρ ι N C _ _ _ o δ εr e T V U₁ U₂ F hδ hεr hcone hbuf c hc q hq1
    hq2 lam hlam hΛ x hx
  let mM := inducedMetricSpace g
  obtain ⟨-, Zf, mZ, z, κ, -, -, hψq, hlip, -⟩ :=
    h M g hg ρ hρ F hδ hεr hcone hbuf c hc q hq1 hq2 lam hlam hΛ
  have hq : q ∈ @ball M ((((inducedMetricSpace g).rescale ((F.zero c hc).radius)⁻¹
      (inv_pos.mpr (F.zero c hc).radius_pos)).rescale lam hlam).toPseudoMetricSpace) q 1 :=
    @mem_ball_self M (((inducedMetricSpace g).rescale ((F.zero c hc).radius)⁻¹
      (inv_pos.mpr (F.zero c hc).radius_pos)).rescale lam hlam).toPseudoMetricSpace q 1
      one_pos
  have h1 := hlip x hx q hq
  simp only [hψq, sub_zero] at h1
  exact h1

end DifferentialGeometry.Geometry.Collapse
