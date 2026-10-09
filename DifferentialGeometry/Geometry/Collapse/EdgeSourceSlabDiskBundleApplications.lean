import DifferentialGeometry.Geometry.Collapse.EdgeSourceSlabDiskBundle
import DifferentialGeometry.Geometry.Collapse.EdgeSourceSlabEnclosure

/-!
# Consumer: the single-index assembly with properness from a compact slab

`edgeSourceSlab_disk_bundle_of_model` with its properness hypothesis produced by B5's
`isCompact_slab_preimage_of_subset_compact`: it suffices that the whole slab `{|f| < β, H ≤ 4Δ}` of
`O` lies in a compact `C ⊆ O` (in LFR28: `B̄(p, 6Δ) ∩ {d_A ≤ 5Δ}`, by (LFR28.6))
(`edgeSourceSlab_disk_bundle_of_compact_slab`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
  DifferentialGeometry.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **Concrete consumer.** LFR28.1 on the actual source slab, with properness from a compact slab. -/
theorem edgeSourceSlab_disk_bundle_of_compact_slab
    {S : Type} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {z₀ : S} {h : S → ℝ} {Wh : Set S} (hW : IsOpen Wh) (hW9 : closedBall z₀ 9 ⊆ Wh)
    (hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh)
    (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0)
    {b : ClosedCell 2 → S} (hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b)
    (hrange : range b = {x | dist x z₀ < 9 ∧ h x ≤ 4}) {Δ : ℝ} (hΔ : 0 < Δ)
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
    {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {r : ℕ} (hr : 3 ≤ r) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r)
    (jN : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N X r) (O : TopologicalSpace.Opens X)
    (hU : ∀ x ∈ edgeModelCylinder z₀ Δ, Θ x ∈ jN.source ∧ jN (Θ x) ∈ O)
    {f H : X → ℝ} (hf : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f O)
    (hH : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H O) {β δ : ℝ}
    (hval : ∀ x : edgeModelCylinder z₀ Δ,
      |f (jN (Θ x)) - (x : ℝ × S).1| ≤ δ ∧ |H (jN (Θ x)) - Δ * h (x : ℝ × S).2| ≤ δ)
    (hrow : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ β + δ →
      (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 ≤ 4 * Δ + δ →
      ∃ X : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X).1 = 1 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ)) x X).1 - 1| ≤ 1 / 1000)
    (hpair : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ β + δ →
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 - 4 * Δ| ≤ δ →
      ∃ X₁ X₂ : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₁).1 = 1 ∧
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₂).1 = 0 ∧
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₁).2 = 0 ∧
        1 / 2 ≤ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X₂).2 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ)) x X₁).1 - 1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ)) x X₂).1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ)) x X₁).2| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ)) x X₂).2 -
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
            (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
            x X₂).2| ≤ 1 / 1000)
    {Q : Set (edgeModelCylinder z₀ Δ)} (hQ : IsCompact Q)
    (hQw : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ δ →
      (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 ≤ 4 * Δ + δ → x ∈ Q)
    (henc : ∀ y ∈ O, |f y| < β → H y ≤ 4 * Δ → ∃ x ∈ edgeModelCylinder z₀ Δ, jN (Θ x) = y)
    {C : Set X} (hC : IsCompact C) (hCO : C ⊆ O)
    (hslab : ∀ y ∈ O, |f y| < β → H y ≤ 4 * Δ → y ∈ C)
    {a₀ b₀ : ℝ} (ha₀ : -β < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < β) :
    letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
    ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f y))
      (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => 4 * Δ - H y))
      (hreg : ∀ y : O, f y = 0 → 0 ≤ 4 * Δ - H y →
        Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f y) y))
      (hregb : ∀ y : O, f y = 0 → 4 * Δ - H y = 0 →
        Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : O => ((f y, 4 * Δ - H y) : ℝ × ℝ)) y)),
      letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
      let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
      Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
        {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y}) ∧
      CompactSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y} ∧
      ConnectedSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y} ∧
      (∃ Θ' : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y} × Q₀ → O,
        ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
        (∀ p, f (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - H (Θ' p)) ∧
        (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
        ∃ O' : Set O, IsOpen O' ∧ (∀ y : O, f y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - H y → y ∈ O') ∧
          ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
            ∀ (y : O) (hy : f y ∈ Ioo a₀ b₀), 0 ≤ 4 * Δ - H y →
              ∃ hR : f (R y) = 0 ∧ 0 ≤ 4 * Δ - H (R y),
                Θ' (⟨R y, hR⟩, ⟨f y, hy⟩) = y) ∧
      ∀ y : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y},
        (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ H y = 4 * Δ := by
  have hfc : ContinuousOn f C := (hf.continuousOn).mono hCO
  have hHc : ContinuousOn H C := (hH.continuousOn).mono hCO
  exact edgeSourceSlab_disk_bundle_of_model hW hW9 hh h4 hb hrange hΔ hr Θ jN O hU hf hH hval
    hrow hpair hQ hQw henc (isCompact_slab_preimage_of_subset_compact hC hCO hfc hHc hslab)
    ha₀ h0 hb₀

end DifferentialGeometry.Geometry.Collapse
