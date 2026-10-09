import DifferentialGeometry.Geometry.Collapse.EdgeCylinderSourceChart

/-!
# LFR28: the actual source slab is a trivial bundle with closed-disk fibre (single index)

Blueprint 207A, LFR28 (A:27223), proof step 4, at ONE index of the sequence: the assembly of B3
(`exists_edgeCylinder_source_partialDiffeomorph`: the model cylinder mapped into the source by
`j ∘ Θ`, the source re-charted along `E3 ≃ ℝ × E2`) and the I6 disk bundle
(`edgeModelCylinder_disk_bundle`). The hypotheses are the per-index estimates the sequence form
produces on its tail: the values (I5, Codex X100), the vector conditions (B4, from (28.3)/(28.4)), the
compact model window (LFR24's enclosure), the enclosure of the whole source slab in the image (B5) and
its properness (B5).

`edgeSourceSlab_disk_bundle_of_model`: the source fibre `{f = 0, H ≤ 4Δ}` in the open set `O` of the
source (with the re-charted structure, a regular sublevel) is diffeomorphic to `ClosedCell 2`, compact
and connected; `f` is trivial over `(a₀, b₀)` with that fibre; its boundary is exactly `H = 4Δ`.
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

/-- **LFR28.1 on the actual source slab (one index).** -/
theorem edgeSourceSlab_disk_bundle_of_model
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
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-β) β →
      IsCompact ((fun y : O => f y) ⁻¹' K ∩ {y : O | 0 ≤ 4 * Δ - H y}))
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
  let _ := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
  have _ : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hUne : Nonempty (edgeModelCylinder z₀ Δ) :=
    ⟨⟨((0 : ℝ), z₀), ⟨⟨by linarith, by linarith⟩, by rw [dist_self]; norm_num⟩⟩⟩
  obtain ⟨J, hJs, hJ, hJt⟩ :=
    exists_edgeCylinder_source_partialDiffeomorph Θ jN (edgeModelCylinder z₀ Δ) hUne O hU
  let u : O → ℝ × ℝ := fun y => (f y, H y)
  have huE : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) ∞ u := by
    intro y
    have h1 : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f y := (hf _ y.2).contMDiffAt (O.isOpen.mem_nhds y.2)
    have h2 : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H y := (hH _ y.2).contMDiffAt (O.isOpen.mem_nhds y.2)
    exact (contMDiffAt_subtype_iff.mpr h1).prodMk_space (contMDiffAt_subtype_iff.mpr h2)
  have hu : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ) ∞ u :=
    (contMDiff_chartedSpaceTransHomeomorph_source_iff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2))
      euclideanThreeProdHomeomorph euclideanThreeProdEquiv euclideanThreeProd_compat
      𝓘(ℝ, ℝ × ℝ) (N := O)).mpr huE
  have huJ : ∀ z : edgeModelCylinder z₀ Δ, u (J z) = ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ) := by
    intro z
    simp only [u, hJ z]
  have hw : (fun z => u (J z)) =
      fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ) := funext huJ
  have hval' : ∀ x : edgeModelCylinder z₀ Δ,
      |(u (J x)).1 - (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ δ ∧
      |(u (J x)).2 - (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2| ≤ δ := by
    intro x
    rw [huJ]
    exact hval x
  have hrow' := hrow
  have hpair' := hpair
  rw [← hw] at hrow' hpair'
  have henc' : ∀ y, |(u y).1| < β → (u y).2 ≤ 4 * Δ → y ∈ J.target := by
    intro y h1 h2
    obtain ⟨x, hx, hxy⟩ := henc y y.2 h1 h2
    exact (hJt y).mpr ⟨⟨x, hx⟩, hxy⟩
  have hreg : ∀ y : O, f y = 0 → 0 ≤ 4 * Δ - H y →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f y) y) :=
    fun y hy hB => edgeInterp_source_regular (by omega) J hJs hu hval' hrow' henc' y
      (by
        change f y = 0 at hy
        rw [show (u y).1 = f y from rfl, hy]
        exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB
  have hregb : ∀ y : O, f y = 0 → 4 * Δ - H y = 0 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : O => ((f y, 4 * Δ - H y) : ℝ × ℝ)) y) :=
    fun y hy hB => edgeInterp_source_regular_boundary (by omega) J hJs hu hval' hpair' henc' y
      (by
        rw [show (u y).1 = f y from rfl, hy]
        exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f y) :=
    contDiff_fst.contMDiff.comp hu
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => 4 * Δ - H y) :=
    (contDiff_const.sub contDiff_snd).contMDiff.comp hu
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo
    (edgeModelCylinder_contMDiff_time (𝓡 2) z₀ Δ h)
    (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
    (edgeModelCylinder_regular (𝓡 2) z₀ Δ (4 * Δ) h)
    (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
  obtain ⟨⟨φ⟩, hc, hconn, hΘ', hbd⟩ := edgeModelCylinder_disk_bundle finrank_real_prod_euclideanTwo
    hW hW9 hh h4 hb hrange hΔ hr J hJs hu hval' hrow' hpair' hQ hQw henc' hprop ha₀ h0 hb₀
  exact ⟨hΨ, hB, hreg, hregb, ⟨φ⟩, hc, hconn, hΘ', hbd⟩

end DifferentialGeometry.Geometry.Collapse
