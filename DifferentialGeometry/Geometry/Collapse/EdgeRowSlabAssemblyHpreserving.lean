import DifferentialGeometry.Geometry.Collapse.EdgeRowSlabAssembly
import DifferentialGeometry.Geometry.Collapse.EdgeSourceSlabDiskBundleHpreserving

/-!
# LFR28 row, stage 4 at one index, with the `H`-preserving trivialization

`edgeRowSlab_disk_bundle_of_estimates_Hpreserving`: `edgeRowSlab_disk_bundle_of_estimates` (same
hypotheses, same proof) through `edgeSourceSlab_disk_bundle_of_model_Hpreserving`: the
trivialization preserves `H` near the side boundary and is the restriction of a flow translating
`f` and preserving `H` on both sides of `{H = 4Δ}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open Bundle DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
  DifferentialGeometry.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **LFR28 row, one index, `H`-preserving trivialization.** `edgeRowSlab_disk_bundle_of_estimates`
with Row-A's `H`-preserving form. -/
theorem edgeRowSlab_disk_bundle_of_estimates_Hpreserving
    {S : Type} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {z₀ : S} {h : S → ℝ} {Wh : Set S} (hW : IsOpen Wh) (hW9 : closedBall z₀ 9 ⊆ Wh)
    (hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh)
    (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0)
    {b : ClosedCell 2 → S} (hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b)
    (hrange : range b = {x | dist x z₀ < 9 ∧ h x ≤ 4}) {Δ : ℝ} (hΔ : 0 < Δ)
    (hQ : IsCompact (Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s z₀ < 9 ∧ h s ≤ 401 / 100}))
    {N : Type} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
    {r : ℕ} (hr : 3 ≤ r) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N r)
    {n n' : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (hΘV : ∀ p : ℝ × S,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) = V (Θ p))
    (GN : N → ℝ)
    (hGN : ∀ s : S, dist s z₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 → ∀ (t a : ℝ) (Y : E2),
      mvfderiv 𝓘(ℝ, E3) GN (Θ (t, s))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) (a, Y)) =
          Δ * mvfderiv (𝓡 2) h s Y)
    (hdir : ∀ s : S, dist s z₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 →
      ∃ Y : E2, κ.inner s Y Y ≤ 1 ∧ 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h s Y)
    {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (jN : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N X r) (O : TopologicalSpace.Opens X)
    (hU : ∀ x ∈ edgeModelCylinder z₀ Δ, Θ x ∈ jN.source ∧ jN (Θ x) ∈ O)
    {f H : X → ℝ} (hf : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f O)
    (hH : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H O)
    (hval : ∀ x ∈ edgeModelCylinder z₀ Δ,
      |f (jN (Θ x)) - x.1| ≤ Δ / 100 ∧ |H (jN (Θ x)) - Δ * h x.2| ≤ Δ / 100)
    (h3 : ∀ x ∈ edgeModelCylinder z₀ Δ, |x.1| ≤ 41 / 10 * Δ → h x.2 ≤ 41 / 10 →
      ∀ Z : TangentSpace 𝓘(ℝ, E3) (Θ x),
        |mvfderiv 𝓘(ℝ, E3) (fun y => f (jN y)) (Θ x) Z - G.inner (Θ x) (V (Θ x)) Z| ≤
          1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z))
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 1000)
    (h4' : ∀ x ∈ edgeModelCylinder z₀ Δ, |x.1| ≤ 41 / 10 * Δ → 39 / 10 ≤ h x.2 →
      h x.2 ≤ 41 / 10 → ∀ Z : E3,
        |mvfderiv 𝓘(ℝ, E3) (fun y => H (jN y)) (Θ x) Z - mvfderiv 𝓘(ℝ, E3) GN (Θ x) Z| ≤
          c * Real.sqrt (G.inner (Θ x) Z Z))
    (henc : ∀ y ∈ O, |f y| < 4 * Δ → H y ≤ 4 * Δ →
      ∃ x ∈ edgeModelCylinder z₀ Δ, jN (Θ x) = y)
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-(4 * Δ)) (4 * Δ) →
      IsCompact ((fun y : O => f y) ⁻¹' K ∩ {y : O | 0 ≤ 4 * Δ - H y}))
    {a₀ b₀ : ℝ} (ha₀ : -(4 * Δ) < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < 4 * Δ) :
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
        (∃ r' : ℝ, 0 < r' ∧ (∀ p, 4 * Δ - H p.1 < r' → H (Θ' p) = H p.1) ∧
          ∃ (U : Set O) (hU : IsOpen U),
          ∃ D : ℝ → (⟨U, hU⟩ : TopologicalSpace.Opens O) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯
              (⟨U, hU⟩ : TopologicalSpace.Opens O),
            ContMDiff (𝓘(ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
              (fun q : ℝ × (⟨U, hU⟩ : TopologicalSpace.Opens O) => D q.1 q.2) ∧
            D 0 = Diffeomorph.refl _ _ ∞ ∧ (∀ s t, (D s).trans (D t) = D (s + t)) ∧
            (∀ p, ∃ hp : (p.1 : O) ∈ U, Θ' p = (D (p.2 : ℝ) ⟨p.1, hp⟩ : O)) ∧
            (∀ z : (⟨U, hU⟩ : TopologicalSpace.Opens O), f (z : O) = 0 →
              -r' ≤ 4 * Δ - H (z : O) → ∀ t ∈ Ioo a₀ b₀, f (D t z : O) = t) ∧
            ∀ (z : (⟨U, hU⟩ : TopologicalSpace.Opens O)) (t : ℝ), |4 * Δ - H (z : O)| < r' →
              H (D t z : O) = H (z : O)) ∧
        ∃ O' : Set O, IsOpen O' ∧ (∀ y : O, f y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - H y → y ∈ O') ∧
          ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
            ∀ (y : O) (hy : f y ∈ Ioo a₀ b₀), 0 ≤ 4 * Δ - H y →
              ∃ hR : f (R y) = 0 ∧ 0 ≤ 4 * Δ - H (R y),
                Θ' (⟨R y, hR⟩, ⟨f y, hy⟩) = y) ∧
      ∀ y : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - H y},
        (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ H y = 4 * Δ := by
  have hrne : ((r : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show r ≠ 0 by omega)
  have hr1 : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast (show 1 ≤ r by omega)
  -- differentiability of the composites at every cylinder point
  have hfj : ∀ x : edgeModelCylinder z₀ Δ,
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f (jN y)) (Θ x) := by
    intro x
    obtain ⟨hs, hO⟩ := hU x x.2
    have hj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) jN (Θ x) :=
      ((jN.contMDiffOn _ hs).contMDiffAt (jN.open_source.mem_nhds hs)).mdifferentiableAt hrne
    have hfx : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f (jN (Θ x)) :=
      ((hf _ hO).contMDiffAt (O.isOpen.mem_nhds hO)).mdifferentiableAt (by simp)
    exact hfx.comp (Θ x) hj
  have hHj : ∀ x : edgeModelCylinder z₀ Δ,
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => H (jN y)) (Θ x) := by
    intro x
    obtain ⟨hs, hO⟩ := hU x x.2
    have hj : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) jN (Θ x) :=
      ((jN.contMDiffOn _ hs).contMDiffAt (jN.open_source.mem_nhds hs)).mdifferentiableAt hrne
    have hHx : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) H (jN (Θ x)) :=
      ((hH _ hO).contMDiffAt (O.isOpen.mem_nhds hO)).mdifferentiableAt (by simp)
    exact hHx.comp (Θ x) hj
  have hhx : ∀ x : edgeModelCylinder z₀ Δ, MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) h (x : ℝ × S).2 := by
    intro x
    have hx9 : (x : ℝ × S).2 ∈ Wh := hW9 (mem_closedBall.mpr x.2.2.le)
    exact ((hh _ hx9).contMDiffAt (hW.mem_nhds hx9)).mdifferentiableAt (by simp)
  -- the row vectors
  have hrow : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ 4 * Δ + Δ / 100 →
      (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 ≤ 4 * Δ + Δ / 100 →
      ∃ X : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) x,
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
          x X).1 = 1 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ))
          x X).1 - 1| ≤ 1 / 1000 := by
    intro x ht hhv
    have ht' : |(x : ℝ × S).1| ≤ 41 / 10 * Δ := by
      change |(x : ℝ × S).1| ≤ 4 * Δ + Δ / 100 at ht
      linarith
    have hh' : h (x : ℝ × S).2 ≤ 41 / 10 := by
      change Δ * h (x : ℝ × S).2 ≤ 4 * Δ + Δ / 100 at hhv
      by_contra hcon
      push Not at hcon
      nlinarith
    exact edgeCylinder_row_of_productChart hrne Θ jN G κ hpull V x (hΘV x) (hhx x) (hfj x)
      (hHj x) (h3 x x.2 ht' hh')
  -- the pair vectors
  have hpair : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ 4 * Δ + Δ / 100 →
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 - 4 * Δ| ≤ Δ / 100 →
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
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ))
          x X₁).1 - 1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ))
          x X₂).1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ))
          x X₁).2| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
          (fun z : edgeModelCylinder z₀ Δ => ((f (jN (Θ z)), H (jN (Θ z))) : ℝ × ℝ))
          x X₂).2 -
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
            (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × S).1, Δ * h (y : ℝ × S).2) : ℝ × ℝ))
            x X₂).2| ≤ 1 / 1000 := by
    intro x ht hhv
    have ht' : |(x : ℝ × S).1| ≤ 41 / 10 * Δ := by
      change |(x : ℝ × S).1| ≤ 4 * Δ + Δ / 100 at ht
      linarith
    change |Δ * h (x : ℝ × S).2 - 4 * Δ| ≤ Δ / 100 at hhv
    have hhv' := abs_le.mp hhv
    have hlo : 39 / 10 ≤ h (x : ℝ × S).2 := by
      by_contra hcon
      push Not at hcon
      nlinarith [hhv'.1]
    have hhi : h (x : ℝ × S).2 ≤ 41 / 10 := by
      by_contra hcon
      push Not at hcon
      nlinarith [hhv'.2]
    have hx9 : dist (x : ℝ × S).2 z₀ < 9 := x.2.2
    obtain ⟨Y, hY1, hY2⟩ := hdir _ hx9 hlo hhi
    have hGNx : ∀ (a : ℝ) (Y : E2), mvfderiv 𝓘(ℝ, E3) GN (Θ x)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (x : ℝ × S) (a, Y)) =
          Δ * mvfderiv (𝓡 2) h (x : ℝ × S).2 Y := by
      intro a Y
      exact hGN _ hx9 hlo hhi (x : ℝ × S).1 a Y
    exact edgeCylinder_vectors_of_productChart hrne Θ jN G κ hpull V x (hΘV x) (hhx x) (hfj x)
      (hHj x) (h3 x x.2 ht' (by linarith)) hc0 hc (h4' x x.2 ht' hlo hhi) hGNx hY1 hY2
  -- the compact model window
  set Qc : Set (edgeModelCylinder z₀ Δ) :=
    Subtype.val ⁻¹' (Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s z₀ < 9 ∧ h s ≤ 401 / 100})
    with hQcdef
  have hQsub : Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s z₀ < 9 ∧ h s ≤ 401 / 100} ⊆
      (edgeModelCylinder z₀ Δ : Set (ℝ × S)) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hs.1⟩
  have hQc : IsCompact Qc := by
    rw [hQcdef, Subtype.isCompact_iff]
    convert hQ using 1
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hQsub hp⟩, hp, rfl⟩
  have hQw : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).1| ≤ Δ / 100 →
      (((x : ℝ × S).1, Δ * h (x : ℝ × S).2) : ℝ × ℝ).2 ≤ 4 * Δ + Δ / 100 → x ∈ Qc := by
    intro x ht hhv
    change |(x : ℝ × S).1| ≤ Δ / 100 at ht
    change Δ * h (x : ℝ × S).2 ≤ 4 * Δ + Δ / 100 at hhv
    refine ⟨abs_le.mp ht, x.2.2, ?_⟩
    by_contra hcon
    push Not at hcon
    nlinarith
  exact edgeSourceSlab_disk_bundle_of_model_Hpreserving hW hW9 hh h4 hb hrange hΔ hr Θ jN O hU hf hH
    (fun x => hval x x.2) hrow hpair hQc hQw henc hprop ha₀ h0 hb₀


end DifferentialGeometry.Geometry.Collapse
