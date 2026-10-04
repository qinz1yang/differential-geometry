import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarBandProduct

/-!
# Consumers of the cusp band product (E3/E5)

* `NearlyCuspidalBoundary.exists_band_diffeomorph_torus`: the band product in the `i`-th collar
  of a nearly cuspidal boundary.
* `NearlyCuspidalBoundary.exists_band_diffeomorph_torus_boundary`: in that product the boundary
  of the band is the image of `T² × {a, b}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

/-- E3/E5 in each collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.exists_band_diffeomorph_torus {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {a b a₀ b₀ : ℝ} (hab : a < b) (ha₀ : 0 ≤ a₀)
    (hb₀ : b₀ ≤ cuspDepth)
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo a₀ b₀,
      0 < deriv (fun s : ℝ => η ((B.collar i).toFun (x, halfSpaceOneLift s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo a₀ b₀, η ((B.collar i).toFun (x, halfSpaceOneLift s)) = a)
    (hband : ∀ y, η y ∈ Icc a b →
      ∃ x : Torus, ∃ s ∈ Ioo a₀ b₀, (B.collar i).toFun (x, halfSpaceOneLift s) = y) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ cs : ChartedSpace (MorseHalfSpace 2) ↥(η ⁻¹' Icc a b),
      letI := cs
      IsManifold (morseModelWithCornersHalfSpace 2) ∞ ↥(η ⁻¹' Icc a b) ∧
      ContMDiff (morseModelWithCornersHalfSpace 2) W.model ∞
        (fun y : ↥(η ⁻¹' Icc a b) => (y : W.Carrier)) ∧
      (∀ y : ↥(η ⁻¹' Icc a b), (morseModelWithCornersHalfSpace 2).IsBoundaryPoint y ↔
        η (y : W.Carrier) = a ∨ η (y : W.Carrier) = b) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace 2)
          (Torus × Icc a b) ↥(η ⁻¹' Icc a b) ∞,
        ∀ p, η (D p : W.Carrier) = (p.2 : ℝ) :=
  (B.collar i).exists_band_diffeomorph_torus hη hab ha₀ hb₀ hvert hcross hband

/-- In the band product, a point of the band is a boundary point exactly when it is the image of
a point of `T² × {a, b}`. -/
theorem NearlyCuspidalBoundary.exists_band_diffeomorph_torus_boundary {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (i : Fin B.count) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {a b a₀ b₀ : ℝ} (hab : a < b) (ha₀ : 0 ≤ a₀)
    (hb₀ : b₀ ≤ cuspDepth)
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo a₀ b₀,
      0 < deriv (fun s : ℝ => η ((B.collar i).toFun (x, halfSpaceOneLift s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo a₀ b₀, η ((B.collar i).toFun (x, halfSpaceOneLift s)) = a)
    (hband : ∀ y, η y ∈ Icc a b →
      ∃ x : Torus, ∃ s ∈ Ioo a₀ b₀, (B.collar i).toFun (x, halfSpaceOneLift s) = y) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ cs : ChartedSpace (MorseHalfSpace 2) ↥(η ⁻¹' Icc a b),
      letI := cs
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace 2)
          (Torus × Icc a b) ↥(η ⁻¹' Icc a b) ∞,
        ∀ p, (morseModelWithCornersHalfSpace 2).IsBoundaryPoint (D p) ↔
          ((p.2 : ℝ) = a ∨ (p.2 : ℝ) = b) := by
  obtain ⟨cs, -, -, hiff, D, hD⟩ :=
    B.exists_band_diffeomorph_torus i hη hab ha₀ hb₀ hvert hcross hband
  exact ⟨cs, D, fun p => (hiff (D p)).trans (by rw [hD p])⟩

end DifferentialGeometry.Geometry.Collapse
