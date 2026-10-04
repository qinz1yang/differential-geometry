import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandVerticalChartInterior

/-!
# Level bands of a cusp collar are torus products (F-e, E3 binding, E5 cusp form)

BCP01 (blueprint 207B:8142–8143, proof 8201–8208): "the level bands have smooth product
trivializations preserving `η_i`".

`CuspEmbedding.exists_band_diffeomorph_torus`: let `η` be smooth on the carrier with positive
derivative along the verticals `s ↦ e (x, s)` of the collar on `a₀ < s < b₀ ≤ 100`; if the band
`η⁻¹[a, b]` lies in `e (T² × (a₀, b₀))` and every vertical meets the level `a`, then the band is a
compact manifold with boundary `η⁻¹{a, b}`, smoothly embedded in the carrier, and diffeomorphic
to `T² × [a, b]` by a diffeomorphism carrying the second coordinate to `η`.

The field of the flow is produced (`exists_contMDiff_field_mvfderiv_pos`), so no field is data;
the carrier is in universe `0` (the Morse library is).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

/-- **E3/E5 on a cusp carrier.** A band `η⁻¹[a, b]` inside the collar, with positive vertical
derivative and bottom level crossed by every vertical, is diffeomorphic to `T² × [a, b]`
preserving `η`. -/
theorem CuspEmbedding.exists_band_diffeomorph_torus {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    {a b a₀ b₀ : ℝ} (hab : a < b) (ha₀ : 0 ≤ a₀) (hb₀ : b₀ ≤ cuspDepth)
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo a₀ b₀,
      0 < deriv (fun s : ℝ => η (e.toFun (x, halfSpaceOneLift s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo a₀ b₀, η (e.toFun (x, halfSpaceOneLift s)) = a)
    (hband : ∀ y, η y ∈ Icc a b →
      ∃ x : Torus, ∃ s ∈ Ioo a₀ b₀, e.toFun (x, halfSpaceOneLift s) = y) :
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
        ∀ p, η (D p : W.Carrier) = (p.2 : ℝ) := by
  have hdimE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (MorseModel (2 + 1)) := by
    simp
  have hdimF : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
    simp
  exact exists_band_diffeomorph_of_interior_vertical_chart
    (ContinuousLinearEquiv.ofFinrankEq hdimE) hdimF hη hab
    (isClosed_Icc.preimage hη.continuous).isCompact (Nat.le_add_left 1 K)
    (e.contMDiffOn_vertical ha₀ hb₀) (e.injOn_vertical ha₀ hb₀)
    (fun p hp => e.injective_mfderiv_vertical ha₀ hb₀ hp)
    (fun p hp => e.isInteriorPoint_vertical ha₀ hb₀ hp) hvert hcross
    (fun y hy => by
      obtain ⟨x, s, hs, rfl⟩ := hband y hy
      exact ⟨(x, s), ⟨mem_univ _, hs⟩, rfl⟩)

end DifferentialGeometry.Geometry.Collapse
