import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandVerticalChart
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing

/-!
# Consumer of E5: torus bands (BCP01 "level bands are `T² × [a, b]`")

In a boundaryless three-manifold modelled on `MorseModel 3`, a compact regular band `f⁻¹[a, b]`
carrying a field `Y` with `df(Y) > 0`, whose bottom level is crossed once by every vertical line of
a `C^k` torus chart `T² × (a₀, b₀) → M`, is diffeomorphic to `T² × [a, b]` preserving the height.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open GC.Endpoint DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse

variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel (2 + 1)) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Torus bands: the band is `T² × [a, b]`, the second coordinate being the height. -/
theorem exists_band_diffeomorph_torus_of_vertical_chart {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b) (hK : IsCompact (f ⁻¹' Icc a b))
    (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (2 + 1))) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle I M)))
    (hpos : ∀ x ∈ f ⁻¹' Icc a b, 0 < mvfderiv (I := I) f x (Y x))
    {k : ℕ} (hk : 1 ≤ k) {a₀ b₀ : ℝ} {j : Torus × ℝ → M}
    (hj : ContMDiffOn (torusModel.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a₀ b₀))
    (hjinj : InjOn j (univ ×ˢ Ioo a₀ b₀))
    (hjd : ∀ p ∈ (univ : Set Torus) ×ˢ Ioo a₀ b₀,
      Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) I j p))
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo a₀ b₀, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo a₀ b₀, f (j (x, s)) = a)
    (hlevel : ∀ z, f z = a → z ∈ j '' (univ ×ˢ Ioo a₀ b₀)) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ cs : ChartedSpace (MorseHalfSpace 2) ↥(f ⁻¹' Icc a b),
      letI := cs
      IsManifold (morseModelWithCornersHalfSpace 2) ∞ ↥(f ⁻¹' Icc a b) ∧
      ContMDiff (morseModelWithCornersHalfSpace 2) I ∞ (fun y : ↥(f ⁻¹' Icc a b) => (y : M)) ∧
      (∀ y : ↥(f ⁻¹' Icc a b), (morseModelWithCornersHalfSpace 2).IsBoundaryPoint y ↔
        f (y : M) = a ∨ f (y : M) = b) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace 2)
          (Torus × Icc a b) ↥(f ⁻¹' Icc a b) ∞,
        ∀ p, f (D p : M) = (p.2 : ℝ) :=
  exists_band_diffeomorph_of_vertical_chart (by simp) hf hab hK Y hY hpos hk hj hjinj hjd hvert
    hcross hlevel

end DifferentialGeometry.Geometry.Collapse
