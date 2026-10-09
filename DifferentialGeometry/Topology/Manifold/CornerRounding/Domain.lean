/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding.Regular
import DifferentialGeometry.Topology.Manifold.RegularSuperlevel

/-!
# Both rounded sides are smooth manifolds with boundary

For globally defined `φ ψ` on a boundaryless manifold, the rounded piece `{F ≥ 0}` and the rounded
complementary side `{F ≤ 0}`, `F = roundedMin ε (φ, ψ)`, carry half-space atlases for which the
inclusion is smooth with bijective differential, and whose boundary points are exactly the common
level `{F = 0}`.  Supplier: `exists_isManifold_superlevel` / `Morse.exists_isManifold_sublevel`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.CornerRounding

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The rounded piece `{roundedMin ε (φ, ψ) ≥ 0}` is a smooth manifold with boundary
`{roundedMin ε (φ, ψ) = 0}`. -/
theorem exists_isManifold_roundedPiece
    {φ ψ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) {δ : ℝ}
    (hφreg : ∀ x, φ x = 0 → 0 ≤ ψ x → mfderiv I 𝓘(ℝ, ℝ) φ x ≠ 0)
    (hψreg : ∀ x, ψ x = 0 → 0 ≤ φ x → mfderiv I 𝓘(ℝ, ℝ) ψ x ≠ 0)
    (hband : ∀ x, 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < δ → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hεδ : 3 * ε ≤ δ) :
    ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1))
          {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)},
        letI := cs
        IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
          {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)} ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
          (fun x : {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)} => x.1) ∧
        (∀ x : {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)}, Function.Bijective
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun y : {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)} => y.1) x)) ∧
        (∀ x : {x : M // 0 ≤ roundedMin ε (φ x) (ψ x)},
          (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔
            roundedMin ε (φ x.1) (ψ x.1) = 0) := by
  obtain ⟨hF, hreg, -⟩ := roundedMin_corner_rounding hφ hψ hφreg hψreg hband hε hεδ
  exact exists_isManifold_superlevel (fun x => roundedMin ε (φ x) (ψ x)) 0 hF
    (fun x hx => hreg x hx)

/-- The rounded complementary side `{roundedMin ε (φ, ψ) ≤ 0}` is a smooth manifold with the SAME
boundary `{roundedMin ε (φ, ψ) = 0}`. -/
theorem exists_isManifold_roundedComplement
    {φ ψ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) {δ : ℝ}
    (hφreg : ∀ x, φ x = 0 → 0 ≤ ψ x → mfderiv I 𝓘(ℝ, ℝ) φ x ≠ 0)
    (hψreg : ∀ x, ψ x = 0 → 0 ≤ φ x → mfderiv I 𝓘(ℝ, ℝ) ψ x ≠ 0)
    (hband : ∀ x, 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < δ → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv I 𝓘(ℝ, ℝ) (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hεδ : 3 * ε ≤ δ) :
    ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1))
          (Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0),
        letI := cs
        IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
          (Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0) ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
          (fun x : Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0 => x.1) ∧
        (∀ x : Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0, Function.Bijective
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun y : Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0 => y.1) x)) ∧
        (∀ x : Morse.SublevelSpace (fun x => roundedMin ε (φ x) (ψ x)) 0,
          (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔
            roundedMin ε (φ x.1) (ψ x.1) = 0) := by
  obtain ⟨hF, hreg, -⟩ := roundedMin_corner_rounding hφ hψ hφreg hψreg hband hε hεδ
  exact Morse.exists_isManifold_sublevel (fun x => roundedMin ε (φ x) (ψ x)) 0 hF
    (fun x hx hc => hreg x hx hc)

end DifferentialGeometry.Topology.Manifold.CornerRounding
