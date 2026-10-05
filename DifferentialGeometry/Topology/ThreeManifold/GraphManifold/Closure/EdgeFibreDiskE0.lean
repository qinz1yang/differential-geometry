import DifferentialGeometry.Topology.Ehresmann.WholeDiskTransport
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

/-!
# Consumer of E0: the `fibre_disk` clause of the rows' `EdgeBundle` from a compact transverse trace

Draft 74, D74-11: `EdgeBundle.fibre_disk` (`FC39P0Base.lean`) asks, for EVERY base point `c`, for a
smooth embedding `φ : ClosedCell 2 → W.Carrier` whose range is the WHOLE fibre `{x ∈ source | proj x
= c, height x ≤ level}`, "given by EDP04's whole-trace isotopy to the original smooth disk (output:
smooth embedding)". `fibreDisk_of_wholeDisk_trace_EFC` produces exactly this clause (and the rim
clause: the boundary circle onto `{proj x = c, height x = level}`) from E0's inputs at `c` on an
open source `O` (EDP04's `Y_i`) together with the FINAL-time fibre identification `{y ∈ O | h(y,1) =
a, T(y,1) ≤ level} = {x ∈ source | proj x = c, height x ≤ level}` (EDP04's "At the final time the
fiber is precisely `f₂⁻¹(w) ∩ X₂`", which needs GAF05 / BASES and is an input here).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology GC.Endpoint

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

universe u

/-- **E0 ⇒ the rows' `fibre_disk` and rim clauses at one base point** (D74-11). On a compact carrier
with boundaryless model, E0's inputs on an open source `O` (family `(h, T)` smooth on `O × ℝ`,
transverse on the whole trace and of rank two on its rim, trace in a compact `Q ⊆ O`, original
smooth disk `φ₀` filling the time-0 fibre with boundary onto the time-0 rim) and the identification
of the time-1 fibre and rim with the whole fibre and rim of `proj` over `c` below `level` give a
smooth embedding of `ClosedCell 2` onto that whole fibre, with boundary circle onto the rim. -/
theorem fibreDisk_of_wholeDisk_trace_EFC (W : CompactCarrier.{u}) [W.model.Boundaryless]
    {B : Type*} (source : TopologicalSpace.Opens W.Carrier) (proj : source → B)
    (height : source → ℝ) (level : ℝ) (c : B) (O : TopologicalSpace.Opens W.Carrier)
    (h T : W.Carrier × ℝ → ℝ)
    (hh : ContMDiffOn (W.model.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h ((O : Set W.Carrier) ×ˢ univ))
    (hT : ContMDiffOn (W.model.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T ((O : Set W.Carrier) ×ˢ univ)) (a : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) ≤ level →
      Surjective (mfderiv W.model 𝓘(ℝ) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) = level →
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set W.Carrier} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) ≤ level → y ∈ Q)
    {φ₀ : ClosedCell 2 → W.Carrier} (hφ₀ : IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ₀)
    (hφ₀r : range φ₀ = {y | y ∈ O ∧ h (y, 0) = a ∧ T (y, 0) ≤ level})
    (hφ₀b : range (φ₀ ∘ cellBoundaryInclusion 2) =
      {y | y ∈ O ∧ h (y, 0) = a ∧ T (y, 0) = level})
    (hfin : {y | y ∈ O ∧ h (y, 1) = a ∧ T (y, 1) ≤ level} =
      Subtype.val '' {x : source | proj x = c ∧ height x ≤ level})
    (hrim : {y | y ∈ O ∧ h (y, 1) = a ∧ T (y, 1) = level} =
      Subtype.val '' {x : source | proj x = c ∧ height x = level}) :
    ∃ φ : ClosedCell 2 → W.Carrier, IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
      range φ = Subtype.val '' {x : source | proj x = c ∧ height x ≤ level} ∧
      range (φ ∘ cellBoundaryInclusion 2) =
        Subtype.val '' {x : source | proj x = c ∧ height x = level} := by
  obtain ⟨φ, hφ, hr, hb, -⟩ := wholeDisk_of_compact_transverse_trace_opens_EFC O h T hh hT a level
    hreg hface hQ hQO hloc hφ₀ hφ₀r hφ₀b
  exact ⟨φ, hφ, hr.trans hfin, hb.trans hrim⟩

end DifferentialGeometry.Topology.Ehresmann
