import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Straighten
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Applications
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SmoothDiffeomorph

/-!
# LFR04: `C²`-diffeomorphic compact manifolds (with or without boundary) are smoothly diffeomorphic

`nonempty_diffeomorph_of_diffeomorph_boundary` (blueprint row LFR04, A:25017): for compact
Hausdorff manifolds with boundary modelled on `𝓡∂ (n + 1)` (the boundary may be empty), a `C^k`
diffeomorphism with `2 ≤ k` gives a smooth diffeomorphism.

Proof: collar straightening (A3-c, `exists_diffeomorph_one_smooth_near_boundary`) replaces `h` by a
`C¹` diffeomorphism that is smooth near `∂A`; W3 relative to the boundary
(`nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary`, `k = 1`) smooths it in the interior.
The boundaryless-model case is W-1's `nonempty_diffeomorph_of_diffeomorph` (recorded below as an
`example`); the verbatim `C²` form is an `example` as well.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- **LFR04** (with-boundary form, `2 ≤ k`). -/
theorem nonempty_diffeomorph_of_diffeomorph_boundary {n : ℕ}
    {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
    {B : Type} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
    [IsManifold (𝓡∂ (n + 1)) ∞ B]
    {k : ℕ} (hk : 2 ≤ k) (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :
    Nonempty (A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) := by
  obtain ⟨h', O', hO', hbO', hsm⟩ := exists_diffeomorph_one_smooth_near_boundary hk h
  exact nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary le_rfl h' hO' hbO' hsm

/-- LFR04, verbatim hypotheses (a `C²` diffeomorphism). -/
example {n : ℕ}
    {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
    {B : Type} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
    [IsManifold (𝓡∂ (n + 1)) ∞ B]
    (h : A ≃ₘ^2⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :
    Nonempty (A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :=
  nonempty_diffeomorph_of_diffeomorph_boundary le_rfl h

/-- LFR04 for boundaryless models (W-1), `C²` hypothesis. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
    [T2Space A] [CompactSpace A]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
    (h : A ≃ₘ^2⟮I, J⟯ B) : Nonempty (A ≃ₘ⟮I, J⟯ B) :=
  nonempty_diffeomorph_of_diffeomorph 2 (by norm_num) h

/-- **Concrete consumer.** A compact manifold with boundary (model `𝓡∂ 1`) that is
`C²`-diffeomorphic to the unit interval is smoothly diffeomorphic to it. -/
theorem nonempty_diffeomorph_Icc_of_diffeomorph_two {A : Type} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace 1) A] [IsManifold (𝓡∂ 1) ∞ A] [T2Space A] [CompactSpace A]
    (h : A ≃ₘ^2⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) :
    Nonempty (A ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) := by
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) A :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) A)
  have : IsManifold (𝓡∂ (0 + 1)) ∞ A := inferInstanceAs (IsManifold (𝓡∂ 1) ∞ A)
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))
  have : IsManifold (𝓡∂ (0 + 1)) ∞ (Icc (0 : ℝ) 1) :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ (Icc (0 : ℝ) 1))
  exact nonempty_diffeomorph_of_diffeomorph_boundary (n := 0) le_rfl h

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
