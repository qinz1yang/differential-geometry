import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Relative
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Consumers of W3

* `exists_diffeomorph_eqOn_of_smooth_near_boundary`: a `C^k` diffeomorphism (`1 ≤ k`) of compact
  manifolds with boundary that is smooth near the boundary is replaced by a smooth diffeomorphism
  of manifolds with boundary agreeing with it near the boundary;
* `nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary`: the resulting smooth type statement
  (the boundary step of LFR04 once the collar straightening has produced such an `h`);
* `exists_smooth_diffeomorph_Icc_eqOn_near_endpoints`: the concrete case of the unit interval.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B]

/-- A `C^k` diffeomorphism (`1 ≤ k`) of compact manifolds with boundary that is smooth on an open
`O ⊇ ∂A` agrees, on a smaller open `O' ⊇ ∂A`, with a smooth diffeomorphism of manifolds with
boundary. -/
theorem exists_diffeomorph_eqOn_of_smooth_near_boundary {k : ℕ} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {O : Set A} (hO : IsOpen O)
    (hbO : (𝓡∂ (n + 1)).boundary A ⊆ O)
    (hsmooth : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ h O) :
    ∃ (O' : Set A) (Φ : A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B),
      IsOpen O' ∧ (𝓡∂ (n + 1)).boundary A ⊆ O' ∧ O' ⊆ O ∧ EqOn Φ h O' := by
  obtain ⟨O', Φ, hO', hbO', hO'O, heq, -⟩ :=
    exists_smooth_diffeomorph_seq_rel_boundary hk h hO hbO hsmooth
  exact ⟨O', Φ 0, hO', hbO', hO'O, heq 0⟩

/-- Smooth type from a `C^k` diffeomorphism (`1 ≤ k`) that is smooth near the boundary. -/
theorem nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary {k : ℕ} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {O : Set A} (hO : IsOpen O)
    (hbO : (𝓡∂ (n + 1)).boundary A ⊆ O)
    (hsmooth : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ h O) :
    Nonempty (A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) := by
  obtain ⟨-, Φ, -⟩ := exists_diffeomorph_eqOn_of_smooth_near_boundary hk h hO hbO hsmooth
  exact ⟨Φ⟩

/-- Concrete consumer: a `C^k` self-diffeomorphism (`1 ≤ k`) of the unit interval that is smooth
near the endpoints agrees near the endpoints with a smooth self-diffeomorphism. -/
theorem exists_smooth_diffeomorph_Icc_eqOn_near_endpoints {k : ℕ} (hk : 1 ≤ k)
    (h : Icc (0 : ℝ) 1 ≃ₘ^k⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) {O : Set (Icc (0 : ℝ) 1)}
    (hO : IsOpen O) (hbO : (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) ⊆ O)
    (hsmooth : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ h O) :
    ∃ (O' : Set (Icc (0 : ℝ) 1)) (Φ : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1),
      IsOpen O' ∧ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) ⊆ O' ∧ O' ⊆ O ∧ EqOn Φ h O' := by
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))
  have : IsManifold (𝓡∂ (0 + 1)) ∞ (Icc (0 : ℝ) 1) :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ (Icc (0 : ℝ) 1))
  exact exists_diffeomorph_eqOn_of_smooth_near_boundary (n := 0) hk h hO hbO hsmooth

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
