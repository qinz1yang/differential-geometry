import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceTypeApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulSurface

/-!
# LFR22: the finite surface types

Row LFR22 (`lem:collapse-finite-complete-surface-types`, master207A:26710): a complete connected
orientable `C^m` surface, `m ≥ 4`, with nonnegative curvature is homeomorphic to one of
`S², T², ℝ², S¹ × ℝ`; in the compact case these are smooth types and the torus metric is flat.

* compact branch: F7-SURF's `finiteSurface_sphere_or_flat_torus` (LFR17, smooth types, flat torus);
* noncompact branch: S6 `nonempty_homeomorph_plane_or_cylinder_finite` (CMS-C, a HOMEOMORPHISM).

`finiteSurface_types` keeps the smooth compact types; `finiteSurface_homeomorph_types` is the row's
first sentence. The row's last sentence (a complete flat surface has Euclidean universal
Riemannian cover, finite category) is NOT delivered here (not part of the CM-S package).
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- `2 ≤ r + 1` in `ℕ∞ω` from `3 ≤ r`. -/
theorem two_le_coe_add_one_of_three_le {r : ℕ∞} (hr : 3 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast (le_trans (by norm_num) hr : (1 : ℕ∞) ≤ r)
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

/-- **LFR22 (smooth compact types).** A complete connected oriented surface modelled on `𝓡 2` with a
metric of class `C^{r+1}`, `r ≥ 3`, and nonnegative curvature is: compact and diffeomorphic to `S²`,
or compact, diffeomorphic to `T²` and flat; or noncompact and homeomorphic to `ℝ²` or to
`S¹ × ℝ`. -/
theorem finiteSurface_types (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    (CompactSpace Z ∧ (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∨
      (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0))) ∨
    (NoncompactSpace Z ∧ (Nonempty (Z ≃ₜ E2) ∨ Nonempty (Z ≃ₜ AddCircle (1 : ℝ) × ℝ))) := by
  by_cases hc : CompactSpace Z
  · exact Or.inl ⟨hc, finiteSurface_sphere_or_flat_torus o (two_le_coe_add_one_of_three_le hr) k hK⟩
  · have : NoncompactSpace Z := not_compactSpace_iff.mp hc
    exact Or.inr ⟨this, FiniteSoul.nonempty_homeomorph_plane_or_cylinder_finite k hr hnorm hK
      (by simp) o⟩

/-- **LFR22 (the row's first sentence).** A complete connected oriented `C^{r+1}` surface,
`r ≥ 3`, with nonnegative curvature is homeomorphic to one of `S², T², ℝ², S¹ × ℝ`, and in the
torus case its metric is flat. -/
theorem finiteSurface_homeomorph_types (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z ≃ₜ S2) ∨
      (Nonempty (Z ≃ₜ T2) ∧ ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) ∨
      Nonempty (Z ≃ₜ E2) ∨ Nonempty (Z ≃ₜ AddCircle (1 : ℝ) × ℝ) := by
  rcases finiteSurface_types o k hr hnorm hK with ⟨-, hS | ⟨hT, hflat⟩⟩ | ⟨-, h | h⟩
  · obtain ⟨Φ⟩ := hS
    exact Or.inl ⟨Φ.toHomeomorph⟩
  · obtain ⟨Φ⟩ := hT
    exact Or.inr (Or.inl ⟨⟨Φ.toHomeomorph⟩, hflat⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end DifferentialGeometry.Geometry.Collapse
