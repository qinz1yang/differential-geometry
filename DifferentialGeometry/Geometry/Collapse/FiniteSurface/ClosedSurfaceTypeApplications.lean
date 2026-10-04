import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceType
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.SurfaceFlatOrPositiveApplications
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ClosedOriented

/-!
# Consumers of LFR17

* LFR17 for a `ConnectedClosedOrientedManifold 2` (`closedOrientedSurface_sphere_or_flat_torus`).
* LFR22, compact clauses (`finiteSurface_compact_types`): a compact connected oriented `C^n`
  surface (`2 ≤ n`, so in particular `m ≥ 4`) with `K ≥ 0` is homeomorphic to `S²` or `T²`, these
  are smooth types (LFR17), and the torus metric is flat. LFR22's noncompact clause (LFR21's
  plane/cylinder statement S6) and its finite-category flat-cover clause are not covered here.
* The smooth case through the finite route (`smoothSurface_sphere_or_flat_torus`).
* On the round two-sphere, regarded as a `C²` metric: its finite-order curvature is positive
  (`roundTwoSphere_sectionalCurvature_pos`), LFR17 returns the sphere branch
  (`roundTwoSphere_finiteSurface_sphere`), and the torus clause shows that `ℝ²/ℤ²` is not
  diffeomorphic to `S²` (`not_nonempty_diffeomorph_torus_sphere`), so the two branches of LFR17
  exclude each other (`finiteSurface_not_sphere_and_torus`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- **LFR17 for a closed oriented surface.** -/
theorem closedOrientedSurface_sphere_or_flat_torus (Z : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 2)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : Z.Carrier → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z.Carrier ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∨
      (Nonempty (Z.Carrier ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) :=
  finiteSurface_sphere_or_flat_torus Z.orientation hn k hK

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]

/-- **LFR22, compact clauses.** A compact connected oriented `C^n` surface (`2 ≤ n`) with
nonnegative curvature is homeomorphic to `S²` or to `T²`, through smooth identifications, and in
the torus case its metric is flat. -/
theorem finiteSurface_compact_types (o : ManifoldOrientation (𝓡 2) Z 2) {n : ℕ∞ω}
    (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z ≃ₜ S2) ∨
      (Nonempty (Z ≃ₜ T2) ∧ ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) := by
  rcases finiteSurface_sphere_or_flat_torus o hn k hK with hS | ⟨hT, hflat⟩
  · obtain ⟨Φ⟩ := hS
    exact Or.inl ⟨Φ.toHomeomorph⟩
  · obtain ⟨Φ⟩ := hT
    exact Or.inr ⟨⟨Φ.toHomeomorph⟩, hflat⟩

/-- **Smooth case through the finite route.** -/
theorem smoothSurface_sphere_or_flat_torus (o : ManifoldOrientation (𝓡 2) Z 2)
    (g : SmoothRiemannianMetric (𝓡 2) Z) (hg : SectionalBoundedBelow g 0) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∨
      (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), g.sectionalCurvature x v w = 0) :=
  finiteSurface_sphere_or_flat_torus o (by simp) g
    (MetricSmoothing.sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hg)

/-- The round two-sphere, regarded as a `C²` metric, has positive finite-order curvature on every
linearly independent pair. -/
theorem roundTwoSphere_sectionalCurvature_pos (x : S2) {v w : TangentSpace (𝓡 2) x}
    (hvw : LinearIndependent ℝ ![v, w]) :
    0 < (MetricSmoothing.SmoothRiemannianMetric.toMetric2 roundTwoSphereShrinkerMetric).sectionalCurvature x v w := by
  rw [MetricSmoothing.sectionalCurvature_toMetric2,
    Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth, sectionalCurvature_def,
    sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    metricRm04StandardAt_sectional_eq_of_finrank_eq_two roundTwoSphereShrinkerMetric
      finrank_euclideanSpace_fin x v w,
    roundTwoSphereShrinkerMetric_scalarCurvature x]
  have hden := sectionalCurvatureDenominator_pos_of_linearIndependent
    roundTwoSphereShrinkerMetric x v w hvw
  exact div_pos (mul_pos (by norm_num) hden) hden

/-- **Consumer on an actual surface.** LFR17 run on the round two-sphere with its `C²` metric lands
in the sphere branch. -/
theorem roundTwoSphere_finiteSurface_sphere : Nonempty (S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) := by
  have := connectedSpace_sphere_euclideanSpace_three
  have : Nonempty S2 := ConnectedSpace.toNonempty
  let x : S2 := Classical.arbitrary _
  obtain ⟨v, w, hvw⟩ :=
    exists_linearIndependent_pair_of_finrank_eq_two (I := 𝓡 2) finrank_euclideanSpace_fin x
  exact finiteSurface_sphere_of_sectionalCurvature_pos (sphereOrientation 2 (by norm_num))
    le_rfl (MetricSmoothing.SmoothRiemannianMetric.toMetric2 roundTwoSphereShrinkerMetric)
    (fun y a b => (MetricSmoothing.sectionalCurvature_toMetric2 roundTwoSphereShrinkerMetric y a b).symm ▸
      MetricSmoothing.sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero
        roundTwoSphereShrinkerMetric roundTwoSphereShrinkerMetric_sectionalBoundedBelow_zero y a b)
    (roundTwoSphere_sectionalCurvature_pos x hvw)

/-- **The torus clause on the round sphere.** `ℝ²/ℤ²` is not diffeomorphic to `S²`: the torus
clause would make the round metric flat. -/
theorem not_nonempty_diffeomorph_torus_sphere :
    ¬ Nonempty (T2 ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓡 2⟯ S2) := by
  rintro ⟨Φ⟩
  have := connectedSpace_sphere_euclideanSpace_three
  have : Nonempty S2 := ConnectedSpace.toNonempty
  let x : S2 := Classical.arbitrary _
  obtain ⟨v, w, hvw⟩ :=
    exists_linearIndependent_pair_of_finrank_eq_two (I := 𝓡 2) finrank_euclideanSpace_fin x
  have hflat :=
    Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod
      finrank_euclideanSpace_fin (MetricSmoothing.SmoothRiemannianMetric.toMetric2 roundTwoSphereShrinkerMetric)
      le_rfl Φ
      (fun y a b => (MetricSmoothing.sectionalCurvature_toMetric2 roundTwoSphereShrinkerMetric y a b).symm ▸
        MetricSmoothing.sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero
          roundTwoSphereShrinkerMetric roundTwoSphereShrinkerMetric_sectionalBoundedBelow_zero y a b)
  exact (roundTwoSphere_sectionalCurvature_pos x hvw).ne' (hflat x v w)

omit [IsManifold (𝓡 2) ∞ Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] in
/-- **The two branches of LFR17 exclude each other.** -/
theorem finiteSurface_not_sphere_and_torus :
    ¬ (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) ∧
      Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ T2)) := by
  rintro ⟨⟨Φ⟩, ⟨Ψ⟩⟩
  exact not_nonempty_diffeomorph_torus_sphere ⟨Ψ.symm.trans Φ⟩

end DifferentialGeometry.Geometry.Collapse
