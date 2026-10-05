import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.UnitSphereCoverOrientation
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectionalSurface
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceType
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# A smooth invariant metric on the unit sphere bundle over a nonnegatively curved surface

Lane LFR54-Q0, group G2. Let `V → B` be a smooth Riemannian line bundle over a closed connected
surface `B` carrying a `C^n` metric `k` (`n ≥ 2`) with `K ≥ 0`. With the covering atlas of the
unit sphere bundle `S(V)` (`RankOneQuotient.UnitSphereCover`):

* `exists_unitSphere_metric`: SF1 + SF2 on the BASE give a smooth metric on `B` which is flat or of
  positive scalar curvature; its pull-back along the local diffeomorphism `proj : S(V) → B` is a
  smooth metric on `S(V)` with the same property, and the fibre involution `τ z = -z` is an
  isometry of it (both `proj` and `τ` have identity differential in the covering atlas);
* `nonempty_unitSphere_diffeomorph_sphere_or_torus` (consumer): when `S(V)` is preconnected and
  the total space is oriented, `S(V)` is diffeomorphic to the round `S²` or to `ℝ²/ℤ²` (LFR17's
  smooth classification applied to the pulled back metric and the induced orientation).
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **T5.** SF1 + SF2 on the base, pulled back to the unit sphere bundle: a smooth metric on
`S(V)` (covering atlas), invariant under the fibre involution, which is flat or has positive
scalar curvature. -/
theorem exists_unitSphere_metric [CompactSpace B] [ConnectedSpace B] [T2Space B]
    (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    letI := coveringChartedSpace (H := E2) hp
    letI : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
    ∃ g : SmoothRiemannianMetric (𝓡 2) {z : TotalSpace F V // ‖z.2‖ = 1},
      (∀ z (v w : TangentSpace (𝓡 2) z),
        g.inner (unitSphereNeg z) (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z v)
          (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z w) = g.inner z v w) ∧
      ((∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt g x v w z u = 0) ∨
        ∀ x, 0 < metricScalarAt g x) := by
  let _ := coveringChartedSpace (H := E2) hp
  let _ : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
  have hπ := isLocalDiffeomorph_unitSphere_proj (EB := E2) hp
  have hinv : ∀ (h : SmoothRiemannianMetric (𝓡 2) B) (z : {z : TotalSpace F V // ‖z.2‖ = 1})
      (v w : TangentSpace (𝓡 2) z),
      (localPullMetric h _ hπ).inner (unitSphereNeg z) (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z v)
        (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z w) = (localPullMetric h _ hπ).inner z v w := by
    intro h z v w
    rw [localPullMetric_inner, localPullMetric_inner, mfderiv_unitSphereNeg (EB := E2) hp,
      mfderiv_unitSphere_proj (EB := E2) hp, mfderiv_unitSphere_proj (EB := E2) hp]
    rfl
  rcases MetricSmoothing.exists_smooth_flat_or_scalar_pos_of_finite_metric_dim_two (I := 𝓡 2)
      (by simp) hn k hK with ⟨h, hflat⟩ | ⟨h, hpos⟩
  · refine ⟨localPullMetric h _ hπ, hinv h, Or.inl fun x v w z u => ?_⟩
    rw [metricRm04StandardAt_localPullMetric]
    exact hflat _ _ _ _ _
  · refine ⟨localPullMetric h _ hπ, hinv h, Or.inr fun x => ?_⟩
    rw [metricScalarAt_localPull]
    exact hpos _

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **G2 consumer (LFR17 on `S(V)`).** For an oriented total space and a preconnected unit sphere
bundle over a closed nonnegatively curved surface, `S(V)` with its covering atlas is diffeomorphic
to the round `S²` or to `ℝ²/ℤ²`. -/
theorem nonempty_unitSphere_diffeomorph_sphere_or_torus [CompactSpace B] [ConnectedSpace B]
    [T2Space B] (hd : finrank ℝ (E2 × F) = 2 + 1)
    (oN : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1})
    (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    letI := coveringChartedSpace (H := E2) hp
    letI : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
    Nonempty ({z : TotalSpace F V // ‖z.2‖ = 1} ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
      Nonempty ({z : TotalSpace F V // ‖z.2‖ = 1} ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  let _ := coveringChartedSpace (H := E2) hp
  let _ : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
  have h2 : finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  have h1 : finrank ℝ F = 1 := by
    rw [Module.finrank_prod, h2] at hd
    omega
  have hcont : IsContinuousRiemannianBundle F V :=
    isContinuousRiemannianBundle_of_contMDiff (EB := E2)
  let _ : CompactSpace {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_compactSpace
  let _ : ConnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_connectedSpace h1 hS
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2)
    (unitSphereSmoothOrientation hp h2 h1 oN)
  let O2 : ManifoldOrientation (𝓡 2) {z : TotalSpace F V // ‖z.2‖ = 1} 2 :=
    Eq.rec (motive := fun m _ => ManifoldOrientation (𝓡 2) {z : TotalSpace F V // ‖z.2‖ = 1} m)
      O h2
  obtain ⟨g, -, hflat | hpos⟩ := exists_unitSphere_metric hp hn k hK
  · exact Or.inr (ClosedSurface.nonempty_diffeomorph_torus_of_rm04_eq_zero O2 g hflat)
  · exact Or.inl (ClosedSurface.nonempty_diffeomorph_sphere_of_scalar_pos O2 g hpos)

end DifferentialGeometry.Geometry.Collapse.ZeroModel
