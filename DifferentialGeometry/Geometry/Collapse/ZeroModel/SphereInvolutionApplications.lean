import DifferentialGeometry.Geometry.Collapse.ZeroModel.SphereInvolution
import DifferentialGeometry.Geometry.Collapse.ZeroModel.UnitSphereMetric

/-!
# The sphere case of Q0 on the actual unit sphere bundle

Lane LFR54-Q0, group G4 consumer. For a rank-one bundle over a closed nonnegatively curved surface
with an oriented total space and a preconnected unit sphere bundle:

* `unitMap_package_of_diffeomorph`: a diffeomorphism `Φ` from a manifold onto `S(V)` (covering
  atlas) gives a smooth injective unit map `x ↦ Φ x` onto the unit sphere bundle whose projection
  is a local diffeomorphism (the shape of the unit maps of Q0);
* `exists_antipodal_unit_map_or_flat_unitSphere`: either the antipodal unit map of Q0 exists
  (positive branch, through `exists_antipodal_diffeomorph_of_scalar_pos_involution`), or `S(V)`
  carries a smooth flat metric for which the fibre involution is an isometry (the torus case).
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- A diffeomorphism onto the unit sphere bundle (covering atlas) is a smooth injective unit map
onto `S(V)` whose projection is a local diffeomorphism. -/
theorem unitMap_package_of_diffeomorph {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] (h1 : finrank ℝ F = 1)
    (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))
    (Φ : letI := coveringChartedSpace (H := E2) hp
      M ≃ₘ⟮IM, 𝓡 2⟯ {z : TotalSpace F V // ‖z.2‖ = 1}) :
    ContMDiff IM ((𝓡 2).prod 𝓘(ℝ, F)) ∞ (fun x => (Φ x).val) ∧
      (∀ x, ‖(Φ x).val.2‖ = 1) ∧ Function.Injective (fun x => (Φ x).val) ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, (Φ x).val = z) ∧
      IsLocalDiffeomorph IM (𝓡 2) ∞ (fun x => (Φ x).val.proj) := by
  let _ := coveringChartedSpace (H := E2) hp
  let _ : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
  refine ⟨(contMDiff_unitSphere_val (EB := E2) hp h1).comp Φ.contMDiff, fun x => (Φ x).property,
    Subtype.val_injective.comp Φ.injective, fun z hz => ⟨Φ.symm ⟨z, hz⟩, by simp⟩,
    fun x => IsLocalDiffeomorphAt.comp (P := B) (𝓡 2) (Φ.isLocalDiffeomorph x)
      (isLocalDiffeomorph_unitSphere_proj (EB := E2) hp (Φ x))⟩

variable [FiniteDimensional ℝ F]

/-- **G4 consumer.** The sphere case of Q0 on the actual bundle: the antipodal unit map exists, or
the unit sphere bundle (covering atlas) carries a smooth flat metric with the fibre involution an
isometry. -/
theorem exists_antipodal_unit_map_or_flat_unitSphere [CompactSpace B] [ConnectedSpace B]
    [T2Space B] (hd : finrank ℝ (E2 × F) = 2 + 1)
    (oN : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1})
    (hp : IsLocalHomeomorph (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj))
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ x, ‖(ν x).2‖ = 1) ∧ Function.Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
      (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) ∨
    (letI := coveringChartedSpace (H := E2) hp
     letI : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
     ∃ g : SmoothRiemannianMetric (𝓡 2) {z : TotalSpace F V // ‖z.2‖ = 1},
      (∀ z (v w : TangentSpace (𝓡 2) z),
        g.inner (unitSphereNeg z) (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z v)
          (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z w) = g.inner z v w) ∧
      ∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt g x v w z u = 0) := by
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
  obtain ⟨g, hgτ, hflat | hpos⟩ := exists_unitSphere_metric hp hn k hK
  · exact Or.inr ⟨g, hgτ, hflat⟩
  · left
    obtain ⟨Φ, hΦ⟩ := exists_antipodal_diffeomorph_of_scalar_pos_involution
      (unitSphereSmoothOrientation hp h2 h1 oN) g hpos unitSphereNeg
      (contMDiff_unitSphereNeg (EB := E2) hp) unitSphereNeg_unitSphereNeg unitSphereNeg_ne hgτ
    obtain ⟨hs, hu, hi, hsurj, hloc⟩ := unitMap_package_of_diffeomorph h1 hp Φ
    exact ⟨fun x => (Φ x).val, hs, hu, hi, hsurj,
      fun x => by change (Φ (-x)).val = _; rw [hΦ]; rfl, hloc⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
