import DifferentialGeometry.Geometry.Collapse.ZeroModel.SphereInvolutionApplications
import DifferentialGeometry.Geometry.Collapse.ZeroModel.FlatTorusInvolution

/-!
# Q0: the equivariant classification of the unit sphere bundle

Lane LFR54-Q0. The frozen statement Q0 of `build-logs/scratch/F7-LFR51/QuotInputs.lean`, verbatim
(`exists_antipodal_or_klein_unit_map`): for a smooth Riemannian line bundle `V` over a closed
surface `B` with a `C^n` metric of `K ≥ 0` (`n ≥ 2`), an oriented total space and a preconnected
unit sphere bundle, the unit sphere bundle with `v ↦ -v` is equivariantly `(S², -1)` or
`(T², (x, y) ↦ (x + ½, -y))`, through a smooth bijective unit map whose projection is a local
diffeomorphism.

Proof: `S(V)` with the covering atlas of `proj` (G2, `RankOneQuotient.UnitSphereCover`), oriented
by the total space with `τ = -1` orientation reversing; SF1 + SF2 on the base pulled back give a
smooth `τ`-invariant metric which is flat or of positive scalar curvature (G2,
`exists_unitSphere_metric`). Positive case: G4 (`exists_antipodal_unit_map_or_flat_unitSphere`).
Flat case: G3 (`exists_klein_diffeomorph_of_flat_involution`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.VectorBundle

open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
open DifferentialGeometry.Geometry.Collapse.ZeroModel

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **Q0 (equivariant classification of the unit sphere bundle)**, the frozen statement verbatim. -/
theorem exists_antipodal_or_klein_unit_map [CompactSpace B] [ConnectedSpace B] [T2Space B]
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (oN : DifferentialGeometry.Topology.Manifold.SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V))
    (hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1})
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ x, ‖(ν x).2‖ = 1) ∧ Function.Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
      (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) ∨
    (∃ ν : T2 → TotalSpace F V, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ p, ‖(ν p).2‖ = 1) ∧ Function.Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) ∧
      (∀ x y : AddCircle (1 : ℝ),
        ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) ∧
      IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)) := by
  have h2 : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  have h1 : Module.finrank ℝ F = 1 := by
    rw [Module.finrank_prod, h2] at hd
    omega
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) oN
  have h3 : Module.finrank ℝ (E2 × F) = 3 := hd
  let o3 : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3 :=
    Eq.rec (motive := fun m _ => ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) m) O h3
  have hcont : IsContinuousRiemannianBundle F V :=
    isContinuousRiemannianBundle_of_contMDiff (EB := E2)
  have hp := isLocalHomeomorph_unitSphere_proj h2 h1 o3
  rcases exists_antipodal_unit_map_or_flat_unitSphere hd o3 hS hp hn k hK with hsph | hflat
  · exact Or.inl hsph
  · right
    let _ := coveringChartedSpace (H := E2) hp
    let _ : IsManifold (𝓡 2) ∞ {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_isManifold hp
    let _ : CompactSpace {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_compactSpace
    let _ : ConnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} := unitSphere_connectedSpace h1 hS
    obtain ⟨g, hgτ, hflat⟩ := hflat
    let oS := unitSphereSmoothOrientation hp h2 h1 o3
    have hneg := contMDiff_unitSphereNeg (EB := E2) (F := F) (V := V) hp
    have hbij : ∀ z, Function.Bijective (mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z) := fun z => by
      rw [mfderiv_unitSphereNeg (EB := E2) hp z]
      exact Function.bijective_id
    have hrev : ∀ z, (pullbackSmoothOrientation (𝓡 2) (𝓡 2) unitSphereNeg hneg hbij oS).val z =
        -oS.val z := by
      intro z
      have he : (differentialEquivOfBijective (𝓡 2) (𝓡 2) unitSphereNeg hbij z).symm.toLinearEquiv =
          LinearEquiv.refl ℝ E2 := by
        apply LinearEquiv.ext
        intro v
        apply (differentialEquivOfBijective (𝓡 2) (𝓡 2) unitSphereNeg hbij z).injective
        change differentialEquivOfBijective (𝓡 2) (𝓡 2) unitSphereNeg hbij z
          ((differentialEquivOfBijective (𝓡 2) (𝓡 2) unitSphereNeg hbij z).symm v) =
          mfderiv (𝓡 2) (𝓡 2) unitSphereNeg z v
        rw [ContinuousLinearEquiv.apply_symm_apply, mfderiv_unitSphereNeg (EB := E2) hp z]
        rfl
      rw [pullbackSmoothOrientation_apply, he, tangentOrientationEquiv_refl,
        unitSphereSmoothOrientation_neg]
    obtain ⟨Φ, hΦ⟩ := exists_klein_diffeomorph_of_flat_involution oS g hflat unitSphereNeg hneg
      unitSphereNeg_unitSphereNeg unitSphereNeg_ne hgτ hbij hrev
    obtain ⟨hs, hu, hi, hsurj, hloc⟩ := unitMap_package_of_diffeomorph h1 hp Φ
    exact ⟨fun p => (Φ p).val, hs, hu, hi, hsurj,
      fun x y => by change (Φ _).val = _; rw [hΦ]; rfl, hloc⟩

end DifferentialGeometry.Topology.VectorBundle
