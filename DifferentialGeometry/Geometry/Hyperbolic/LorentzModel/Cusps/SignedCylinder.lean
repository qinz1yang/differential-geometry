import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Ends
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.QuotientCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.RayCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoreOpening
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open MobiusBoundary (ptInfty)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal ofCoords)
open HorosphereProjection (quotientHorosphereCoordinates)
open BusemannCocycle (poConfFactor)

variable {m : ℕ} {Γ : Subgroup (PO (m + 1) 1)} {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r)
  (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))

theorem horoballCylinderMap_quotientHorosphereCoordinates
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ.val = ptInfty)
    (x : Horizontal m) (t : Set.Ici (0 : ℝ)) :
    D.horoballCylinderMap hΓ ξ (quotientHorosphereCoordinates P ξ.val (D.level ξ) a ha x, t) =
      πΓ ((poMulAction (Nat.le_add_left 1 m)).smul a⁻¹
        (ofCoords x
          (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ.val) - D.level ξ + t.val))
          (Real.exp_pos _))) := by
  change πΓ (AsymptoticRays.rayTo ((poMulAction (Nat.le_add_left 1 m)).smul a⁻¹
    (ofCoords x (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ.val) - D.level ξ))
      (Real.exp_pos _))) ξ.val t.val) = _
  rw [Horospherical.rayTo_inv_smul_ofCoords_exp ξ.val a ha x]

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (2 + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (2 + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r) (ξ : D.centers)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (2 + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (2 + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (2 + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1)))
local notation "K" => 𝓘(ℝ, Fin 2 → ℝ)
local notation "T" => ModelWithCorners.prod (𝓡 1) (𝓡 1)
local notation "J" => ModelWithCorners.prod T 𝓘(ℝ, ℝ)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (2 + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) Γ hΓ

private local instance : IsCancelSMul P (HUpper (2 + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show P ≤ Γ from inf_le_left)

private local instance : ChartedSpace (Fin 2 → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

theorem exists_partialDiffeomorph_horoballCylinderMap_at_depth
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    {L : ModelWithCorners ℝ E H} (e : QΓ ≃ₜ N)
    (he : IsLocalDiffeomorph I L ∞ (e ∘ πΓ))
    (F : Diffeomorph T K (Circle × Circle) S ∞) (R : ℝ) (hR : 0 < R) :
    ∃ Φ : PartialDiffeomorph J L ((Circle × Circle) × ℝ) N ∞,
      Φ.source = {z | 0 < R + z.2} ∧
      Φ.target = (e ∘ πΓ) '' {p | Busemann.busemann ξ.val p < D.level ξ} ∧
      (∀ q, (q, 0) ∈ Φ.source) ∧
      (∀ (z : (Circle × Circle) × ℝ) (hz : 0 < R + z.2),
        Φ z = e (D.horoballCylinderMap hΓ ξ (F z.1, ⟨R + z.2, hz.le⟩))) ∧
      ∀ c t (ht : 0 < t),
        Φ.symm (e (D.horoballCylinderMap hΓ ξ (c, ⟨t, ht.le⟩))) =
          (F.symm c, t - R) := by
  obtain ⟨A, hAs, hAf, _⟩ := D.exists_partialDiffeomorph_horoballCylinderMap ξ
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := Γ) (M := HUpper (2 + 1)) (n := ∞) I
  have he' : IsLocalDiffeomorph I L ∞ e := by
    intro q
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (he p) (hπ p)
  let E' := he'.diffeomorphOfBijective e.bijective
  let shift : Diffeomorph J (ModelWithCorners.prod K 𝓘(ℝ, ℝ)) ((Circle × Circle) × ℝ) (S × ℝ) ∞ :=
    { toFun := fun z => (F z.1, R + z.2)
      invFun := fun z => (F.symm z.1, z.2 - R)
      left_inv := fun z => Prod.ext (F.symm_apply_apply z.1) (by ring)
      right_inv := fun z => Prod.ext (F.apply_symm_apply z.1) (by ring)
      contMDiff_toFun := (F.contMDiff.comp contMDiff_fst).prodMk
        (contMDiff_const.add contMDiff_snd)
      contMDiff_invFun := (F.symm.contMDiff.comp contMDiff_fst).prodMk
        (contMDiff_snd.sub contMDiff_const) }
  let B := (shift.toPartialDiffeomorph.trans A).trans E'.toPartialDiffeomorph
  let U : Set ((Circle × Circle) × ℝ) := {z | 0 < R + z.2}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.add continuous_snd)
  let Φ := Topology.PartialDiffeomorph.restrict B U hU
  have hBs : U ⊆ B.source := by
    intro z hz
    exact ⟨⟨mem_univ _, hAs (F z.1) (R + z.2) hz.le⟩, mem_univ _⟩
  have hΦs : Φ.source = U := by
    change B.source ∩ U = U
    exact inter_eq_right.mpr hBs
  have hΦf (z : (Circle × Circle) × ℝ) (hz : 0 < R + z.2) :
      Φ z = e (D.horoballCylinderMap hΓ ξ (F z.1, ⟨R + z.2, hz.le⟩)) := by
    change e (A (F z.1, R + z.2)) = _
    rw [← hAf (F z.1, ⟨R + z.2, hz.le⟩)]
  have hΦi (c : S) (t : ℝ) (ht : 0 < t) :
      Φ.symm (e (D.horoballCylinderMap hΓ ξ (c, ⟨t, ht.le⟩))) =
        (F.symm c, t - R) := by
    have heq : R + (t - R) = t := by ring
    have hz : 0 < R + (t - R) := by rwa [heq]
    have hs : (F.symm c, t - R) ∈ Φ.source := by rw [hΦs]; exact hz
    have hf := hΦf (F.symm c, t - R) hz
    simp only [F.apply_symm_apply, heq] at hf
    rw [← hf]
    exact Φ.left_inv hs
  refine ⟨Φ, hΦs, ?_, ?_, hΦf, hΦi⟩
  · have hΦt : Φ '' Φ.source = Φ.target :=
      Φ.toOpenPartialHomeomorph.image_source_eq_target
    rw [← hΦt, hΦs]
    have himage : Φ '' U = e ''
        ((D.horoballCylinderMap hΓ ξ) '' {z | 0 < z.2.val}) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        change 0 < R + z.2 at hz
        exact ⟨D.horoballCylinderMap hΓ ξ (F z.1, ⟨R + z.2, hz.le⟩),
          ⟨(F z.1, ⟨R + z.2, hz.le⟩), hz, rfl⟩, (hΦf z hz).symm⟩
      · rintro _ ⟨_, ⟨⟨c, t⟩, ht, rfl⟩, rfl⟩
        have heq : R + (t.val - R) = t.val := by ring
        have hz : 0 < R + (t.val - R) := by rwa [heq]
        refine ⟨(F.symm c, t.val - R), hz, ?_⟩
        simpa only [F.apply_symm_apply, heq] using hΦf (F.symm c, t.val - R) hz
    change Φ '' U = _
    rw [himage, D.horoballCylinderMap_image_pos hΓ ξ, image_image]
    rfl
  · intro q
    rw [hΦs]
    change 0 < R + 0
    simpa only [add_zero] using hR

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
