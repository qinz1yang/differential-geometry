import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Ends
import DifferentialGeometry.Topology.Ends.CylindricalCore

noncomputable section

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere horoball)
open MeasureTheory (HasFundamentalDomain covolume)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))

local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

theorem range_horoballCylinderMap (ξ : D.centers) :
    Set.range (D.horoballCylinderMap hΓ ξ) = πΓ '' horoball ξ.val (D.level ξ) := by
  change Set.range (D.horoballQuotientInclusion ξ ∘
    (D.horoballQuotientHomeomorph hΓ ξ).symm) = _
  rw [(D.horoballQuotientHomeomorph hΓ ξ).symm.surjective.range_comp]
  ext q
  constructor
  · rintro ⟨⟨p, s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨_, ⟨p, hp, rfl⟩⟩, rfl⟩

theorem isOpen_image_horoballCylinderMap_pos (ξ : D.centers) :
    IsOpen ((D.horoballCylinderMap hΓ ξ) '' {p | 0 < p.2.val}) := by
  rw [D.horoballCylinderMap_image_pos hΓ ξ]
  let := EquivariantMap.subAction hn Γ
  let : ContinuousConstSMul Γ (HUpper n) :=
    ⟨fun γ ↦ (ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id)⟩
  apply (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := HUpper n)).isOpenMap
  exact isOpen_lt (HorosphereProjection.continuous_busemann ξ.val) continuous_const

theorem pairwise_disjoint_range_horoballCylinderMap :
    Pairwise fun ξ η : D.centers ↦
      Disjoint (Set.range (D.horoballCylinderMap hΓ ξ))
        (Set.range (D.horoballCylinderMap hΓ η)) := by
  intro ξ η hξη
  rw [D.range_horoballCylinderMap hΓ ξ, D.range_horoballCylinderMap hΓ η]
  exact D.pairwise_disjoint_image_horoball hΓ hξη

theorem exists_retraction_cylindricalCore (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    ∃ f : C(QΓ, QΓ),
      (∀ ξ p, f (D.horoballCylinderMap hΓ ξ p) =
        D.horoballCylinderMap hΓ ξ
          (p.1, ⟨min p.2.val (R ξ), le_min p.2.property (hR ξ)⟩)) ∧
      Set.EqOn f id (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) ∧
      Set.range f = Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R := by
  let : Finite D.centers := D.finite_centers
  exact Topology.exists_retraction_cylindricalCore
    (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

theorem isConnected_cylindricalCore (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    IsConnected (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) := by
  let : PathConnectedSpace (HUpper n) := HyperbolicGeodesic.pathConnectedSpace hn
  let : Finite D.centers := D.finite_centers
  exact Topology.isConnected_cylindricalCore
    (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

theorem cylindricalCore_zero :
    Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (fun _ ↦ 0) =
      πΓ '' truncatedSet hn Γ D.centers D.level := by
  unfold Topology.cylindricalCore
  simp_rw [D.horoballCylinderMap_image_pos hΓ]
  exact D.compl_iUnion_image_open_horoball

include hΓ in
theorem isConnected_quotient :
    IsConnected (πΓ '' truncatedSet hn Γ D.centers D.level) := by
  rw [← D.cylindricalCore_zero hΓ]
  exact D.isConnected_cylindricalCore hΓ (fun _ ↦ 0) (fun _ ↦ le_rfl)

theorem isCompact_cylindricalCore (hdim : 2 ≤ n)
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ p : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε p))
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    IsCompact (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) := by
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (endStabilizer hn Γ {ξ.val}) (HUpper n) _
      (EquivariantMap.subAction hn (endStabilizer hn Γ {ξ.val})))) ''
        horosphere ξ.val (D.level ξ)
  let : Finite D.centers := D.finite_centers
  let : ∀ ξ : D.centers, CompactSpace (C ξ) := fun ξ ↦
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere hΓ ξ hdim hcov hr hre hgeom)
  apply Topology.isCompact_cylindricalCore
    (C := C) (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ) ?_ R hR
  rw [D.cylindricalCore_zero hΓ]
  exact D.isCompact_quotient

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
