import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Count
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Embedding
import DifferentialGeometry.Topology.Ends.Cylindrical

noncomputable section

namespace DifferentialGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (poBoundaryMulAction)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere horoball)
open AsymptoticRays (rayTo)
open MeasureTheory (HasFundamentalDomain covolume)
open Geometry.Topology (endCount endCount_eq_card_of_finite_cylindrical_ends)

namespace CuspTruncation.FiniteCuspTruncation

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "πP" => Quotient.mk
  (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

def horoballCylinderMap :
    C((πP '' horosphere ξ.val (D.level ξ)) × Set.Ici (0 : ℝ), QΓ) :=
  (D.horoballQuotientInclusion ξ).comp
    ⟨(D.horoballQuotientHomeomorph hΓ ξ).symm,
      (D.horoballQuotientHomeomorph hΓ ξ).symm.continuous⟩

@[simp] theorem horoballCylinderMap_apply_mk (p : HUpper n)
    (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : Set.Ici (0 : ℝ)) :
    D.horoballCylinderMap hΓ ξ (⟨πP p, ⟨p, hp, rfl⟩⟩, t) =
      πΓ (rayTo p ξ.val t.val) := rfl

theorem horoballCylinderMap_isClosedEmbedding :
    _root_.Topology.IsClosedEmbedding (D.horoballCylinderMap hΓ ξ) :=
  (D.horoballQuotientInclusion_isClosedEmbedding hΓ ξ).comp
    (D.horoballQuotientHomeomorph hΓ ξ).symm.isClosedEmbedding

theorem horoballCylinderMap_image_pos :
    (D.horoballCylinderMap hΓ ξ) '' {z | 0 < z.2.val} =
      πΓ '' {p | busemann ξ.val p < D.level ξ} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨⟨q, p, hp, rfl⟩, t⟩, ht, rfl⟩
    refine ⟨rayTo p ξ.val t.val, ?_, rfl⟩
    change busemann ξ.val (rayTo p ξ.val t.val) < D.level ξ
    rw [HorosphereProjection.busemann_rayTo, show busemann ξ.val p = D.level ξ from hp]
    exact sub_lt_self _ ht
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : busemann ξ.val p < D.level ξ := hp
    let q : πP '' horoball ξ.val (D.level ξ) := ⟨πP p, ⟨p, by
      change busemann ξ.val p ≤ D.level ξ
      exact hp'.le, rfl⟩⟩
    refine ⟨D.horoballQuotientHomeomorph hΓ ξ q, ?_, ?_⟩
    · change 0 < D.level ξ - busemann ξ.val p
      exact sub_pos.mpr hp
    · change D.horoballQuotientInclusion ξ
        ((D.horoballQuotientHomeomorph hΓ ξ).symm
          (D.horoballQuotientHomeomorph hΓ ξ q)) = πΓ p
      rw [Homeomorph.symm_apply_apply]
      rfl

include hΓ in
theorem pairwise_disjoint_image_horoball :
    Pairwise fun ξ η : D.centers =>
      Disjoint (πΓ '' horoball ξ.val (D.level ξ)) (πΓ '' horoball η.val (D.level η)) := by
  intro ξ η hξη
  apply Set.disjoint_left.mpr
  rintro q ⟨p, hp, hpq⟩ ⟨s, hs, hsq⟩
  obtain ⟨γ, hγ⟩ := Quotient.exact (hpq.trans hsq.symm)
  have hne : (poBoundaryMulAction hn).smul (γ : PO n 1) η.val ≠
      (poBoundaryMulAction hn).smul (1 : PO n 1) ξ.val := by
    intro h
    have hfix := h.trans ((poBoundaryMulAction hn).one_smul ξ.val)
    exact hξη (D.distinct_orbits η ξ γ hfix).symm
  have hd := D.disjoint_horoballs hΓ η ξ γ 1 hne
  exact Set.disjoint_left.mp hd ⟨s, hs, hγ⟩
    ⟨p, hp, (poMulAction hn).one_smul p⟩

theorem compl_iUnion_image_open_horoball :
    (⋃ ξ : D.centers, πΓ '' {p | busemann ξ.val p < D.level ξ})ᶜ =
      πΓ '' truncatedSet hn Γ D.centers D.level := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    refine ⟨p, ?_, rfl⟩
    intro hp
    obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.mp hp
    obtain ⟨γ, s, hs, hsp⟩ := Set.mem_iUnion.mp hξ
    apply hq
    have hps : πΓ p = πΓ s := Quotient.sound ⟨γ, hsp⟩
    exact Set.mem_iUnion.mpr ⟨ξ, s, hs, hps.symm⟩
  · rintro ⟨p, hp, hpq⟩ hq
    obtain ⟨ξ, s, hs, hsq⟩ := Set.mem_iUnion.mp hq
    obtain ⟨γ, hγ⟩ := Quotient.exact (hpq.trans hsq.symm)
    exact hp (Set.mem_iUnion.mpr ⟨ξ, Set.mem_iUnion.mpr ⟨γ, s, hs, hγ⟩⟩)

include hΓ in
theorem endCount_quotient_eq_ncard_centers (hdim : 2 ≤ n)
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ p : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε p)) :
    endCount QΓ = (D.centers.ncard : ℕ∞) := by
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (@MulAction.orbitRel (endStabilizer hn Γ {ξ.val}) (HUpper n) _
      (EquivariantMap.subAction hn (endStabilizer hn Γ {ξ.val})))) ''
        horosphere ξ.val (D.level ξ)
  let e (ξ : D.centers) : C ξ × Set.Ici (0 : ℝ) → QΓ := D.horoballCylinderMap hΓ ξ
  let : Finite D.centers := D.finite_centers
  let : ∀ ξ : D.centers, CompactSpace (C ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere hΓ ξ hdim hcov hr hre hgeom)
  let : ∀ ξ : D.centers, ConnectedSpace (C ξ) := fun ξ =>
    isConnected_iff_connectedSpace.mp (D.isConnected_quotient_horosphere ξ)
  have he (ξ : D.centers) : _root_.Topology.IsClosedEmbedding (e ξ) :=
    D.horoballCylinderMap_isClosedEmbedding hΓ ξ
  have hopen (ξ : D.centers) : IsOpen (e ξ '' {p | 0 < p.2.val}) := by
    change IsOpen ((D.horoballCylinderMap hΓ ξ) '' {p | 0 < p.2.val})
    rw [D.horoballCylinderMap_image_pos hΓ ξ]
    let := EquivariantMap.subAction hn Γ
    let : ContinuousConstSMul Γ (HUpper n) :=
      ⟨fun γ => (ContinuousAction.continuous_po_smul hn).comp
        (continuous_const.prodMk continuous_id)⟩
    apply (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := HUpper n)).isOpenMap
    exact isOpen_lt (HorosphereProjection.continuous_busemann ξ.val) continuous_const
  have hdisjoint : Pairwise fun ξ η : D.centers =>
      Disjoint (e ξ '' {p | 0 < p.2.val}) (e η '' {p | 0 < p.2.val}) := by
    intro ξ η hξη
    change Disjoint ((D.horoballCylinderMap hΓ ξ) '' {p | 0 < p.2.val})
      ((D.horoballCylinderMap hΓ η) '' {p | 0 < p.2.val})
    rw [D.horoballCylinderMap_image_pos hΓ ξ, D.horoballCylinderMap_image_pos hΓ η]
    have hsub (ζ : D.centers) :
        {p | busemann ζ.val p < D.level ζ} ⊆ horoball ζ.val (D.level ζ) := by
      intro p hp
      change busemann ζ.val p ≤ D.level ζ
      exact le_of_lt hp
    exact (D.pairwise_disjoint_image_horoball hΓ hξη).mono
      (Set.image_mono (hsub ξ)) (Set.image_mono (hsub η))
  have hcore : IsCompact (⋃ ξ : D.centers, e ξ '' {p | 0 < p.2.val})ᶜ := by
    have heq : (⋃ ξ : D.centers, e ξ '' {p | 0 < p.2.val}) =
        ⋃ ξ : D.centers, πΓ '' {p | busemann ξ.val p < D.level ξ} := by
      congr 1
      funext ξ
      exact D.horoballCylinderMap_image_pos hΓ ξ
    rw [heq, D.compl_iUnion_image_open_horoball]
    exact D.isCompact_quotient
  simpa only [Nat.card_coe_set_eq] using
    endCount_eq_card_of_finite_cylindrical_ends C e he hopen hdisjoint hcore

end CuspTruncation.FiniteCuspTruncation

namespace CuspCorrespondence

variable {n : ℕ}

theorem endCount_quotient_eq_cuspCount (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    letI := EquivariantMap.subAction hn Γ
    endCount (MulAction.orbitRel.Quotient Γ (HUpper n)) = cuspCount hn Γ := by
  obtain ⟨ε, hε, hgeom⟩ := BoundaryStabilizer.exists_margulis_geometry_constant hn
  have hr : 0 < ε / 2 := half_pos hε
  have hre : ε / 2 < ε := half_lt_self hε
  have hn2 : 2 ≤ n := (show 2 ≤ 3 by decide).trans hdim
  obtain ⟨D⟩ := CuspTruncation.exists_finite_cusp_truncation hn hn2 Γ hΓ hcov
    hr hre (hgeom Γ hΓ)
  exact (D.endCount_quotient_eq_ncard_centers hΓ hn2 hcov hr hre (hgeom Γ hΓ)).trans
    (D.cuspCount_eq_ncard_centers hdim hΓ hcov hr hre (hgeom Γ hΓ)).symm

end CuspCorrespondence

end DifferentialGeometry
