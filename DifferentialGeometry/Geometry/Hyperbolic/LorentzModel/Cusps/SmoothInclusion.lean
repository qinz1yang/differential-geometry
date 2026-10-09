import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.QuotientInclusion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothCylinder
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere horoball)

variable {m : ℕ}

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

variable {Γ : Subgroup (PO (m + 1) 1)} {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r)
  (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "F" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) (Nat.le_add_left 1 m) inf_le_left
local notation "U" => D.openHoroballQuotient hΓ ξ
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))

@[simp] theorem quotientInclusion_eq_horoballQuotientInclusion
    (q : πP '' horoball ξ.val (D.level ξ)) :
    F q.val = D.horoballQuotientInclusion ξ q := rfl

theorem quotientInclusion_injOn_openHoroballQuotient : Set.InjOn F (U : Set QP) := by
  intro q hq q' hq' he
  have hclosed {z : QP} (hz : z ∈ U) : z ∈ πP '' horoball ξ.val (D.level ξ) := by
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨p, (show busemann ξ.val p < D.level ξ from hp).le, rfl⟩
  have h := D.horoballQuotientInclusion_injective hΓ ξ
    (a₁ := ⟨q, hclosed hq⟩) (a₂ := ⟨q', hclosed hq'⟩) he
  exact congrArg Subtype.val h

theorem quotientInclusion_image_openHoroballQuotient :
    F '' (U : Set QP) = πΓ '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ} :=
  EquivariantMap.quotientInclusion_image (Nat.le_add_left 1 m) inf_le_left _

theorem openHoroballQuotient_nonempty : (U : Set QP).Nonempty := by
  let p := AsymptoticRays.rayTo (HyperbolicFaithful.basepointH : HUpper (m + 1)) ξ.val (1 - D.level ξ)
  have hp : busemann ξ.val p < D.level ξ := by
    dsimp only [p]
    rw [HorosphereProjection.busemann_rayTo, Busemann.busemann_basepointH]
    linarith
  exact ⟨πP p, ⟨p, hp, rfl⟩⟩

variable [IsCancelSMul Γ (HUpper (m + 1))]

private theorem peripheral_isCancelSMul : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

omit [IsCancelSMul Γ (HUpper (m + 1))] in
include hΓ in
private theorem peripheral_properlyDiscontinuousSMul : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)

omit [IsCancelSMul Γ (HUpper (m + 1))] in
include hΓ in
private theorem ambient_properlyDiscontinuousSMul : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

private theorem quotientInclusion_localDiffeomorph :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    IsLocalDiffeomorph I I ∞ F := by
  let _ := peripheral_isCancelSMul D ξ
  let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
  let _ := ambient_properlyDiscontinuousSMul hΓ
  exact EquivariantMap.isLocalDiffeomorph_quotientInclusion (show P ≤ Γ from inf_le_left) ∞

private theorem exists_openHoroballQuotientPartialDiffeomorph :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    ∃ Φ : PartialDiffeomorph I I QP QΓ ∞,
      Φ.source = U ∧ Φ.target = πΓ '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ} ∧
      Φ.toFun = F := by
  let _ := peripheral_isCancelSMul D ξ
  let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
  let _ := ambient_properlyDiscontinuousSMul hΓ
  obtain ⟨Φ, hsource, htarget, hmap⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      ((quotientInclusion_localDiffeomorph D hΓ ξ).isLocalDiffeomorphOn U)
      (U).isOpen (D.openHoroballQuotient_nonempty hΓ ξ)
        (D.quotientInclusion_injOn_openHoroballQuotient hΓ ξ)
  exact ⟨Φ, hsource, htarget.trans (D.quotientInclusion_image_openHoroballQuotient hΓ ξ), hmap⟩

def openHoroballQuotientPartialDiffeomorph :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    PartialDiffeomorph I I QP QΓ ∞ :=
  (exists_openHoroballQuotientPartialDiffeomorph D hΓ ξ).choose

@[simp] theorem openHoroballQuotientPartialDiffeomorph_source :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).source = U :=
  (exists_openHoroballQuotientPartialDiffeomorph D hΓ ξ).choose_spec.1

@[simp] theorem openHoroballQuotientPartialDiffeomorph_target :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).target =
      πΓ '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ} :=
  (exists_openHoroballQuotientPartialDiffeomorph D hΓ ξ).choose_spec.2.1

theorem openHoroballQuotientPartialDiffeomorph_toFun :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).toFun = F :=
  (exists_openHoroballQuotientPartialDiffeomorph D hΓ ξ).choose_spec.2.2

@[simp] theorem openHoroballQuotientPartialDiffeomorph_apply_mk (p : HUpper (m + 1)) :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    D.openHoroballQuotientPartialDiffeomorph hΓ ξ (πP p) = πΓ p := by
  rw [show (D.openHoroballQuotientPartialDiffeomorph hΓ ξ : QP → QΓ) = F from
    D.openHoroballQuotientPartialDiffeomorph_toFun hΓ ξ]
  rfl

theorem openHoroballQuotientPartialDiffeomorph_symm_apply_mk (p : HUpper (m + 1))
    (hp : busemann ξ.val p < D.level ξ) :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    let _ := ambient_properlyDiscontinuousSMul hΓ
    (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).symm (πΓ p) = πP p := by
  let _ := peripheral_isCancelSMul D ξ
  let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
  let _ := ambient_properlyDiscontinuousSMul hΓ
  have hs : πP p ∈ (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).source := by
    rw [D.openHoroballQuotientPartialDiffeomorph_source hΓ ξ]
    exact ⟨p, hp, rfl⟩
  have he := (D.openHoroballQuotientPartialDiffeomorph hΓ ξ).left_inv hs
  rwa [D.openHoroballQuotientPartialDiffeomorph_apply_mk hΓ ξ p] at he

theorem exists_openHoroballQuotientPartialDiffeomorph_of_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (e : QΓ ≃ₜ N) (he : IsLocalDiffeomorph I J ∞ (e ∘ πΓ)) :
    let _ := peripheral_isCancelSMul D ξ
    let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
    ∃ Φ : PartialDiffeomorph I J QP N ∞,
      Φ.source = U ∧
      Φ.target = (e ∘ πΓ) '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ} ∧
      Φ.toFun = e ∘ F := by
  let _ := peripheral_isCancelSMul D ξ
  let _ := peripheral_properlyDiscontinuousSMul D hΓ ξ
  let : ContMDiffConstSMul I ∞ P (HUpper (m + 1)) :=
    ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := ∞) I
  have hlocal : IsLocalDiffeomorph I J ∞ (e ∘ F) := by
    intro q
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (he p) (hπ p)
  have hinj : Set.InjOn (e ∘ F) (U : Set QP) := by
    intro q hq q' hq' heq
    exact D.quotientInclusion_injOn_openHoroballQuotient hΓ ξ hq hq' (e.injective heq)
  obtain ⟨Φ, hs, ht, hf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hlocal.isLocalDiffeomorphOn U) (U).isOpen (D.openHoroballQuotient_nonempty hΓ ξ) hinj
  refine ⟨Φ, hs, ht.trans ?_, hf⟩
  change (e ∘ F) '' (πP '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ}) = _
  rw [Set.image_image]
  rfl

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
