import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphRegion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothCylinder
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenPartialHomeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

variable {m : ℕ}

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (m + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (m + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r) (ξ : D.centers)

local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)
local notation "E" => D.horosphereHeightHomeomorph hΓ ξ
local notation "A" => D.horosphereGraphChart hΓ ξ

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

private local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) P ((hΓ).mono inf_le_left)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

private local instance : ChartedSpace (Fin m → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

private local instance : IsManifold K ∞ S := D.isManifold_quotient_horosphere hΓ ξ

def horosphereHeightDiffeomorph : QP ≃ₘ⟮I, J⟯ S × ℝ := by
  let hhor := CuspCrossSections.horospherical_endStabilizer
    (Nat.le_add_left 1 m) Γ hΓ (D.region_nonempty ξ)
  let e := HorosphereProjection.quotientHorosphereDiffeomorph
    P ξ.val hhor (D.level ξ)
  refine
    { toEquiv := (E).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hs : ContMDiff I J ∞ (fun q : QP => ((e q).1, D.level ξ - (e q).2)) :=
      e.contMDiff.fst.prodMk (contMDiff_const.sub e.contMDiff.snd)
    apply hs.congr
    intro q
    apply Prod.ext
    · rfl
    · change HorosphereProjection.quotientBusemann (Nat.le_add_left 1 m) P ξ.val hhor q =
        D.level ξ - (D.level ξ - HorosphereProjection.quotientBusemann (Nat.le_add_left 1 m) P ξ.val hhor q)
      ring
  · have hs : ContMDiff J J ∞ (fun z : S × ℝ => (z.1, D.level ξ - z.2)) :=
      contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
    exact e.symm.contMDiff.comp hs

theorem horosphereHeightDiffeomorph_toHomeomorph :
    (D.horosphereHeightDiffeomorph ξ).toHomeomorph = E := rfl

@[simp] theorem horosphereHeightDiffeomorph_apply (q : QP) :
    D.horosphereHeightDiffeomorph ξ q = E q := rfl

@[simp] theorem horosphereHeightDiffeomorph_symm_apply (z : S × ℝ) :
    (D.horosphereHeightDiffeomorph ξ).symm z = (E).symm z := rfl

theorem isLocalDiffeomorph_horosphereGraphChart : IsLocalDiffeomorph J I ∞ A := by
  have hj := EquivariantMap.isLocalDiffeomorph_quotientInclusion (show P ≤ Γ from inf_le_left) ∞
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (f := (D.horosphereHeightDiffeomorph ξ).symm) hj
    (D.horosphereHeightDiffeomorph ξ).symm.isLocalDiffeomorph
  exact h

def horosphereGraphPartialDiffeomorph : PartialDiffeomorph J I (S × ℝ) QΓ ∞ :=
  (A).toPartialDiffeomorph
    ((D.isLocalDiffeomorph_horosphereGraphChart ξ).isLocalDiffeomorphOn (A).source)

theorem horosphereGraphPartialDiffeomorph_toOpenPartialHomeomorph :
    (D.horosphereGraphPartialDiffeomorph ξ).toOpenPartialHomeomorph = A := rfl

@[simp] theorem horosphereGraphPartialDiffeomorph_source :
    (D.horosphereGraphPartialDiffeomorph ξ).source = (A).source := rfl

@[simp] theorem horosphereGraphPartialDiffeomorph_target :
    (D.horosphereGraphPartialDiffeomorph ξ).target = (A).target := rfl

@[simp] theorem horosphereGraphPartialDiffeomorph_apply (z : S × ℝ) :
    D.horosphereGraphPartialDiffeomorph ξ z = A z := rfl

@[simp] theorem horosphereGraphPartialDiffeomorph_symm_apply (y : QΓ) :
    (D.horosphereGraphPartialDiffeomorph ξ).symm y = (A).symm y := rfl

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
