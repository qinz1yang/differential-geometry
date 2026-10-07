import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Section
import DifferentialGeometry.Topology.Ends.CylindricalOpening
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section

open Set
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

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 m) Γ hΓ

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 m) (show P ≤ Γ from inf_le_left)

private local instance : ChartedSpace (Fin m → ℝ) S := D.horosphereQuotientChartedSpace hΓ ξ

theorem exists_partialDiffeomorph_horoballCylinderMap :
    ∃ A : PartialDiffeomorph J I (S × ℝ) QΓ ∞,
      (∀ c t, 0 ≤ t → (c, t) ∈ A.source) ∧
      (∀ p : S × Ici (0 : ℝ), D.horoballCylinderMap hΓ ξ p = A (p.1, p.2.val)) ∧
      A.target = πΓ '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val}) := by
  let T : Diffeomorph J J (S × ℝ) (S × ℝ) ∞ :=
    { toFun := fun z => (z.1, D.level ξ - z.2)
      invFun := fun z => (z.1, D.level ξ - z.2)
      left_inv := fun z => Prod.ext rfl (by ring)
      right_inv := fun z => Prod.ext rfl (by ring)
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd) }
  let A := T.toPartialDiffeomorph.trans (D.horosphereGraphPartialDiffeomorph ξ)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro c t ht
    refine ⟨mem_univ _, ?_⟩
    change (D.horosphereHeightHomeomorph hΓ ξ).symm (c, D.level ξ - t) ∈
      πP '' interior (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})
    obtain ⟨c, p, hp, rfl⟩ := c
    change πP (AsymptoticRays.rayTo p ξ.val (D.level ξ - (D.level ξ - t))) ∈ _
    refine ⟨AsymptoticRays.rayTo p ξ.val (D.level ξ - (D.level ξ - t)),
      D.horoball_inside ξ ?_, rfl⟩
    change Busemann.busemann ξ.val (AsymptoticRays.rayTo p ξ.val
      (D.level ξ - (D.level ξ - t))) ≤ D.level ξ
    rw [HorosphereProjection.busemann_rayTo, show Busemann.busemann ξ.val p = D.level ξ from hp]
    linarith
  · rintro ⟨⟨c, p, hp, rfl⟩, t⟩
    change D.horoballCylinderMap hΓ ξ (⟨πP p, ⟨p, hp, rfl⟩⟩, t) =
      D.horosphereGraphChart hΓ ξ (⟨πP p, ⟨p, hp, rfl⟩⟩, D.level ξ - t.val)
    rw [D.horoballCylinderMap_apply_mk hΓ ξ p hp t,
      D.horosphereGraphChart_apply_mk hΓ ξ p hp]
    congr 2
    ring
  · change (D.horosphereGraphPartialDiffeomorph ξ).target ∩
      (D.horosphereGraphPartialDiffeomorph ξ).symm ⁻¹' univ = _
    rw [preimage_univ, inter_univ, D.horosphereGraphPartialDiffeomorph_target,
      D.horosphereGraphChart_target]
    rfl

omit ξ in
theorem exists_diffeomorph_interior_truncated_quotient :
    let U : TopologicalSpace.Opens QΓ :=
      ⟨interior (πΓ '' truncatedSet (Nat.le_add_left 1 m) Γ D.centers D.level), isOpen_interior⟩
    ∃ f : Diffeomorph I I U QΓ ∞,
      (∀ x : U, (∀ ξ : D.centers, x.val ∉ πΓ '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) → f x = x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ πΓ '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) → (f.symm y).val = y := by
  classical
  let C (ξ : D.centers) : Type :=
    (Quotient.mk (MulAction.orbitRel (endStabilizer (Nat.le_add_left 1 m) Γ {ξ.val})
      (HUpper (m + 1)))) '' Busemann.horosphere ξ.val (D.level ξ)
  let : Finite D.centers := D.finite_centers
  let : ∀ ξ : D.centers, CompactSpace (C ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let : ∀ ξ : D.centers, ChartedSpace (Fin m → ℝ) (C ξ) := fun ξ =>
    D.horosphereQuotientChartedSpace hΓ ξ
  choose A hsource heq htarget using fun ξ => exists_partialDiffeomorph_horoballCylinderMap D ξ
  have h := Topology.exists_diffeomorph_interior_cylindricalCore_zero
    («I» := I) («J» := K) (D := C) (fun ξ => D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) A hsource heq
  dsimp only at h ⊢
  rw [D.cylindricalCore_zero hΓ] at h
  simpa only [htarget] using h

omit ξ in
theorem exists_diffeomorph_interior_truncated_image
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    {L : ModelWithCorners ℝ F G} (e : QΓ ≃ₜ N)
    (he : IsLocalDiffeomorph I L ∞ (e ∘ πΓ)) :
    let U : TopologicalSpace.Opens N :=
      ⟨interior ((e ∘ πΓ) '' truncatedSet (Nat.le_add_left 1 m) Γ D.centers D.level), isOpen_interior⟩
    ∃ f : Diffeomorph L L U N ∞,
      (∀ x : U, (∀ ξ : D.centers, x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) → f x = x.val) ∧
      ∀ y, (∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) → (f.symm y).val = y := by
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := Γ) (M := HUpper (m + 1)) (n := ∞) I
  have he' : IsLocalDiffeomorph I L ∞ e := by
    intro q
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (he p) (hπ p)
  let E := he'.diffeomorphOfBijective e.bijective
  let U : TopologicalSpace.Opens QΓ :=
    ⟨interior (πΓ '' truncatedSet (Nat.le_add_left 1 m) Γ D.centers D.level), isOpen_interior⟩
  let restriction := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo
    E.toPartialDiffeomorph (U := U) (subset_univ _)
  let V : TopologicalSpace.Opens N :=
    ⟨(E : QΓ → N) '' (U : Set QΓ), DifferentialGeometry.image_opens_isOpen
      E.toPartialDiffeomorph (subset_univ _)⟩
  have hV : V = (⟨interior ((e ∘ πΓ) ''
      truncatedSet (Nat.le_add_left 1 m) Γ D.centers D.level), isOpen_interior⟩ : TopologicalSpace.Opens N) := by
    apply SetLike.coe_injective
    change e '' interior (πΓ '' truncatedSet (Nat.le_add_left 1 m) Γ D.centers D.level) = _
    rw [e.image_interior, image_image]
    rfl
  obtain ⟨ψ, hψ, hψi⟩ := D.exists_diffeomorph_interior_truncated_quotient
  let f : Diffeomorph L L V N ∞ := restriction.symm.trans (ψ.trans E)
  have houtside (y : N)
      (hy : ∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) :
      ∀ ξ : D.centers, E.symm y ∉ πΓ '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val}) := by
    intro ξ hξ
    obtain ⟨p, hp, heq⟩ := hξ
    apply hy ξ
    refine ⟨p, hp, ?_⟩
    change E (πΓ p) = y
    rw [heq, E.apply_symm_apply]
  have hf (x : V)
      (hx : ∀ ξ : D.centers, x.val ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) : f x = x.val := by
    have hs : (restriction.symm x).val = E.symm x.val := rfl
    have hfix := hψ (restriction.symm x) (hs.symm ▸ houtside x hx)
    change E (ψ (restriction.symm x)) = x.val
    rw [hfix, hs, E.apply_symm_apply]
  have hfi (y : N)
      (hy : ∀ ξ : D.centers, y ∉ (e ∘ πΓ) '' interior
        (OrbifoldThinRegions.thinRegion (Nat.le_add_left 1 m) Γ r {ξ.val})) : (f.symm y).val = y := by
    change E ((ψ.symm (E.symm y)).val) = y
    rw [hψi (E.symm y) (houtside y hy), E.apply_symm_apply]
  dsimp only
  rw [← hV]
  exact ⟨f, hf, hfi⟩

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
