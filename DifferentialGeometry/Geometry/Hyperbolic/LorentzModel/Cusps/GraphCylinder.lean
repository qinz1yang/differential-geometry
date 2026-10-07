import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphRegion
import Mathlib.Topology.Constructions.SumProd

noncomputable section

open Set

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Busemann (horosphere)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "QP" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
local notation "πΓ" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "C" => (πP '' horosphere ξ.val (D.level ξ))
local notation "E" => D.horosphereHeightHomeomorph hΓ ξ
local notation "A" => D.horosphereGraphChart hΓ ξ
local notation "F" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) hn inf_le_left

private def graphDepthHomeomorph {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) : X × ℝ ≃ₜ X × ℝ where
  toFun z := (z.1, f z.1 - z.2)
  invFun z := (z.1, f z.1 - z.2)
  left_inv z := Prod.ext rfl (sub_sub_cancel (f z.1) z.2)
  right_inv z := Prod.ext rfl (sub_sub_cancel (f z.1) z.2)
  continuous_toFun := continuous_fst.prodMk ((hf.comp continuous_fst).sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk ((hf.comp continuous_fst).sub continuous_snd)

private theorem isEmbedding_graphCylinder {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (a : OpenPartialHomeomorph (X × ℝ) Y) (f : X → ℝ) (hf : Continuous f)
    (hmem : ∀ z : X × Ici (0 : ℝ), (z.1, f z.1 - z.2.val) ∈ a.source) :
    _root_.Topology.IsEmbedding (fun z : X × Ici (0 : ℝ) => a (z.1, f z.1 - z.2.val)) := by
  have hcoords : _root_.Topology.IsEmbedding (fun z : X × Ici (0 : ℝ) => (z.1, f z.1 - z.2.val)) :=
    (graphDepthHomeomorph f hf).isEmbedding.comp
      (_root_.Topology.IsEmbedding.id.prodMap _root_.Topology.IsEmbedding.subtypeVal)
  exact a.isEmbedding_restrict.comp (hcoords.codRestrict a.source hmem)

def horosphereGraphCylinderMap (f : C → ℝ) (hf : Continuous f) : C(C × Ici (0 : ℝ), QΓ) where
  toFun z := A (z.1, f z.1 - z.2.val)
  continuous_toFun := (F).continuous.comp ((E).symm.continuous.comp
    (continuous_fst.prodMk ((hf.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd))))

@[simp] theorem horosphereGraphCylinderMap_apply (f : C → ℝ) (hf : Continuous f)
    (z : C × Ici (0 : ℝ)) :
    D.horosphereGraphCylinderMap hΓ ξ f hf z = A (z.1, f z.1 - z.2.val) := rfl

theorem horosphereGraphCylinderMap_apply_mk (f : C → ℝ) (hf : Continuous f)
    (p : HUpper n) (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : Ici (0 : ℝ)) :
    D.horosphereGraphCylinderMap hΓ ξ f hf (⟨πP p, ⟨p, hp, rfl⟩⟩, t) =
      πΓ (AsymptoticRays.rayTo p ξ.val (D.level ξ - f ⟨πP p, ⟨p, hp, rfl⟩⟩ + t.val)) := by
  change A (⟨πP p, ⟨p, hp, rfl⟩⟩, f ⟨πP p, ⟨p, hp, rfl⟩⟩ - t.val) = _
  rw [D.horosphereGraphChart_apply_mk hΓ ξ p hp]
  congr 2
  ring

theorem horosphereGraphCylinderMap_zero (f : C → ℝ) (hf : Continuous f) (s : C) :
    D.horosphereGraphCylinderMap hΓ ξ f hf (s, ⟨0, by simp⟩) = A (s, f s) := by
  change A (s, f s - 0) = _
  rw [sub_zero]

theorem range_horosphereGraphCylinderMap (f : C → ℝ) (hf : Continuous f) :
    range (D.horosphereGraphCylinderMap hΓ ξ f hf) = D.closedGraphRegion hΓ ξ f := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(E).symm (z.1, f z.1 - z.2.val), ?_, rfl⟩
    change (E ((E).symm (z.1, f z.1 - z.2.val))).2 ≤ f (E ((E).symm (z.1, f z.1 - z.2.val))).1
    rw [(E).apply_symm_apply]
    exact sub_le_self _ z.2.property
  · rintro ⟨q, hq, rfl⟩
    refine ⟨((E q).1, ⟨f (E q).1 - (E q).2, by change 0 ≤ f (E q).1 - (E q).2; exact sub_nonneg.mpr hq⟩), ?_⟩
    change F ((E).symm ((E q).1, f (E q).1 - (f (E q).1 - (E q).2))) = F q
    rw [sub_sub_cancel, Prod.eta, (E).symm_apply_apply]

theorem image_pos_horosphereGraphCylinderMap (f : C → ℝ) (hf : Continuous f) :
    (D.horosphereGraphCylinderMap hΓ ξ f hf) '' {z | 0 < z.2.val} = D.openGraphRegion hΓ ξ f := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(E).symm (z.1, f z.1 - z.2.val), ?_, rfl⟩
    change (E ((E).symm (z.1, f z.1 - z.2.val))).2 < f (E ((E).symm (z.1, f z.1 - z.2.val))).1
    rw [(E).apply_symm_apply]
    exact sub_lt_self _ hz
  · rintro ⟨q, hq, rfl⟩
    refine ⟨((E q).1, ⟨f (E q).1 - (E q).2, by change 0 ≤ f (E q).1 - (E q).2; exact sub_nonneg.mpr (le_of_lt hq)⟩), ?_, ?_⟩
    · change 0 < f (E q).1 - (E q).2
      exact sub_pos.mpr hq
    · change F ((E).symm ((E q).1, f (E q).1 - (f (E q).1 - (E q).2))) = F q
      rw [sub_sub_cancel, Prod.eta, (E).symm_apply_apply]

variable (hr : 0 < r)
  (hgeom : ∀ p : HUpper n,
    BoundaryStabilizer.ElementaryGeometry hn (OrbifoldStrata.closedSmallSubgroup hn Γ r p))

include hr hgeom in
private theorem cylinder_coordinates_mem_source (f : C → ℝ)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    (z.1, f z.1 - z.2.val) ∈ (A).source := by
  apply D.graph_sublevel_subset_interior_thinRegion hΓ ξ hr hgeom f hgraph
  change (E ((E).symm (z.1, f z.1 - z.2.val))).2 ≤ f (E ((E).symm (z.1, f z.1 - z.2.val))).1
  rw [(E).apply_symm_apply]
  exact sub_le_self _ z.2.property

include hr hgeom in
theorem horosphereGraphCylinderMap_isClosedEmbedding (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) :
    _root_.Topology.IsClosedEmbedding (D.horosphereGraphCylinderMap hΓ ξ f hf) := by
  refine ⟨isEmbedding_graphCylinder A f hf
    (cylinder_coordinates_mem_source D hΓ ξ hr hgeom f hgraph), ?_⟩
  rw [D.range_horosphereGraphCylinderMap hΓ ξ f hf]
  exact D.isClosed_closedGraphRegion hΓ ξ hr hgeom f hf hgraph

include hr hgeom in
theorem range_horosphereGraphCylinderMap_eq_closure (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) :
    range (D.horosphereGraphCylinderMap hΓ ξ f hf) = closure (D.openGraphRegion hΓ ξ f) := by
  rw [D.range_horosphereGraphCylinderMap hΓ ξ f hf,
    D.closure_openGraphRegion hΓ ξ hr hgeom f hf hgraph]

include hr hgeom in
theorem horosphereGraphChart_symm_horosphereGraphCylinderMap (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    (A).symm (D.horosphereGraphCylinderMap hΓ ξ f hf z) = (z.1, f z.1 - z.2.val) :=
  (A).left_inv (cylinder_coordinates_mem_source D hΓ ξ hr hgeom f hgraph z)

include hr hgeom in
theorem horosphereGraphCylinderMap_inverse_depth (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    f ((A).symm (D.horosphereGraphCylinderMap hΓ ξ f hf z)).1 -
      ((A).symm (D.horosphereGraphCylinderMap hΓ ξ f hf z)).2 = z.2.val := by
  rw [D.horosphereGraphChart_symm_horosphereGraphCylinderMap hΓ ξ hr hgeom f hf hgraph]
  exact sub_sub_cancel _ _

include hr hgeom in
theorem horosphereGraphCylinderMap_mem_openGraphRegion_iff (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    D.horosphereGraphCylinderMap hΓ ξ f hf z ∈ D.openGraphRegion hΓ ξ f ↔ 0 < z.2.val := by
  rw [D.horosphereGraphCylinderMap_apply,
    D.mem_openGraphRegion_iff hΓ ξ hr hgeom f hgraph _
      (cylinder_coordinates_mem_source D hΓ ξ hr hgeom f hgraph z)]
  change f z.1 - z.2.val < f z.1 ↔ 0 < z.2.val
  constructor <;> intro h <;> linarith

include hr hgeom in
theorem horosphereGraphCylinderMap_notMem_openGraphRegion_iff (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    D.horosphereGraphCylinderMap hΓ ξ f hf z ∉ D.openGraphRegion hΓ ξ f ↔ z.2.val = 0 := by
  rw [D.horosphereGraphCylinderMap_mem_openGraphRegion_iff hΓ ξ hr hgeom f hf hgraph]
  exact ⟨fun h => le_antisymm (le_of_not_gt h) z.2.property, fun h => by rw [h]; exact lt_irrefl 0⟩

include hr hgeom in
theorem horosphereGraphCylinderMap_frontier_iff (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) (z : C × Ici (0 : ℝ)) :
    D.horosphereGraphCylinderMap hΓ ξ f hf z ∈ frontier (D.openGraphRegion hΓ ξ f) ↔ z.2.val = 0 := by
  rw [frontier, (D.isOpen_openGraphRegion hΓ ξ f hf).interior_eq,
    D.closure_openGraphRegion hΓ ξ hr hgeom f hf hgraph]
  have hmem : D.horosphereGraphCylinderMap hΓ ξ f hf z ∈ D.closedGraphRegion hΓ ξ f := by
    rw [← D.range_horosphereGraphCylinderMap hΓ ξ f hf]
    exact mem_range_self z
  simp only [mem_sdiff, hmem, true_and]
  exact D.horosphereGraphCylinderMap_notMem_openGraphRegion_iff hΓ ξ hr hgeom f hf hgraph z

include hr hgeom in
theorem horosphereGraphCylinderMap_of_projection
    {Y : Type*} [TopologicalSpace Y] (e : QΓ ≃ₜ Y) (pH : HUpper n → Y)
    (hrep : ∀ p : HUpper n, e (πΓ p) = pH p)
    (f : C → ℝ) (hf : Continuous f)
    (hgraph : ∀ s : C, (s, f s) ∈ (A).source) :
    let e_f := fun z : C × Ici (0 : ℝ) => e (D.horosphereGraphCylinderMap hΓ ξ f hf z)
    _root_.Topology.IsClosedEmbedding e_f ∧
      range e_f = e '' D.closedGraphRegion hΓ ξ f ∧
      range e_f = closure (e '' D.openGraphRegion hΓ ξ f) ∧
      e_f '' {z | 0 < z.2.val} = e '' D.openGraphRegion hΓ ξ f ∧
      (∀ s : C, e_f (s, ⟨0, by simp⟩) = e (A (s, f s))) ∧
      (∀ (p : HUpper n) (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : Ici (0 : ℝ)),
        e_f (⟨πP p, ⟨p, hp, rfl⟩⟩, t) =
          pH (AsymptoticRays.rayTo p ξ.val (D.level ξ - f ⟨πP p, ⟨p, hp, rfl⟩⟩ + t.val))) ∧
      (∀ z : C × Ici (0 : ℝ),
        e_f z ∉ e '' D.openGraphRegion hΓ ξ f ↔ z.2.val = 0) ∧
      ∀ z : C × Ici (0 : ℝ),
        f ((A).symm (e.symm (e_f z))).1 - ((A).symm (e.symm (e_f z))).2 = z.2.val := by
  dsimp only
  have hrange : range (fun z => e (D.horosphereGraphCylinderMap hΓ ξ f hf z)) =
      e '' D.closedGraphRegion hΓ ξ f := by
    exact (range_comp e (D.horosphereGraphCylinderMap hΓ ξ f hf)).trans
      (congrArg (Set.image e) (D.range_horosphereGraphCylinderMap hΓ ξ f hf))
  refine ⟨e.isClosedEmbedding.comp (D.horosphereGraphCylinderMap_isClosedEmbedding hΓ ξ hr hgeom f hf hgraph),
    hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrange, ← e.image_closure, D.closure_openGraphRegion hΓ ξ hr hgeom f hf hgraph]
  · rw [← image_image, D.image_pos_horosphereGraphCylinderMap hΓ ξ f hf]
  · intro s
    rw [D.horosphereGraphCylinderMap_zero]
  · intro p hp t
    rw [D.horosphereGraphCylinderMap_apply_mk hΓ ξ f hf p hp t]
    exact hrep _
  · intro z
    rw [e.injective.mem_set_image]
    exact D.horosphereGraphCylinderMap_notMem_openGraphRegion_iff hΓ ξ hr hgeom f hf hgraph z
  · intro z
    rw [e.symm_apply_apply]
    exact D.horosphereGraphCylinderMap_inverse_depth hΓ ξ hr hgeom f hf hgraph z

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
