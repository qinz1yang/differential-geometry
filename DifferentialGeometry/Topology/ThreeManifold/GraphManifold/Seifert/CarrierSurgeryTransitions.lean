import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySmoothPatches

/-!
Actual transition maps between retained half collars and the interior of a torus-pairing quotient.
Disjoint seam and retained collar targets have empty transition domains.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

theorem surgeryExternal_target_notMem_block (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {x : C.Carrier} (hx : x ∈ (E.collar i).target) (j : Fin P.count) :
    x ∉ P.gluing.block j := by
  intro hj
  rcases hj with hl | hr
  · rw [← P.leftCollar_zero_range] at hl
    obtain ⟨t, rfl⟩ := hl
    exact (he i (.inl j)).le_bot ⟨hx, (P.leftCollar j).map_source' (by
      rw [P.left_source]
      exact zero_mem_halfCollarSource t)⟩
  · rw [← P.rightCollar_zero_range] at hr
    obtain ⟨t, rfl⟩ := hr
    exact (he i (.inr j)).le_bot ⟨hx, (P.rightCollar j).map_source' (by
      rw [P.right_source]
      exact zero_mem_halfCollarSource t)⟩

theorem surgeryExternalCollar_preimage_target (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : P.quotientMap ⁻¹' (P.surgeryExternalCollar E he i).target =
      (E.collar i).target := by
  rw [P.surgeryExternalCollar_target]
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy := P.gluing.eq_of_rel_of_notMem
      (P.surgeryExternal_target_notMem_block E he i hy)
      ((P.surgery_quotientMap_eq_iff y x).mp hyx)
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem surgeryExternalCollar_symm_quotientMap (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) {x : C.Carrier} (hx : x ∈ (E.collar i).target) :
    (P.surgeryExternalCollar E he i).symm (P.quotientMap x) = (E.collar i).symm x := by
  change (E.collar i).symm ((P.surgeryExternalPatch E he i).symm (P.quotientMap x)) = _
  rw [P.surgeryExternalPatch_symm_quotientMap E he i hx]

theorem contMDiffOn_surgeryInteriorPatch_trans_external_symm (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : ContMDiffOn C.model halfCollarModel ∞
      ((P.surgeryInteriorPatch D hb).trans (P.surgeryExternalCollar E he i).symm)
      ((P.surgeryInteriorPatch D hb).trans (P.surgeryExternalCollar E he i).symm).source := by
  have hsub : ((P.surgeryInteriorPatch D hb).trans
      (P.surgeryExternalCollar E he i).symm).source ⊆ (E.collar i).target := by
    intro x hx
    have hi : x ∈ C.interior := (P.surgeryInteriorPatch_source D hb).subset hx.1
    have hq := hx.2
    change P.surgeryInteriorPatch D hb x ∈ (P.surgeryExternalCollar E he i).target at hq
    rw [P.surgeryInteriorPatch_apply D hb hi] at hq
    exact (P.surgeryExternalCollar_preimage_target E he i).subset hq
  apply ((E.collar i).contMDiffOn_invFun.mono hsub).congr
  intro x hx
  have hi : x ∈ C.interior := (P.surgeryInteriorPatch_source D hb).subset hx.1
  change (P.surgeryExternalCollar E he i).symm (P.surgeryInteriorPatch D hb x) = _
  rw [P.surgeryInteriorPatch_apply D hb hi]
  exact P.surgeryExternalCollar_symm_quotientMap E he i (hsub hx)

theorem contMDiffOn_surgeryExternal_trans_interior_symm (P : TorusPairing C)
    (D : C.Components) (hb : (⋃ j, P.gluing.block j) ⊆ C.model.boundary C.Carrier)
    {n : ℕ} (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (i : Fin n) : ContMDiffOn halfCollarModel C.model ∞
      ((P.surgeryExternalCollar E he i).trans (P.surgeryInteriorPatch D hb).symm)
      ((P.surgeryExternalCollar E he i).trans (P.surgeryInteriorPatch D hb).symm).source := by
  have hsub : ((P.surgeryExternalCollar E he i).trans
      (P.surgeryInteriorPatch D hb).symm).source ⊆ (E.collar i).source := by
    intro p hp
    exact (E.source_eq i).symm.subset ((P.surgeryExternalCollar_source E he i).subset hp.1)
  apply ((E.collar i).contMDiffOn.mono hsub).congr
  intro p hp
  have hs : p ∈ halfCollarSource := (P.surgeryExternalCollar_source E he i).subset hp.1
  have hq := hp.2
  change P.surgeryExternalCollar E he i p ∈ (P.surgeryInteriorPatch D hb).target at hq
  rw [P.surgeryExternalCollar_apply E he i hs] at hq
  have hi : E.collar i p ∈ C.interior :=
    (P.surgeryInteriorPatch_preimage_target D hb).subset hq
  change (P.surgeryInteriorPatch D hb).symm (P.surgeryExternalCollar E he i p) = _
  rw [P.surgeryExternalCollar_apply E he i hs]
  exact P.surgeryInteriorPatch_symm_quotientMap D hb hi

theorem surgeryExternalCollar_targets_disjoint (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target) :
    Pairwise fun i j => Disjoint (P.surgeryExternalCollar E he i).target
      (P.surgeryExternalCollar E he j).target := by
  intro i j hij
  apply disjoint_left.mpr
  intro q hqi hqj
  obtain ⟨x, rfl⟩ := P.surgery_quotientMap_surjective q
  exact (E.disjoint hij).le_bot
    ⟨(P.surgeryExternalCollar_preimage_target E he i).subset hqi,
      (P.surgeryExternalCollar_preimage_target E he j).subset hqj⟩

theorem surgeryExternalCollar_seam_disjoint (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (i : Fin n) (j : Fin P.count) :
    Disjoint (P.surgeryExternalCollar E he i).target (P.surgerySignedSeam hd j).target := by
  apply disjoint_left.mpr
  intro q hqe hqs
  obtain ⟨x, rfl⟩ := P.surgery_quotientMap_surjective q
  have hx := (P.surgeryExternalCollar_preimage_target E he i).subset hqe
  rw [P.surgerySignedSeam_target] at hqs
  rcases (P.surgerySeamMap_preimage_range hd j).subset hqs with hl | hr
  · exact (he i (.inl j)).le_bot ⟨hx, hl⟩
  · exact (he i (.inr j)).le_bot ⟨hx, hr⟩

end GC.GraphManifold.TorusPairing

namespace GC.Seifert

section Transitions

variable {E F H K M N Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
  [ChartedSpace H M] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

theorem contMDiffOn_surgerySelfTransition (e : OpenPartialHomeomorph M Q) :
    ContMDiffOn I I ∞ (e.trans e.symm) (e.trans e.symm).source := by
  apply contMDiffOn_id.congr
  intro x hx
  exact e.left_inv hx.1

theorem contMDiffOn_surgeryDisjointTransition (e : OpenPartialHomeomorph M Q)
    (f : OpenPartialHomeomorph N Q) (hd : Disjoint e.target f.target) :
    ContMDiffOn I J ∞ (e.trans f.symm) (e.trans f.symm).source := by
  intro x hx
  exact False.elim (hd.le_bot ⟨e.map_source hx.1, hx.2⟩)

end Transitions

end GC.Seifert
