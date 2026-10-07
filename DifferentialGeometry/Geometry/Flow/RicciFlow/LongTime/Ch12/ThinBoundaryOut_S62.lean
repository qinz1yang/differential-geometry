import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryProducerBase_S51

set_option autoImplicit false

/-!
# CH12-S62 G1: `hout` -- the deep part of the collar `φ i` misses all seam collars

For a point `p` of `cuspDomain` of height `≥ 1`, the point `φ i p` (= `cores.map c t` of the cusp
point of the level-`S` truncation) is not of the form `F.collar k (t'', s)` with `|s| ≤ 7/8`:
the seam collars of height `|s| ≤ 7/8` consist of core points (`s ≤ 0`) and of cusp points of
height `≤ 7/8` (`s ≥ 0`), and a cusp point of height `≥ 1` is neither (HyperbolicTruncation
`intersection`, `cusp_disjoint`, injectivity of `cuspMap`, `cores.disjoint`, `cores.embedding`).
-/

noncomputable section

open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

/-- A cusp point of positive height is not in the core of the truncation. -/
theorem cuspMap_not_mem_range_inclusion_S62 {H : FiniteVolumeHyperbolicModel.{u}}
    (T : HyperbolicTruncation H) (q : Fin T.count) {p : CuspHalfSpace} (hp : 0 < p.2.val 0) :
    T.cuspMap q p ∉ range T.inclusion := by
  intro hmem
  have h1 : T.cuspMap q p ∈ range T.inclusion ∩ range (T.cuspMap q) := ⟨hmem, p, rfl⟩
  rw [T.intersection q] at h1
  obtain ⟨x, hx⟩ := h1
  have hxp : (x, halfZero) = p := (T.cuspEmbedding q).isEmbedding.injective hx
  rw [← hxp] at hp
  exact lt_irrefl _ hp

/-- The cusp parametrizations of a truncation are jointly injective. -/
theorem cuspMap_inj_S62 {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)
    {q q' : Fin T.count} {p p' : CuspHalfSpace} (h : T.cuspMap q p = T.cuspMap q' p') :
    q = q' ∧ p = p' := by
  by_cases hq : q = q'
  · subst hq
    exact ⟨rfl, (T.cuspEmbedding q).isEmbedding.injective h⟩
  · exact absurd h (fun h' => Set.disjoint_left.mp (T.cusp_disjoint hq) ⟨p, rfl⟩ ⟨p', h'.symm⟩)

section Out

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

/-- A deep cusp point (height `≥ 1`) of the stage is not a seam-collar point of height `≤ 7/8`. -/
theorem stageCusp_ne_collar_S62 (x y : SliceIdx_S19 D) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hp1 : 1 ≤ p.2.val 0) (t'' : Torus) {s : ℝ} (hs1 : -7 / 8 ≤ s) (hs2 : s ≤ 7 / 8) :
    cores.map x.1 t ht ((D.truncation x.1).cuspMap x.2 p) ≠ stageCollar_S19 D ht y (t'', s) := by
  intro h
  obtain ⟨c, q⟩ := x
  obtain ⟨c', q'⟩ := y
  have hpd := stageCusp_mem_domain_S51 D ⟨c, q⟩ hp
  have hsrc : (t'', s) ∈ signedCollarSource := mem_signedSource_S51 t'' (by linarith) (by linarith)
  rcases le_total 0 s with hs0 | hs0
  · rw [stageCollar_pos_S19 D ht ⟨c', q'⟩ t'' s hs0 (by linarith)] at h
    have hpd' := stageCusp_mem_domain_S51 D ⟨c', q'⟩ (p := (t'', halfPoint s hs0))
      (by change (halfPoint s hs0).val 0 < 100; rw [GC.GraphManifold.halfPoint_val_zero]; linarith)
    by_cases hc : c = c'
    · subst hc
      have heq : (⟨_, hpd⟩ : cores.domain c t) = ⟨_, hpd'⟩ :=
        (cores.embedding c t ht).isEmbedding.injective (a₁ := ⟨_, hpd⟩) (a₂ := ⟨_, hpd'⟩) h
      have h2 := (cuspMap_inj_S62 (D.truncation c) (congrArg Subtype.val heq)).2
      have h3 : p.2.val 0 = (halfPoint s hs0).val 0 := congrArg (fun z : CuspHalfSpace => z.2.val 0) h2
      rw [GC.GraphManifold.halfPoint_val_zero] at h3
      linarith
    · exact Set.disjoint_left.mp (cores.disjoint t ht hc) ⟨_, hpd, rfl⟩ ⟨_, hpd', h.symm⟩
  · rw [stageCollar_apply_S19 D ht ⟨c', q'⟩ _ hsrc] at h
    have hwt : D.collar c' q' (t'', s) ∈ (D.collar c' q').target :=
      (D.collar c' q').map_source (by rw [collar_source_S19]; exact hsrc)
    have hwd := D.collar_target_subset_domain c' q' hwt
    have hw : D.collar c' q' (t'', s) ∈ range (D.truncation c').inclusion := by
      rw [TruncatedCutData_IF4.truncation, truncationAtLevel_core_image_C1]
      refine Or.inr (mem_iUnion.mpr ⟨q', ⟨(t'', halfSpaceOneLift (s + D.level)), ⟨trivial, ?_⟩, ?_⟩⟩)
      · change (halfSpaceOneLift (s + D.level)).val 0 ≤ D.level
        rw [GC.LongTime.CuspP1.lift_height_CPA2 (by linarith [D.two_le])]; linarith
      · exact (levelSignedCollar_apply_C2a (D.base c') D.level q' (t'', s)).symm
    by_cases hc : c = c'
    · subst hc
      have heq : (⟨_, hpd⟩ : cores.domain c t) = ⟨_, hwd⟩ :=
        (cores.embedding c t ht).isEmbedding.injective (a₁ := ⟨_, hpd⟩) (a₂ := ⟨_, hwd⟩) h
      exact cuspMap_not_mem_range_inclusion_S62 (D.truncation c) q (p := p) (by linarith)
        (Set.mem_of_eq_of_mem (congrArg Subtype.val heq) hw)
    · exact Set.disjoint_left.mp (cores.disjoint t ht hc) ⟨_, hpd, rfl⟩ ⟨_, hwd, h.symm⟩

/-- **G1 (hout).**  Points of `cuspDomain` of height `≥ 1` are mapped by `φ` outside every seam
collar of height `|s| ≤ 7/8` of the component family. -/
theorem phi_out_S62
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (x : CIdx_S19 D ht C) (φ : CuspHalfSpace → (sliceM_S28 C).Carrier)
    (hφ : ∀ p ∈ cuspDomain, (φ p).val =
      cores.map x.1.1 t ht ((D.truncation x.1.1).cuspMap x.1.2 p)) :
    ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 → ∀ k : Fin (componentFamily_S19 D ht C).count,
      φ p ∉ (componentFamily_S19 D ht C).collar k '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)) := by
  intro p hp hp1 k hk
  obtain ⟨⟨t'', s⟩, ⟨-, hs1, hs2⟩, hcol⟩ := hk
  have hsrc : (t'', s) ∈ (stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1).source := by
    rw [stageCollar_source_S19]; exact mem_signedSource_S51 t'' (by linarith) (by linarith)
  have hval : ((φ p).val : (postStage F.observation t).Carrier) =
      stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1 (t'', s) := by
    have h1 : (((componentFamily_S19 D ht C).collar k (t'', s)).val :
        (postStage F.observation t).Carrier) =
        stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1 (t'', s) :=
      restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (t'', s) hsrc
    rw [← hcol]
    exact h1
  rw [hφ p hp] at hval
  exact stageCusp_ne_collar_S62 D ht x.1 ((cidxEquiv_S19 D ht C).symm k).1 hp hp1 t'' hs1 hs2 hval

end Out

end GC.LongTime.Ch12
