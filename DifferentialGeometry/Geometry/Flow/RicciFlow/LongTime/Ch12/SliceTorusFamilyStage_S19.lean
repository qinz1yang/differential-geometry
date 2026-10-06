import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceTorusFamilyEmbed_S19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevelCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1 GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}

/-- All level-`S` cusp tori of all cores, as a flat index type. -/
abbrev SliceIdx_S19 (D : TruncatedCutData_IF4 cores t) : Type :=
  Σ i : Fin cores.count, Fin (D.base i).count

variable (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

theorem collar_source_S19 (i : Fin cores.count) (q : Fin (D.base i).count) :
    (D.collar i q).source = signedCollarSource :=
  levelSignedCollar_source_C2a (D.base i) D.two_le q

theorem nonemptyTorus_S19 : Nonempty Torus := ⟨(1, 1)⟩

theorem collar_target_nonempty_S19 (i : Fin cores.count) (q : Fin (D.base i).count) :
    ((D.collar i q).target).Nonempty := by
  have hs : (@Classical.choice Torus (nonemptyTorus_S19), (0 : ℝ)) ∈ (D.collar i q).source := by
    rw [collar_source_S19]; simp [signedCollarSource]
  exact ⟨_, (D.collar i q).map_source hs⟩

theorem domain_nonempty_S19 (i : Fin cores.count) (q : Fin (D.base i).count) :
    Nonempty (cores.domain i t) :=
  let ⟨y, hy⟩ := collar_target_nonempty_S19 D i q
  ⟨⟨y, D.collar_target_subset_domain i q hy⟩⟩

/-- The pushforward chart `cores.map i t` as a partial diffeomorphism with source the domain. -/
def mapChart_S19 (i : Fin cores.count) (q : Fin (D.base i).count) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (cores.model i).Carrier (postStage F.observation t).Carrier ∞ :=
  haveI := domain_nonempty_S19 (t := t) D i q
  Classical.choose (exists_openEmbChart_S19 (cores.domain i t) this (cores.map i t ht)
    (cores.embedding i t ht))

theorem mapChart_spec_S19 (i : Fin cores.count) (q : Fin (D.base i).count) :
    (mapChart_S19 D ht i q).source = (cores.domain i t : Set _) ∧
      (∀ x ∈ cores.domain i t, mapChart_S19 D ht i q x = cores.map i t ht x) ∧
      (mapChart_S19 D ht i q).target = cores.map i t ht '' (cores.domain i t : Set _) :=
  Classical.choose_spec (exists_openEmbChart_S19 (cores.domain i t) (domain_nonempty_S19 D i q)
    (cores.map i t ht) (cores.embedding i t ht))

/-- The signed collar of the `q`-th level torus of core `i`, pushed into the stage at time `t`. -/
def stageCollar_S19 (x : SliceIdx_S19 D) :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) (postStage F.observation t).Carrier ∞ :=
  (D.collar x.1 x.2).trans (mapChart_S19 D ht x.1 x.2)

theorem stageCollar_source_S19 (x : SliceIdx_S19 D) :
    (stageCollar_S19 D ht x).source = signedCollarSource := by
  have h1 := (mapChart_spec_S19 D ht x.1 x.2).1
  change (D.collar x.1 x.2).source ∩ (D.collar x.1 x.2) ⁻¹' (mapChart_S19 D ht x.1 x.2).source = _
  rw [h1, collar_source_S19]
  refine inter_eq_left.mpr fun p hp => ?_
  apply D.collar_target_subset_domain
  rw [← collar_source_S19 D x.1 x.2] at hp
  exact (D.collar x.1 x.2).map_source hp

theorem stageCollar_apply_S19 (x : SliceIdx_S19 D) (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    stageCollar_S19 D ht x p = cores.map x.1 t ht (D.collar x.1 x.2 p) := by
  change mapChart_S19 D ht x.1 x.2 (D.collar x.1 x.2 p) = _
  apply (mapChart_spec_S19 D ht x.1 x.2).2.1
  apply D.collar_target_subset_domain
  rw [← collar_source_S19 D x.1 x.2] at hp
  exact (D.collar x.1 x.2).map_source hp

theorem stageCollar_target_subset_S19 (x : SliceIdx_S19 D) :
    (stageCollar_S19 D ht x).target ⊆ cores.map x.1 t ht '' (D.collar x.1 x.2).target := by
  intro y hy
  have hy' : y ∈ (mapChart_S19 D ht x.1 x.2).target ∧
      (mapChart_S19 D ht x.1 x.2).symm y ∈ (D.collar x.1 x.2).target := hy
  obtain ⟨h1, h2⟩ := hy'
  refine ⟨_, h2, ?_⟩
  exact ((mapChart_spec_S19 D ht x.1 x.2).2.1 _
    (D.collar_target_subset_domain _ _ h2)).symm.trans ((mapChart_S19 D ht x.1 x.2).right_inv h1)

theorem stageCollar_disjoint_S19 {x y : SliceIdx_S19 D} (hxy : x ≠ y) :
    Disjoint (stageCollar_S19 D ht x).target (stageCollar_S19 D ht y).target := by
  obtain ⟨i, q⟩ := x
  obtain ⟨j, r⟩ := y
  by_cases hij : i = j
  · subst hij
    have hqr : q ≠ r := fun h => hxy (by rw [h])
    refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
    obtain ⟨a, ha, rfl⟩ := stageCollar_target_subset_S19 D ht ⟨i, q⟩ hz1
    obtain ⟨b, hb, hab⟩ := stageCollar_target_subset_S19 D ht ⟨i, r⟩ hz2
    have ha' := D.collar_target_subset_domain i q ha
    have hb' := D.collar_target_subset_domain i r hb
    have : (⟨b, hb'⟩ : cores.domain i t) = ⟨a, ha'⟩ :=
      (cores.embedding i t ht).isEmbedding.injective hab
    have hba : b = a := congrArg Subtype.val this
    subst hba
    exact Set.disjoint_left.mp (levelSignedCollar_disjoint_C2a (D.base i) (S := D.level) hqr) ha hb
  · refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
    obtain ⟨a, ha, rfl⟩ := stageCollar_target_subset_S19 D ht ⟨i, q⟩ hz1
    obtain ⟨b, hb, hab⟩ := stageCollar_target_subset_S19 D ht ⟨j, r⟩ hz2
    exact Set.disjoint_left.mp (cores.disjoint t ht hij)
      ⟨a, D.collar_target_subset_domain i q ha, rfl⟩
      ⟨b, D.collar_target_subset_domain j r hb, hab⟩

/-- **The torus family of the slice (stage level).** All level-`S` cusp tori of all cores, pushed
to the stage by `cores.map · t`, as one disjoint family of signed collars; index `Σ i, Fin (base i).count`
up to the enumeration `Fintype.equivFin`. -/
def stageFamily_S19 : CollaredTorusFamily_C2a (postStage F.observation t).Carrier where
  count := Fintype.card (SliceIdx_S19 D)
  collar := fun k => stageCollar_S19 D ht ((Fintype.equivFin (SliceIdx_S19 D)).symm k)
  source_eq := fun k => stageCollar_source_S19 D ht _
  disjoint := fun k l hkl => stageCollar_disjoint_S19 D ht
    (fun h => hkl ((Equiv.injective _) h))

theorem zero_mem_source_S19 (p : Torus) : (p, (0 : ℝ)) ∈ signedCollarSource := by
  simp [signedCollarSource]

/-- The seam torus is the image under `cores.map` of the boundary torus of the truncation
`D.truncation` (the `LateCutFamily.truncation` of this slice). -/
theorem stageCollar_zero_S19 (x : SliceIdx_S19 D) (p : Torus) :
    stageCollar_S19 D ht x (p, 0) =
      cores.map x.1 t ht ((D.truncation x.1).cuspMap x.2 (p, halfZero)) := by
  rw [stageCollar_apply_S19 D ht x _ (zero_mem_source_S19 p)]
  exact congrArg _ (levelSignedCollar_zero_C2a (D.base x.1) D.two_le x.2 p)

/-- Signed convention (R1 7.3), positive side: `s ≥ 0` lies in the cusp beyond the truncation. -/
theorem stageCollar_pos_S19 (x : SliceIdx_S19 D) (p : Torus) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    stageCollar_S19 D ht x (p, s) =
      cores.map x.1 t ht ((D.truncation x.1).cuspMap x.2 (p, halfPoint s hs0)) := by
  have hsrc : (p, s) ∈ signedCollarSource := by
    simp only [signedCollarSource, mem_setOf_eq]; exact ⟨by linarith, hs1⟩
  rw [stageCollar_apply_S19 D ht x _ hsrc]
  exact congrArg _ (levelSignedCollar_pos_C2a (D.base x.1) D.two_le x.2 p s hs0)

/-- Signed convention, negative side: `s ≤ 0` lies in the core of the truncation. -/
theorem stageCollar_neg_mem_core_S19 (x : SliceIdx_S19 D) (p : Torus) (s : ℝ) (hs0 : s ≤ 0)
    (hs1 : -1 < s) :
    stageCollar_S19 D ht x (p, s) ∈
      cores.map x.1 t ht '' range (D.truncation x.1).inclusion := by
  have hsrc : (p, s) ∈ signedCollarSource := by
    simp only [signedCollarSource, mem_setOf_eq]; exact ⟨hs1, by linarith⟩
  rw [stageCollar_apply_S19 D ht x _ hsrc]
  refine ⟨_, ?_, rfl⟩
  rw [TruncatedCutData_IF4.truncation, truncationAtLevel_core_image_C1]
  refine Or.inr (mem_iUnion.mpr ⟨x.2, ⟨(p, halfSpaceOneLift (s + D.level)), ⟨trivial, ?_⟩, ?_⟩⟩)
  · change (halfSpaceOneLift (s + D.level)).val 0 ≤ D.level
    rw [lift_height_CPA2 (by linarith [D.two_le])]; linarith
  · exact (levelSignedCollar_apply_C2a (D.base x.1) D.level x.2 (p, s)).symm

/-- Truncation data from a buffered core: the level-`S` collars (heights `≤ S + 200`) of the base
truncations lie in the buffer ball `B(x, 2/accuracy)` (R1 1.2: `C(S_n) ∪ collar ⋐ B(x, n)` is more
than enough), hence in the domain by `buffer_domain`. -/
def TruncatedCutData_IF4.ofBuffered_S19 (B : BufferedPersistentCores F K) {t : ℝ}
    (ht : B.start ≤ t) (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℝ)
    (two_le : 2 ≤ level)
    (hball : ∀ i (q : Fin (base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ level + 200 →
      (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
        (2 * (B.accuracy t)⁻¹)) :
    TruncatedCutData_IF4 B.toCores t where
  base := base
  level := level
  two_le := two_le
  deep_domain := fun i q p hp => B.buffer_domain i t ht (hball i q p hp)

end GC.LongTime.Ch12
