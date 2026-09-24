/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Embedding.Compact
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

open Filter Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

theorem exists_smoothTwoSidedCollar_eq_of_localDiffeomorphAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {e : B → A} (he : Injective e) (Φ : B × ℝ → A) (hΦ : Continuous Φ)
    (hzero : ∀ x, Φ (x, 0) = e x)
    (hloc : ∀ x, IsLocalDiffeomorphAt (I.prod (modelWithCornersSelf ℝ ℝ)) J ∞ Φ (x, 0))
    (r : ℝ) (hr : 0 < r) :
    ∃ c : SmoothTwoSidedCollar I J e, c.radius ≤ r ∧
      ∀ p, c.toFun p = Φ (p.1, p.2.val) := by
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  have hinjloc : ∀ x, ∃ W ∈ nhds (x, (0 : ℝ)), InjOn Φ W := by
    intro x
    obtain ⟨φ, hx, heq⟩ := hloc x
    refine ⟨φ.source, φ.open_source.mem_nhds hx, ?_⟩
    intro p hp q hq hpq
    apply φ.toPartialEquiv.injOn hp hq
    rw [← heq hp, ← heq hq]
    exact hpq
  obtain ⟨U, hU, hinjU⟩ := exists_injOn_prod_nhds_of_compact hΦ
    (by simpa only [hzero] using he) hinjloc
  let good : Set (B × ℝ) := {p | IsLocalDiffeomorphAt IP J ∞ Φ p}
  have hgood (x : B) : good ∈ nhds (x, 0) := by
    obtain ⟨φ, hx, heq⟩ := hloc x
    filter_upwards [φ.open_source.mem_nhds hx] with p hp
    exact ⟨φ, hp, heq⟩
  have hprod : good ∈ nhdsSet (univ : Set B) ×ˢ nhds (0 : ℝ) :=
    isCompact_univ.mem_nhdsSet_prod_of_forall (fun x _ ↦ by
      simpa [nhds_prod_eq] using hgood x)
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hprod
  have hVall : ∀ x, x ∈ V := by
    have : V = univ := by simpa using hV
    simp [this]
  obtain ⟨δ, hδ, hδUW⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hW)
  let ε := min δ r
  have hε : 0 < ε := lt_min hδ hr
  have hinterval : Ioo (-ε) ε ⊆ U ∩ W := by
    have hδinterval : Ioo (-δ) δ ⊆ U ∩ W := by
      simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hδUW
    apply Subset.trans (b := Ioo (-δ) δ) ?_ hδinterval
    exact Ioo_subset_Ioo (neg_le_neg (min_le_left δ r)) (min_le_left δ r)
  let Z : TopologicalSpace.Opens (B × ℝ) :=
    ⟨univ ×ˢ Ioo (-ε) ε, isOpen_univ.prod isOpen_Ioo⟩
  let d : Diffeomorph IP IP (B × symmetricOpenInterval ε) Z ∞ := {
    toEquiv := {
      toFun := fun p ↦ ⟨(p.1, p.2.val), mem_univ _, p.2.property⟩
      invFun := fun p ↦ (p.val.1, ⟨p.val.2, p.property.2⟩)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff Z _).mp
      exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    contMDiff_invFun := by
      apply ContMDiff.prodMk
      · exact contMDiff_fst.comp contMDiff_subtype_val
      · apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval ε) _).mp
        exact contMDiff_snd.comp contMDiff_subtype_val }
  have hlocZ : IsLocalDiffeomorph IP J ∞ (fun p : Z ↦ Φ p) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open Z (fun p ↦
      hVW ⟨hVall p.val.1, (hinterval p.property.2).2⟩)
  let f : B × symmetricOpenInterval ε → A := fun p ↦ Φ (p.1, p.2.val)
  have hf : IsLocalDiffeomorph IP J ∞ f := by
    intro p
    exact (d.isLocalDiffeomorph p).comp J A (hlocZ (d p))
  have hfInj : Injective f := by
    intro p q hpq
    have heq : (p.1, p.2.val) = (q.1, q.2.val) := hinjU
      ⟨mem_univ _, (hinterval p.2.property).1⟩
      ⟨mem_univ _, (hinterval q.2.property).1⟩ hpq
    exact Prod.ext (congrArg (fun z : B × ℝ ↦ z.1) heq)
      (Subtype.ext (congrArg (fun z : B × ℝ ↦ z.2) heq))
  exact ⟨{
    radius := ε
    radius_pos := hε
    neighborhood := hf.image
    toDiffeomorph := diffeomorphRangeOfInjective hf hfInj
    zero_eq := fun x ↦ hzero x }, min_le_right δ r, fun _ ↦ rfl⟩

theorem exists_smoothTwoSidedCollar_of_localDiffeomorphAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {e : B → A} (he : Injective e) (Φ : B × ℝ → A) (hΦ : Continuous Φ)
    (hzero : ∀ x, Φ (x, 0) = e x)
    (hloc : ∀ x, IsLocalDiffeomorphAt (I.prod (modelWithCornersSelf ℝ ℝ)) J ∞ Φ (x, 0)) :
    Nonempty (SmoothTwoSidedCollar I J e) := by
  obtain ⟨c, _⟩ := exists_smoothTwoSidedCollar_eq_of_localDiffeomorphAt_zero he Φ hΦ hzero hloc 1 zero_lt_one
  exact ⟨c⟩

end DifferentialGeometry.Topology
