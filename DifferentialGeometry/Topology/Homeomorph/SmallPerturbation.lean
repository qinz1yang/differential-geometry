import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.PartitionOfUnity
open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem image_frontier_of_continuous_injective_isOpenMap_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {g : X → Y} (hg : Continuous g)
    (hinj : Function.Injective g) (hopen : IsOpenMap g) {C : Set X} (hC : IsCompact C) :
    g '' frontier C = frontier (g '' C) := by
  have hpre : g ⁻¹' frontier (g '' C) = frontier C := by
    rw [hopen.preimage_frontier_eq_frontier_preimage hg, preimage_image_eq _ hinj]
  rw [← hpre, image_preimage_eq_of_subset]
  exact (hC.image hg).isClosed.frontier_subset.trans (image_subset_range _ _)

private theorem locallyFinite_frontier_exhaustion {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) : LocallyFinite (fun i => frontier (K (i + 1))) := by
  intro x
  obtain ⟨k, hk⟩ := K.exists_mem x
  refine ⟨interior (K (k + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ k hk), ?_⟩
  apply (Set.finite_Iio (k + 1)).subset
  rintro i ⟨y, hy, hyk⟩
  change i < k + 1
  by_contra hle
  have hki : k + 1 ≤ i + 1 := by omega
  exact hy.2 (interior_mono (K.subset hki) hyk)

private theorem exists_continuous_pos_ball_subset_component {X : Type*} [MetricSpace X]
    [LocallyConnectedSpace X] :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧
      ∀ x, Metric.closedBall x (δ x) ⊆ connectedComponent x := by
  let C : ConnectedComponents X → Set X := fun c => ConnectedComponents.mk ⁻¹' {c}
  have hC : ∀ c, IsClopen (C c) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simpa only [C, connectedComponents_preimage_singleton] using
      (isClopen_connectedComponent (x := x))
  have hfin : LocallyFinite C := by
    intro x
    refine ⟨C (ConnectedComponents.mk x), (hC _).isOpen.mem_nhds rfl, ?_⟩
    apply (finite_singleton (ConnectedComponents.mk x)).subset
    rintro c ⟨y, hyc, hyx⟩
    exact hyc.symm.trans hyx
  obtain ⟨δ, hδpos, hδ⟩ := Metric.exists_continuous_real_forall_closedBall_subset
    (fun c => (hC c).isClosed) (fun c => (hC c).isOpen) (fun _ => Subset.rfl) hfin
  refine ⟨δ, hδpos, fun x => ?_⟩
  simpa only [C, connectedComponents_preimage_singleton] using hδ (ConnectedComponents.mk x) x rfl

private theorem surjective_of_exhaustion_frontier_disjoint {X : Type*} [TopologicalSpace X]
    [T2Space X] (K : CompactExhaustion X) {g : X → X} (hg : Continuous g)
    (hinj : Function.Injective g) (hopen : IsOpenMap g)
    (hjoined : ∀ x, Joined x (g x))
    (hfrontier : ∀ i, Disjoint (g '' frontier (K (i + 1))) (K i)) :
    Function.Surjective g := by
  intro y
  let p : Path y (g y) := (hjoined y).somePath
  obtain ⟨i, hi⟩ := K.exists_superset_of_isCompact (isCompact_range p.continuous)
  have hclosed : IsClosed (g '' K (i + 1)) := ((K.isCompact _).image hg).isClosed
  have hav : Disjoint (range p) (frontier (g '' K (i + 1))) := by
    rw [← image_frontier_of_continuous_injective_isOpenMap_of_isCompact hg hinj hopen (K.isCompact _)]
    exact (hfrontier i).symm.mono_left hi
  have hcover : range p ⊆ interior (g '' K (i + 1)) ∪ (g '' K (i + 1))ᶜ := by
    intro z hz
    by_cases hgz : z ∈ g '' K (i + 1)
    · left
      by_contra hn
      exact Set.disjoint_left.mp hav hz (hclosed.frontier_eq ▸ ⟨hgz, hn⟩)
    · exact Or.inr hgz
  have hbase : g y ∈ interior (g '' K (i + 1)) := by
    rcases hcover p.target_mem_range with hmem | hmem
    · exact hmem
    · exact False.elim (hmem ⟨y, K.subset_succ i (hi p.source_mem_range), rfl⟩)
  have hsub := (isConnected_range p.continuous).isPreconnected.subset_left_of_subset_union
    isOpen_interior hclosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover
    ⟨g y, p.target_mem_range, hbase⟩
  obtain ⟨x, _, hx⟩ := interior_subset (hsub p.source_mem_range)
  exact ⟨x, hx⟩

theorem exists_continuous_pos_surjective_of_dist_lt {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (K : CompactExhaustion X) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧
      ∀ g : X → X, Continuous g → Function.Injective g → IsOpenMap g →
        (∀ x, dist (g x) x < δ x) → Function.Surjective g := by
  have hdis : ∀ i, frontier (K (i + 1)) ⊆ (K i)ᶜ := by
    intro i x hx hxi
    exact hx.2 (K.subset_interior_succ i hxi)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.exists_continuous_real_forall_closedBall_subset
    (fun i => isClosed_frontier (s := K (i + 1)))
    (fun i => (K.isCompact i).isClosed.isOpen_compl) hdis (locallyFinite_frontier_exhaustion K)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_continuous_pos_ball_subset_component (X := X)
  refine ⟨⟨fun x => min (δ₁ x) (δ₂ x), δ₁.continuous.min δ₂.continuous⟩,
    fun x => lt_min (hδ₁pos x) (hδ₂pos x), ?_⟩
  intro g hg hinj hopen hclose
  apply surjective_of_exhaustion_frontier_disjoint K hg hinj hopen
  · intro x
    have hx := hδ₂ x (Metric.mem_closedBall.mpr ((hclose x).trans_le (min_le_right _ _)).le)
    have hcomp : connectedComponent x = connectedComponent (g x) := connectedComponent_eq hx
    exact (connectedComponent_eq_iff_joined x (g x)).mp hcomp
  · intro i
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ hz
    exact hδ₁ i x hx (Metric.mem_closedBall.mpr ((hclose x).trans_le (min_le_left _ _)).le) hz

private theorem exists_continuous_pos_ball_subset_open {Y : Type*} [MetricSpace Y]
    {V : Set Y} (hV : IsOpen V) :
    ∃ δ : C(V, ℝ), (∀ x, 0 < δ x) ∧ ∀ x : V, Metric.ball (x : Y) (δ x) ⊆ V := by
  by_cases hne : Vᶜ.Nonempty
  · refine ⟨⟨fun x => Metric.infDist (x : Y) Vᶜ,
      (Metric.continuous_infDist_pt Vᶜ).comp continuous_subtype_val⟩, ?_, ?_⟩
    · intro x
      exact (hV.isClosed_compl.notMem_iff_infDist_pos hne).mp (not_not.mpr x.property)
    · intro x
      exact Metric.ball_infDist_compl_subset
  · have hVu : ∀ y : Y, y ∈ V := by
      intro y
      by_contra hy
      exact hne ⟨y, hy⟩
    exact ⟨⟨fun _ => 1, continuous_const⟩, fun _ => zero_lt_one, fun _ _ _ => hVu _⟩

private def compactExhaustionHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (K : CompactExhaustion X) (e : X ≃ₜ Y) : CompactExhaustion Y where
  toFun i := e '' K i
  isCompact' i := (K.isCompact i).image e.continuous
  subset_interior_succ' i := by
    rw [← e.image_interior]
    exact image_mono (K.subset_interior_succ i)
  iUnion_eq' := by
    rw [← image_iUnion, K.iUnion_eq, image_univ, e.surjective.range_eq]

theorem exists_continuousOn_pos_image_eq_of_dist_lt
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [LocallyPathConnectedSpace Y]
    {U : Set X} {h : X → Y} (hh : Topology.IsEmbedding (U.domRestrict h))
    (himage : IsOpen (h '' U)) (K : CompactExhaustion U)
    (φ : X → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ ε : X → ℝ, ContinuousOn ε U ∧ (∀ x ∈ U, 0 < ε x) ∧
      (∀ x ∈ U, ε x ≤ φ x) ∧
      ∀ f : X → Y, ContinuousOn f U → InjOn f U → IsOpenMap (U.domRestrict f) →
        (∀ x ∈ U, dist (f x) (h x) < ε x) → f '' U = h '' U := by
  classical
  let V : Set Y := range (U.domRestrict h)
  have hV : IsOpen V := by
    simpa only [V, Set.range_domRestrict] using himage
  let e : U ≃ₜ V := hh.toHomeomorph
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  let L : CompactExhaustion V := compactExhaustionHomeomorph K e
  obtain ⟨δ, hδpos, hδ⟩ := exists_continuous_pos_surjective_of_dist_lt L
  obtain ⟨r, hrpos, hr⟩ := exists_continuous_pos_ball_subset_open hV
  let ε : X → ℝ := fun x => if hx : x ∈ U then
    min (φ x) (min (r (e ⟨x, hx⟩)) (δ (e ⟨x, hx⟩))) else 0
  have hε : ∀ x : U, ε x = min (φ x) (min (r (e x)) (δ (e x))) := by
    intro x
    simp only [ε, dite_eq_left x.property]
  have hεcont : ContinuousOn ε U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : U.domRestrict ε = fun x : U => min (φ x) (min (r (e x)) (δ (e x))) := funext hε
    rw [heq]
    exact hφ.domRestrict.min ((r.continuous.comp e.continuous).min (δ.continuous.comp
        e.continuous))
  have hεpos : ∀ x ∈ U, 0 < ε x := by
    intro x hx
    rw [hε ⟨x, hx⟩]
    exact lt_min (hpos x hx) (lt_min (hrpos _) (hδpos _))
  refine ⟨ε, hεcont, hεpos, ?_, ?_⟩
  · intro x hx
    rw [hε ⟨x, hx⟩]
    exact min_le_left _ _
  · intro f hfcont hfinj hfopen hclose
    have hsmall : ∀ x : U, dist (f x) (h x) < min (φ x) (min (r (e x)) (δ (e x))) := by
      intro x
      rw [← hε]
      exact hclose x x.property
    have hfV : ∀ x : U, f x ∈ V := by
      intro x
      apply hr (e x)
      exact Metric.mem_ball.mpr ((hsmall x).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    let F : U → V := fun x => ⟨f x, hfV x⟩
    have hFcont : Continuous F := hfcont.domRestrict.subtype_mk hfV
    have hFinj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      exact hfinj x.property y.property (congrArg Subtype.val hxy)
    have hFopen : IsOpenMap F := hfopen.codRestrict hfV
    let g : V → V := F ∘ e.symm
    have hg : Function.Surjective g := by
      apply hδ g (hFcont.comp e.symm.continuous) (hFinj.comp e.symm.injective)
        (hFopen.comp e.symm.isOpenMap)
      intro y
      have hbound := (hsmall (e.symm y)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
      change dist (F (e.symm y)) (e (e.symm y)) < δ (e (e.symm y)) at hbound
      change dist (F (e.symm y)) y < δ y
      simpa only [e.apply_symm_apply] using hbound
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hy := hfV ⟨x, hx⟩
      change f x ∈ range (U.domRestrict h) at hy
      rwa [Set.range_domRestrict] at hy
    · intro y hy
      have hyV : y ∈ V := by
        change y ∈ range (U.domRestrict h)
        rwa [Set.range_domRestrict]
      obtain ⟨z, hz⟩ := hg ⟨y, hyV⟩
      exact ⟨e.symm z, (e.symm z).property, congrArg Subtype.val hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
