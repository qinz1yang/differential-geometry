/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Topology.MetricSpace.PartitionOfUnity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem image_frontier_of_compact {X Y : Type*} [TopologicalSpace X]
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
    rw [← image_frontier_of_compact hg hinj hopen (K.isCompact _)]
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

private theorem exists_continuous_pos_surjective_of_dist_lt {X : Type*} [MetricSpace X]
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

private def compactExhaustion_of_pieceTower {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}
    (T : LocallyFinitePieceTower n X U) (hU : IsOpen U) : CompactExhaustion U where
  toFun i := Subtype.val ⁻¹' T.N i
  isCompact' i := Topology.IsInducing.subtypeVal.isCompact_preimage' (T.isCompact i)
    (by simpa only [Subtype.range_coe] using T.subset i)
  subset_interior_succ' i := fun x hx =>
    preimage_interior_subset_interior_preimage continuous_subtype_val (T.subset_interior hU i hx)
  iUnion_eq' := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    have hx : (x : X) ∈ ⋃ i, T.N i := by
      rw [T.iUnion_eq]
      exact x.property
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, hi⟩

private def compactExhaustion_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (K : CompactExhaustion X) (e : X ≃ₜ Y) : CompactExhaustion Y where
  toFun i := e '' K i
  isCompact' i := (K.isCompact i).image e.continuous
  subset_interior_succ' i := by
    rw [← e.image_interior]
    exact image_mono (K.subset_interior_succ i)
  iUnion_eq' := by
    rw [← image_iUnion, K.iUnion_eq, image_univ, e.surjective.range_eq]

section HomeomorphInto

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

def IsPLHomeomorphInto (n : ℕ) {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] (f : M → N) (K : Set M) : Prop :=
  IsPLOn n n f K ∧ InjOn f K ∧
    ∀ y ∈ f '' K, ∃ g : N → M, IsPLWithinAt n n g (f '' K) y ∧ LeftInvOn g f K

variable {f : M → N} {K : Set M}

theorem IsPLHomeomorphInto.isPLOn (hf : IsPLHomeomorphInto n f K) : IsPLOn n n f K :=
  hf.1

theorem IsPLHomeomorphInto.injOn (hf : IsPLHomeomorphInto n f K) : InjOn f K :=
  hf.2.1

theorem IsPLHomeomorphInto.continuousOn (hf : IsPLHomeomorphInto n f K) : ContinuousOn f K :=
  fun x hx => (hf.isPLOn x hx).continuousWithinAt

theorem IsPLHomeomorphInto.isPLOn_inverse (hf : IsPLHomeomorphInto n f K)
    {g : N → M} (hg : LeftInvOn g f K) : IsPLOn n n g (f '' K) := by
  intro y hy
  obtain ⟨g', hg', hleft⟩ := hf.2.2 y hy
  apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem hg' _ hy
  rintro z ⟨x, hx, rfl⟩
  exact (hg hx).trans (hleft hx).symm

theorem isPLHomeomorphInto_iff_exists_inverse [Nonempty M] :
    IsPLHomeomorphInto n f K ↔
      IsPLOn n n f K ∧ InjOn f K ∧
        ∃ g : N → M, IsPLOn n n g (f '' K) ∧ LeftInvOn g f K := by
  constructor
  · intro hf
    have hleft := hf.injOn.leftInvOn_invFunOn
    exact ⟨hf.isPLOn, hf.injOn, Function.invFunOn f K, hf.isPLOn_inverse hleft, hleft⟩
  · rintro ⟨hf, hinj, g, hg, hleft⟩
    exact ⟨hf, hinj, fun y hy => ⟨g, hg y hy, hleft⟩⟩

theorem isPLHomeomorphInto_empty (f : M → N) : IsPLHomeomorphInto n f ∅ := by
  refine ⟨fun _ hx => False.elim hx, fun _ hx => False.elim hx, ?_⟩
  simp

theorem IsPLHomeomorphInto.isOpen_image (hf : IsPLHomeomorphInto n f K) (hK : IsOpen K) :
    IsOpen (f '' K) :=
  isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin n))
    hK hf.continuousOn hf.injOn

theorem IsPLHomeomorphInto.isOpenMap_domRestrict (hf : IsPLHomeomorphInto n f K)
    (hK : IsOpen K) : IsOpenMap (K.domRestrict f) := by
  intro W hW
  have hWK : Subtype.val '' W ⊆ K := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hopen := isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin n))
    (hK.isOpenMap_subtype_val W hW) (hf.continuousOn.mono hWK) (hf.injOn.mono hWK)
  change IsOpen ((fun x : K => f x) '' W)
  simpa only [image_image] using hopen

theorem IsPLHomeomorphInto.image_frontier [T2Space M] [T2Space N]
    (hf : IsPLHomeomorphInto n f K) (hK : IsOpen K) {P : Set M}
    (hP : IsCompact P) (hPK : P ⊆ K) : f '' frontier P = frontier (f '' P) := by
  let C : Set K := Subtype.val ⁻¹' P
  have hPrange : P ⊆ range (Subtype.val : K → M) := by
    simpa only [Subtype.range_coe] using hPK
  have hC : IsCompact C := Topology.IsInducing.subtypeVal.isCompact_preimage' hP hPrange
  have hCP : Subtype.val '' C = P := image_preimage_eq_of_subset hPrange
  have hsub := image_frontier_of_compact continuous_subtype_val Subtype.val_injective
    hK.isOpenMap_subtype_val hC
  rw [hCP] at hsub
  have hinj : Function.Injective (K.domRestrict f) := by
    intro x y hxy
    exact Subtype.ext (hf.injOn x.property y.property hxy)
  have hmain := image_frontier_of_compact hf.continuousOn.domRestrict hinj
    (hf.isOpenMap_domRestrict hK) hC
  have himage : (K.domRestrict f) '' C = f '' P := by
    rw [← hCP, image_image]
    rfl
  rw [himage] at hmain
  rw [← hsub, image_image]
  exact hmain

end HomeomorphInto

theorem IsPLHomeomorphInto.image_polyhedralBoundary {m : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [T2Space M] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    {f : M → N} {U P : Set M} (hf : IsPLHomeomorphInto (m + 1) f U) (hU : IsOpen U)
    (hP : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P) (hPU : P ⊆ U) :
    f '' polyhedralBoundary (m + 1) P hP = frontier (f '' P) := by
  rw [← frontier_eq_polyhedralBoundary hP]
  exact hf.image_frontier hU hP.isCompact hPU

def Moise352 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ (φ : M₁ → ℝ), ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x

theorem Moise352.exists_approx_of_isOpen {m : ℕ} (h352 : Moise352.{u} (m + 1))
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂]
    [HasGroupoid M₁ (plGroupoid (m + 1))] [HasGroupoid M₂ (plGroupoid (m + 1))]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto (m + 1) f U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  by_cases hne : U.Nonempty
  · let : Nonempty M₁ := ⟨hne.choose⟩
    exact h352 (isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen hU) hh φ hφ hpos
  · have hUempty : U = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst U
    exact ⟨h, isPLHomeomorphInto_empty h, fun _ hx => False.elim hx⟩

theorem Moise352.exists_approx_image_eq_of_isOpen {m : ℕ} (h352 : Moise352.{u} (m + 1))
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂]
    [HasGroupoid M₁ (plGroupoid (m + 1))] [HasGroupoid M₂ (plGroupoid (m + 1))]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto (m + 1) f U ∧ f '' U = h '' U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x := by
  classical
  by_cases hne : U.Nonempty
  · let : Nonempty M₁ := ⟨hne.choose⟩
    obtain ⟨T, hT⟩ := exists_locallyFinitePieceTower_of_isOpen (m := m) hU
    have hhcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
    have hhinj : InjOn h U := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hh.injective (show (U.domRestrict h) ⟨x, hx⟩ =
        (U.domRestrict h) ⟨y, hy⟩ from hxy))
    let V : Set M₂ := range (U.domRestrict h)
    have hV : IsOpen V := by
      change IsOpen (range (U.domRestrict h))
      rw [Set.range_domRestrict]
      exact isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin (m + 1))) hU hhcont hhinj
    let e : U ≃ₜ V := hh.toHomeomorph
    let : LocallyPathConnectedSpace M₂ :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (m + 1))) M₂
    let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
    let K : CompactExhaustion V := compactExhaustion_homeomorph (compactExhaustion_of_pieceTower T
        hU) e
    obtain ⟨δ, hδpos, hδ⟩ := exists_continuous_pos_surjective_of_dist_lt K
    obtain ⟨r, hrpos, hr⟩ := exists_continuous_pos_ball_subset_open hV
    let ε : M₁ → ℝ := fun x => if hx : x ∈ U then
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
    obtain ⟨f, hf, hclose⟩ := h352 ⟨T, hT⟩ hh ε hεcont hεpos
    have hsmall : ∀ x : U, dist (f x) (h x) < min (φ x) (min (r (e x)) (δ (e x))) := by
      intro x
      rw [← hε]
      exact hclose x x.property
    have hfV : ∀ x : U, f x ∈ V := by
      intro x
      apply hr (e x)
      exact Metric.mem_ball.mpr ((hsmall x).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    let F : U → V := fun x => ⟨f x, hfV x⟩
    have hFcont : Continuous F := hf.continuousOn.domRestrict.subtype_mk hfV
    have hFinj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      exact hf.injOn x.property y.property (congrArg Subtype.val hxy)
    have hFopen : IsOpenMap F := (hf.isOpenMap_domRestrict hU).codRestrict hfV
    let g : V → V := F ∘ e.symm
    have hg : Function.Surjective g := by
      apply hδ g (hFcont.comp e.symm.continuous) (hFinj.comp e.symm.injective)
        (hFopen.comp e.symm.isOpenMap)
      intro y
      have hbound := (hsmall (e.symm y)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
      change dist (F (e.symm y)) (e (e.symm y)) < δ (e (e.symm y)) at hbound
      change dist (F (e.symm y)) y < δ y
      simpa only [e.apply_symm_apply] using hbound
    refine ⟨f, hf, ?_, fun x hx => (hsmall ⟨x, hx⟩).trans_le (min_le_left _ _)⟩
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
  · have hUempty : U = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst U
    exact ⟨h, isPLHomeomorphInto_empty h, rfl, fun _ hx => False.elim hx⟩

theorem exists_plh_approx_of_isOpen (h352 : Moise352.{u} 3)
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ f '' U = h '' U ∧
      ∀ x ∈ U, dist (f x) (h x) < φ x :=
  h352.exists_approx_image_eq_of_isOpen hU hh φ hφ hpos

end DifferentialGeometry.Topology.PiecewiseLinear
