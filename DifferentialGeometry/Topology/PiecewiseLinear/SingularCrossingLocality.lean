/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_preimage_mem_nhdsWithin {E F : Type*} [TopologicalSpace E] {f : E → F}
    {P C : Set E} {V : Set F} {c : E} (hC : C ∈ 𝓝[P] c) : C ∩ f ⁻¹' V ∈ 𝓝[P ∩ f ⁻¹' V] c :=
  Filter.inter_mem (nhdsWithin_mono c inter_subset_left hC)
    (Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right)

theorem exists_mem_nhds_inter_subset_inter_preimage {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] {g : E → F} {P : Set E} (hg : ContinuousOn g P) {V : Set F}
    (hV : IsOpen V) {a : E} (ha : a ∈ P ∩ g ⁻¹' V) : ∃ W ∈ 𝓝 a, P ∩ W ⊆ P ∩ g ⁻¹' V := by
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.mp hg V hV
  exact ⟨u, hu.mem_nhds (hueq.subset ⟨ha.2, ha.1⟩).1,
    fun x hx => ⟨hx.1, (hueq.superset ⟨hx.2, hx.1⟩).1⟩⟩

theorem eventually_inter_preimage_singleton_subset {E F : Type*} [TopologicalSpace F]
    {g : E → F} (P : Set E) {V : Set F} (hV : IsOpen V) {y : F} (hy : y ∈ V) :
    ∀ᶠ z in 𝓝 y, P ∩ g ⁻¹' {z} ⊆ P ∩ g ⁻¹' V := by
  filter_upwards [hV.mem_nhds hy] with z hz x hx
  exact ⟨hx.1, show g x ∈ V from (mem_singleton_iff.mp hx.2).symm ▸ hz⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isPLHomeomorphOn_inter_preimage_of_isOpen {f : E → F} {A : Set E}
    (hf : IsPLHomeomorphOn f A (f '' A)) {V : Set F} (hV : IsOpen V) :
    IsPLHomeomorphOn f (A ∩ f ⁻¹' V) (f '' (A ∩ f ⁻¹' V)) := by
  have hinj : InjOn f (A ∩ f ⁻¹' V) := hf.bijOn.injOn.mono inter_subset_left
  refine ⟨hinj.bijOn_image, ?_, ?_⟩
  · simpa only [Function.id_comp] using
      (isPiecewiseAffineOn_id (u := V) hV).comp hf.isPiecewiseAffineOn
  · rw [image_inter_preimage]
    refine (hf.isPiecewiseAffineOn_invFunOn.inter_of_isOpen hV).congr ?_
    rintro z ⟨⟨x, hx, rfl⟩, hfx⟩
    rw [hinj.leftInvOn_invFunOn ⟨hx, hfx⟩, hf.bijOn.injOn.leftInvOn_invFunOn hx]

theorem HasPLDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E} {y : F}
    {V : Set F} (hV : IsOpen V) (hy : y ∈ V) (h : HasPLDoubleCrossingAt f P y) :
    HasPLDoubleCrossingAt f (P ∩ f ⁻¹' V) y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := h
  have haV : f a ∈ V := hfa.symm ▸ hy
  have hbV : f b ∈ V := hfb.symm ▸ hy
  refine ⟨a, b, A ∩ f ⁻¹' V, B ∩ f ⁻¹' V, ⟨ha, haV⟩, ⟨hb, hbV⟩, hfa, hfb,
    inter_subset_inter hAP Subset.rfl, inter_subset_inter hBP Subset.rfl,
    hdis.mono inter_subset_left inter_subset_left, inter_preimage_mem_nhdsWithin hA,
    inter_preimage_mem_nhdsWithin hB, isPLHomeomorphOn_inter_preimage_of_isOpen hfA hV,
    isPLHomeomorphOn_inter_preimage_of_isOpen hfB hV, ?_, ?_⟩
  · rw [image_inter_preimage, image_inter_preimage]
    apply hcross.congr <;>
      filter_upwards [hV.mem_nhds hy] with z hz <;>
        simp only [mem_inter_iff, hz, and_true]
  · filter_upwards [hcov] with z hz x hx
    exact (hz ⟨hx.1.1, hx.2⟩).elim (fun hm => Or.inl ⟨hm, hx.1.2⟩)
      (fun hm => Or.inr ⟨hm, hx.1.2⟩)

theorem HasPLBoundaryDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E}
    {Mb : Set F} {y : F} {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLBoundaryDoubleCrossingAt f P Mb y) :
    HasPLBoundaryDoubleCrossingAt f (P ∩ f ⁻¹' V) Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := h
  have haV : f a ∈ V := hfa.symm ▸ hy
  have hbV : f b ∈ V := hfb.symm ▸ hy
  refine ⟨a, b, A ∩ f ⁻¹' V, B ∩ f ⁻¹' V, ⟨ha, haV⟩, ⟨hb, hbV⟩, hfa, hfb,
    inter_subset_inter hAP Subset.rfl, inter_subset_inter hBP Subset.rfl,
    hdis.mono inter_subset_left inter_subset_left, inter_preimage_mem_nhdsWithin hA,
    inter_preimage_mem_nhdsWithin hB, isPLHomeomorphOn_inter_preimage_of_isOpen hfA hV,
    isPLHomeomorphOn_inter_preimage_of_isOpen hfB hV, ?_, ?_⟩
  · rw [image_inter_preimage, image_inter_preimage]
    apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) <;>
      filter_upwards [hV.mem_nhds hy] with z hz <;>
        simp only [mem_inter_iff, hz, and_true]
  · filter_upwards [hcov] with z hz x hx
    exact (hz ⟨hx.1.1, hx.2⟩).elim (fun hm => Or.inl ⟨hm, hx.1.2⟩)
      (fun hm => Or.inr ⟨hm, hx.1.2⟩)

theorem HasPLNormalDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E}
    {Bd : Set F} {y : F} {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) :
    HasPLNormalDoubleCrossingAt f (P ∩ f ⁻¹' V) Bd y := by
  rcases h with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.inter_preimage_of_isOpen hV hy⟩
  · exact Or.inr ⟨hyB, hcross.inter_preimage_of_isOpen hV hy⟩

theorem HasPLDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E} {y : F}
    (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLDoubleCrossingAt f P y) : HasPLDoubleCrossingAt g P' y := by
  have h₁ : HasPLDoubleCrossingAt g (P ∩ f ⁻¹' V) y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

theorem HasPLBoundaryDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E}
    {Mb : Set F} {y : F} (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLBoundaryDoubleCrossingAt f P Mb y) :
    HasPLBoundaryDoubleCrossingAt g P' Mb y := by
  have h₁ : HasPLBoundaryDoubleCrossingAt g (P ∩ f ⁻¹' V) Mb y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

theorem HasPLNormalDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E}
    {Bd : Set F} {y : F} (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt g P' Bd y := by
  have h₁ : HasPLNormalDoubleCrossingAt g (P ∩ f ⁻¹' V) Bd y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

theorem HasPLNormalDoubleCrossingAt.of_eqOn_of_isOpen_self {f : E → F} {P : Set E}
    {Bd : Set F} {y : F} (hf : ContinuousOn f P) {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt f P Bd y :=
  h.of_eqOn_of_isOpen hf hV hy rfl fun _ _ => rfl

theorem HasPLNormalDoubleCrossingAt.of_eqOn_sdiff_preimage_of_isClosed {f g : E → F}
    {P : Set E} {Bd C : Set F} {y : F} (hg : ContinuousOn g P) (hC : IsClosed C)
    (hy : y ∉ C) (hfg : EqOn f g (P \ f ⁻¹' C)) (hmaps : MapsTo g (P ∩ f ⁻¹' C) C)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt g P Bd y := by
  have hdiff : P ∩ f ⁻¹' Cᶜ = P \ f ⁻¹' C := by rw [preimage_compl, Set.sdiff_eq]
  have hfg' : EqOn f g (P ∩ f ⁻¹' Cᶜ) := by rw [hdiff]; exact hfg
  have hPP' : P ∩ f ⁻¹' Cᶜ = P ∩ g ⁻¹' Cᶜ := by
    refine Subset.antisymm (fun x hx => ⟨hx.1, ?_⟩) (fun x hx => ⟨hx.1, ?_⟩)
    · rw [mem_preimage, ← hfg' hx]
      exact hx.2
    · have hgx : g x ∉ C := hx.2
      exact show f x ∉ C from fun hxC => hgx (hmaps ⟨hx.1, hxC⟩)
  exact h.of_eqOn_of_isOpen hg hC.isOpen_compl (show y ∈ Cᶜ from hy) hPP' hfg'

theorem exists_isOpen_inter_preimage_eq_of_eventually_eq_fiber {α β : Type*}
    [TopologicalSpace β] {f g : α → β} {P Q : Set α} {y : β}
    (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z}) :
    ∃ U : Set β, IsOpen U ∧ y ∈ U ∧ P ∩ f ⁻¹' U = Q ∩ g ⁻¹' U ∧ EqOn f g (P ∩ f ⁻¹' U) := by
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hfiber
  have hforward : ∀ x ∈ P, f x ∈ U → x ∈ Q ∧ g x = f x := fun x hx hfx =>
    (hUsub hfx).subset ⟨hx, rfl⟩
  have hback : ∀ x ∈ Q, g x ∈ U → x ∈ P ∧ f x = g x := fun x hx hgx =>
    (hUsub hgx).superset ⟨hx, rfl⟩
  refine ⟨U, hU, hyU, Subset.antisymm (fun x hx => ⟨(hforward x hx.1 hx.2).1, ?_⟩)
    (fun x hx => ⟨(hback x hx.1 hx.2).1, ?_⟩), fun x hx => (hforward x hx.1 hx.2).2.symm⟩
  · change g x ∈ U
    rw [(hforward x hx.1 hx.2).2]
    exact hx.2
  · change f x ∈ U
    rw [(hback x hx.1 hx.2).2]
    exact hx.2

theorem HasPLDoubleCrossingAt.of_eventually_eq_fiber {f g : E → F} {P Q : Set E} {y : F}
    (hg : ContinuousOn g Q) (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (h : HasPLDoubleCrossingAt f P y) : HasPLDoubleCrossingAt g Q y := by
  obtain ⟨U, hU, hyU, hPQ, hfg⟩ := exists_isOpen_inter_preimage_eq_of_eventually_eq_fiber hfiber
  exact h.of_eqOn_of_isOpen hg hU hyU hPQ hfg

theorem HasPLBoundaryDoubleCrossingAt.of_eventually_eq_fiber {f g : E → F} {P Q : Set E}
    {Mb : Set F} {y : F} (hg : ContinuousOn g Q)
    (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (h : HasPLBoundaryDoubleCrossingAt f P Mb y) : HasPLBoundaryDoubleCrossingAt g Q Mb y := by
  obtain ⟨U, hU, hyU, hPQ, hfg⟩ := exists_isOpen_inter_preimage_eq_of_eventually_eq_fiber hfiber
  exact h.of_eqOn_of_isOpen hg hU hyU hPQ hfg

theorem HasPLNormalDoubleCrossingAt.of_eventually_eq_fiber {f g : E → F} {P Q : Set E}
    {Bd : Set F} {y : F} (hg : ContinuousOn g Q)
    (hfiber : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} = Q ∩ g ⁻¹' {z})
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt g Q Bd y := by
  obtain ⟨U, hU, hyU, hPQ, hfg⟩ := exists_isOpen_inter_preimage_eq_of_eventually_eq_fiber hfiber
  exact h.of_eqOn_of_isOpen hg hU hyU hPQ hfg

theorem eventually_eq_fiber_comp_openPartialHomeomorph {X α : Type*} [TopologicalSpace X]
    {d : ℕ} (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d))) {f g : α → X} (P : Set α)
    {y : X} (hy : y ∈ e.source) (hfiber : ∀ᶠ z in 𝓝 y, f ⁻¹' {z} = g ⁻¹' {z}) :
    ∀ᶠ z in 𝓝 (e y), (P ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {z} =
      (P ∩ g ⁻¹' e.source) ∩ (e ∘ g) ⁻¹' {z} := by
  have hback : ∀ᶠ z in 𝓝 (e y), f ⁻¹' {e.symm z} = g ⁻¹' {e.symm z} := by
    have h := (e.continuousAt_symm (e.map_source hy))
      (show ∀ᶠ z in 𝓝 (e.symm (e y)), f ⁻¹' {z} = g ⁻¹' {z} from by rwa [e.left_inv hy])
    exact h
  filter_upwards [e.open_target.mem_nhds (e.map_source hy), hback] with z hz heq
  have hiff (u : α → X) (x : α) :
      x ∈ (P ∩ u ⁻¹' e.source) ∩ (e ∘ u) ⁻¹' {z} ↔ x ∈ P ∧ u x = e.symm z := by
    constructor
    · rintro ⟨⟨hxP, hxu⟩, hxz⟩
      refine ⟨hxP, ?_⟩
      have hxz' : e (u x) = z := hxz
      rw [← hxz', e.left_inv hxu]
    · rintro ⟨hxP, hxu⟩
      refine ⟨⟨hxP, ?_⟩, ?_⟩
      · change u x ∈ e.source
        rw [hxu]
        exact e.map_target hz
      · change e (u x) = z
        rw [hxu, e.right_inv hz]
  ext x
  rw [hiff f, hiff g]
  exact and_congr_right fun _ => Set.ext_iff.mp heq x

theorem hasPLDoubleCrossingAt_comp_openPartialHomeomorph_iff_of_eventually_eq_fiber
    {X : Type*} [TopologicalSpace X] {d : ℕ}
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin d))) {f g : E → X} {P : Set E}
    (hf : ContinuousOn f P) (hg : ContinuousOn g P) {y : X} (hy : y ∈ e.source)
    (hfiber : ∀ᶠ z in 𝓝 y, f ⁻¹' {z} = g ⁻¹' {z}) :
    (HasPLDoubleCrossingAt (e ∘ f) (P ∩ f ⁻¹' e.source) (e y) ↔
      HasPLDoubleCrossingAt (e ∘ g) (P ∩ g ⁻¹' e.source) (e y)) ∧
      ∀ M, HasPLBoundaryDoubleCrossingAt (e ∘ f) (P ∩ f ⁻¹' e.source) M (e y) ↔
        HasPLBoundaryDoubleCrossingAt (e ∘ g) (P ∩ g ⁻¹' e.source) M (e y) := by
  have heq := eventually_eq_fiber_comp_openPartialHomeomorph e P hy hfiber
  have heq' := heq.mono fun _ h => h.symm
  have hfc : ContinuousOn (e ∘ f) (P ∩ f ⁻¹' e.source) :=
    e.continuousOn.comp (hf.mono inter_subset_left) (fun _ hx => hx.2)
  have hgc : ContinuousOn (e ∘ g) (P ∩ g ⁻¹' e.source) :=
    e.continuousOn.comp (hg.mono inter_subset_left) (fun _ hx => hx.2)
  exact ⟨⟨HasPLDoubleCrossingAt.of_eventually_eq_fiber hgc heq,
    HasPLDoubleCrossingAt.of_eventually_eq_fiber hfc heq'⟩,
    fun _ => ⟨HasPLBoundaryDoubleCrossingAt.of_eventually_eq_fiber hgc heq,
      HasPLBoundaryDoubleCrossingAt.of_eventually_eq_fiber hfc heq'⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
