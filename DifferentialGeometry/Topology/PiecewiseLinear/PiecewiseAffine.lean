/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Polytope
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def IsPiecewiseAffineWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F),
    (∀ i, IsHPolytope (C i) ∧ C i ⊆ s ∧ EqOn f (A i) (C i)) ∧ (⋃ i, C i) ∈ 𝓝[s] x

def IsPiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x

theorem interior_iUnion_eq_empty_of_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {C : ι → Set X} (hC : ∀ i, IsClosed (C i)) (h : ∀ i, interior (C i) = ∅) :
    interior (⋃ i, C i) = ∅ := by
  classical
  cases nonempty_fintype ι
  have key : ∀ s : Finset ι, interior (⋃ i ∈ s, C i) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hC a) ih, h a]
  simpa using key Finset.univ

theorem iUnion_interior_nonempty_mem_nhds {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {C : ι → Set X} (hC : ∀ i, IsClosed (C i)) {x : X} (hx : (⋃ i, C i) ∈ 𝓝 x) :
    (⋃ i : {i // (interior (C i)).Nonempty}, C i) ∈ 𝓝 x := by
  have hK : IsClosed (⋃ i : {i // (interior (C i)).Nonempty}, C i) :=
    isClosed_iUnion_of_finite fun i => hC i
  have hD : interior (⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i) = ∅ :=
    interior_iUnion_eq_empty_of_finite (fun i => hC i)
      fun i => Set.not_nonempty_iff_eq_empty.mp i.2
  obtain ⟨N, hNsub, hNopen, hxN⟩ := mem_nhds_iff.mp hx
  refine mem_nhds_iff.mpr ⟨N, ?_, hNopen, hxN⟩
  intro y hy
  by_contra hyK
  have hW : IsOpen (N \ ⋃ i : {i // (interior (C i)).Nonempty}, C i) := hNopen.sdiff hK
  have hWsub : N \ (⋃ i : {i // (interior (C i)).Nonempty}, C i) ⊆
      ⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hNsub hz.1)
    by_cases hint : (interior (C i)).Nonempty
    · exact absurd (mem_iUnion.mpr ⟨⟨i, hint⟩, hi⟩) hz.2
    · exact mem_iUnion.mpr ⟨⟨i, hint⟩, hi⟩
  have hmem : y ∈ interior (⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i) :=
    interior_maximal hWsub hW ⟨hy, hyK⟩
  rw [hD] at hmem
  exact hmem

theorem linear_injective_of_injOn_of_interior_nonempty {A : E →ᵃ[ℝ] F} {C : Set E}
    (hA : InjOn A C) (hC : (interior C).Nonempty) : Function.Injective A.linear := by
  obtain ⟨x₀, hx₀⟩ := hC
  intro v w hvw
  have hker : A.linear (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  by_contra hne
  have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hcont : ContinuousAt (fun t : ℝ => x₀ + t • (v - w)) 0 := by fun_prop
  have hmem : {t : ℝ | x₀ + t • (v - w) ∈ interior C} ∈ 𝓝 (0 : ℝ) :=
    hcont.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  set t : ℝ := ε / 2 with ht_def
  have htne : t ≠ 0 := by positivity
  have ht : x₀ + t • (v - w) ∈ interior C := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hval : A (x₀ + t • (v - w)) = A x₀ := by
    have h := A.map_vadd x₀ (t • (v - w))
    rw [vadd_eq_add, vadd_eq_add, map_smul, hker, smul_zero, zero_add, add_comm] at h
    exact h
  have heq : x₀ + t • (v - w) = x₀ := hA (interior_subset ht) (interior_subset hx₀) hval
  have hzero : t • (v - w) = 0 := by simpa using heq
  rcases smul_eq_zero.mp hzero with h | h
  · exact htne h
  · exact hne' h

namespace IsPiecewiseAffineWithinAt

variable {f : E → F} {s t : Set E} {x : E}

theorem congr (hf : IsPiecewiseAffineWithinAt f s x) {g : E → F} (hfg : EqOn g f s) :
    IsPiecewiseAffineWithinAt g s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  exact ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1,
    fun y hy => (hfg ((hC i).2.1 hy)).trans ((hC i).2.2 hy)⟩, hCx⟩

theorem inter_of_mem_nhds [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x)
    (ht : t ∈ 𝓝 x) : IsPiecewiseAffineWithinAt f (s ∩ t) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  have := hι
  obtain ⟨Q, hQ, hQt, hQx⟩ := exists_isHPolytope_subset_mem_nhds ht
  refine ⟨ι, inferInstance, fun i => C i ∩ Q, A, fun i => ⟨(hC i).1.inter hQ,
    inter_subset_inter (hC i).2.1 hQt, (hC i).2.2.mono inter_subset_left⟩, ?_⟩
  rw [← iUnion_inter]
  exact inter_mem (nhdsWithin_mono x inter_subset_left hCx) (mem_nhdsWithin_of_mem_nhds hQx)

theorem of_inter_of_mem_nhds (hf : IsPiecewiseAffineWithinAt f (s ∩ t) x) (ht : t ∈ 𝓝 x) :
    IsPiecewiseAffineWithinAt f s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1.trans inter_subset_left, (hC i).2.2⟩, ?_⟩
  rwa [nhdsWithin_restrict' s ht]

theorem continuousWithinAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x) :
    ContinuousWithinAt f s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  have := hι
  have hsub : (⋃ i, C i) ⊆ s := iUnion_subset fun i => (hC i).2.1
  have heq : 𝓝[s] x = 𝓝[⋃ i, C i] x := by
    rw [← nhdsWithin_inter_of_mem' hCx, inter_eq_right.mpr hsub]
  have hi : ∀ i, ContinuousWithinAt f (C i) x := by
    intro i
    by_cases hxi : x ∈ C i
    · exact ((A i).continuous_of_finiteDimensional.continuousWithinAt).congr
        (fun y hy => (hC i).2.2 hy) ((hC i).2.2 hxi)
    · exact continuousWithinAt_of_notMem_closure (by rwa [(hC i).1.isClosed.closure_eq])
  change Tendsto f (𝓝[s] x) (𝓝 (f x))
  rw [heq, nhdsWithin_iUnion, tendsto_iSup]
  exact hi

theorem continuousAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x)
    (hs : s ∈ 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp hf.continuousWithinAt

theorem comp [FiniteDimensional ℝ E] {g : F → G} {t : Set F}
    (hg : IsPiecewiseAffineWithinAt g t (f x)) (hf : IsPiecewiseAffineWithinAt f s x) :
    IsPiecewiseAffineWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x := by
  have hcont : ContinuousWithinAt f (s ∩ f ⁻¹' t) x :=
    hf.continuousWithinAt.mono inter_subset_left
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := hg
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ A p.1 ⁻¹' D p.2,
    fun p => (B p.2).comp (A p.1), fun p => ⟨(hC p.1).1.inter_preimage (hD p.2).1 (A p.1), ?_, ?_⟩,
    ?_⟩
  · intro y hy
    refine ⟨(hC p.1).2.1 hy.1, ?_⟩
    change f y ∈ t
    rw [(hC p.1).2.2 hy.1]
    exact (hD p.2).2.1 hy.2
  · intro y hy
    have hfy : f y = A p.1 y := (hC p.1).2.2 hy.1
    simp only [Function.comp_apply, AffineMap.comp_apply]
    rw [hfy]
    exact (hD p.2).2.2 hy.2
  · have himg : f '' (s ∩ f ⁻¹' t) ⊆ t :=
      (image_mono inter_subset_right).trans (image_preimage_subset f t)
    have hpre : f ⁻¹' (⋃ j, D j) ∈ 𝓝[s ∩ f ⁻¹' t] x :=
      hcont.preimage_mem_nhdsWithin' (nhdsWithin_mono _ himg hDx)
    have hC' : (⋃ i, C i) ∈ 𝓝[s ∩ f ⁻¹' t] x := nhdsWithin_mono _ inter_subset_left hCx
    filter_upwards [hC', hpre] with y hy hy'
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy'
    refine mem_iUnion.mpr ⟨(i, j), hi, ?_⟩
    rw [mem_preimage, ← (hC i).2.2 hi]
    exact hj

end IsPiecewiseAffineWithinAt

theorem isPiecewiseAffineOn_of_affine_of_isHPolytope (A : E →ᵃ[ℝ] F) {P : Set E}
    (hP : IsHPolytope P) : IsPiecewiseAffineOn A P := by
  intro x _
  exact ⟨Unit, inferInstance, fun _ => P, fun _ => A, fun _ => ⟨hP, subset_rfl, fun _ _ => rfl⟩, by
    rw [iUnion_const]
    exact self_mem_nhdsWithin⟩

theorem isPiecewiseAffineOn_of_affine [FiniteDimensional ℝ E] (A : E →ᵃ[ℝ] F) {u : Set E}
    (hu : IsOpen u) : IsPiecewiseAffineOn A u := by
  intro x hx
  obtain ⟨C, hC, hCu, hCx⟩ := exists_isHPolytope_subset_mem_nhds (hu.mem_nhds hx)
  exact ⟨Unit, inferInstance, fun _ => C, fun _ => A, fun _ => ⟨hC, hCu, fun _ _ => rfl⟩, by
    rw [iUnion_const]
    exact mem_nhdsWithin_of_mem_nhds hCx⟩

theorem isPiecewiseAffineOn_id [FiniteDimensional ℝ E] {u : Set E} (hu : IsOpen u) :
    IsPiecewiseAffineOn (id : E → E) u :=
  isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E) hu

theorem isPiecewiseAffineOn_of_subsingleton [Subsingleton E] (f : E → F) (u : Set E) :
    IsPiecewiseAffineOn f u := by
  intro x _
  refine ⟨Unit, inferInstance, fun _ => univ, fun _ => AffineMap.const ℝ E (f x),
    fun _ => ⟨IsHPolytope.univ_of_subsingleton, fun y _ => ?_, fun y _ => ?_⟩, by
      rw [iUnion_const]
      exact univ_mem⟩
  · rwa [Subsingleton.elim y x]
  · rw [Subsingleton.elim y x]
    simp

theorem isPiecewiseAffineOn_of_locally {f : E → F} {u : Set E}
    (h : ∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ IsPiecewiseAffineOn f (u ∩ v)) :
    IsPiecewiseAffineOn f u := by
  intro x hx
  obtain ⟨v, hv, hxv, hfv⟩ := h x hx
  exact (hfv x ⟨hx, hxv⟩).of_inter_of_mem_nhds (hv.mem_nhds hxv)

namespace IsPiecewiseAffineOn

variable {f : E → F} {u : Set E}

theorem mono [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) {v : Set E} (hv : IsOpen v)
    (hvu : v ⊆ u) : IsPiecewiseAffineOn f v := by
  intro x hx
  have h := (hf x (hvu hx)).inter_of_mem_nhds (hv.mem_nhds hx)
  rwa [inter_eq_right.mpr hvu] at h

theorem congr {g : E → F} (hf : IsPiecewiseAffineOn f u) (hfg : EqOn g f u) :
    IsPiecewiseAffineOn g u :=
  fun x hx => (hf x hx).congr hfg

theorem continuousOn [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) :
    ContinuousOn f u :=
  fun x hx => (hf x hx).continuousWithinAt

theorem continuousAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) (hu : IsOpen u)
    {x : E} (hx : x ∈ u) : ContinuousAt f x :=
  (hf x hx).continuousAt (hu.mem_nhds hx)

theorem comp [FiniteDimensional ℝ E] {g : F → G} {v : Set F} (hg : IsPiecewiseAffineOn g v)
    (hf : IsPiecewiseAffineOn f u) : IsPiecewiseAffineOn (g ∘ f) (u ∩ f ⁻¹' v) :=
  fun x hx => (hg (f x) hx.2).comp (hf x hx.1)

theorem symm [FiniteDimensional ℝ E] {e : OpenPartialHomeomorph E E}
    (he : IsPiecewiseAffineOn e e.source) : IsPiecewiseAffineOn e.symm e.target := by
  intro y hy
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := he (e.symm y) (e.map_target hy)
  have := hι
  rw [nhdsWithin_eq_nhds.mpr (e.open_source.mem_nhds (e.map_target hy))] at hCx
  have hlin : ∀ i, (interior (C i)).Nonempty → Function.Injective (A i).linear := by
    intro i hi
    refine linear_injective_of_injOn_of_interior_nonempty ?_ hi
    intro a ha b hb hab
    apply e.injOn ((hC i).2.1 ha) ((hC i).2.1 hb)
    rw [(hC i).2.2 ha, (hC i).2.2 hb]
    exact hab
  have hdec : ∀ i, ∀ p, A i p = (A i).linear p + A i 0 := fun i p => by
    simpa using (A i).map_vadd 0 p
  let T : {i // (interior (C i)).Nonempty} → E ≃ᵃ[ℝ] E := fun i =>
    AffineEquiv.mk' (A i) (LinearEquiv.ofInjectiveEndo (A i).linear (hlin i i.2)) 0 fun p => by
      change A i p = (A i).linear (p - 0) + A i 0
      rw [sub_zero]
      exact hdec i p
  have hT : ∀ i p, T i p = A i p := fun i p => rfl
  refine ⟨{i // (interior (C i)).Nonempty}, inferInstance, fun i => e '' C i,
    fun i => (T i).symm.toAffineMap, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · have himg : e '' C i = T i '' C i := image_congr fun a ha => by rw [hT, ← (hC i).2.2 ha]
    change IsHPolytope (e '' C i)
    rw [himg]
    exact (hC i).1.image_affineEquiv (T i)
  · change e '' C i ⊆ e.target
    rw [← e.image_source_eq_target]
    exact image_mono (hC i).2.1
  · change EqOn e.symm (T i).symm.toAffineMap (e '' C i)
    rintro _ ⟨a, ha, rfl⟩
    rw [e.left_inv ((hC i).2.1 ha), AffineEquiv.coe_toAffineMap]
    have hea : e a = T i a := by rw [hT, ← (hC i).2.2 ha]
    rw [hea, AffineEquiv.symm_apply_apply]
  · change (⋃ i : {i // (interior (C i)).Nonempty}, e '' C i) ∈ 𝓝[e.target] y
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← image_iUnion, ← e.right_inv hy, ← e.map_nhds_eq (e.map_target hy)]
    exact image_mem_map (iUnion_interior_nonempty_mem_nhds (fun i => (hC i).1.isClosed) hCx)

end IsPiecewiseAffineOn

end DifferentialGeometry.Topology.PiecewiseLinear
