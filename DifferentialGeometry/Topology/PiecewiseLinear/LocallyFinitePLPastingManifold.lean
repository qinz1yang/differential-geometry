/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Union

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

theorem IsPLWithinAt.union {f : M → N} {s t : Set M} {x : M}
    (hs : IsPLWithinAt n m f s x) (ht : IsPLWithinAt n m f t x) :
    IsPLWithinAt n m f (s ∪ t) x := by
  refine ⟨hs.1.union ht.1, ?_⟩
  rw [preimage_union]
  exact IsPiecewiseAffineWithinAt.union hs.2 ht.2

theorem IsPLOn.congr {f g : M → N} {s : Set M} (hf : IsPLOn n m f s) (hg : EqOn g f s) :
    IsPLOn n m g s := fun x hx =>
  piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem (hf x hx) hg hx

theorem IsPLOn.union_of_isClosed {f : M → N} {s t : Set M} (hs : IsPLOn n m f s)
    (ht : IsPLOn n m f t) (hsc : IsClosed s) (htc : IsClosed t) : IsPLOn n m f (s ∪ t) := by
  intro x hx
  by_cases hxs : x ∈ s
  · by_cases hxt : x ∈ t
    · exact IsPLWithinAt.union (hs x hxs) (ht x hxt)
    · have hset : (fun y => y ∈ s) =ᶠ[𝓝 x] (fun y => y ∈ s ∪ t) := by
        filter_upwards [htc.isOpen_compl.mem_nhds hxt] with y hy
        apply propext
        exact ⟨Or.inl, fun h => h.resolve_right hy⟩
      exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp
        (hs x hxs)
  · have hxt : x ∈ t := hx.resolve_left hxs
    have hset : (fun y => y ∈ t) =ᶠ[𝓝 x] (fun y => y ∈ s ∪ t) := by
      filter_upwards [hsc.isOpen_compl.mem_nhds hxs] with y hy
      apply propext
      exact ⟨Or.inr, fun h => h.resolve_left hy⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp
      (ht x hxt)

theorem IsPLOn.union_biUnion_finset {ι : Type*} {f : M → N} {s : Set M} {S : ι → Set M}
    (hs : IsPLOn n m f s) (hsc : IsClosed s) (hS : ∀ i, IsPLOn n m f (S i))
    (hSc : ∀ i, IsClosed (S i)) (u : Finset ι) : IsPLOn n m f (s ∪ ⋃ i ∈ u, S i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using hs
  | @insert i u hi ih =>
      have hun := IsPLOn.union_of_isClosed ih (hS i)
        (hsc.union (isClosed_biUnion_finset fun j _ => hSc j)) (hSc i)
      simpa [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using hun

theorem isPLOn_union_iUnion_of_locallyFinite {ι : Type*} {f : M → N} {s : Set M} {S : ι → Set M}
    (hs : IsPLOn n m f s) (hsc : IsClosed s) (hS : ∀ i, IsPLOn n m f (S i))
    (hSc : ∀ i, IsClosed (S i))
    (hloc : ∀ x ∈ s ∪ ⋃ i, S i, ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite) :
    IsPLOn n m f (s ∪ ⋃ i, S i) := by
  classical
  intro x hx
  obtain ⟨U, hU, hfin⟩ := hloc x hx
  have hxu : x ∈ s ∪ ⋃ i ∈ hfin.toFinset, S i := by
    rcases hx with hxs | hxS
    · exact Or.inl hxs
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxS
      exact Or.inr (mem_iUnion₂.mpr
        ⟨i, hfin.mem_toFinset.mpr ⟨x, hxi, mem_of_mem_nhds hU⟩, hxi⟩)
  have hbase := IsPLOn.union_biUnion_finset hs hsc hS hSc hfin.toFinset x hxu
  have hset : (fun z => z ∈ s ∪ ⋃ i ∈ hfin.toFinset, S i) =ᶠ[𝓝 x]
      (fun z => z ∈ s ∪ ⋃ i, S i) := by
    filter_upwards [hU] with z hz
    apply propext
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨i, -, hzi⟩ := mem_iUnion₂.mp h
        exact Or.inr (mem_iUnion.mpr ⟨i, hzi⟩)
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨i, hzi⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion₂.mpr ⟨i, hfin.mem_toFinset.mpr ⟨z, hzi, hz⟩, hzi⟩)
  exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hbase

end Union

section Pasting

variable {n : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

open Classical in
theorem exists_isPLHomeomorphInto_union_of_locallyFinite_pieces {ι : Type*} {A : Set M}
    {B : Set N} {S : ι → Set M} {T : ι → Set N} {F₀ : M → N} {f : ι → M → N}
    (hA : IsClosed A) (hB : IsClosed B) (hSc : ∀ i, IsClosed (S i))
    (hTc : ∀ i, IsClosed (T i)) (hF : IsPLHomeomorphInto n F₀ A) (hFim : F₀ '' A = B)
    (hf : ∀ i, IsPLHomeomorphInto n (f i) (S i)) (hfim : ∀ i, f i '' S i = T i)
    (hbase : ∀ i, EqOn F₀ (f i) (A ∩ S i)) (hbaseMeet : ∀ i, F₀ '' (A ∩ S i) = B ∩ T i)
    (hcompat : ∀ i j, EqOn (f i) (f j) (S i ∩ S j))
    (hmeet : ∀ i j, f i '' (S i ∩ S j) = T i ∩ T j)
    (hsourceLocal : ∀ x ∈ A ∪ ⋃ i, S i, ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite)
    (htargetLocal : ∀ y ∈ B ∪ ⋃ i, T i, ∃ V ∈ 𝓝 y, {i | (T i ∩ V).Nonempty}.Finite) :
    ∃ G : M → N, IsPLHomeomorphInto n G (A ∪ ⋃ i, S i) ∧ EqOn G F₀ A ∧
      (∀ i, EqOn G (f i) (S i)) ∧ G '' (A ∪ ⋃ i, S i) = B ∪ ⋃ i, T i := by
  have hFbij : BijOn F₀ A B := ⟨fun x hx => hFim ▸ mem_image_of_mem F₀ hx, hF.injOn, hFim.ge⟩
  have hfbij : ∀ i, BijOn (f i) (S i) (T i) := fun i =>
    ⟨fun x hx => (hfim i) ▸ mem_image_of_mem (f i) hx, (hf i).injOn, (hfim i).ge⟩
  rcases eq_empty_or_nonempty (A ∪ ⋃ i, S i) with hK | ⟨x₀, hx₀⟩
  · have hout : ∀ x, x ∈ A ∪ ⋃ i, S i → False := by
      intro x hx
      rw [hK] at hx
      exact hx
    have hAe : A = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx => hout x (Or.inl hx)
    have hSe : ∀ i, S i = ∅ := fun i =>
      Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
        hout x (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
    have hBe : B = ∅ := by rw [← hFim, hAe, image_empty]
    have hTe : ∀ i, T i = ∅ := fun i => by rw [← hfim i, hSe i, image_empty]
    refine ⟨F₀, by rw [hK]; exact isPLHomeomorphInto_empty F₀, fun x _ => rfl,
      fun i x hx => absurd hx (by rw [hSe i]; exact notMem_empty x), ?_⟩
    rw [hK, image_empty, hBe]
    simp [hTe]
  · have : Nonempty M := ⟨x₀⟩
    set K : Set M := A ∪ ⋃ i, S i with hKdef
    set Y : Set N := B ∪ ⋃ i, T i with hYdef
    set G : M → N := fun x =>
      if hx : x ∈ A then F₀ x
      else if hx' : ∃ i, x ∈ S i then f (Classical.choose hx') x else F₀ x with hGdef
    have hGA : EqOn G F₀ A := fun x hx => by simp [hGdef, hx]
    have hGS : ∀ i, EqOn G (f i) (S i) := by
      intro i x hx
      by_cases hxA : x ∈ A
      · rw [show G x = F₀ x by simp [hGdef, hxA], hbase i ⟨hxA, hx⟩]
      · have hx' : ∃ j, x ∈ S j := ⟨i, hx⟩
        simp only [hGdef, dite_eq_right hxA, dite_eq_left hx']
        exact hcompat _ i ⟨Classical.choose_spec hx', hx⟩
    have hGmaps : MapsTo G K Y := by
      rintro x (hxA | hxS)
      · rw [hGA hxA]
        exact Or.inl (hFbij.mapsTo hxA)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxS
        rw [hGS i hxi]
        exact Or.inr (mem_iUnion.mpr ⟨i, (hfbij i).mapsTo hxi⟩)
    have hcrossA : ∀ i, ∀ x ∈ A, ∀ y ∈ S i, G x = G y → x = y := by
      intro i x hxA y hy hxy
      have hyim : G y ∈ B ∩ T i := by
        refine ⟨hxy ▸ (hGA hxA ▸ hFbij.mapsTo hxA), ?_⟩
        rw [hGS i hy]
        exact (hfbij i).mapsTo hy
      obtain ⟨z, hz, hzy⟩ := (hbaseMeet i).symm.subset hyim
      have hxz : x = z := by
        refine hFbij.injOn hxA hz.1 ?_
        rw [← hGA hxA, hxy, hzy]
      have hzy' : z = y := by
        refine (hfbij i).injOn hz.2 hy ?_
        rw [← hbase i ⟨hz.1, hz.2⟩, hzy, hGS i hy]
      exact hxz.trans hzy'
    have hcross : ∀ i j, ∀ x ∈ S i, ∀ y ∈ S j, G x = G y → x = y := by
      intro i j x hx y hy hxy
      have him : G x ∈ T i ∩ T j := by
        refine ⟨hGS i hx ▸ (hfbij i).mapsTo hx, ?_⟩
        rw [hxy, hGS j hy]
        exact (hfbij j).mapsTo hy
      obtain ⟨z, hz, hzx⟩ := (hmeet i j).symm.subset him
      have hxz : x = z := by
        refine (hfbij i).injOn hx hz.1 ?_
        rw [← hGS i hx, hzx]
      have hzy : z = y := by
        refine (hfbij j).injOn hz.2 hy ?_
        rw [← hcompat i j hz, hzx, hxy, hGS j hy]
      exact hxz.trans hzy
    have hGinj : InjOn G K := by
      rintro x (hxA | hxS) y (hyA | hyS) hxy
      · exact hFbij.injOn hxA hyA ((hGA hxA).symm.trans (hxy.trans (hGA hyA)))
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
        exact hcrossA j x hxA y hj hxy
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxS
        exact (hcrossA i y hyA x hi hxy.symm).symm
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxS
        obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
        exact hcross i j x hi y hj hxy
    have hGsurj : SurjOn G K Y := by
      rintro y (hyB | hyT)
      · obtain ⟨x, hx, hxy⟩ := hFbij.surjOn hyB
        exact ⟨x, Or.inl hx, (hGA hx).trans hxy⟩
      · obtain ⟨i, hyi⟩ := mem_iUnion.mp hyT
        obtain ⟨x, hx, hxy⟩ := (hfbij i).surjOn hyi
        exact ⟨x, Or.inr (mem_iUnion.mpr ⟨i, hx⟩), (hGS i hx).trans hxy⟩
    have hGbij : BijOn G K Y := ⟨hGmaps, hGinj, hGsurj⟩
    have hGpl : IsPLOn n n G K :=
      isPLOn_union_iUnion_of_locallyFinite (IsPLOn.congr hF.isPLOn hGA) hA
        (fun i => IsPLOn.congr (hf i).isPLOn (hGS i)) hSc hsourceLocal
    have hGleft : LeftInvOn (Function.invFunOn G K) G K := hGinj.leftInvOn_invFunOn
    have hleftA : LeftInvOn (Function.invFunOn G K) F₀ A := by
      intro x hx
      rw [← hGA hx]
      exact hGleft (Or.inl hx)
    have hleftS : ∀ i, LeftInvOn (Function.invFunOn G K) (f i) (S i) := by
      intro i x hx
      rw [← hGS i hx]
      exact hGleft (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
    have hinvB : IsPLOn n n (Function.invFunOn G K) B := by
      have h := hF.isPLOn_inverse hleftA
      rwa [hFim] at h
    have hinvT : ∀ i, IsPLOn n n (Function.invFunOn G K) (T i) := by
      intro i
      have h := (hf i).isPLOn_inverse (hleftS i)
      rwa [hfim i] at h
    have hinvpl : IsPLOn n n (Function.invFunOn G K) Y :=
      isPLOn_union_iUnion_of_locallyFinite hinvB hB hinvT hTc htargetLocal
    refine ⟨G, ⟨hGpl, hGinj, fun y hy => ⟨Function.invFunOn G K, ?_, hGleft⟩⟩, hGA, hGS,
      hGbij.image_eq⟩
    rw [hGbij.image_eq]
    exact hinvpl y (hGbij.image_eq ▸ hy)

end Pasting

end DifferentialGeometry.Topology.PiecewiseLinear
