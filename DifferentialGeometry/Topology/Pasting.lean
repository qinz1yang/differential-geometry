import Mathlib.Topology.SeparatedMap
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Piecewise

open Set Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*}

open Classical in
theorem piecewise_postcomp_preimage_singleton_of_eqOn_compl
    (P : Set X) (f : X → Y) {h : Y → Y} (hh : Function.Injective h)
    {U : Set Y} (hfix : EqOn h id Uᶜ) {y : Y} (hy : y ∉ U) :
    (P.piecewise (h ∘ f) f) ⁻¹' {y} = f ⁻¹' {y} := by
  ext x
  by_cases hx : x ∈ P
  · simp only [mem_preimage, mem_singleton_iff, piecewise_eq_of_mem P (h ∘ f) f hx,
      Function.comp_apply]
    constructor
    · intro hxy
      exact hh (hxy.trans (hfix hy).symm)
    · intro hxy
      rw [hxy]
      exact hfix hy
  · simp only [mem_preimage, piecewise_eq_of_notMem P (h ∘ f) f hx]

open Classical in
theorem encard_fiber_piecewise_postcomp_le
    (f : X → Y) (S P : Set X) {h : Y → Y} (hh : Function.Injective h)
    {U : Set Y} (hfix : EqOn h id Uᶜ) (hP : InjOn f (S ∩ P)) {n : ℕ∞}
    (hcard : ∀ y, (S ∩ f ⁻¹' {y}).encard ≤ n + 1)
    (hrest : ∀ y ∈ U, ((S \ P) ∩ f ⁻¹' {y}).encard ≤ n) :
    ∀ y, (S ∩ (P.piecewise (h ∘ f) f) ⁻¹' {y}).encard ≤ n + 1 := by
  intro y
  by_cases hy : y ∈ U
  · let A := (S ∩ P) ∩ (h ∘ f) ⁻¹' {y}
    let B := (S \ P) ∩ f ⁻¹' {y}
    have hA : A.encard ≤ 1 := by
      apply encard_le_one_iff_subsingleton.mpr
      intro x hx z hz
      exact hP hx.1 hz.1 (hh (hx.2.trans hz.2.symm))
    have hsub : S ∩ (P.piecewise (h ∘ f) f) ⁻¹' {y} ⊆ A ∪ B := by
      intro x hx
      by_cases hxP : x ∈ P
      · exact Or.inl ⟨⟨hx.1, hxP⟩, by
          simpa only [mem_preimage, piecewise_eq_of_mem P (h ∘ f) f hxP] using hx.2⟩
      · exact Or.inr ⟨⟨hx.1, hxP⟩, by
          simpa only [mem_preimage, piecewise_eq_of_notMem P (h ∘ f) f hxP] using hx.2⟩
    exact (encard_mono hsub).trans ((encard_union_le A B).trans
      (by simpa only [add_comm 1 n] using add_le_add hA (hrest y hy)))
  · rw [piecewise_postcomp_preimage_singleton_of_eqOn_compl P f hh hfix hy]
    exact hcard y

open Classical in
theorem IsLocallyInjective.piecewise_postcomp_of_isClosed
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {h : Y → Y} {P Q : Set X}
    (hf : IsLocallyInjective ((P ∪ Q).domRestrict f)) (hcont : ContinuousOn f (P ∪ Q))
    (hP : IsClosed P) (hQ : IsClosed Q) (hh : Function.Injective h)
    (hfix : ∀ x ∈ P ∩ Q, ∀ᶠ y in 𝓝 (f x), h y = y) :
    IsLocallyInjective ((P ∪ Q).domRestrict (P.piecewise (h ∘ f) f)) := by
  rw [isLocallyInjective_iff_nhds] at hf ⊢
  intro x
  obtain ⟨W, hW, hinj⟩ := hf x
  by_cases hxP : (x : X) ∈ P
  · by_cases hxQ : (x : X) ∈ Q
    · have hc := (continuousOn_iff_continuous_domRestrict.mp hcont).continuousAt (x := x)
      have heq : {z : ↥(P ∪ Q) | h (f z) = f z} ∈ 𝓝 x := hc.eventually (hfix x ⟨hxP, hxQ⟩)
      refine ⟨W ∩ {z : ↥(P ∪ Q) | h (f z) = f z}, Filter.inter_mem hW heq, ?_⟩
      have hagree : ∀ z : ↥(P ∪ Q), h (f z) = f z → P.piecewise (h ∘ f) f z = f z := by
        intro z hz
        by_cases hzP : (z : X) ∈ P
        · rw [piecewise_eq_of_mem P (h ∘ f) f hzP]
          exact hz
        · exact piecewise_eq_of_notMem P (h ∘ f) f hzP
      intro y hy z hz hyz
      apply hinj hy.1 hz.1
      change P.piecewise (h ∘ f) f y = P.piecewise (h ∘ f) f z at hyz
      rwa [hagree y hy.2, hagree z hz.2] at hyz
    · have hN : {z : ↥(P ∪ Q) | (z : X) ∉ Q} ∈ 𝓝 x :=
        (hQ.isOpen_compl.preimage continuous_subtype_val).mem_nhds hxQ
      refine ⟨W ∩ {z : ↥(P ∪ Q) | (z : X) ∉ Q}, Filter.inter_mem hW hN, ?_⟩
      intro y hy z hz hyz
      have hyP : (y : X) ∈ P := y.property.resolve_right hy.2
      have hzP : (z : X) ∈ P := z.property.resolve_right hz.2
      apply hinj hy.1 hz.1
      apply hh
      change P.piecewise (h ∘ f) f y = P.piecewise (h ∘ f) f z at hyz
      rwa [piecewise_eq_of_mem P (h ∘ f) f hyP, piecewise_eq_of_mem P (h ∘ f) f hzP] at hyz
  · have hN : {z : ↥(P ∪ Q) | (z : X) ∉ P} ∈ 𝓝 x :=
      (hP.isOpen_compl.preimage continuous_subtype_val).mem_nhds hxP
    refine ⟨W ∩ {z : ↥(P ∪ Q) | (z : X) ∉ P}, Filter.inter_mem hW hN, ?_⟩
    intro y hy z hz hyz
    apply hinj hy.1 hz.1
    change P.piecewise (h ∘ f) f y = P.piecewise (h ∘ f) f z at hyz
    rwa [piecewise_eq_of_notMem P (h ∘ f) f hy.2,
      piecewise_eq_of_notMem P (h ∘ f) f hz.2] at hyz

open Classical in
theorem exists_isOpen_piecewise_postcomp_eqOn_of_finite
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {P Q : Set X} (hf : ContinuousOn f (P ∪ Q)) (hP : IsClosed P) (hQ : IsClosed Q)
    {ι : Type*} [Finite ι] (C : ι → Set X) (hC : ∀ i, IsCompact (C i))
    (hCS : ∀ i, C i ⊆ P ∪ Q) (hinj : ∀ i, InjOn f (C i))
    {y : Y} (hy : y ∉ f '' (P ∩ Q)) {V : Set Y} (hV : V ∈ 𝓝 y) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧
      ∀ h : Y → Y, EqOn h id Uᶜ → ∀ i,
        EqOn (P.piecewise (h ∘ f) f) (h ∘ f) (C i) ∨ EqOn (P.piecewise (h ∘ f) f) f (C i) := by
  let A := fun i => f '' (C i ∩ P)
  let B := fun i => f '' (C i ∩ Q)
  have hAclosed : ∀ i, IsClosed (A i) := fun i =>
    (((hC i).inter_right hP).image_of_continuousOn (hf.mono (inter_subset_left.trans (hCS i)))).isClosed
  have hBclosed : ∀ i, IsClosed (B i) := fun i =>
    (((hC i).inter_right hQ).image_of_continuousOn (hf.mono (inter_subset_left.trans (hCS i)))).isClosed
  let W := fun i => if y ∈ A i then (B i)ᶜ else (A i)ᶜ
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    dsimp only [W]
    split_ifs
    · exact (hBclosed i).isOpen_compl
    · exact (hAclosed i).isOpen_compl
  have hyW : ∀ i, y ∈ W i := by
    intro i
    dsimp only [W]
    split_ifs with hyA
    · obtain ⟨a, ha, hfa⟩ := hyA
      rintro ⟨b, hb, hfb⟩
      have hab : a = b := hinj i ha.1 hb.1 (hfa.trans hfb.symm)
      exact hy ⟨a, ⟨ha.2, by rw [hab]; exact hb.2⟩, hfa⟩
    · exact hyA
  let U := interior V ∩ ⋂ i, W i
  have hU : IsOpen U := isOpen_interior.inter (isOpen_iInter_of_finite hW)
  have hUW : ∀ i, U ⊆ W i := fun i => inter_subset_right.trans (iInter_subset W i)
  refine ⟨U, hU, ⟨mem_interior_iff_mem_nhds.mpr hV, mem_iInter.mpr hyW⟩,
    inter_subset_left.trans interior_subset, fun h hfix i => ?_⟩
  by_cases hyA : y ∈ A i
  · refine Or.inl ?_
    intro x hx
    by_cases hxP : x ∈ P
    · exact piecewise_eq_of_mem P (h ∘ f) f hxP
    · have hxQ : x ∈ Q := (hCS i hx).resolve_left hxP
      have hfxU : f x ∉ U := by
        intro hfx
        have hnot := hUW i hfx
        rw [show W i = (B i)ᶜ from if_pos hyA] at hnot
        exact hnot ⟨x, ⟨hx, hxQ⟩, rfl⟩
      rw [piecewise_eq_of_notMem P (h ∘ f) f hxP]
      exact (hfix hfxU).symm
  · refine Or.inr ?_
    intro x hx
    by_cases hxP : x ∈ P
    · have hfxU : f x ∉ U := by
        intro hfx
        have hnot := hUW i hfx
        rw [show W i = (A i)ᶜ from if_neg hyA] at hnot
        exact hnot ⟨x, ⟨hx, hxP⟩, rfl⟩
      rw [piecewise_eq_of_mem P (h ∘ f) f hxP]
      exact hfix hfxU
    · exact piecewise_eq_of_notMem P (h ∘ f) f hxP
theorem mem_nhdsWithin_of_eventually_preimage_subset_union
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {P A B : Set X} {a : X}
    (hf : ContinuousWithinAt f P a) (ha : a ∈ A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hcover : ∀ᶠ z in 𝓝 (f a), P ∩ f ⁻¹' {z} ⊆ A ∪ B) : A ∈ 𝓝[P] a := by
  have haB : a ∉ B := fun haB => Set.disjoint_left.mp hAB ha haB
  filter_upwards [hf.eventually hcover, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hB.isOpen_compl.mem_nhds haB)] with x hx hxP hxB
  exact (hx ⟨hxP, rfl⟩).resolve_right hxB

end DifferentialGeometry.Topology
