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

end DifferentialGeometry.Topology
