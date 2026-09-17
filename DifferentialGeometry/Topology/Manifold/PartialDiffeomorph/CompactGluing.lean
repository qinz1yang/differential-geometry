import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Topology.Separation.Regular

open Set Filter Topology
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [T2Space N] {n : ℕ∞ω}

theorem exists_gluing_of_isCompact {ι : Type*}
    (φ : ι → PartialDiffeomorph I J M N n)
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    {U : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hs : ∀ i, U i ⊆ (φ i).source)
    (hcover : K ⊆ ⋃ i, U i) (heq : ∀ i j, EqOn (φ i) (φ j) (U i ∩ U j))
    (himage : ∀ i j, φ i '' (K ∩ U i) ∩ φ j '' (K ∩ U j) ⊆
      φ i '' (K ∩ U i ∩ U j)) :
    ∃ ψ : PartialDiffeomorph I J M N n,
      K ⊆ ψ.source ∧ ∀ i, EqOn ψ (φ i) (ψ.source ∩ U i) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨i₀, _⟩ := mem_iUnion.mp (hcover hx₀)
  let f : M → N := fun x => if hx : ∃ i, x ∈ U i then φ (Classical.choose hx) x else φ i₀ x
  have hf (i : ι) : EqOn f (φ i) (U i) := by
    intro x hx
    have hex : ∃ j, x ∈ U j := ⟨i, hx⟩
    dsimp only [f]
    rw [dif_pos hex]
    exact heq (Classical.choose hex) i ⟨Classical.choose_spec hex, hx⟩
  have hlocal : IsLocalDiffeomorphOn I J n f K := by
    intro x
    obtain ⟨i, hx⟩ := mem_iUnion.mp (hcover x.property)
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
      (Filter.eventuallyEq_of_mem ((hU i).mem_nhds hx) (fun y hy => hf i hy))
      ((φ i).isLocalDiffeomorphAt I J n (hs i hx))
  have hinj : InjOn f K := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    have hφxy : φ i x = φ j y := (hf i hxi).symm.trans (hxy.trans (hf j hyj))
    obtain ⟨z, hz, hzx⟩ := himage i j
      ⟨⟨x, ⟨hx, hxi⟩, rfl⟩, ⟨y, ⟨hy, hyj⟩, hφxy.symm⟩⟩
    have hzx' : z = x := (φ i).toPartialEquiv.injOn (hs i hz.1.2) (hs i hxi) hzx
    have hzy : φ j z = φ j y := (heq i j ⟨hz.1.2, hz.2⟩).symm.trans (hzx.trans hφxy)
    exact hzx'.symm.trans ((φ j).toPartialEquiv.injOn (hs j hz.2) (hs j hyj) hzy)
  obtain ⟨ψ, hsrc, hψ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      hlocal hK ⟨x₀, hx₀⟩ hinj
  exact ⟨ψ, hsrc, fun i x hx => (congrFun hψ x).trans (hf i hx.2)⟩

omit [T2Space N] in
theorem exists_eqOn_neighborhoods_of_isCompact [T3Space M]
    (D₀ D₁ : Diffeomorph I J M N n)
    {K₀ K₁ O : Set M} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hO : IsOpen O) (hKO : K₀ ∩ K₁ ⊆ O) (heq : EqOn D₀ D₁ O)
    (himage : D₀ '' K₀ ∩ D₁ '' K₁ ⊆ D₀ '' (K₀ ∩ K₁)) :
    ∃ ψ : PartialDiffeomorph I J M N n, ∃ U₀ U₁ : Set M,
      IsOpen U₀ ∧ IsOpen U₁ ∧ K₀ ⊆ U₀ ∧ K₁ ⊆ U₁ ∧ U₀ ∪ U₁ ⊆ ψ.source ∧
      EqOn ψ D₀ U₀ ∧ EqOn ψ D₁ U₁ := by
  let _ : T2Space N := T2Space.of_injective_continuous D₀.symm.injective D₀.symm.continuous
  classical
  rcases (K₀ ∪ K₁).eq_empty_or_nonempty with hzero | hne
  · have h₀ : K₀ = ∅ := Set.Subset.antisymm (hzero ▸ subset_union_left) (empty_subset _)
    have h₁ : K₁ = ∅ := Set.Subset.antisymm (hzero ▸ subset_union_right) (empty_subset _)
    subst K₀ K₁
    exact ⟨D₀.toPartialDiffeomorph, ∅, ∅, isOpen_empty, isOpen_empty,
      subset_rfl, subset_rfl, by simp, eqOn_empty _ _, eqOn_empty _ _⟩
  have hW : IsOpen (K₁ \ O)ᶜ := (hK₁.isClosed.inter hO.isClosed_compl).isOpen_compl
  have hK₀W : K₀ ⊆ (K₁ \ O)ᶜ := fun x hx h => h.2 (hKO ⟨hx, h.1⟩)
  obtain ⟨V, hV, hK₀V, hVW⟩ := hK₀.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hK₀W)
  let W := O ∪ (closure V)ᶜ
  have hWopen : IsOpen W := hO.union isClosed_closure.isOpen_compl
  have hK₁W : K₁ ⊆ W := by
    intro x hx
    by_cases hxV : x ∈ closure V
    · exact Or.inl (not_not.mp (fun hxO => hVW hxV ⟨hx, hxO⟩))
    · exact Or.inr hxV
  have hVWsub : V ∩ W ⊆ O := by
    intro x hx
    exact hx.2.resolve_right (fun h => h (subset_closure hx.1))
  let f := V.piecewise D₀ D₁
  have hf₀ : EqOn f D₀ V := fun x hx => if_pos hx
  have hf₁ : EqOn f D₁ W := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact (hf₀ hxV).trans (heq (hVWsub ⟨hxV, hx⟩))
    · exact if_neg hxV
  have hfK₀ : EqOn f D₀ K₀ := hf₀.mono hK₀V
  have hfK₁ : EqOn f D₁ K₁ := hf₁.mono hK₁W
  have hcross {x y : M} (hx : x ∈ K₀) (hy : y ∈ K₁) (hxy : D₀ x = D₁ y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := himage ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
    have hzx' : z = x := D₀.injective hzx
    have hzy : z = y := D₁.injective ((heq (hKO hz)).symm.trans (hzx.trans hxy))
    exact hzx'.symm.trans hzy
  have hinj : InjOn f (K₀ ∪ K₁) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact D₀.injective ((hfK₀ hx).symm.trans (hxy.trans (hfK₀ hy)))
    · exact hcross hx hy ((hfK₀ hx).symm.trans (hxy.trans (hfK₁ hy)))
    · exact (hcross hy hx ((hfK₀ hy).symm.trans (hxy.symm.trans (hfK₁ hx)))).symm
    · exact D₁.injective ((hfK₁ hx).symm.trans (hxy.trans (hfK₁ hy)))
  have hlocal : IsLocalDiffeomorphOn I J n f (K₀ ∪ K₁) := by
    intro x
    rcases x.property with hx | hx
    · exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (eventuallyEq_of_mem (hV.mem_nhds (hK₀V hx)) (fun y hy => hf₀ hy))
        (D₀.isLocalDiffeomorph x)
    · exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (eventuallyEq_of_mem (hWopen.mem_nhds (hK₁W hx)) (fun y hy => hf₁ hy))
        (D₁.isLocalDiffeomorph x)
  obtain ⟨ψ, hsrc, hψ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      hlocal (hK₀.union hK₁) hne hinj
  refine ⟨ψ, ψ.source ∩ V, ψ.source ∩ W, ψ.open_source.inter hV,
    ψ.open_source.inter hWopen, ?_, ?_, union_subset inter_subset_left inter_subset_left, ?_, ?_⟩
  · exact fun x hx => ⟨hsrc (Or.inl hx), hK₀V hx⟩
  · exact fun x hx => ⟨hsrc (Or.inr hx), hK₁W hx⟩
  · exact fun x hx => (congrFun hψ x).trans (hf₀ hx.2)
  · exact fun x hx => (congrFun hψ x).trans (hf₁ hx.2)

end PartialDiffeomorph
