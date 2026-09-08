import DifferentialGeometry.Topology.Morse.BoundaryIsotopy
import DifferentialGeometry.Topology.Diffeomorph.Extension

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

theorem exists_diffeomorph_image_boundaryMorsePerturbation_sublevels_in_chart
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ))
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V →
      ∃ Φ : Diffeomorph I I M M ∞,
        Φ '' (U : Set M) = U ∧
        Φ '' (Subtype.val '' {x : U | (c x).val 0 = 0}) =
          Subtype.val '' {x : U | (c x).val 0 = 0} ∧
        Φ '' (Subtype.val '' {x : U | 0 ≤ (c x).val 0}) =
          Subtype.val '' {x : U | 0 ≤ (c x).val 0} ∧
        (∀ x : U, a ≤ (c x).val 0 ∨ b.rOut ≤ ‖Fin.tail (c x).val‖ →
          Φ x = (x : M) ∧ Φ.symm x = (x : M)) ∧
        (∀ r ∈ ({lower, upper} : Set ℝ),
          Φ '' (Subtype.val '' {x : U | 0 ≤ (c x).val 0 ∧
            ((∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0) ≤ r}) =
          Subtype.val '' {x : U | 0 ≤ (c x).val 0 ∧
            boundaryMorsePerturbation d b a (c x) ≤ r}) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
          Set.EqOn Φ id Kᶜ ∧ Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_diffeomorph_image_boundaryMorsePerturbation_sublevels_with_support d hd b hlower hupper
  refine ⟨δ, hδ, ?_⟩
  intro a ha hbox
  obtain ⟨ψ, himages, hnormal, houter, K, hK, hKV, hfix, hfixi⟩ :=
    h a ha V V.isOpen hbox
  let K' : Set V := Subtype.val ⁻¹' K
  have himK : Subtype.val '' K' = K := by
    apply Set.image_preimage_eq_of_subset
    intro z hz
    exact ⟨⟨z, hKV hz⟩, rfl⟩
  have hK' : IsCompact K' := Subtype.isCompact_iff.mpr (by rw [himK]; exact hK)
  obtain ⟨Ξ, hΞ, hΞi, hΞU, hΞc, hΞci, hΞid, hΞK⟩ :=
    Diffeomorph.exists_extension_conjugate_of_isCompact
      (L := 𝓘(ℝ, ℝ)) c (fun _ : ℝ => ψ)
      (ψ.contMDiff.comp contMDiff_snd) (ψ.symm.contMDiff.comp contMDiff_snd) hK'
      (by intro t; simpa only [himK] using hfix)
  let Φ := Ξ 0
  have hΦU : Φ '' (U : Set M) = U := hΞU 0
  have hconj (x y : U) : Φ x = (y : M) ↔ ψ (c x : Fin (n + 1) → ℝ) = (c y : Fin (n + 1) → ℝ) := by
    simpa only [c.symm_apply_apply] using hΞc 0 x (c y)
  have hΦmem (x : U) : Φ x ∈ U := by
    change Φ x ∈ (U : Set M)
    rw [← hΦU]
    exact Set.mem_image_of_mem Φ x.property
  have hΦimem (y : U) : Φ.symm y ∈ U := by
    have hy : (y : M) ∈ (U : Set M) := y.property
    rw [← hΦU] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, Φ.symm_apply_apply]
    exact hx
  have htransport (S T : Set (Fin (n + 1) → ℝ)) (hst : ψ '' S = T) :
      Φ '' (Subtype.val '' {x : U | (c x : Fin (n + 1) → ℝ) ∈ S}) =
        Subtype.val '' {x : U | (c x : Fin (n + 1) → ℝ) ∈ T} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      let y : U := ⟨Φ x, hΦmem x⟩
      have hxy : ψ (c x : Fin (n + 1) → ℝ) = (c y : Fin (n + 1) → ℝ) :=
        (hconj x y).mp rfl
      have hxS : (c x : Fin (n + 1) → ℝ) ∈ S := hx
      have hmem := Set.mem_image_of_mem ψ hxS
      rw [hst, hxy] at hmem
      exact ⟨y, hmem, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      let x : U := ⟨Φ.symm y, hΦimem y⟩
      have hxy : ψ (c x : Fin (n + 1) → ℝ) = (c y : Fin (n + 1) → ℝ) :=
        (hconj x y).mp (Φ.apply_symm_apply y)
      change (c y : Fin (n + 1) → ℝ) ∈ T at hy
      obtain ⟨z, hz, hzy⟩ := hst.symm ▸ hy
      have hzx : z = (c x : Fin (n + 1) → ℝ) := ψ.injective (hzy.trans hxy.symm)
      rw [hzx] at hz
      exact ⟨x, ⟨x, hz, rfl⟩, Φ.apply_symm_apply y⟩
  have hpreserve (P : (Fin (n + 1) → ℝ) → Prop) (hp : ∀ z, P z ↔ P (ψ z)) :
      ψ '' {z | P z} = {z | P z} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact (hp z).mp hz
    · intro z hz
      exact ⟨ψ.symm z, (hp (ψ.symm z)).mpr (by simpa using hz), ψ.apply_symm_apply z⟩
  refine ⟨Φ, hΦU, htransport _ _ (hpreserve (fun z => z 0 = 0) (fun z => (hnormal z).1)),
    htransport _ _ (hpreserve (fun z => 0 ≤ z 0) (fun z => (hnormal z).2)), ?_,
    fun r hr => htransport _ _ (himages r hr),
    (fun y : V => (c.symm y : M)) '' K', hΞK.1, ?_, (hΞK.2 0).1, (hΞK.2 0).2⟩
  · intro x hx
    constructor
    · exact (hconj x x).mpr (houter (c x) hx).1
    · have h := (hΞci 0 x (c x)).mpr (houter (c x) hx).2
      simpa only [c.symm_apply_apply] using h
  · rintro _ ⟨y, hy, rfl⟩
    exact (c.symm y).property

theorem exists_diffeomorph_image_sublevels_of_boundaryMorseChart
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ))
    (D : Set M) (hD : ∀ x : U, (x : M) ∈ D ↔ 0 ≤ (c x).val 0)
    (f : M → ℝ)
    (hf : ∀ x : U, (x : M) ∈ D → f x = (∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V →
      ∀ g : M → ℝ, (∀ x : U, (x : M) ∈ D → g x = boundaryMorsePerturbation d b a (c x)) →
      Set.EqOn g f ((U : Set M)ᶜ ∩ D) →
      ∃ Φ : Diffeomorph I I M M ∞,
        Φ '' D = D ∧
        (∀ r ∈ ({lower, upper} : Set ℝ),
          Φ '' {x | x ∈ D ∧ f x ≤ r} = {x | x ∈ D ∧ g x ≤ r}) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
          Set.EqOn Φ id Kᶜ ∧ Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_diffeomorph_image_boundaryMorsePerturbation_sublevels_in_chart c d hd b hlower hupper
  refine ⟨δ, hδ, ?_⟩
  intro a ha hbox g hg hgf
  obtain ⟨Φ, hΦU, hboundary, hside, houter, hlevels, K, hK, hKU, hfix, hfixi⟩ := h a ha hbox
  have hfixU : Set.EqOn Φ id (U : Set M)ᶜ := by
    intro x hx
    exact hfix (fun hxK => hx (hKU hxK))
  have hglue (S T : Set M) (hlocal : Φ '' ((U : Set M) ∩ S) = (U : Set M) ∩ T)
      (hout : (U : Set M)ᶜ ∩ S = (U : Set M)ᶜ ∩ T) : Φ '' S = T := by
    have hS : S = ((U : Set M) ∩ S) ∪ ((U : Set M)ᶜ ∩ S) := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    have hT : T = ((U : Set M) ∩ T) ∪ ((U : Set M)ᶜ ∩ T) := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    calc
      Φ '' S = Φ '' ((U : Set M) ∩ S) ∪ Φ '' ((U : Set M)ᶜ ∩ S) := by
        rw [← Set.image_union]
        exact congrArg (fun A : Set M => Φ '' A) hS
      _ = ((U : Set M) ∩ T) ∪ ((U : Set M)ᶜ ∩ T) := by
        rw [hlocal, (hfixU.mono Set.inter_subset_left).image_eq_self, hout]
      _ = T := hT.symm
  have hdomain : (U : Set M) ∩ D = Subtype.val '' {x : U | 0 ≤ (c x).val 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx.1⟩, (hD ⟨x, hx.1⟩).mp hx.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, (hD y).mpr hy⟩
  refine ⟨Φ, hglue D D (by simpa only [hdomain] using hside) rfl, ?_,
    K, hK, hKU, hfix, hfixi⟩
  intro r hr
  apply hglue
  · have hsource : (U : Set M) ∩ {x | x ∈ D ∧ f x ≤ r} =
        Subtype.val '' {x : U | 0 ≤ (c x).val 0 ∧
          ((∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0) ≤ r} := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hx.1⟩, ⟨(hD ⟨x, hx.1⟩).mp hx.2.1,
          (hf ⟨x, hx.1⟩ hx.2.1) ▸ hx.2.2⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, (hD y).mpr hy.1, (hf y ((hD y).mpr hy.1)).symm ▸ hy.2⟩
    have htarget : (U : Set M) ∩ {x | x ∈ D ∧ g x ≤ r} =
        Subtype.val '' {x : U | 0 ≤ (c x).val 0 ∧
          boundaryMorsePerturbation d b a (c x) ≤ r} := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hx.1⟩, ⟨(hD ⟨x, hx.1⟩).mp hx.2.1,
          (hg ⟨x, hx.1⟩ hx.2.1) ▸ hx.2.2⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, (hD y).mpr hy.1, (hg y ((hD y).mpr hy.1)).symm ▸ hy.2⟩
    rw [hsource, htarget]
    exact hlevels r hr
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.1, (hgf ⟨hx.1, hx.2.1⟩).symm ▸ hx.2.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.1, (hgf ⟨hx.1, hx.2.1⟩) ▸ hx.2.2⟩

end DifferentialGeometry.Topology.Morse
