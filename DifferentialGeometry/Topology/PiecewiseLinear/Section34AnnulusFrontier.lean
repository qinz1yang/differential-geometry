import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_range_cylinder_eq {E M N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [CompactSpace M] [ChartedSpace E (M × ℝ)]
    [TopologicalSpace N] [T2Space N] [ChartedSpace E N]
    (g : M × unitInterval → N) (hg : Continuous g) (hinj : Function.Injective g) :
    frontier (range g) =
      g '' {p | (p.2 : ℝ) = 0} ∪ g '' {p | (p.2 : ℝ) = 1} := by
  refine Subset.antisymm (frontier_range_cylinder_subset (E := E) g hg hinj) ?_
  have hend (a : M × unitInterval) (ha : (a.2 : ℝ) = 0 ∨ (a.2 : ℝ) = 1) :
      g a ∉ interior (range g) := by
    let φ := (hg.isClosedEmbedding hinj).isEmbedding.toHomeomorph
    let j : M × unitInterval → M × ℝ := fun p => (p.1, p.2.val)
    have hj : Continuous j := continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)
    have hji : Function.Injective j := by
      intro x y hxy
      exact Prod.ext (congrArg (fun z : M × ℝ => z.1) hxy)
        (Subtype.ext (congrArg (fun z : M × ℝ => z.2) hxy))
    let k : N → M × ℝ := Function.extend Subtype.val (j ∘ φ.symm) (fun _ => j a)
    have hkeq (z : range g) : k z.val = j (φ.symm z) :=
      Function.Injective.extend_apply Subtype.val_injective (j ∘ φ.symm) (fun _ => j a) z
    have hkg (b : M × unitInterval) : k (g b) = j b := by
      calc
        k (g b) = j (φ.symm (φ b)) := hkeq (φ b)
        _ = j b := by rw [φ.symm_apply_apply]
    have hkc : ContinuousOn k (range g) := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hj.comp φ.symm.continuous using 1
      funext z
      exact hkeq z
    have hki : InjOn k (range g) := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      rw [hkg, hkg] at hxy
      exact congrArg g (hji hxy)
    intro hint
    have hopen := DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
      (E := E) isOpen_interior (hkc.mono interior_subset) (hki.mono interior_subset)
    have hsub : k '' interior (range g) ⊆ (univ : Set M) ×ˢ Icc (0 : ℝ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨b, rfl⟩ := interior_subset hz
      rw [hkg]
      exact ⟨mem_univ _, b.2.property⟩
    have hx := interior_maximal hsub hopen (mem_image_of_mem k hint)
    rw [hkg, interior_prod_eq, interior_univ, interior_Icc] at hx
    rcases ha with ha | ha
    · have hz : 0 < (a.2 : ℝ) := hx.2.1
      linarith
    · have hz : (a.2 : ℝ) < 1 := hx.2.2
      linarith
  rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact ⟨subset_closure ⟨a, rfl⟩, hend a (Or.inl ha)⟩
  · exact ⟨subset_closure ⟨a, rfl⟩, hend a (Or.inr ha)⟩

theorem IsAnnulusOn.frontier_eq_ends {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {A A₀ A₁ : Set M}
    (hA : IsAnnulusOn A A₀ A₁) : frontier A = A₀ ∪ A₁ := by
  let E := EuclideanSpace ℝ (Fin 1) × ℝ
  let C := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [E, Module.finrank_prod])
  let _ : ChartedSpace E (C × ℝ) := prodChartedSpace _ _ _ _
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := e.symm.toHomeomorph.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (C × ℝ) :=
    ChartedSpace.comp _ E (C × ℝ)
  obtain ⟨φ, h₀, h₁⟩ := hA
  let g : C × unitInterval → M := fun p => (φ p).val
  have hg : Continuous g := continuous_subtype_val.comp φ.continuous
  have hi : Function.Injective g := Subtype.val_injective.comp φ.injective
  have hrange : range g = A := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (φ p).property
    · intro hx
      obtain ⟨p, hp⟩ := φ.surjective ⟨x, hx⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  rw [← hrange]
  simpa only [g, image_image, h₀, h₁] using
    frontier_range_cylinder_eq (E := EuclideanSpace ℝ (Fin 2)) g hg hi


theorem IsAnnulusOn.ends_disjoint_interior_of_inter {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ S T : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hAT : A = S ∩ T) : Disjoint (A₀ ∪ A₁) (interior T) := by
  have hAS : A ⊆ S := hAT ▸ inter_subset_left
  have hfront := (hA.preimage_subtype hAS).frontier_eq_ends
  have hsub : (Subtype.val : S → M) ⁻¹' interior T ⊆ Subtype.val ⁻¹' A := by
    intro x hx
    rw [hAT]
    exact ⟨x.2, interior_subset hx⟩
  have hint := interior_maximal hsub (isOpen_interior.preimage continuous_subtype_val)
  refine disjoint_left.mpr ?_
  intro x hx hxT
  have hxS : x ∈ S := hAS ((union_subset hA.first_subset hA.second_subset) hx)
  have hxfront : (⟨x, hxS⟩ : S) ∈ frontier ((Subtype.val : S → M) ⁻¹' A) := by
    rw [hfront]
    exact hx
  exact hxfront.2 (hint hxT)


theorem IsAnnulusOn.disjoint_ends_of_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {A A₀ A₁ B B₀ B₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) (hB : IsAnnulusOn B B₀ B₁)
    (hAB : A ⊆ B) (hends : Disjoint (A₀ ∪ A₁) (B₀ ∪ B₁)) : Disjoint A (B₀ ∪ B₁) := by
  refine disjoint_left.mpr ?_
  intro x hxA hxB
  have hxfrontB : x ∈ frontier B := hB.frontier_eq_ends.symm ▸ hxB
  have hxfrontA : x ∈ frontier A :=
    ⟨subset_closure hxA, fun hx => hxfrontB.2 (interior_mono hAB hx)⟩
  exact disjoint_left.mp hends (hA.frontier_eq_ends ▸ hxfrontA) hxB

theorem IsAnnulusOn.disjoint_ends_of_subset_within {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ B B₀ B₁ S : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hB : IsAnnulusOn B B₀ B₁) (hBS : B ⊆ S)
    (hAB : A ⊆ B) (hends : Disjoint (A₀ ∪ A₁) (B₀ ∪ B₁)) : Disjoint A (B₀ ∪ B₁) := by
  have hsub : (Subtype.val : S → M) ⁻¹' A ⊆ Subtype.val ⁻¹' B := fun _ hx => hAB hx
  have hdis := (hA.preimage_subtype (hAB.trans hBS)).disjoint_ends_of_subset
    (hB.preimage_subtype hBS) hsub
    (disjoint_left.mpr fun _ hx hy => disjoint_left.mp hends hx hy)
  refine disjoint_left.mpr fun x hx hy => ?_
  have hx' : (⟨x, hBS (hAB hx)⟩ : S) ∈ (Subtype.val : S → M) ⁻¹' A := hx
  exact disjoint_left.mp hdis hx' hy

end DifferentialGeometry.Topology.PiecewiseLinear
