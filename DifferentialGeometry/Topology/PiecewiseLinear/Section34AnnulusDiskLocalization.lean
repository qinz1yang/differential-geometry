import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_range_cylinder_subset {E M N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [CompactSpace M] [ChartedSpace E (M × ℝ)]
    [TopologicalSpace N] [T2Space N] [ChartedSpace E N]
    (g : M × unitInterval → N) (hg : Continuous g) (hinj : Function.Injective g) :
    frontier (range g) ⊆
      g '' {p | (p.2 : ℝ) = 0} ∪ g '' {p | (p.2 : ℝ) = 1} := by
  have hmiddle : ∀ a : M × unitInterval, (a.2 : ℝ) ∈ Ioo (0 : ℝ) 1 →
      g a ∈ interior (range g) := by
    intro a ha
    let U : Set (M × ℝ) := univ ×ˢ Ioo (0 : ℝ) 1
    let k : U → M × unitInterval := fun p =>
      (p.val.1, ⟨p.val.2, Ioo_subset_Icc_self p.property.2⟩)
    have hkc : Continuous k := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hki : Function.Injective k := by
      intro p q hpq
      exact Subtype.ext (congrArg (fun z : M × unitInterval => (z.1, (z.2 : ℝ))) hpq)
    let f : U → N := g ∘ k
    let f₀ : M × ℝ → N := Function.extend Subtype.val f (fun _ => g a)
    have heq (z : U) : f₀ z.val = f z :=
      Function.Injective.extend_apply Subtype.val_injective f (fun _ => g a) z
    have hc : ContinuousOn f₀ U := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hg.comp hkc using 1
      funext z
      exact heq z
    have hi : InjOn f₀ U := by
      intro z hz w hw hzw
      exact congrArg (fun p : U => (p : M × ℝ))
        ((hinj.comp hki) ((heq ⟨z, hz⟩).symm.trans (hzw.trans (heq ⟨w, hw⟩))))
    have hopen := DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
      (E := E) (show IsOpen U from isOpen_univ.prod isOpen_Ioo) hc hi
    have hsub : f₀ '' U ⊆ range g := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨k ⟨z, hz⟩, (heq ⟨z, hz⟩).symm⟩
    apply interior_maximal hsub hopen
    exact ⟨(a.1, (a.2 : ℝ)), ⟨mem_univ _, ha⟩, heq ⟨_, ⟨mem_univ _, ha⟩⟩⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (isCompact_range hg).isClosed.frontier_subset hz
  by_cases h₀ : (a.2 : ℝ) = 0
  · exact Or.inl ⟨a, h₀, rfl⟩
  by_cases h₁ : (a.2 : ℝ) = 1
  · exact Or.inr ⟨a, h₁, rfl⟩
  exact False.elim (hz.2 (hmiddle a
    ⟨lt_of_le_of_ne a.2.property.1 (fun h => h₀ h.symm),
      lt_of_le_of_ne a.2.property.2 h₁⟩))

theorem IsAnnulusOn.frontier_subset {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {A A₀ A₁ : Set M}
    (hA : IsAnnulusOn A A₀ A₁) : frontier A ⊆ A₀ ∪ A₁ := by
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
    frontier_range_cylinder_subset (E := EuclideanSpace ℝ (Fin 2)) g hg hi

theorem IsAnnulusOn.subset_of_isPreconnected_of_disjoint_boundary {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {A A₀ A₁ D : Set M} (hA : IsAnnulusOn A A₀ A₁) (hD : IsPreconnected D)
    (hDA : (D ∩ A).Nonempty) (hbound : Disjoint D (A₀ ∪ A₁)) : D ⊆ A := by
  exact IsPreconnected.subset_of_disjoint_frontier hD hDA
    (hbound.mono_right hA.frontier_subset)

theorem IsAnnulusOn.preimage_subtype {M : Type*} [TopologicalSpace M]
    {S A A₀ A₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S) :
    IsAnnulusOn ((Subtype.val : S → M) ⁻¹' A)
      (Subtype.val ⁻¹' A₀) (Subtype.val ⁻¹' A₁) := by
  let e : A ≃ₜ ((Subtype.val : S → M) ⁻¹' A) :=
    { toFun := fun x => ⟨⟨x.val, hAS x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  obtain ⟨φ, h₀, h₁⟩ := hA
  refine ⟨φ.trans e, ?_, ?_⟩
  · rw [h₀]
    ext x
    constructor
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      exact ⟨e (φ p), ⟨p, hp, rfl⟩, Subtype.ext hy⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      exact ⟨φ p, ⟨p, hp, rfl⟩, congrArg Subtype.val hy⟩
  · rw [h₁]
    ext x
    constructor
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      exact ⟨e (φ p), ⟨p, hp, rfl⟩, Subtype.ext hy⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      exact ⟨φ p, ⟨p, hp, rfl⟩, congrArg Subtype.val hy⟩

theorem IsAnnulusOn.subset_of_isPreconnected_of_disjoint_boundary_within {M : Type*}
    [TopologicalSpace M] [T2Space M] {S A A₀ A₁ D : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S) (hDS : D ⊆ S)
    (hD : IsPreconnected D) (hDA : (D ∩ A).Nonempty)
    (hbound : Disjoint D (A₀ ∪ A₁)) : D ⊆ A := by
  have hD' : IsPreconnected ((Subtype.val : S → M) ⁻¹' D) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hDS] using hD
  have hDA' : (((Subtype.val : S → M) ⁻¹' D) ∩ (Subtype.val ⁻¹' A)).Nonempty := by
    obtain ⟨x, hxD, hxA⟩ := hDA
    exact ⟨⟨x, hDS hxD⟩, hxD, hxA⟩
  have hb : Disjoint ((Subtype.val : S → M) ⁻¹' D)
      ((Subtype.val ⁻¹' A₀) ∪ (Subtype.val ⁻¹' A₁)) :=
    disjoint_left.mpr fun _ hx hy => disjoint_left.mp hbound hx hy
  have hsub := (hA.preimage_subtype hAS).subset_of_isPreconnected_of_disjoint_boundary
    hD' hDA' hb
  exact fun x hx => hsub (show (⟨x, hDS hx⟩ : S) ∈ Subtype.val ⁻¹' D from hx)

theorem IsPLSphere.nonempty_chartedSpace_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 2 S) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) S) := by
  obtain ⟨K, hKfin, hKspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (hKspace.symm ▸ hS)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) K.space := combinatorialChartedSpace K hK
  exact ⟨(Homeomorph.setCongr hKspace).chartedSpace⟩

theorem IsPLSphere.subset_annulus_of_isPreconnected_of_disjoint_boundary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ D : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (hDS : D ⊆ S) (hD : IsPreconnected D)
    (hDA : (D ∩ A).Nonempty) (hbound : Disjoint D (A₀ ∪ A₁)) : D ⊆ A := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_two
  let _ := hchart
  exact hA.subset_of_isPreconnected_of_disjoint_boundary_within hAS hDS hD hDA hbound

theorem IsPLCellOn.nonempty_chartedSpace_boundary {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M}
    (hS : IsPLCellOn 3 S B) : Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) B) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  let f : frontier P → M := fun x => u x.val
  have hf : Continuous f := (hu.continuousOn.mono hfront).domRestrict
  have hi : Function.Injective f := fun x y hxy =>
    Subtype.ext (hu.injOn (hfront x.property) (hfront y.property) hxy)
  let _ : CompactSpace (frontier P) :=
    isCompact_iff_compactSpace.mp hP.isPLSphere_frontier.isPolyhedron.isCompact
  have hfemb := (hf.isClosedEmbedding hi).isEmbedding
  have hrange : range f = B := by
    rw [hB]
    exact range_comp u Subtype.val |>.trans (by rw [Subtype.range_coe])
  obtain ⟨hchart⟩ := hP.isPLSphere_frontier.nonempty_chartedSpace_two
  let _ := hchart
  exact ⟨(hfemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).chartedSpace⟩

theorem IsPLCellOn.subset_annulus_of_isPreconnected_of_disjoint_boundary {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ D : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hDB : D ⊆ B) (hD : IsPreconnected D)
    (hDA : (D ∩ A).Nonempty) (hbound : Disjoint D (A₀ ∪ A₁)) : D ⊆ A := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  exact hA.subset_of_isPreconnected_of_disjoint_boundary_within hAB hDB hD hDA hbound

theorem IsAnnulusOn.isPreconnected_ends {M : Type*} [TopologicalSpace M]
    {A A₀ A₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) :
    IsPreconnected A₀ ∧ IsPreconnected A₁ := by
  let C := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hC : IsPreconnected C := by
    apply isPreconnected_sphere
    rw [← Module.finrank_eq_rank']
    norm_num
  let _ : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  obtain ⟨φ, h₀, h₁⟩ := hA
  have hlevel (t : unitInterval) :
      IsPreconnected (Subtype.val '' (φ '' {p | (p.2 : ℝ) = (t : ℝ)})) := by
    let f : C → M := fun x => (φ (x, t)).val
    have hf : Continuous f := continuous_subtype_val.comp
      (φ.continuous.comp (continuous_id.prodMk continuous_const))
    have hrange : range f = Subtype.val '' (φ '' {p | (p.2 : ℝ) = (t : ℝ)}) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨φ (x, t), ⟨(x, t), rfl, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
        have ht : p.2 = t := Subtype.ext hp
        exact ⟨p.1, congrArg (fun q => (φ q).val) (Prod.ext rfl ht.symm)⟩
    rw [← hrange]
    exact isPreconnected_range hf
  exact ⟨h₀ ▸ hlevel 0, h₁ ▸ hlevel 1⟩

theorem IsPLSphere.exists_disk_in_annulus_or_separating_ends {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ J : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (hJ : IsPLSphere 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    (∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J) ∨
    ∃ (D₀ D₁ : Set E) (r₀ r₁ : (Fin 3 → ℝ) → E),
      D₀ ∪ D₁ = S ∧ D₀ ∩ D₁ = J ∧
      IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      r₀ '' stdSimplexBoundary 2 = J ∧ r₁ '' stdSimplexBoundary 2 = J ∧
      A₀ ⊆ D₀ ∧ A₁ ⊆ D₁ := by
  obtain ⟨D₀, D₁, hU, hI, r₀, r₁, hr₀, hr₁, hb₀, hb₁⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ (hJA.trans hAS)
  have hside : ∀ C, C ⊆ S → IsPreconnected C → Disjoint C J →
      C ⊆ D₀ ∨ C ⊆ D₁ := by
    intro C hCS hC hCJ
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hC D₀ D₁
      (IsPLBall.isPolyhedron ⟨r₀, hr₀⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁, hr₁⟩).isClosed (hU ▸ hCS) ?_
    rw [hI]
    exact hCJ.inter_eq
  have hdisk : ∀ (D D' : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      D ∪ D' = S → D ∩ D' = J → A₀ ⊆ D' → A₁ ⊆ D' → D ⊆ A := by
    intro D D' r hr hcover hmeet h₀ h₁
    have hJD : J ⊆ D := hmeet ▸ inter_subset_left
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAS
      (hcover ▸ subset_union_left) (IsPLBall.isConnected ⟨r, hr⟩).isPreconnected
    · obtain ⟨x, hx⟩ := hJ.nonempty
      exact ⟨x, hJD hx, hJA hx⟩
    · refine disjoint_left.mpr fun x hxD hxend => ?_
      have hxD' : x ∈ D' := (union_subset h₀ h₁) hxend
      exact disjoint_left.mp hends (hmeet ▸ ⟨hxD, hxD'⟩) hxend
  rcases hside A₀ (hA.first_subset.trans hAS) hA.isPreconnected_ends.1
      (hends.mono_right subset_union_left).symm with h₀ | h₀ <;>
    rcases hside A₁ (hA.second_subset.trans hAS) hA.isPreconnected_ends.2
      (hends.mono_right subset_union_right).symm with h₁ | h₁
  · exact Or.inl ⟨D₁, r₁, hr₁, hdisk D₁ D₀ r₁ hr₁
      (by rwa [union_comm]) (by rwa [inter_comm]) h₀ h₁, hb₁⟩
  · exact Or.inr ⟨D₀, D₁, r₀, r₁, hU, hI, hr₀, hr₁, hb₀, hb₁, h₀, h₁⟩
  · exact Or.inr ⟨D₁, D₀, r₁, r₀, by rwa [union_comm], by rwa [inter_comm],
      hr₁, hr₀, hb₁, hb₀, h₀, h₁⟩
  · exact Or.inl ⟨D₀, r₀, hr₀, hdisk D₀ D₁ r₀ hr₀ hU hI h₀ h₁, hb₀⟩

end DifferentialGeometry.Topology.PiecewiseLinear
