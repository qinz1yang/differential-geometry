import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellInjectivity
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem crossing_of_glue_boundary_arc {D D₁ D₂ : SingularTwoCell M} {BdM : Set M}
    {P Q B : Set (EuclideanSpace ℝ (Fin 2))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf₁ : IsPLHomeomorphOn f₁ P D₁.domain) (hf₂ : IsPLHomeomorphOn f₂ Q D₂.domain)
    (hDP : EqOn D (D₁ ∘ f₁) P) (hDQ : EqOn D (D₂ ∘ f₂) Q)
    (hdom : D.domain = P ∪ Q) (hB : f₂ '' (P ∩ Q) = B)
    (hD₂inj : InjOn D₂ D₂.domain)
    (hD₂disj : ∀ x ∈ D₂.domain, x ∉ B → ∀ z ∈ D₁.domain, D₂ x ≠ D₁ z)
    (hdisj : Disjoint (doublePointSet D₁ D₁.domain) (D₂ '' D₂.domain))
    (hD₁cross : ∀ y ∈ doublePointSet D₁ D₁.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D₁) (D₁.domain ∩ D₁ ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y)) :
    ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y) := by
  have hdouble := doublePointSet_of_glue_boundary_arc hf₁ hf₂ hDP hDQ hdom hB hD₂inj hD₂disj
  have hluneClosed : IsClosed (D₂ '' D₂.domain) :=
    (D₂.isPLBall_domain.isPolyhedron.isCompact.image_of_continuousOn D₂.continuousOn).isClosed
  have hQP : ∀ x ∈ D.domain, D x ∉ D₂ '' D₂.domain → x ∈ P := by
    intro x hx hnot
    rw [hdom] at hx
    rcases hx with hxP | hxQ
    · exact hxP
    · exact absurd ⟨f₂ x, hf₂.bijOn.mapsTo hxQ, (hDQ hxQ).symm⟩ hnot
  intro y hy
  rw [hdouble] at hy
  obtain ⟨e, he, hye, hcross⟩ := hD₁cross y hy
  have hyO : y ∈ (D₂ '' D₂.domain)ᶜ := Set.disjoint_left.mp hdisj hy
  have hmapsTo : MapsTo f₁ (P ∩ D ⁻¹' e.source) (D₁.domain ∩ D₁ ⁻¹' e.source) := by
    intro x hx
    have hval : D₁ (f₁ x) = D x := (hDP hx.1).symm
    exact ⟨hf₁.bijOn.mapsTo hx.1, by rw [mem_preimage, hval]; exact hx.2⟩
  have hback : ∀ x ∈ P, f₁ x ∈ D₁.domain ∩ D₁ ⁻¹' e.source → x ∈ P ∩ D ⁻¹' e.source := by
    intro x hxP hmem
    exact ⟨hxP, by rw [mem_preimage, hDP hxP]; exact hmem.2⟩
  have hbij : BijOn f₁ (P ∩ D ⁻¹' e.source) (D₁.domain ∩ D₁ ⁻¹' e.source) := by
    refine ⟨hmapsTo, hf₁.bijOn.injOn.mono inter_subset_left, ?_⟩
    rintro w hw
    obtain ⟨x, hxP, rfl⟩ := hf₁.bijOn.surjOn hw.1
    exact ⟨x, hback x hxP hw, rfl⟩
  have hstep1 := hcross.precomp_bijOn_of_isPLHomeomorphOn hf₁ hbij inter_subset_left
    inter_subset_left hback
  have hstep2 : HasPLNormalDoubleCrossingAt (e ∘ D) (P ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y) :=
    hstep1.congr_source fun x hx => congrArg e (hDP hx.1).symm
  refine ⟨e, he, hye, hstep2.mono_of_subset ?_ Subset.rfl ?_ ?_⟩
  · intro x hx
    exact ⟨by rw [hdom]; exact Or.inl hx.1, hx.2⟩
  · intro a ha hay
    have haD : D a = y := e.injOn ha.2 hye hay
    have hpre : D ⁻¹' (D₂ '' D₂.domain)ᶜ ∈ 𝓝[D.domain] a := by
      refine (D.continuousOn a (by rw [hdom]; exact Or.inl ha.1)).preimage_mem_nhdsWithin ?_
      rw [haD]
      exact hluneClosed.isOpen_compl.mem_nhds hyO
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    refine ⟨V, hV, ?_⟩
    rintro x ⟨⟨hxd, hxe⟩, hxV⟩
    exact ⟨hQP x hxd (hVsub ⟨hxV, hxd⟩), hxe⟩
  · have hWopen : IsOpen (e.target ∩ e.symm ⁻¹' (D₂ '' D₂.domain)ᶜ) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hluneClosed.isOpen_compl
    have hWmem : e y ∈ e.target ∩ e.symm ⁻¹' (D₂ '' D₂.domain)ᶜ := by
      refine ⟨e.map_source hye, ?_⟩
      rw [mem_preimage, e.left_inv hye]
      exact hyO
    filter_upwards [hWopen.mem_nhds hWmem] with z hz x hx
    have hz' : e (D x) = z := hx.2
    have hval : D x = e.symm z := by
      rw [← hz', e.left_inv hx.1.2]
    exact ⟨hQP x hx.1.1 (by rw [hval]; exact hz.2), hx.1.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
