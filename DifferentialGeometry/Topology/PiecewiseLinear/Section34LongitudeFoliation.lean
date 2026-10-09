import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianProjection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryLongitudeCut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_full_proper_longitude_family
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hdim : Module.finrank ℝ F = 3)
    {g : E × ℝ → F} (hg : IsCylindricalDiagram g D.space M.space)
    (hends : ∀ x ∈ D.space, g (x, 0) = g (x, 1))
    {J Q : Set F} {f : F × F → F}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) (boundaryComplex 3 M).space)
    (hL : ∀ q ∈ Q, IsPLSphere 1 (f '' (J ×ˢ {q})))
    (hnon : ∀ q ∈ Q, ∀ hLC : f '' (J ×ˢ {q}) ⊆ M.space,
      ¬ (⟨inclusion hLC, continuous_inclusion hLC⟩ :
        C(f '' (J ×ˢ {q}), M.space)).Nullhomotopic)
    (hmark : ∀ q ∈ Q, ∃ z ∈ J,
      (g '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ))) ∩
        (f '' (J ×ˢ {q})) = {f (z, q)}) :
    ∃ (π : E → F) (γ : (boundaryComplex 2 D).space → ℝ → E × ℝ),
      IsPLHomeomorphOn π (boundaryComplex 2 D).space Q ∧
      Pairwise (fun x y => Disjoint (γ x '' Icc 0 1) (γ y '' Icc 0 1)) ∧
      (⋃ x, γ x '' Icc 0 1) = (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
      ∀ x, IsPLHomeomorphOn (γ x) (Icc 0 1)
          ((D.space ×ˢ Icc (0 : ℝ) 1) ∩ g ⁻¹' (f '' (J ×ˢ {π x}))) ∧
        γ x 0 = ((x : E), 0) ∧ γ x 1 = ((x : E), 1) ∧
        γ x '' Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) =
          {((x : E), 0)} ∧
        (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({1} : Set ℝ)) =
          {((x : E), 1)} := by
  have hbd := boundaryComplex_space_subset 2 D
  have hbdPL := isPolyhedron_space (boundaryComplex 2 D)
  have hslice := hg.isPLHomeomorphOn_slice hD.isPolyhedron (by norm_num :
    (0 : ℝ) ∈ Icc 0 1)
  have hbase : IsPLHomeomorphOn (fun x => g (x, 0)) (boundaryComplex 2 D).space
      (g '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ))) := by
    simpa only [prod_singleton, image_image] using hslice.restrict hbdPL hbd
  have hside := hg.image_side_eq_boundaryComplex D M hD hM hdim
  have hKB : g '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) ⊆
      (boundaryComplex 3 M).space := by
    rw [← hside]
    exact image_mono (prod_mono_right (by norm_num))
  obtain ⟨hπ, hfiber⟩ := hbase.projection_of_singleton_product_fibers hbdPL hf hKB hmark
  let π : E → F := fun x => (Function.invFunOn f (J ×ˢ Q) (g (x, 0))).2
  have hπ' : IsPLHomeomorphOn π (boundaryComplex 2 D).space Q := hπ
  have hLB (q : F) (hq : q ∈ Q) : f '' (J ×ˢ {q}) ⊆
      (boundaryComplex 3 M).space :=
    (image_mono (prod_mono_right (singleton_subset_iff.mpr hq))).trans hf.image_eq.subset
  have hex (x : (boundaryComplex 2 D).space) :
      ∃ γ : ℝ → E × ℝ, IsPLHomeomorphOn γ (Icc 0 1)
          ((D.space ×ˢ Icc (0 : ℝ) 1) ∩ g ⁻¹' (f '' (J ×ˢ {π x}))) ∧
        γ 0 = ((x : E), 0) ∧ γ 1 = ((x : E), 1) ∧
        γ '' Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        (γ '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) =
          {((x : E), 0)} ∧
        (γ '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({1} : Set ℝ)) =
          {((x : E), 1)} := by
    have hxQ := hπ'.bijOn.mapsTo x.2
    obtain ⟨z, -, hz⟩ := hmark (π x) hxQ
    have heq : g (x, 0) = f (z, π x) :=
      hz.subset ⟨hbase.bijOn.mapsTo x.2, hfiber x x.2⟩
    have htrace : (f '' (J ×ˢ {π x})) ∩
        (g '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ))) = {g (x, 0)} := by
      rw [inter_comm, hz, heq]
    obtain ⟨a, γ, ha, hap, hγ, hγ0, hγ1, hγside, -, hγbot, hγtop, -⟩ :=
      hg.exists_proper_boundary_longitude_cut D M hD hM hdim hends
        (hL (π x) hxQ) (hLB (π x) hxQ) (hnon (π x) hxQ _) htrace
    have hax : a = x := hslice.bijOn.injOn (hbd ha) (hbd x.2) hap
    exact ⟨γ, hγ, hax ▸ hγ0, hax ▸ hγ1, hγside, hax ▸ hγbot, hax ▸ hγtop⟩
  choose γ hγ hγ0 hγ1 hγside hγbot hγtop using hex
  refine ⟨π, γ, hπ', ?_, ?_, fun x =>
    ⟨hγ x, hγ0 x, hγ1 x, hγside x, hγbot x, hγtop x⟩⟩
  · intro x y hxy
    refine disjoint_left.mpr ?_
    intro w hwx hwy
    obtain ⟨v, hv, hvw⟩ := ((hγ x).image_eq.subset hwx).2
    obtain ⟨v', hv', hvw'⟩ := ((hγ y).image_eq.subset hwy).2
    have hvQ := hv.2.symm ▸ hπ'.bijOn.mapsTo x.2
    have hvQ' := hv'.2.symm ▸ hπ'.bijOn.mapsTo y.2
    have heq := hf.bijOn.injOn ⟨hv.1, hvQ⟩ ⟨hv'.1, hvQ'⟩ (hvw.trans hvw'.symm)
    exact hxy (Subtype.ext (hπ'.bijOn.injOn x.2 y.2
      (hv.2.symm.trans ((congrArg Prod.snd heq).trans hv'.2))))
  · apply Subset.antisymm
    · exact iUnion_subset fun x => hγside x
    · intro w hw
      have hgw : g w ∈ (boundaryComplex 3 M).space := hside ▸ mem_image_of_mem g hw
      obtain ⟨v, hv, hvw⟩ := hf.bijOn.surjOn hgw
      obtain ⟨x, hx, hxv⟩ := hπ'.bijOn.surjOn hv.2
      apply mem_iUnion.mpr
      refine ⟨⟨x, hx⟩, (hγ ⟨x, hx⟩).image_eq.symm.subset ?_⟩
      exact ⟨⟨hbd hw.1, hw.2⟩, ⟨v, ⟨hv.1, hxv.symm⟩, hvw⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
