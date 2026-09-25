import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedFillingCylinder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLHomeomorphInto.exists_aligned_cylinder_of_carrying_rims
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite B.faces] [Finite R.faces] (hB : IsPLBall 2 B.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {g : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g B.space R.space)
    (hends : ∀ z ∈ B.space, g (z, 0) = g (z, 1))
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hRP : R.space ⊆ P)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hRS : u '' R.space ⊆ S)
    (L : Fin 2 → Set M) (hL : ∀ k, IsPolyhedralSphere (n := 3) 1 (L k))
    (hLC : ∀ k, L k ⊆ u '' frontier R.space)
    (hdis : Pairwise fun k l => Disjoint (L k) (L l))
    (hcarry : ∀ k, CarriesFundamentalGroupOnto (L k) S) :
    ∃ (g' : E × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → (boundaryComplex 2 B).space),
      IsCylindricalDiagram g' B.space R.space ∧
      (∀ z ∈ B.space, g' (z, 0) = g' (z, 1)) ∧ Function.Injective a ∧
      ∀ k, (u ∘ g') '' ({(a k : E)} ×ˢ Icc (0 : ℝ) 1) = L k := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hC := hg.isCombinatorialSolidTorus hB (by simp)
  obtain ⟨J, Q', f, p, hJ, hQ, hf, hp, hpinj, hLfamily⟩ :=
    hu.exists_boundary_product_coordinates_of_carrying_rims hC hRP hS hRS L (by norm_num)
      hL hLC hdis hcarry
  have hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {p 0})) S :=
    hLfamily 0 ▸ hcarry 0
  obtain ⟨g₀, q, hg₀, he₀, hq, -, -, hmark⟩ :=
    hu.exists_cylinder_with_marked_meridian B R hB hR hg hends hRP hJ hQ hf ⟨p 0, hp 0⟩
      hS hRS hgen
  have hlong (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ Q') :=
    hu.not_nullhomotopic_all_model_product_fibers hC hRP hJ hQ hf
      hS hRS (hp 0) hgen hz
  have hfrontR := frontier_space_eq_boundaryComplex_space_of_finrank (by simp) R hR
  have hfB : IsPLHomeomorphOn f (J ×ˢ Q') (boundaryComplex 3 R).space := hfrontR ▸ hf
  obtain ⟨g', hg', hends', hq', hseam, -⟩ :=
    hg₀.exists_rotation_with_prescribed_meridian B hB he₀ (by norm_num) hq rfl
  have hmark' : ∀ z ∈ Q', ∃ x ∈ J,
      (g' '' ((boundaryComplex 2 B).space ×ˢ ({0} : Set ℝ))) ∩
        (f '' (J ×ˢ {z})) = {f (x, z)} := by
    intro z hz
    obtain ⟨x, hx, heq, -⟩ := hmark z hz
    exact ⟨x, hx, hseam.symm ▸ heq⟩
  obtain ⟨π, γ, hπ, hdis, hcover, hγ⟩ :=
    hg'.exists_full_proper_longitude_family B R hB hR (by simp) hends' hfB
      (fun z hz => (hlong z hz).1) (fun z hz => (hlong z hz).2.2) hmark'
  choose a₀ ha₀ hπa using fun k => hπ.bijOn.surjOn (hp k)
  let a : Fin 2 → (boundaryComplex 2 B).space := fun k => ⟨a₀ k, ha₀ k⟩
  have hainj : Function.Injective a := by
    intro k l hkl
    apply hpinj
    have heq := congrArg (fun z : (boundaryComplex 2 B).space => π (z : E)) hkl
    exact (hπa k).symm.trans (heq.trans (hπa l))
  have himage (k : Fin 2) : (u ∘ g' ∘ γ (a k)) '' Icc 0 1 =
      (u ∘ f) '' (J ×ˢ {p k}) := by
    have hγk := (hγ (a k)).1.image_eq
    change γ (a k) '' Icc 0 1 =
      (B.space ×ˢ Icc (0 : ℝ) 1) ∩ g' ⁻¹' (f '' (J ×ˢ {π (a₀ k)})) at hγk
    rw [hπa k] at hγk
    have hLC : f '' (J ×ˢ {p k}) ⊆ R.space := (hlong (p k) (hp k)).2.1
    have hgL : g' '' ((B.space ×ˢ Icc (0 : ℝ) 1) ∩
        g' ⁻¹' (f '' (J ×ˢ {p k}))) = f '' (J ×ˢ {p k}) := by
      rw [image_inter_preimage, hg'.image_eq, inter_eq_right.mpr hLC]
    simp only [image_comp, hγk, hgL]
  have hxy : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hainj h)
  obtain ⟨Φ, hΦ, hfix, hmap⟩ :=
    exists_prism_straightening_of_full_arc_family B hB hdis hcover
      (fun x => ⟨(hγ x).1.image_eq.symm ▸ (hγ x).1, (hγ x).2⟩) hxy
  obtain ⟨hg'', hends'', -⟩ := hg'.precomp_fixed_caps_with_ends hends' hΦ hfix
  refine ⟨g' ∘ Φ, a, hg'', hends'', hainj, fun k => ?_⟩
  have heq : (u ∘ (g' ∘ Φ)) '' ({(a k : E)} ×ˢ Icc (0 : ℝ) 1) =
      (u ∘ g' ∘ γ (a k)) '' Icc 0 1 := by
    rw [singleton_prod, image_image]
    apply image_congr
    intro t ht
    apply congrArg (u ∘ g')
    fin_cases k
    · exact (hmap t ht).1
    · exact (hmap t ht).2
  exact heq.trans ((himage k).trans (hLfamily k).symm)

end DifferentialGeometry.Topology.PiecewiseLinear
