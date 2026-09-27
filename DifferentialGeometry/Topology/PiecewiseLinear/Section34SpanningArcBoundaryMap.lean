import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_rims_and_spanning_arcs
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {P : Set E} (hP : IsPolyhedron P) {a : ι → E} (ha : ∀ i, a i ∈ P)
    {A : ι → Set (E × ℝ)} {γ : ι → ℝ → E × ℝ}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (A i))
    (hγ0 : ∀ i, γ i 0 = (a i, 0)) (hγ1 : ∀ i, γ i 1 = (a i, 1))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hrim : ∀ i, A i ∩ (P ×ˢ ({0, 1} : Set ℝ)) = {(a i, 0), (a i, 1)}) :
    ∃ φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn φ
        ((P ×ˢ ({0, 1} : Set ℝ)) ∪ ⋃ i, ({a i} ×ˢ Icc (0 : ℝ) 1))
        ((P ×ˢ ({0, 1} : Set ℝ)) ∪ ⋃ i, A i) ∧
      EqOn φ id (P ×ˢ ({0, 1} : Set ℝ)) ∧
      ∀ i t, t ∈ Icc (0 : ℝ) 1 → φ (a i, t) = γ i t := by
  let R := P ×ˢ ({0, 1} : Set ℝ)
  let V : ι → Set (E × ℝ) := fun i => {a i} ×ˢ Icc (0 : ℝ) 1
  let f : ι → E × ℝ → E × ℝ := fun i x => γ i x.2
  have hR : IsPolyhedron R := hP.prod
    ((isHPolytope_singleton (0 : ℝ)).isPolyhedron.union
      (isHPolytope_singleton (1 : ℝ)).isPolyhedron)
  have hV (i : ι) : IsPolyhedron (V i) :=
    (isHPolytope_singleton (a i)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hf (i : ι) : IsPLHomeomorphOn (f i) (V i) (A i) := by
    have hs := (isPiecewiseAffineOn_of_affine
      (LinearMap.snd ℝ E ℝ).toAffineMap isOpen_univ).mono_of_isPolyhedron (hV i)
      (subset_univ _)
    have hpl := (hγ i).isPiecewiseAffineOn.comp hs
    change IsPiecewiseAffineOn (f i) (V i ∩ Prod.snd ⁻¹' Icc 0 1) at hpl
    rw [inter_eq_left.mpr (show V i ⊆ Prod.snd ⁻¹' Icc 0 1 from fun _ hx => hx.2)] at hpl
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (hV i) hpl
    refine ⟨fun x hx => (hγ i).bijOn.mapsTo hx.2, ?_, ?_⟩
    · intro x hx y hy hxy
      exact Prod.ext (hx.1.trans hy.1.symm) ((hγ i).bijOn.injOn hx.2 hy.2 hxy)
    · intro y hy
      obtain ⟨t, ht, hty⟩ := (hγ i).bijOn.surjOn hy
      exact ⟨(a i, t), ⟨rfl, ht⟩, hty⟩
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hi : (a i, (0 : ℝ)) ∈ A i :=
      hγ0 i ▸ (hγ i).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    have hj : (a j, (0 : ℝ)) ∈ A j :=
      hγ0 j ▸ (hγ j).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    exact disjoint_left.mp (hdis hne) hi (hij.symm ▸ hj)
  have hVdis : Pairwise fun i j => Disjoint (V i) (V j) := by
    intro i j hij
    exact disjoint_left.mpr fun x hx hy => hij (hinj (hx.1.symm.trans hy.1))
  obtain ⟨g, hg, hgi⟩ := exists_isPLHomeomorphOn_iUnion hV hf
    (fun i j x hx => by
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · exact (disjoint_left.mp (hVdis hij) hx.1 hx.2).elim)
    (fun i j => by
      rcases eq_or_ne i j with rfl | hij
      · rw [inter_self, inter_self, (hf i).image_eq]
      · rw [(hVdis hij).inter_eq, (hdis hij).inter_eq, image_empty])
  have hVr (i : ι) : V i ∩ R = {(a i, 0), (a i, 1)} := by
    ext x
    constructor
    · rintro ⟨hx, _, ht | ht⟩
      · exact Or.inl (Prod.ext hx.1 ht)
      · exact Or.inr (Prod.ext hx.1 ht)
    · rintro (rfl | rfl)
      · exact ⟨⟨rfl, le_rfl, zero_le_one⟩, ha i, Or.inl rfl⟩
      · exact ⟨⟨rfl, zero_le_one, le_rfl⟩, ha i, Or.inr rfl⟩
  have hfix : EqOn g id (R ∩ ⋃ i, V i) := by
    rintro x ⟨hxR, hxV⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
    rw [hgi i hi]
    rcases (hVr i).subset ⟨hi, hxR⟩ with rfl | rfl
    · exact hγ0 i
    · exact hγ1 i
  have hinter : R ∩ (⋃ i, V i) = R ∩ ⋃ i, A i := by
    rw [inter_iUnion, inter_iUnion]
    congr 1
    funext i
    rw [inter_comm R (V i), hVr, inter_comm R (A i), hrim]
  obtain ⟨φ, hφ, hφR, hφg⟩ := exists_isPLHomeomorphOn_union hR
    (IsPolyhedron.iUnion hV) hR.isPLHomeomorphOn_id hg hfix.symm
    (by rw [← hinter]; exact surjOn_id _)
  refine ⟨φ, hφ, hφR, ?_⟩
  intro i t ht
  have hmem : (a i, t) ∈ V i := ⟨rfl, ht⟩
  exact (hφg (mem_iUnion.mpr ⟨i, hmem⟩)).trans (hgi i hmem)

end DifferentialGeometry.Topology.PiecewiseLinear
