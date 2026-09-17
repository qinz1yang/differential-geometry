import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_iUnion {ι : Type*} [Finite ι]
    {P : ι → Set E} {Q : ι → Set F} {f : ι → E → F}
    (hP : ∀ i, IsPolyhedron (P i)) (hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (P i ∩ P j))
    (hmeet : ∀ i j, f i '' (P i ∩ P j) = Q i ∩ Q j) :
    ∃ g : E → F, IsPLHomeomorphOn g (⋃ i, P i) (⋃ i, Q i) ∧ ∀ i, EqOn g (f i) (P i) := by
  classical
  let g : E → F := fun x => if hx : ∃ i, x ∈ P i then f (Classical.choose hx) x else 0
  have hgEq : ∀ i, EqOn g (f i) (P i) := by
    intro i x hx
    have hex : ∃ j, x ∈ P j := ⟨i, hx⟩
    dsimp only [g]
    rw [dif_pos hex]
    exact hcompat _ i ⟨Classical.choose_spec hex, hx⟩
  have hgP : ∀ s : Finset ι, IsPiecewiseAffineOn g (⋃ i ∈ s, P i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (show IsPiecewiseAffineOn g ∅ from fun _ hx => hx.elim)
    | @insert i s hi ih =>
        rw [Finset.set_biUnion_insert]
        exact ((hf i).congr (hgEq i)).isPiecewiseAffineOn.union_of_isClosed ih (hP i).isClosed
          (isClosed_biUnion_finset fun j _ => (hP j).isClosed)
  let : Fintype ι := Fintype.ofFinite ι
  have hgPL : IsPiecewiseAffineOn g (⋃ i, P i) := by
    simpa only [Finset.mem_univ, iUnion_true] using hgP Finset.univ
  refine ⟨g, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (IsPolyhedron.iUnion hP) hgPL
    ⟨?_, ?_, ?_⟩, hgEq⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [hgEq i hxi]
    exact mem_iUnion.mpr ⟨i, (hf i).bijOn.mapsTo hxi⟩
  · intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hxy' : f i x = f j y := (hgEq i hxi).symm.trans (hxy.trans (hgEq j hyj))
    have hfy : f i x ∈ Q i ∩ Q j := by
      refine ⟨(hf i).bijOn.mapsTo hxi, ?_⟩
      rw [hxy']
      exact (hf j).bijOn.mapsTo hyj
    obtain ⟨z, hz, hfz⟩ := (hmeet i j).symm.subset hfy
    have hxz : x = z := (hf i).bijOn.injOn hxi hz.1 hfz.symm
    have hzy : z = y := (hf j).bijOn.injOn hz.2 hyj
      ((hcompat i j hz).symm.trans (hfz.trans hxy'))
    exact hxz.trans hzy
  · intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    obtain ⟨x, hx, hfx⟩ := (hf i).bijOn.surjOn hyi
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩, (hgEq i hx).trans hfx⟩

theorem exists_isPLHomeomorphOn_iUnion_of_subsingleton_inter {ι : Type*} [Finite ι]
    {P : ι → Set E} {Q : ι → Set F} {f : ι → E → F}
    (hP : ∀ i, IsPolyhedron (P i)) (hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i))
    (hQ : Pairwise fun i j => (Q i ∩ Q j).Subsingleton)
    (hmem : ∀ i j, ∀ x ∈ P i, f i x ∈ Q j ↔ x ∈ P j) :
    ∃ g : E → F, IsPLHomeomorphOn g (⋃ i, P i) (⋃ i, Q i) ∧ ∀ i, EqOn g (f i) (P i) := by
  apply exists_isPLHomeomorphOn_iUnion hP hf
  · intro i j x hx
    by_cases hij : i = j
    · subst j
      rfl
    · exact hQ hij ⟨(hf i).bijOn.mapsTo hx.1, (hmem i j x hx.1).mpr hx.2⟩
        ⟨(hmem j i x hx.2).mpr hx.1, (hf j).bijOn.mapsTo hx.2⟩
  · intro i j
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hf i).bijOn.mapsTo hx.1, (hmem i j x hx.1).mpr hx.2⟩
    · intro y hy
      obtain ⟨x, hx, hfx⟩ := (hf i).bijOn.surjOn hy.1
      exact ⟨x, ⟨hx, (hmem i j x hx).mp (hfx.symm ▸ hy.2)⟩, hfx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
