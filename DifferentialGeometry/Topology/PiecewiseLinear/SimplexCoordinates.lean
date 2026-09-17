import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Algebra

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

theorem linearCombination_image_stdSimplex (v : ι → E) :
    Fintype.linearCombination ℝ v '' stdSimplex ℝ ι = convexHull ℝ (range v) := by
  classical
  have hmap : (Fintype.linearCombination ℝ v) ∘ (fun i : ι => Pi.single i (1 : ℝ)) = v := by
    funext i
    simp only [Function.comp_apply, Fintype.linearCombination_apply_single, one_smul]
  rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← range_comp, hmap]

theorem linearCombination_mem_convexHull_image_iff_of_affineIndependent {v : ι → E}
    (hv : AffineIndependent ℝ v) (J : Set ι) {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) :
    Fintype.linearCombination ℝ v x ∈ convexHull ℝ (v '' J) ↔ ∀ i ∉ J, x i = 0 := by
  classical
  have hcomb : Fintype.linearCombination ℝ v x = Finset.univ.affineCombination ℝ v x :=
    (Finset.affineCombination_eq_linear_combination _ _ _ hx.2).symm
  constructor
  · intro h i hi
    exact hv.eq_zero_of_affineCombination_mem_affineSpan hx.2
      (by rw [← hcomb]; exact convexHull_subset_affineSpan _ h) (Finset.mem_univ i) hi
  · intro hzero
    let d := Finset.univ.filter (fun i => i ∈ J)
    have hd (i) : i ∈ d ↔ i ∈ J := by simp [d]
    have hsum : ∑ i ∈ d, x i = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i (fun h => hi ((hd i).mpr h)))]
      exact hx.2
    have hval : ∑ i ∈ d, x i • v i = Fintype.linearCombination ℝ v x := by
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        rw [hzero i (fun h => hi ((hd i).mpr h)), zero_smul])
    rw [← hval]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hsum
      (fun i hi => subset_convexHull ℝ _ ⟨i, (hd i).mp hi, rfl⟩)

end Algebra

theorem isPLHomeomorphOn_linearCombination_of_affineIndependent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type} [Fintype ι] {v : ι → E} (hv : AffineIndependent ℝ v) :
    IsPLHomeomorphOn (Fintype.linearCombination ℝ v) (stdSimplex ℝ ι) (convexHull ℝ (range v)) := by
  have himage := linearCombination_image_stdSimplex v
  have hinj : InjOn (Fintype.linearCombination ℝ v) (stdSimplex ℝ ι) := by
    intro x hx y hy hxy
    apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ v).mp hv x y hx.2 hy.2
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hx.2,
      Finset.affineCombination_eq_linear_combination _ _ _ hy.2]
    exact hxy
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isHPolytope_stdSimplex ι).isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope (Fintype.linearCombination ℝ v).toAffineMap
      (isHPolytope_stdSimplex ι))
    ⟨fun _ hx => himage.subset ⟨_, hx, rfl⟩, hinj, fun _ hy => himage.symm.subset hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
