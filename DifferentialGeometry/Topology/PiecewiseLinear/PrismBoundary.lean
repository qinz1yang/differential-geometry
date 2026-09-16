import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.isPLHomeomorphOn_prod_const {P : Set E} (hP : IsPolyhedron P) (a : ℝ) :
    IsPLHomeomorphOn (fun x : E => (x, a)) P (P ×ˢ {a}) := by
  let f := (AffineMap.id ℝ E).prod (AffineMap.const ℝ E a)
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine f isOpen_univ).mono_of_isPolyhedron hP (subset_univ _))
  exact ⟨fun _ hx => ⟨hx, rfl⟩, fun _ _ _ _ heq => congrArg Prod.fst heq,
    fun y hy => ⟨y.1, hy.1, Prod.ext rfl hy.2.symm⟩⟩

theorem IsPolyhedron.isPLHomeomorphOn_fst_prod_const {P : Set E} (hP : IsPolyhedron P) (a : ℝ) :
    IsPLHomeomorphOn (Prod.fst : E × ℝ → E) (P ×ˢ {a}) P := by
  have h := hP.isPLHomeomorphOn_prod_const a
  exact h.symm.congr fun x hx => (congrArg Prod.fst (h.bijOn.invOn_invFunOn.2 hx)).symm

open Classical in
theorem prod_left_endpoint_subset_boundaryComplex [d : DecidableEq (E × ℝ)] {P : Set E} (hP : IsPLBall 2 P)
    {a b : ℝ} (hab : a < b) (A : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite A.faces]
    (hAP : A.space = P ×ˢ Icc a b) :
    P ×ˢ {a} ⊆ (boundaryComplex 3 A).space := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  have hA : IsPLBall 3 A.space := hAP.symm ▸ isPLBall_three_prod hP (isPLBall_Icc hab)
  let B := P ×ˢ Icc (2 * a - b) a
  have hB : IsPLBall 3 B := isPLBall_three_prod hP (isPLBall_Icc (by linarith))
  have hC : IsPLBall 3 (P ×ˢ Icc (2 * a - b) b) :=
    isPLBall_three_prod hP (isPLBall_Icc (by linarith))
  obtain ⟨K, hfin, hspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have hK : IsPLBall 3 K.space := hspace.symm ▸ hC
  have hAK : A.space ⊆ K.space := by
    rw [hAP, hspace]
    rintro x ⟨hx, hxa, hxb⟩
    exact ⟨hx, by linarith, hxb⟩
  have hBK : B ⊆ K.space := by
    rw [hspace]
    rintro x ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, by linarith⟩
  have hmeet : A.space ∩ B = P ×ˢ {a} := by
    rw [hAP]
    ext x
    simp only [B, mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx, ha, _⟩, ⟨_, _, hb⟩⟩
      exact ⟨hx, le_antisymm hb ha⟩
    · rintro ⟨hx, heq⟩
      rw [heq]
      exact ⟨⟨hx, le_rfl, hab.le⟩, hx, by linarith, le_rfl⟩
  have hI : IsPLBall 2 (A.space ∩ B) := by
    rw [hmeet]
    exact hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hi := hK.isCombinatorialManifoldWithBoundary.inter_subset_boundaryComplex_of_isPLBall
    A hA hAK hB hBK hI
  rwa [hmeet] at hi

end DifferentialGeometry.Topology.PiecewiseLinear
