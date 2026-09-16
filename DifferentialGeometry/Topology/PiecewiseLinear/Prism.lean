import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLBall_of_linear_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {P : Set E} (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] E) (g : E → Fin (n + 1) → ℝ)
    (hf : MapsTo f (stdSimplex ℝ (Fin (n + 1))) P)
    (hg : MapsTo g P (stdSimplex ℝ (Fin (n + 1))))
    (hgf : LeftInvOn g f (stdSimplex ℝ (Fin (n + 1)))) (hfg : RightInvOn g f P) :
    IsPLBall n P := by
  refine ⟨f, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_stdSimplex (Fin (n + 1))).isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope f.toAffineMap
      (isHPolytope_stdSimplex (Fin (n + 1)))) ?_⟩
  exact ⟨hf, hgf.injOn, fun y hy => ⟨g y, hg hy, hfg hy⟩⟩

private theorem isPLBall_lower_triangle_prism :
    IsPLBall 3 {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ x 1} := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun v => WithLp.toLp 2 ![v 1, v 2 + v 3, v 3]
      map_add' := by intro v w; ext i; fin_cases i <;> simp; ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp; ring }
  let g := fun x : EuclideanSpace ℝ (Fin 3) => ![1 - x 0 - x 1, x 0, x 1 - x 2, x 2]
  apply isPLBall_of_linear_coordinates (n := 3) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    change 0 ≤ v 1 ∧ 0 ≤ v 2 + v 3 ∧ v 1 + (v 2 + v 3) ≤ 1 ∧ 0 ≤ v 3 ∧ v 3 ≤ v 2 + v 3
    have h0 := hv.1 0
    have h1 := hv.1 1
    have h2 := hv.1 2
    have h3 := hv.1 3
    exact ⟨h1, by linarith, by linarith, h3, by linarith⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [g] <;> rcases hx with ⟨h0, h1, hsum, h2, h21⟩ <;> linarith
    · simp [g, Fin.sum_univ_four]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    ext i
    fin_cases i <;> simp [g, f]; linarith
  · intro x _
    ext i
    fin_cases i <;> simp [g, f]

private theorem isPLBall_middle_triangle_prism :
    IsPLBall 3 {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 0 + x 1} := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun v => WithLp.toLp 2 ![v 1 + v 2, v 3, v 2 + v 3]
      map_add' := by intro v w; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp <;> ring }
  let g := fun x : EuclideanSpace ℝ (Fin 3) => ![1 - x 0 - x 1, x 0 + x 1 - x 2, x 2 - x 1, x 1]
  apply isPLBall_of_linear_coordinates (n := 3) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    change 0 ≤ v 1 + v 2 ∧ 0 ≤ v 3 ∧ v 1 + v 2 + v 3 ≤ 1 ∧ v 3 ≤ v 2 + v 3 ∧
      v 2 + v 3 ≤ v 1 + v 2 + v 3
    have h0 := hv.1 0
    have h1 := hv.1 1
    have h2 := hv.1 2
    have h3 := hv.1 3
    exact ⟨by linarith, h3, by linarith, by linarith, by linarith⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp [g] <;> rcases hx with ⟨h0, h1, hsum, h21, h2sum⟩ <;> linarith
    · simp [g, Fin.sum_univ_four]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    ext i
    fin_cases i <;> simp [g, f]; linarith
  · intro x _
    ext i
    fin_cases i <;> simp [g, f]

private theorem isPLBall_upper_triangle_prism :
    IsPLBall 3 {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ x 2 ∧ x 2 ≤ 1} := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun v => WithLp.toLp 2 ![v 2, v 3, v 1 + v 2 + v 3]
      map_add' := by intro v w; ext i; fin_cases i <;> simp; ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp; ring }
  let g := fun x : EuclideanSpace ℝ (Fin 3) => ![1 - x 2, x 2 - x 0 - x 1, x 0, x 1]
  apply isPLBall_of_linear_coordinates (n := 3) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    change 0 ≤ v 2 ∧ 0 ≤ v 3 ∧ v 2 + v 3 ≤ v 1 + v 2 + v 3 ∧ v 1 + v 2 + v 3 ≤ 1
    have h0 := hv.1 0
    have h1 := hv.1 1
    exact ⟨hv.1 2, hv.1 3, by linarith, by linarith⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp [g] <;> rcases hx with ⟨h0, h1, hsum, h2⟩ <;> linarith
    · simp [g, Fin.sum_univ_four]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    ext i
    fin_cases i <;> simp [g, f] <;> linarith
  · intro x _
    ext i
    fin_cases i <;> simp [g, f]; ring

private theorem isPLBall_triangle_prism_section (b : Bool) :
    IsPLBall 2 {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ x 2 = if b then x 0 + x 1 else x 1} := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun v => WithLp.toLp 2 ![v 1, v 2, if b then v 1 + v 2 else v 2]
      map_add' := by intro v w; ext i; fin_cases i <;> cases b <;> simp; ring
      map_smul' := by intro a v; ext i; fin_cases i <;> cases b <;> simp; ring }
  let g := fun x : EuclideanSpace ℝ (Fin 3) => ![1 - x 0 - x 1, x 0, x 1]
  apply isPLBall_of_linear_coordinates (n := 2) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    refine ⟨hv.1 1, hv.1 2, ?_, rfl⟩
    change v 1 + v 2 ≤ 1
    linarith [hv.1 0]
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp [g] <;> rcases hx with ⟨h0, h1, hsum, heq⟩ <;> linarith
    · simp [g, Fin.sum_univ_three]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    ext i
    fin_cases i <;> simp [g, f]; linarith
  · intro x hx
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hx.2.2.2.symm

theorem isPLBall_triangle_prism :
    IsPLBall 3 {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1} := by
  let P := {x : EuclideanSpace ℝ (Fin 3) |
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ x 1}
  let Q := {x : EuclideanSpace ℝ (Fin 3) |
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 0 + x 1}
  let R := {x : EuclideanSpace ℝ (Fin 3) |
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ x 2 ∧ x 2 ≤ 1}
  have hP : IsPLBall 3 P := isPLBall_lower_triangle_prism
  have hQ : IsPLBall 3 Q := isPLBall_middle_triangle_prism
  have hR : IsPLBall 3 R := isPLBall_upper_triangle_prism
  have hi : P ∩ Q = {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ x 2 = x 1} := by
    ext x
    simp only [P, Q, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1, hsum, h2, h21⟩, ⟨_, _, _, h12, _⟩⟩
      exact ⟨h0, h1, hsum, le_antisymm h21 h12⟩
    · rintro ⟨h0, h1, hsum, heq⟩
      rw [heq]
      exact ⟨⟨h0, h1, hsum, h1, le_rfl⟩, h0, h1, hsum, le_rfl, by linarith⟩
  have hI : IsPLBall 2 (P ∩ Q) := by
    rw [hi]
    exact isPLBall_triangle_prism_section false
  have hPQ : IsPLBall 3 (P ∪ Q) := isPLBall_union_of_inter_isPLBall_two hP hQ hI
    (hQ.inter_subset_frontier_of_isPLBall hI (by decide))
    (by
      rw [inter_comm] at hI ⊢
      exact hP.inter_subset_frontier_of_isPLBall hI (by decide))
  have hj : (P ∪ Q) ∩ R = {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ x 2 = x 0 + x 1} := by
    ext x
    simp only [P, Q, R, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h | h, h0, h1, hsum2, h2⟩
      · rcases h with ⟨_, _, hsum, _, h21⟩
        exact ⟨h0, h1, hsum, by linarith⟩
      · rcases h with ⟨_, _, hsum, _, h2sum⟩
        exact ⟨h0, h1, hsum, le_antisymm h2sum hsum2⟩
    · rintro ⟨h0, h1, hsum, heq⟩
      rw [heq]
      exact ⟨Or.inr ⟨h0, h1, hsum, by linarith, le_rfl⟩, h0, h1, le_rfl, hsum⟩
  have hJ : IsPLBall 2 ((P ∪ Q) ∩ R) := by
    rw [hj]
    exact isPLBall_triangle_prism_section true
  have hball := isPLBall_union_of_inter_isPLBall_two hPQ hR hJ
    (hR.inter_subset_frontier_of_isPLBall hJ (by decide))
    (by
      rw [inter_comm] at hJ ⊢
      exact hPQ.inter_subset_frontier_of_isPLBall hJ (by decide))
  have hcover : (P ∪ Q) ∪ R = {x : EuclideanSpace ℝ (Fin 3) |
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1} := by
    ext x
    simp only [P, Q, R, mem_union, mem_ofPred_eq]
    constructor
    · rintro ((⟨h0, h1, hsum, h2, h21⟩ | ⟨h0, h1, hsum, h12, h2sum⟩) | ⟨h0, h1, hsum2, h2⟩)
      · exact ⟨h0, h1, hsum, h2, by linarith⟩
      · exact ⟨h0, h1, hsum, by linarith, by linarith⟩
      · exact ⟨h0, h1, by linarith, by linarith, h2⟩
    · rintro ⟨h0, h1, hsum, h2, h2one⟩
      rcases le_total (x 2) (x 1) with h21 | h12
      · exact Or.inl (Or.inl ⟨h0, h1, hsum, h2, h21⟩)
      · rcases le_total (x 2) (x 0 + x 1) with h2sum | hsum2
        · exact Or.inl (Or.inr ⟨h0, h1, hsum, h12, h2sum⟩)
        · exact Or.inr ⟨h0, h1, hsum2, h2one⟩
  exact hcover ▸ hball

private theorem isPLBall_coordinate_triangle :
    IsPLBall 2 {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun v => ![v 1, v 2]
      map_add' := by intro v w; ext i; fin_cases i <;> rfl
      map_smul' := by intro a v; ext i; fin_cases i <;> rfl }
  let g := fun x : Fin 2 → ℝ => ![1 - x 0 - x 1, x 0, x 1]
  apply isPLBall_of_linear_coordinates (n := 2) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    refine ⟨hv.1 1, hv.1 2, ?_⟩
    change v 1 + v 2 ≤ 1
    linarith [hv.1 0]
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp [g] <;> rcases hx with ⟨h0, h1, hsum⟩ <;> linarith
    · simp [g, Fin.sum_univ_three]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hv.2
    ext i
    fin_cases i <;> simp [g, f]
    linarith
  · intro x _
    ext i
    fin_cases i <;> rfl

theorem isPLHomeomorphOn_triangle_prism_coordinates :
    IsPLHomeomorphOn (fun x : EuclideanSpace ℝ (Fin 3) => (![x 0, x 1], x 2))
      {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1}
      ({x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} ×ˢ Icc (0 : ℝ) 1) := by
  let f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ((Fin 2 → ℝ) × ℝ) :=
    { toFun := fun x => (![x 0, x 1], x 2)
      map_add' := by
        intro v w
        apply Prod.ext
        · ext i; fin_cases i <;> rfl
        · rfl
      map_smul' := by
        intro a v
        apply Prod.ext
        · ext i; fin_cases i <;> rfl
        · rfl }
  let g := fun x : (Fin 2 → ℝ) × ℝ => WithLp.toLp 2 ![x.1 0, x.1 1, x.2]
  have hleft : Function.LeftInverse g f := by
    intro x
    ext i
    fin_cases i <;> rfl
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPLBall_triangle_prism.isPolyhedron
    ((isPiecewiseAffineOn_of_affine f.toAffineMap isOpen_univ).mono_of_isPolyhedron
      isPLBall_triangle_prism.isPolyhedron (subset_univ _))
  refine ⟨?_, hleft.injective.injOn, ?_⟩
  · rintro x ⟨h0, h1, hsum, h2, h21⟩
    exact ⟨⟨h0, h1, hsum⟩, h2, h21⟩
  · rintro x ⟨⟨h0, h1, hsum⟩, h2, h21⟩
    refine ⟨g x, ⟨h0, h1, hsum, h2, h21⟩, ?_⟩
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rfl

theorem isPLBall_three_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsPLBall 2 P) (hQ : IsPLBall 1 Q) :
    IsPLBall 3 (P ×ˢ Q) := by
  have hmodel := isPLBall_triangle_prism.of_isPLHomeomorphOn isPLHomeomorphOn_triangle_prism_coordinates
  obtain ⟨t, ht⟩ := isPLBall_coordinate_triangle
  obtain ⟨u, hu⟩ := isPLBall_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  exact hmodel.of_isPLHomeomorphOn ((ht.symm.trans hp).prodMap (hu.symm.trans hq))
end DifferentialGeometry.Topology.PiecewiseLinear
