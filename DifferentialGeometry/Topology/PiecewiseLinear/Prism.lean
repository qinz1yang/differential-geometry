import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.DiskUnion

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

theorem isPLBall_coordinate_triangle :
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
private theorem isPLBall_scaled_triangle {c : ℝ} (hc : 0 < c) :
    IsPLBall 2 {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ c} := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun v => (c * v 1, c * v 2)
      map_add' := by intro v w; ext <;> dsimp <;> ring
      map_smul' := by intro a v; ext <;> dsimp <;> ring }
  let g := fun x : ℝ × ℝ => ![1 - x.1 / c - x.2 / c, x.1 / c, x.2 / c]
  apply isPLBall_of_linear_coordinates (n := 2) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_three] using hv.2
    exact ⟨mul_nonneg hc.le (hv.1 1), mul_nonneg hc.le (hv.1 2), by
      dsimp [f]
      nlinarith [hv.1 0]⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · change 0 ≤ 1 - x.1 / c - x.2 / c
        have hsum : x.1 / c + x.2 / c ≤ 1 := by
          rw [← add_div, div_le_one hc]
          exact hx.2.2
        linarith
      · exact div_nonneg hx.1 hc.le
      · exact div_nonneg hx.2.1 hc.le
    · simp [g, Fin.sum_univ_three]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_three] using hv.2
    ext i
    fin_cases i <;> simp [g, f, hc.ne']
    linarith
  · intro x _
    ext <;> dsimp [g, f] <;> field_simp

private theorem isPLBall_upper_square_triangle :
    IsPLBall 2 {x : ℝ × ℝ | x.1 ≤ 1 ∧ x.2 ≤ 1 ∧ 1 ≤ x.1 + x.2} := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun v => (v 1 + v 2, v 0 + v 2)
      map_add' := by intro v w; ext <;> dsimp <;> ring
      map_smul' := by intro a v; ext <;> dsimp <;> ring }
  let g := fun x : ℝ × ℝ => ![1 - x.1, 1 - x.2, x.1 + x.2 - 1]
  apply isPLBall_of_linear_coordinates (n := 2) f g
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_three] using hv.2
    change v 1 + v 2 ≤ 1 ∧ v 0 + v 2 ≤ 1 ∧ 1 ≤ (v 1 + v 2) + (v 0 + v 2)
    exact ⟨by linarith [hv.1 0], by linarith [hv.1 1], by linarith [hv.1 2]⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> simp [g] <;> rcases hx with ⟨h0, h1, hsum⟩ <;> linarith
    · simp [g, Fin.sum_univ_three]
      ring
  · intro v hv
    have hsum : v 0 + v 1 + v 2 = 1 := by simpa [Fin.sum_univ_three] using hv.2
    ext i
    fin_cases i <;> simp [g, f] <;> linarith
  · intro x _
    ext <;> simp [g, f]

theorem isPLBall_unit_square : IsPLBall 2 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  let C : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1}
  let D : Set (ℝ × ℝ) := {x | x.1 ≤ 1 ∧ x.2 ≤ 1 ∧ 1 ≤ x.1 + x.2}
  let B : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 2}
  have hC : IsPLBall 2 C := isPLBall_scaled_triangle (by norm_num)
  have hD : IsPLBall 2 D := isPLBall_upper_square_triangle
  have hB : IsPLBall 2 B := isPLBall_scaled_triangle (by norm_num)
  have hCB : C ⊆ B := by rintro x ⟨hx, hy, hxy⟩; exact ⟨hx, hy, by linarith⟩
  have hDB : D ⊆ B := by rintro x ⟨hx, hy, hxy⟩; exact ⟨by linarith, by linarith, by linarith⟩
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
    (AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ)
  have hI := isPLBall_Icc (by norm_num : (0 : ℝ) < 1)
  have hf : IsPLHomeomorphOn f (Icc (0 : ℝ) 1) (C ∩ D) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hI.isPolyhedron
      ((isPiecewiseAffineOn_of_affine f isOpen_univ).mono_of_isPolyhedron
        hI.isPolyhedron (subset_univ _))
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change (0 ≤ x ∧ 0 ≤ 1 - x ∧ x + (1 - x) ≤ 1) ∧
        x ≤ 1 ∧ 1 - x ≤ 1 ∧ 1 ≤ x + (1 - x)
      exact ⟨⟨hx.1, by linarith [hx.2], by linarith⟩,
        hx.2, by linarith [hx.1], by linarith⟩
    · intro x _ y _ heq
      exact congrArg Prod.fst heq
    · rintro x ⟨hxC, hxD⟩
      refine ⟨x.1, ⟨hxC.1, hxD.1⟩, Prod.ext rfl ?_⟩
      change 1 - x.1 = x.2
      linarith [hxC.2.2, hxD.2.2]
  have h := isPLBall_union_of_inter_isPLBall_one_in_ball hB hC hD hCB hDB
    (hI.of_isPLHomeomorphOn hf)
  have hunion : C ∪ D = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro (⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩)
      · exact ⟨⟨hx, by linarith⟩, hy, by linarith⟩
      · exact ⟨⟨by linarith, hx⟩, by linarith, hy⟩
    · rintro ⟨⟨hx0, hx1⟩, hy0, hy1⟩
      rcases le_total (x.1 + x.2) 1 with hxy | hxy
      · exact Or.inl ⟨hx0, hy0, hxy⟩
      · exact Or.inr ⟨hx1, hy1, hxy⟩
  exact hunion ▸ h

theorem isPLBall_two_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsPLBall 1 P) (hQ : IsPLBall 1 Q) :
    IsPLBall 2 (P ×ˢ Q) := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hP
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hQ
  exact isPLBall_unit_square.of_isPLHomeomorphOn (hf.prodMap hg)

end DifferentialGeometry.Topology.PiecewiseLinear
