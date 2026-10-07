import DifferentialGeometry.Geometry.Metric.Isometry.Conjugation
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryFixedPoint
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Busemann
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlaneFixedPoint

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem lorentzExtension_mul_apply (f g : Hyperboloid E ≃ᵢ Hyperboloid E)
    (v : ℝ × E) :
    lorentzExtension (f * g) v = lorentzExtension f (lorentzExtension g v) := by
  change lorentzExtension (g.trans f) v = _
  rw [lorentzExtension_trans]
  rfl

private theorem lorentzExtension_pow_apply_of_eigenvector
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (v : ℝ × E) (a : ℝ)
    (hv : lorentzExtension f v = a • v) (n : ℕ) :
    lorentzExtension (f ^ n) v = a ^ n • v := by
  induction n with
  | zero =>
    change lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) v = _
    simp only [lorentzExtension_refl, pow_zero, one_smul]
    rfl
  | succ n ih =>
    rw [pow_succ', lorentzExtension_mul_apply, ih, map_smul, hv,
      smul_smul, pow_succ]

private theorem exists_null_midpoint (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η) :
    ∃ (x : Hyperboloid E) (c : ℝ),
      (x.time, x.space) = c • ((1, (ξ : E)) + (1, (η : E))) := by
  let u : E := (2 : ℝ)⁻¹ • ((ξ : E) + (η : E))
  have hd : 0 < ‖(ξ : E) - (η : E)‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hne (Subtype.ext h)))
  have hs : ‖(ξ : E) + (η : E)‖ < 2 := by
    have ha := norm_add_sq_real (ξ : E) (η : E)
    have hb := norm_sub_sq_real (ξ : E) (η : E)
    simp only [norm_eq_of_mem_sphere, one_pow] at ha hb
    nlinarith only [ha, hb, hd, norm_nonneg ((ξ : E) + (η : E))]
  have hu : ‖u‖ < 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith only [hs]
  let z : Metric.ball (0 : E) 1 :=
    ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu⟩
  let x : Hyperboloid E := kleinHomeomorph.symm z
  refine ⟨x, x.time / 2, ?_⟩
  apply Prod.ext
  · change x.time = x.time / 2 * (1 + 1)
    ring
  · change x.space = (x.time / 2) • ((ξ : E) + (η : E))
    rw [show x.space = x.time • u by
      dsimp only [x]
      rw [kleinHomeomorph_symm_space, kleinHomeomorph_symm_time]]
    dsimp only [u]
    rw [smul_smul, div_eq_mul_inv]

theorem exists_forall_dist_eq_abs_log_lorentzExtension_time
    (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η) :
    ∃ x : Hyperboloid E, ∀ f : Hyperboloid E ≃ᵢ Hyperboloid E,
      boundaryHomeomorph f ξ = ξ → boundaryHomeomorph f η = η →
        dist x (f x) = |Real.log ((lorentzExtension f (1, (ξ : E))).1)| := by
  obtain ⟨x, c, hx⟩ := exists_null_midpoint ξ η hne
  refine ⟨x, ?_⟩
  intro f hfξ hfη
  let u : ℝ × E := (1, (ξ : E))
  let v : ℝ × E := (1, (η : E))
  let a := (lorentzExtension f u).1
  have ha : 0 < a := lorentzExtension_sphere_time_pos f ξ
  have huv : lorentzForm E u v = lorentzForm E v u := (lorentzForm_isSymm E).eq u v
  have huu : lorentzForm E u u = 0 := by
    simp only [u, lorentzForm_apply, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere,
      one_pow, mul_one, sub_self]
  have hvv : lorentzForm E v v = 0 := by
    simp only [v, lorentzForm_apply, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere,
      one_pow, mul_one, sub_self]
  change (x.time, x.space) = c • (u + v) at hx
  have hxx : lorentzForm E (x.time, x.space) (x.time, x.space) = -1 := by
    change inner ℝ x.space x.space - x.time * x.time = -1
    nlinarith only [x.time_sq_sub_inner_self]
  have hcoef : 2 * c ^ 2 * lorentzForm E u v = -1 := by
    rw [hx] at hxx
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, huu, hvv, ← huv] at hxx
    nlinarith only [hxx]
  have hfu : lorentzExtension f u = a • u := by
    simpa only [hfξ] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph f ξ
  have hfv : lorentzExtension f v = a⁻¹ • v := by
    have hab := boundary_time_mul_eq_one_of_fixed f ξ η hfξ hfη hne
    have hb : (lorentzExtension f (1, (η : E))).1 = a⁻¹ := by
      apply mul_left_cancel₀ ha.ne'
      rw [mul_inv_cancel₀ ha.ne']
      exact hab
    simpa only [hfη, hb] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph f η
  have hfx : lorentzExtension f (x.time, x.space) = c • (a • u + a⁻¹ • v) := by
    rw [hx, map_smul, map_add, hfu, hfv]
  have hform : lorentzForm E (x.time, x.space) (lorentzExtension f (x.time, x.space)) =
      -(a + a⁻¹) / 2 := by
    rw [hfx, hx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, huu, hvv, ← huv]
    calc
      _ = (a + a⁻¹) / 2 * (2 * c ^ 2 * lorentzForm E u v) := by ring
      _ = _ := by rw [hcoef]; ring
  have hcosh : Real.cosh (dist x (f x)) = Real.cosh (Real.log a) := by
    rw [lorentzExtension_apply] at hform
    simp only [lorentzForm_apply] at hform
    rw [cosh_dist, Real.cosh_log ha]
    nlinarith only [hform]
  have hle := Real.cosh_le_cosh.mp hcosh.le
  have hge := Real.cosh_le_cosh.mp hcosh.ge
  simpa only [abs_of_nonneg dist_nonneg] using le_antisymm hle hge

theorem finite_setOf_exists_dist_apply_le_of_boundary_fixed
    [FiniteDimensional ℝ E]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ]
    (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η)
    (hξ : ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (hη : ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) η = η)
    (R : ℝ) :
    Set.Finite {g : Γ | ∃ y : Hyperboloid E, dist y ((g : Hyperboloid E ≃ᵢ Hyperboloid E) y) ≤ R} := by
  obtain ⟨x, hx⟩ := exists_forall_dist_eq_abs_log_lorentzExtension_time ξ η hne
  have hΓ : IsClosed (Γ : Set (Hyperboloid E ≃ᵢ Hyperboloid E)) :=
    Subgroup.isClosed_of_discreteTopology
  have hfin : Set.Finite {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x ≤ R} :=
    (hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage
      (IsometryEquiv.isCompact_setOf_dist_apply_le x R)).finite_of_discrete
  apply hfin.subset
  rintro g ⟨y, hy⟩
  change dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x ≤ R
  have heq := hx (g : Hyperboloid E ≃ᵢ Hyperboloid E) (hξ g) (hη g)
  have hle := abs_log_lorentzExtension_time_le_dist_of_boundary_fixed
    (g : Hyperboloid E ≃ᵢ Hyperboloid E) ξ (hξ g) y
  rw [dist_comm, heq]
  exact hle.trans hy

private theorem lorentzForm_sphere_image_nonpos
    (g : Hyperboloid E ≃ᵢ Hyperboloid E) (η : Metric.sphere (0 : E) 1) :
    lorentzForm E (1, (η : E)) (lorentzExtension g (1, (η : E))) ≤ 0 := by
  rw [lorentzExtension_sphere_eq_smul_boundaryHomeomorph, map_smul]
  apply mul_nonpos_of_nonneg_of_nonpos (lorentzExtension_sphere_time_pos g η).le
  change inner ℝ (η : E) (boundaryHomeomorph g η : E) - 1 * 1 ≤ 0
  have h := real_inner_le_norm (η : E) (boundaryHomeomorph g η : E)
  simp only [norm_eq_of_mem_sphere, mul_one] at h
  linarith only [h]

theorem exists_forall_dist_pow_apply_le_of_boundary_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ η : Metric.sphere (0 : E) 1)
    (hne : ξ ≠ η) (hfξ : boundaryHomeomorph f ξ = ξ)
    (hfη : boundaryHomeomorph f η = η)
    (ha : 1 ≤ (lorentzExtension f (1, (ξ : E))).1) :
    ∃ x : Hyperboloid E, ∀ g : Hyperboloid E ≃ᵢ Hyperboloid E,
      boundaryHomeomorph g ξ = ξ → ∀ n : ℕ,
        dist (g ((f ^ n) x)) ((f ^ n) x) ≤ dist (g x) x := by
  let u : ℝ × E := (1, (ξ : E))
  let v : ℝ × E := (1, (η : E))
  let a := (lorentzExtension f u).1
  have ha0 : 0 < a := lorentzExtension_sphere_time_pos f ξ
  have hab := boundary_time_mul_eq_one_of_fixed f ξ η hfξ hfη hne
  have hfu : lorentzExtension f u = a • u := by
    simpa only [hfξ] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph f ξ
  have hfv : lorentzExtension f v = a⁻¹ • v := by
    have hb : (lorentzExtension f v).1 = a⁻¹ := by
      apply mul_left_cancel₀ ha0.ne'
      rw [mul_inv_cancel₀ ha0.ne']
      exact hab
    change (lorentzExtension f (1, (η : E))).1 = a⁻¹ at hb
    simpa only [hfη, hb] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph f η
  obtain ⟨x, c, hx⟩ := exists_null_midpoint ξ η hne
  change (x.time, x.space) = c • (u + v) at hx
  refine ⟨x, ?_⟩
  intro g hgξ n
  let b := (lorentzExtension g u).1
  have hgu : lorentzExtension g u = b • u := by
    simpa only [hgξ] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph g ξ
  have huu : lorentzForm E u (lorentzExtension g u) = 0 := by
    rw [hgu, map_smul]
    have hu : lorentzForm E u u = 0 := by
      simp only [u, lorentzForm_apply, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere,
        one_pow, mul_one, sub_self]
    rw [hu, smul_eq_mul, mul_zero]
  have hvv : lorentzForm E v (lorentzExtension g v) ≤ 0 :=
    lorentzForm_sphere_image_nonpos g η
  let r := a ^ n
  have hr : 1 ≤ r := one_le_pow₀ ha
  have hri : 0 < r⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr)
  have hri1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have hri2 : r⁻¹ ^ 2 ≤ 1 := by nlinarith only [hri.le, hri1]
  have hy : (((f ^ n) x).time, ((f ^ n) x).space) =
      c • (r • u + r⁻¹ • v) := by
    rw [← lorentzExtension_apply, hx, map_smul, map_add,
      lorentzExtension_pow_apply_of_eigenvector f u a hfu n,
      lorentzExtension_pow_apply_of_eigenvector f v a⁻¹ hfv n, inv_pow]
  have hform : lorentzForm E (c • (r • u + r⁻¹ • v))
      (lorentzExtension g (c • (r • u + r⁻¹ • v))) =
      c ^ 2 * (lorentzForm E u (lorentzExtension g v) +
        lorentzForm E v (lorentzExtension g u) + r⁻¹ ^ 2 * lorentzForm E v (lorentzExtension g v)) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, huu]
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (lt_of_lt_of_le zero_lt_one hr).ne'
    calc
      _ = c ^ 2 * ((r * r⁻¹) * (lorentzForm E u (lorentzExtension g v) +
          lorentzForm E v (lorentzExtension g u)) + r⁻¹ ^ 2 *
            lorentzForm E v (lorentzExtension g v)) := by ring
      _ = _ := by rw [hrr, one_mul]
  have hbase : lorentzForm E (x.time, x.space) (lorentzExtension g (x.time, x.space)) =
      c ^ 2 * (lorentzForm E u (lorentzExtension g v) +
        lorentzForm E v (lorentzExtension g u) + lorentzForm E v (lorentzExtension g v)) := by
    rw [hx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huu]
    ring
  have hle : lorentzForm E (x.time, x.space) (lorentzExtension g (x.time, x.space)) ≤
      lorentzForm E (((f ^ n) x).time, ((f ^ n) x).space)
        (lorentzExtension g (((f ^ n) x).time, ((f ^ n) x).space)) := by
    rw [hy, hform, hbase]
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hvv, hri2]) (sq_nonneg c)
  have hcosh : Real.cosh (dist (g ((f ^ n) x)) ((f ^ n) x)) ≤ Real.cosh (dist (g x) x) := by
    rw [lorentzExtension_apply, lorentzExtension_apply] at hle
    simp only [lorentzForm_apply] at hle
    rw [cosh_dist, cosh_dist, real_inner_comm ((f ^ n) x).space (g ((f ^ n) x)).space,
      real_inner_comm x.space (g x).space]
    nlinarith only [hle]
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hcosh

private theorem boundaryHomeomorph_mul_apply (f g : Hyperboloid E ≃ᵢ Hyperboloid E)
    (ξ : Metric.sphere (0 : E) 1) :
    boundaryHomeomorph (f * g) ξ = boundaryHomeomorph f (boundaryHomeomorph g ξ) := by
  change boundaryHomeomorph (g.trans f) ξ = _
  rw [boundaryHomeomorph_trans]
  rfl

private theorem boundaryHomeomorph_pow_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) (n : ℕ) :
    boundaryHomeomorph (f ^ n) ξ = ξ := by
  induction n with
  | zero =>
    change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ = ξ
    rw [boundaryHomeomorph_refl]
    rfl
  | succ n ih =>
    rw [pow_succ', boundaryHomeomorph_mul_apply, ih, hξ]

private theorem boundary_fixed_of_commute_of_lorentzExtension_time_gt_one
    (f g : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ η : Metric.sphere (0 : E) 1)
    (hne : ξ ≠ η) (hfξ : boundaryHomeomorph f ξ = ξ)
    (hfη : boundaryHomeomorph f η = η) (hgξ : boundaryHomeomorph g ξ = ξ)
    (ha : 1 < (lorentzExtension f (1, (ξ : E))).1) (n : ℕ) (hn : 0 < n)
    (hcomm : Commute (f ^ n) g) : boundaryHomeomorph g η = η := by
  let a := (lorentzExtension f (1, (ξ : E))).1
  have hA : lorentzExtension f (1, (ξ : E)) = a • (1, (ξ : E)) := by
    simpa only [hfξ] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph f ξ
  have htime : (lorentzExtension (f ^ n) (1, (ξ : E))).1 = a ^ n := by
    have h := congrArg Prod.fst (lorentzExtension_pow_apply_of_eigenvector f _ a hA n)
    change (lorentzExtension (f ^ n) (1, (ξ : E))).1 = a ^ n * 1 at h
    simpa only [mul_one] using h
  have hfξn := boundaryHomeomorph_pow_fixed f ξ hfξ n
  have hfηn := boundaryHomeomorph_pow_fixed f η hfη n
  have hfree : ∀ x : Hyperboloid E, (f ^ n) x ≠ x := by
    intro x hx
    have h := abs_log_lorentzExtension_time_le_dist_of_boundary_fixed (f ^ n) ξ hfξn x
    rw [htime, hx, dist_self] at h
    have hp : 0 < Real.log (a ^ n) := Real.log_pos (one_lt_pow₀ ha hn.ne')
    exact (not_le_of_gt (abs_pos.mpr hp.ne')) h
  have hcard := fixedPoints_boundaryHomeomorph_encard_le_two (f ^ n) hfree
  have hpair : ({ξ, η} : Set (Metric.sphere (0 : E) 1)) ⊆
      Function.fixedPoints (boundaryHomeomorph (f ^ n)) := by
    intro ζ hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | hζ
    · exact hfξn
    · rw [Set.mem_singleton_iff.mp hζ]
      exact hfηn
  have heq : ({ξ, η} : Set (Metric.sphere (0 : E) 1)) =
      Function.fixedPoints (boundaryHomeomorph (f ^ n)) :=
    ((Set.finite_singleton η).insert ξ).eq_of_subset_of_encard_le hpair
      (by simpa only [Set.encard_pair hne] using hcard)
  have hfix : boundaryHomeomorph (f ^ n) (boundaryHomeomorph g η) =
      boundaryHomeomorph g η := by
    rw [← boundaryHomeomorph_mul_apply, hcomm.eq, boundaryHomeomorph_mul_apply, hfηn]
  have hmem : boundaryHomeomorph g η ∈ ({ξ, η} : Set (Metric.sphere (0 : E) 1)) := by
    rw [heq]
    exact hfix
  rcases Set.mem_insert_iff.mp hmem with h | h
  · exact (hne ((boundaryHomeomorph g).injective (hgξ.trans h.symm))).elim
  · exact Set.mem_singleton_iff.mp h

private theorem boundary_fixed_of_discrete_of_lorentzExtension_time_gt_one
    [FiniteDimensional ℝ E]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ]
    (f g : Γ) (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η)
    (hfξ : boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (hfη : boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid E) η = η)
    (hgξ : boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (ha : 1 < (lorentzExtension (f : Hyperboloid E ≃ᵢ Hyperboloid E) (1, (ξ : E))).1) :
    boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) η = η := by
  obtain ⟨x, hx⟩ := exists_forall_dist_pow_apply_le_of_boundary_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) ξ η hne hfξ hfη ha.le
  obtain ⟨n, hn, hcomm⟩ := IsometryEquiv.exists_pos_pow_commute_of_bounded_displacement Γ f g x
    (dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x)
    (fun n => by simpa only [Subgroup.coe_pow] using hx g hgξ n)
  apply boundary_fixed_of_commute_of_lorentzExtension_time_gt_one
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) g ξ η hne hfξ hfη hgξ ha n hn
  exact congrArg Subtype.val hcomm

theorem boundary_fixed_of_discrete_of_lorentzExtension_time_ne_one
    [FiniteDimensional ℝ E]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ]
    (f g : Γ) (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η)
    (hfξ : boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (hfη : boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid E) η = η)
    (hgξ : boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (ha : (lorentzExtension (f : Hyperboloid E ≃ᵢ Hyperboloid E) (1, (ξ : E))).1 ≠ 1) :
    boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) η = η := by
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · let F : Hyperboloid E ≃ᵢ Hyperboloid E := f
    let a := (lorentzExtension F (1, (ξ : E))).1
    have ha0 : 0 < a := lorentzExtension_sphere_time_pos F ξ
    have hfξi : boundaryHomeomorph (↑(f⁻¹) : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ := by
      change boundaryHomeomorph F.symm ξ = ξ
      rw [← boundaryHomeomorph_symm]
      exact (boundaryHomeomorph F).symm_apply_eq.mpr hfξ.symm
    have hfηi : boundaryHomeomorph (↑(f⁻¹) : Hyperboloid E ≃ᵢ Hyperboloid E) η = η := by
      change boundaryHomeomorph F.symm η = η
      rw [← boundaryHomeomorph_symm]
      exact (boundaryHomeomorph F).symm_apply_eq.mpr hfη.symm
    have hA : lorentzExtension F (1, (ξ : E)) = a • (1, (ξ : E)) := by
      have hfξF : boundaryHomeomorph F ξ = ξ := hfξ
      simpa only [hfξF] using lorentzExtension_sphere_eq_smul_boundaryHomeomorph F ξ
    have hAi : lorentzExtension F.symm (1, (ξ : E)) = a⁻¹ • (1, (ξ : E)) := by
      rw [lorentzExtension_symm]
      apply (lorentzExtension F).injective
      change lorentzExtension F ((lorentzExtension F).symm (1, (ξ : E))) =
        lorentzExtension F (a⁻¹ • (1, (ξ : E)))
      calc
        _ = (1, (ξ : E)) := (lorentzExtension F).toLinearEquiv.apply_symm_apply _
        _ = _ := by rw [map_smul, hA, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul]
    have htime : (lorentzExtension F.symm (1, (ξ : E))).1 = a⁻¹ := by
      have h := congrArg Prod.fst hAi
      change (lorentzExtension F.symm (1, (ξ : E))).1 = a⁻¹ * 1 at h
      simpa only [mul_one] using h
    apply boundary_fixed_of_discrete_of_lorentzExtension_time_gt_one
      Γ f⁻¹ g ξ η hne hfξi hfηi hgξ
    change 1 < (lorentzExtension F.symm (1, (ξ : E))).1
    rw [htime]
    exact (one_lt_inv₀ ha0).mpr hlt
  · exact boundary_fixed_of_discrete_of_lorentzExtension_time_gt_one
      Γ f g ξ η hne hfξ hfη hgξ hgt

theorem exists_common_boundary_fixed_ne_of_discrete_of_lorentzExtension_time_ne_one
    (Γ : Subgroup (Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin 3)))) [DiscreteTopology Γ]
    (ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hξ : ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin 3))) ξ = ξ)
    (f : Γ)
    (ha : (lorentzExtension (f : Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
      Hyperboloid (EuclideanSpace ℝ (Fin 3))) (1, (ξ : EuclideanSpace ℝ (Fin 3)))).1 ≠ 1) :
    ∃ η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, η ≠ ξ ∧
      ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
        Hyperboloid (EuclideanSpace ℝ (Fin 3))) η = η := by
  obtain ⟨η, hη, hfη⟩ := exists_boundary_fixedPoint_ne_of_lorentzExtension_time_ne_one
    f ξ (hξ f) ha
  exact ⟨η, hη, fun g => boundary_fixed_of_discrete_of_lorentzExtension_time_ne_one
    Γ f g ξ η hη.symm (hξ f) hfη (hξ g) ha⟩

end DifferentialGeometry.Hyperboloid
