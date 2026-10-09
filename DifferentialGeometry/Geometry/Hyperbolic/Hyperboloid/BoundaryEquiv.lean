import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMap

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

variable (f : C(Hyperboloid E, Hyperboloid F)) (g : C(Hyperboloid F, Hyperboloid E))
  (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
  (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid F,
    L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
  (hgf : ∃ C : ℝ, ∀ x : Hyperboloid E, dist (g (f x)) x ≤ C)

include hgf in
private theorem boundaryMap_left_inverse :
    Function.LeftInverse (boundaryMap g hg) (boundaryMap f hf) := by
  obtain ⟨C, hC⟩ := hgf
  intro u
  let c := geodesicLine (origin : Hyperboloid E) (0, (u : E))
    (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
      ← dist_zero_right, Metric.mem_sphere.mp u.property, one_pow]) (by simp [lorentzForm_apply])
  have hc : Filter.Tendsto (fun t => (kleinHomeomorph (c t) : E))
      Filter.atTop (𝓝 (u : E)) := by
    simpa only [origin_time, origin_space, add_zero, zero_add, inv_one, one_smul] using
      tendsto_kleinHomeomorph_geodesicLine_atTop (origin : Hyperboloid E) (0, (u : E))
        (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
          ← dist_zero_right, Metric.mem_sphere.mp u.property, one_pow]) (by simp [lorentzForm_apply])
  have hf_limit : Filter.Tendsto (fun t => (kleinHomeomorph (f (c t)) : F))
      Filter.atTop (𝓝 (boundaryMap f hf u : F)) :=
    tendsto_kleinHomeomorph_boundaryMap f hf hc
  have hcomposite : Filter.Tendsto (fun t => (kleinHomeomorph (g (f (c t))) : E))
      Filter.atTop (𝓝 (boundaryMap g hg (boundaryMap f hf u) : E)) :=
    tendsto_kleinHomeomorph_boundaryMap g hg hf_limit
  have hclose : Filter.Tendsto (fun t => (kleinHomeomorph (g (f (c t))) : E))
      Filter.atTop (𝓝 (u : E)) :=
    tendsto_kleinHomeomorph_of_dist_bounded (x := c) (y := fun t => g (f (c t)))
      (ξ := u) (C := C)
      (Filter.Eventually.of_forall fun t => (dist_comm _ _).trans_le (hC (c t))) hc
  apply Subtype.ext
  exact tendsto_nhds_unique hcomposite hclose

variable (hfg : ∃ C : ℝ, ∀ y : Hyperboloid F, dist (f (g y)) y ≤ C)

include hgf hfg in
def boundaryHomeomorphOfCoarseInverse : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 where
  toFun := boundaryMap f hf
  invFun := boundaryMap g hg
  left_inv := boundaryMap_left_inverse f g hf hg hgf
  right_inv := boundaryMap_left_inverse g f hg hf hfg
  continuous_toFun := (boundaryMap f hf).continuous
  continuous_invFun := (boundaryMap g hg).continuous

@[simp]
theorem boundaryHomeomorphOfCoarseInverse_toContinuousMap :
    (boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg :
      C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1)) = boundaryMap f hf := rfl

@[simp]
theorem boundaryHomeomorphOfCoarseInverse_symm_toContinuousMap :
    ((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).symm :
      C(Metric.sphere (0 : F) 1, Metric.sphere (0 : E) 1)) = boundaryMap g hg := rfl

@[simp]
theorem boundaryHomeomorphOfCoarseInverse_apply (u : Metric.sphere (0 : E) 1) :
    boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg u = boundaryMap f hf u := rfl

@[simp]
theorem boundaryHomeomorphOfCoarseInverse_symm_apply (v : Metric.sphere (0 : F) 1) :
    (boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).symm v = boundaryMap g hg v := rfl

theorem boundaryHomeomorphOfCoarseInverse_symm :
    (boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).symm =
      boundaryHomeomorphOfCoarseInverse g f hg hf hfg hgf := by
  ext v
  rfl

end DifferentialGeometry.Hyperboloid
