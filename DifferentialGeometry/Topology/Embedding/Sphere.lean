import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Euclidean.Inversion.Calculus

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

open EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def inversionChart (v : E) : OpenPartialHomeomorph E E where
  toFun := inversion v 2
  invFun := inversion v 2
  source := {v}ᶜ
  target := {v}ᶜ
  map_source' x hx := by simpa using hx
  map_target' x hx := by simpa using hx
  left_inv' x _ := inversion_inversion v (by norm_num) x
  right_inv' x _ := inversion_inversion v (by norm_num) x
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (fun x hx => hx)
  continuousOn_invFun := continuousOn_const.inversion continuousOn_const continuousOn_id
    (fun x hx => hx)

private def sphereFlattening (v : E) : OpenPartialHomeomorph E E :=
  (inversionChart v).trans (Homeomorph.addRight v).toOpenPartialHomeomorph

private theorem sphereFlattening_mem_maximalAtlas (v : E) :
    sphereFlattening v ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ E := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply ContDiffOn.contMDiffOn
    change ContDiffOn ℝ ∞ (fun x => inversion v 2 x + v) _
    exact (contDiffOn_const.inversion contDiffOn_const contDiffOn_id
      (fun x hx => hx.1)).add contDiffOn_const
  · apply ContDiffOn.contMDiffOn
    change ContDiffOn ℝ ∞ (fun x => inversion v 2 (x + -v)) _
    exact contDiffOn_const.inversion contDiffOn_const
      (contDiffOn_id.add contDiffOn_const) (fun x hx => hx.2)

private theorem sphereFlattening_apply (v x : Metric.sphere (0 : E) 1) (hx : x ≠ v) :
    sphereFlattening (v : E) (x : E) = (stereoToFun (v : E) x : E) := by
  have hv : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have hxx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have hne : (x : E) ≠ (v : E) := fun h => hx (Subtype.ext h)
  have hd : dist (x : E) (v : E) ^ 2 = 2 * (1 - inner ℝ (v : E) (x : E)) := by
    rw [dist_eq_norm, norm_sub_sq_real, hxx, hv, real_inner_comm]
    ring
  have hs : (x : E) = inner ℝ (v : E) (x : E) • (v : E) +
      ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x : E) := by
    calc
      (x : E) = (ℝ ∙ (v : E)).starProjection x +
          (ℝ ∙ (v : E))ᗮ.starProjection x :=
        ((ℝ ∙ (v : E)).starProjection_add_starProjection_orthogonal (x : E)).symm
      _ = _ := by rw [Submodule.starProjection_unit_singleton ℝ hv]; rfl
  have ha : 1 - inner ℝ (v : E) (x : E) ≠ 0 := by
    have := (inner_lt_one_iff_real_of_norm_eq_one hv hxx).mpr hne.symm
    linarith
  change inversion (v : E) 2 (x : E) + v = _
  simp only [inversion, vsub_eq_sub, vadd_eq_add, div_pow, hd, stereoToFun,
    Submodule.coe_smul_of_tower, innerSL_apply_apply]
  calc
    ((2 : ℝ) ^ 2 / (2 * (1 - inner ℝ (v : E) (x : E)))) • ((x : E) - (v : E)) + (v : E) + (v : E) =
        ((2 : ℝ) ^ 2 / (2 * (1 - inner ℝ (v : E) (x : E)))) •
          ((inner ℝ (v : E) (x : E) • (v : E) +
            ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x : E)) - (v : E)) + (v : E) + (v : E) := by
      rw [← hs]
    _ = _ := by
      match_scalars
      all_goals field_simp
      all_goals ring

private def sphereChartEquiv {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] E := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  let V : ℝ ≃ₗ[ℝ] (ℝ ∙ (v : E)) := LinearEquiv.ofFinrankEq ℝ _ (by
    rw [Module.finrank_self, finrank_span_singleton (ne_zero_of_mem_unit_sphere v)])
  exact ((U.symm.toLinearEquiv.prodCongr V).trans
    ((ℝ ∙ (v : E))ᗮ.prodEquivOfIsCompl (ℝ ∙ (v : E))
      (Submodule.isCompl_orthogonal (ℝ ∙ (v : E))).symm)).toContinuousLinearEquiv

private theorem sphereChartEquiv_apply_zero {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (u : EuclideanSpace ℝ (Fin n)) :
    sphereChartEquiv v (u, 0) =
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (ne_zero_of_mem_unit_sphere v)).repr.symm u : (ℝ ∙ (v : E))ᗮ) : E) := by
  simp [sphereChartEquiv]

theorem isSmoothEmbedding_coe_sphere {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    Manifold.IsSmoothEmbedding (𝓡 n) 𝓘(ℝ, E) ∞
      (Subtype.val : Metric.sphere (0 : E) 1 → E) := by
  refine ⟨?_, .subtypeVal⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (sphereChartEquiv (-x))
    (stereographic' n (-x)) (sphereFlattening (-x : E))
  · simpa using ne_neg_of_mem_unit_sphere ℝ x
  · change (x : E) ∈ (inversionChart (-x : E)).source ∧ _
    exact ⟨fun h => (ne_neg_of_mem_unit_sphere ℝ x) (Subtype.ext h), Set.mem_univ _⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨-x, rfl⟩
  · exact sphereFlattening_mem_maximalAtlas (-x : E)
  · intro u hu
    change sphereFlattening (-x : E) (((stereographic' n (-x)).symm u) : E) =
      sphereChartEquiv (-x) (u, 0)
    have hy : (stereographic' n (-x)).symm u ≠ -x := by
      have hmem := (stereographic' n (-x)).map_target (show u ∈ _ by simp)
      simpa using hmem
    have hflat := sphereFlattening_apply (-x) ((stereographic' n (-x)).symm u) hy
    rw [coe_neg_sphere] at hflat
    rw [hflat, sphereChartEquiv_apply_zero]
    change ((stereographic (norm_eq_of_mem_sphere (-x)))
      ((stereographic' n (-x)).symm u) : E) = _
    let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
      (ne_zero_of_mem_unit_sphere (-x))).repr
    change ((stereographic (norm_eq_of_mem_sphere (-x)))
      ((stereographic (norm_eq_of_mem_sphere (-x))).symm (U.symm u)) : E) =
        (U.symm u : E)
    exact congrArg (Subtype.val : (ℝ ∙ (-x : E))ᗮ → E)
      (stereo_right_inv (norm_eq_of_mem_sphere (-x)) (U.symm u))

end
