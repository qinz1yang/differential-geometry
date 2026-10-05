import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! CFS27 (master207B, B:3618): pruning identically zero blocks before choosing the auxiliary planes.

For a reference chart `a`, `K_a` is the orthogonal projection deleting every block `V i` with `R i ≤ R a / 2`.
* (PR) at any preimage `q` with `3 R_a / 4 ≤ ρ q` (the reference domain `U_a`, by CFS26's (AS)), every deleted block
  of the original map vanishes and `K_a (F' q) = F' q`;
* (PP) the plane `range (K_a ∘ T)` of the pruned graph lies in the orthogonal complement of every deleted block;
* value / `C¹` comparison errors and upper derivative bounds do not increase; the retained reference coordinate keeps
  the graph identity, so rank is controlled by the retained identity component (not by projecting a plane). -/

set_option autoImplicit false
noncomputable section

namespace GC.MetricGeometry

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- `K_a`: orthogonal projection deleting every block `V i` with `R i ≤ R a / 2` (CFS27). -/
def actualCloudPrunedProjection (V : A → Submodule ℝ H) (R : A → ℝ) (a : A) : H →L[ℝ] H :=
  (⨆ (i : A) (_ : R i ≤ R a / 2), V i)ᗮ.starProjection

theorem actualCloudPrunedProjection_norm_le (V : A → Submodule ℝ H) (R : A → ℝ) (a : A) :
    ‖actualCloudPrunedProjection V R a‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- Every output of `K_a` is orthogonal to every deleted block. -/
theorem actualCloudPrunedProjection_apply_mem_orthogonal (V : A → Submodule ℝ H) (R : A → ℝ)
    (a i : A) (hi : R i ≤ R a / 2) (y : H) :
    actualCloudPrunedProjection V R a y ∈ (V i)ᗮ := by
  have hle : V i ≤ ⨆ (j : A) (_ : R j ≤ R a / 2), V j :=
    le_iSup₂_of_le (f := fun (j : A) (_ : R j ≤ R a / 2) => V j) i hi le_rfl
  exact Submodule.orthogonal_le hle (Submodule.starProjection_apply_mem _ y)

/-- A vector orthogonal to every deleted block is fixed by `K_a`. -/
theorem actualCloudPrunedProjection_apply_eq_self (V : A → Submodule ℝ H) (R : A → ℝ) (a : A)
    {y : H} (hy : ∀ i, R i ≤ R a / 2 → (V i).starProjection y = 0) :
    actualCloudPrunedProjection V R a y = y := by
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
  intro i
  by_cases hi : R i ≤ R a / 2
  · rw [iSup_pos hi]
    exact ((V i).starProjection_apply_eq_zero_iff).mp (hy i hi)
  · rw [iSup_neg hi, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top

/-- The retained identity component: a coordinate map killing every deleted block is unchanged by `K_a`. -/
theorem actualCloudPrunedProjection_retained_identity {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (V : A → Submodule ℝ H) (R : A → ℝ) (a : A) (Qc : H →L[ℝ] F)
    (hQc : ∀ i, R i ≤ R a / 2 → ∀ v ∈ V i, Qc v = 0) :
    Qc.comp (actualCloudPrunedProjection V R a) = Qc := by
  set W : Submodule ℝ H := ⨆ (i : A) (_ : R i ≤ R a / 2), V i with hW
  have hker : W ≤ LinearMap.ker (Qc : H →ₗ[ℝ] F) := by
    refine iSup₂_le fun i hi v hv => ?_
    exact (LinearMap.mem_ker).mpr (hQc i hi v hv)
  ext y
  have hmem : y - Wᗮ.starProjection y ∈ W := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) y
    rwa [Submodule.orthogonal_orthogonal] at h
  have h0 : Qc (y - Wᗮ.starProjection y) = 0 := hker hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

/-- CFS27: (PR) at a reference-domain preimage, deleted blocks vanish at the image and on the (PP) plane, and the
value comparison with the pruned graph does not increase. -/
theorem actualCloud_pruned_model_plane {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F' : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (R : A → ℝ)
    (hnonneg : ∀ i q, 0 ≤ marker i (F' q))
    (hsupport : ∀ i q, 0 < marker i (F' q) → 3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hblock : ∀ i q, marker i (F' q) = 0 → (V i).starProjection (F' q) = 0)
    (a : A) (ha : 0 < R a) (q : M) (hq : 3 * R a / 4 ≤ ρ q) (T : E →L[ℝ] H) :
    actualCloudPrunedProjection V R a (F' q) = F' q ∧
    (∀ i, R i ≤ R a / 2 → (V i).starProjection (F' q) = 0 ∧
      LinearMap.range (((actualCloudPrunedProjection V R a).comp T : E →L[ℝ] H) : E →ₗ[ℝ] H) ≤
        (V i)ᗮ) ∧
    ∀ y : H, ‖F' q - actualCloudPrunedProjection V R a y‖ ≤ ‖F' q - y‖ := by
  have hzero : ∀ i, R i ≤ R a / 2 → (V i).starProjection (F' q) = 0 := by
    intro i hi
    apply hblock i q
    apply le_antisymm ?_ (hnonneg i q)
    by_contra hpos
    have hs := hsupport i q (lt_of_not_ge hpos)
    linarith [hs.2]
  have hfix := actualCloudPrunedProjection_apply_eq_self V R a hzero
  refine ⟨hfix, fun i hi => ⟨hzero i hi, ?_⟩, ?_⟩
  · rintro w ⟨t, rfl⟩
    exact actualCloudPrunedProjection_apply_mem_orthogonal V R a i hi (T t)
  · intro y
    calc ‖F' q - actualCloudPrunedProjection V R a y‖
        = ‖actualCloudPrunedProjection V R a (F' q - y)‖ := by rw [map_sub, hfix]
      _ ≤ ‖actualCloudPrunedProjection V R a‖ * ‖F' q - y‖ :=
          (actualCloudPrunedProjection V R a).le_opNorm _
      _ ≤ 1 * ‖F' q - y‖ :=
          mul_le_mul_of_nonneg_right (actualCloudPrunedProjection_norm_le V R a) (norm_nonneg _)
      _ = ‖F' q - y‖ := one_mul _

/-- CFS27: the `C¹` comparison error with the pruned graph and its upper derivative bound do not increase, given
(PR) for the derivative (`K_a ∘ D = D`). -/
theorem actualCloudPrunedProjection_error_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (V : A → Submodule ℝ H) (R : A → ℝ) (a : A) (D : E →L[ℝ] H)
    (hD : (actualCloudPrunedProjection V R a).comp D = D) (T : G →L[ℝ] H) (L : E →L[ℝ] G) :
    ‖D - ((actualCloudPrunedProjection V R a).comp T).comp L‖ ≤ ‖D - T.comp L‖ ∧
      ‖(actualCloudPrunedProjection V R a).comp T‖ ≤ ‖T‖ := by
  set K := actualCloudPrunedProjection V R a
  have hK := actualCloudPrunedProjection_norm_le V R a
  constructor
  · have heq : D - (K.comp T).comp L = K.comp (D - T.comp L) := by
      conv_lhs => rw [← hD]
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc]
    rw [heq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hK (norm_nonneg _)).trans_eq (one_mul _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hK (norm_nonneg _)).trans_eq (one_mul _))

end GC.MetricGeometry
