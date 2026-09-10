import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Normalize
import DifferentialGeometry.Topology.SphereSeparation.GlobalNormal

open Function Set Matrix
open scoped ContDiff Manifold Topology Matrix.Norms.Elementwise

namespace Poincare.Topology.SphereSeparation

abbrev R3 := Fin 3 → ℝ

noncomputable def matrixAdjugateNormal
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x : R3) : R3 :=
  A.adjugateᵀ *ᵥ x

theorem continuous_matrixAdjugateNormal :
    Continuous fun p : Matrix (Fin 3) (Fin 3) ℝ × R3 ↦
      matrixAdjugateNormal p.1 p.2 := by
  exact (continuous_fst.matrix_adjugate.matrix_transpose).matrix_mulVec continuous_snd

theorem contDiff_matrixAdjugateNormal :
    ContDiff ℝ ∞ fun p : Matrix (Fin 3) (Fin 3) ℝ × R3 ↦
      matrixAdjugateNormal p.1 p.2 := by
  have hentry : ∀ i j : Fin 3,
      ContDiff ℝ ∞ fun p : Matrix (Fin 3) (Fin 3) ℝ × R3 ↦ p.1 i j := by
    intro i j
    fun_prop
  have hadj : ∀ i j : Fin 3,
      ContDiff ℝ ∞ fun p : Matrix (Fin 3) (Fin 3) ℝ × R3 ↦
        p.1.adjugate i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_three] using
        (hentry 1 1).mul (hentry 2 2) |>.sub ((hentry 1 2).mul (hentry 2 1))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentry 0 1).mul (hentry 2 2)).neg.add ((hentry 0 2).mul (hentry 2 1))
    · simpa [Matrix.adjugate_fin_three] using
        (hentry 0 1).mul (hentry 1 2) |>.sub ((hentry 0 2).mul (hentry 1 1))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentry 1 0).mul (hentry 2 2)).neg.add ((hentry 1 2).mul (hentry 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentry 0 0).mul (hentry 2 2) |>.sub ((hentry 0 2).mul (hentry 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentry 0 0).mul (hentry 1 2)).neg.add ((hentry 0 2).mul (hentry 1 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentry 1 0).mul (hentry 2 1) |>.sub ((hentry 1 1).mul (hentry 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentry 0 0).mul (hentry 2 1)).neg.add ((hentry 0 1).mul (hentry 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentry 0 0).mul (hentry 1 1) |>.sub ((hentry 0 1).mul (hentry 1 0))
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ ∞ fun p : Matrix (Fin 3) (Fin 3) ℝ × R3 ↦
    ∑ j, p.1.adjugate j i * p.2 j
  exact ContDiff.sum fun j _ ↦
    (hadj j i).mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)

noncomputable def adjugateNormal (A : R3 →ₗ[ℝ] R3) (x : R3) : R3 :=
  matrixAdjugateNormal (LinearMap.toMatrix' A) x

private lemma adjugate_col_zero (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate.col 0 = A.row 1 ⨯₃ A.row 2 := by
  ext i
  fin_cases i <;> simp [Matrix.adjugate_fin_three, cross_apply]
  ring

private lemma adjugate_col_one (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate.col 1 = A.row 2 ⨯₃ A.row 0 := by
  ext i
  fin_cases i <;> simp [Matrix.adjugate_fin_three, cross_apply] <;> ring

private lemma adjugate_col_two (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate.col 2 = A.row 0 ⨯₃ A.row 1 := by
  ext i
  fin_cases i <;> simp [Matrix.adjugate_fin_three, cross_apply]
  ring

theorem rank_le_one_of_adjugate_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hadj : A.adjugate = 0) : A.rank ≤ 1 := by
  have h12 : A.row 1 ⨯₃ A.row 2 = 0 := by
    rw [← adjugate_col_zero A, hadj]
    rfl
  have h20 : A.row 2 ⨯₃ A.row 0 = 0 := by
    rw [← adjugate_col_one A, hadj]
    rfl
  have h01 : A.row 0 ⨯₃ A.row 1 = 0 := by
    rw [← adjugate_col_two A, hadj]
    rfl
  have h02 : A.row 0 ⨯₃ A.row 2 = 0 := by
    rw [← cross_anticomm, h20, neg_zero]
  have h10 : A.row 1 ⨯₃ A.row 0 = 0 := by
    rw [← cross_anticomm, h01, neg_zero]
  have h21 : A.row 2 ⨯₃ A.row 1 = 0 := by
    rw [← cross_anticomm, h12, neg_zero]
  by_cases hrow : ∃ i, A.row i ≠ 0
  · obtain ⟨i, hi⟩ := hrow
    have hcross : ∀ j, A.row i ⨯₃ A.row j = 0 := by
      intro j
      fin_cases i <;> fin_cases j
      · exact cross_self _
      · exact h01
      · exact h02
      · exact h10
      · exact cross_self _
      · exact h12
      · exact h20
      · exact h21
      · exact cross_self _
    have hmultiple : ∀ j, ∃ c : ℝ, c • A.row i = A.row j := by
      intro j
      have hdep : ¬ LinearIndependent ℝ ![A.row i, A.row j] := by
        rw [← crossProduct_ne_zero_iff_linearIndependent]
        simp [hcross j]
      rw [LinearIndependent.pair_iff' hi, not_forall_not] at hdep
      exact hdep
    rw [Matrix.rank_eq_finrank_span_row]
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) ≤
          Module.finrank ℝ (ℝ ∙ A.row i) := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro v ⟨j, rfl⟩
        exact Submodule.mem_span_singleton.mpr (hmultiple j)
      _ = 1 := finrank_span_singleton hi
  · have hAzero : A = 0 := by
      ext i j
      have hi : A.row i = 0 := not_ne_iff.mp (not_exists.mp hrow i)
      exact congrFun hi j
    simp [hAzero]


theorem adjugate_ne_zero_of_rank_eq_two (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hrank : A.rank = 2) : A.adjugate ≠ 0 := by
  intro hadj
  have := rank_le_one_of_adjugate_eq_zero A hadj
  omega


theorem adjugateNormal_orthogonal (A : R3 →ₗ[ℝ] R3) (x w : R3)
    (hdet : (LinearMap.toMatrix' A).det = 0) :
    A w ⬝ᵥ adjugateNormal A x = 0 := by
  let M := LinearMap.toMatrix' A
  rw [← LinearMap.toMatrix'_mulVec A w]
  change (M *ᵥ w) ⬝ᵥ (M.adjugateᵀ *ᵥ x) = 0
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet]
  simp

theorem adjugateNormal_ne_zero_of_rank_two_of_mem_ker
    (A : R3 →ₗ[ℝ] R3) (x : R3) (hx : x ≠ 0)
    (hxker : A x = 0)
    (hrank : Module.finrank ℝ (LinearMap.range A) = 2) :
    adjugateNormal A x ≠ 0 := by
  let M := LinearMap.toMatrix' A
  have hrankM : M.rank = 2 := by
    rw [Matrix.rank, ← Matrix.toLin'_apply']
    change Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' A))) = 2
    rw [Matrix.toLin'_toMatrix']
    exact hrank
  have hdet : M.det = 0 := by
    by_contra hdet
    have hfull : M.rank = 3 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    omega
  have hadj : M.adjugate ≠ 0 := adjugate_ne_zero_of_rank_eq_two M hrankM
  have hkerfin : Module.finrank ℝ (LinearMap.ker A) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker A
    rw [hrank] at h
    norm_num [Module.finrank_fin_fun] at h
    omega
  have hspan : ℝ ∙ x = LinearMap.ker A := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hxker
    · rw [finrank_span_singleton hx, hkerfin]
  have hlinne : Matrix.toLin' M.adjugate ≠ 0 := by
    intro hzero
    apply hadj
    apply Matrix.toLin'.injective
    simpa using hzero
  obtain ⟨z, hz⟩ : ∃ z : R3, Matrix.toLin' M.adjugate z ≠ 0 := by
    apply Classical.byContradiction
    intro hnone
    apply hlinne
    apply LinearMap.ext
    intro z
    exact not_ne_iff.mp (not_exists.mp hnone z)
  let y := M.adjugate *ᵥ z
  have hyne : y ≠ 0 := by simpa [y, Matrix.toLin'_apply] using hz
  have hyker : A y = 0 := by
    rw [← LinearMap.toMatrix'_mulVec A y]
    change M *ᵥ (M.adjugate *ᵥ z) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet]
    simp
  have hyspan : y ∈ ℝ ∙ x := by
    rw [hspan]
    exact hyker
  rw [Submodule.mem_span_singleton] at hyspan
  obtain ⟨c, hcy⟩ := hyspan
  intro hnormal
  have hnormal' : M.adjugateᵀ *ᵥ x = 0 := by
    simpa [adjugateNormal, matrixAdjugateNormal, M] using hnormal
  have hdot : x ⬝ᵥ c • x = 0 := by
    rw [hcy]
    change x ⬝ᵥ M.adjugate *ᵥ z = 0
    rw [← Matrix.dotProduct_transpose_mulVec M.adjugate z x]
    simp [hnormal']
  rw [dotProduct_smul, smul_eq_mul] at hdot
  have hc : c ≠ 0 := by
    intro hc
    apply hyne
    rw [← hcy]
    simp [hc]
  have hself : x ⬝ᵥ x = 0 := (mul_eq_zero.mp hdot).resolve_left hc
  exact hx (dotProduct_self_eq_zero.mp hself)


noncomputable abbrev e3coord :
    EuclideanThree ≃L[ℝ] R3 :=
  EuclideanSpace.equiv (Fin 3) ℝ


noncomputable def coordinateLinearMap
    (A : EuclideanThree →L[ℝ]
      EuclideanThree) : R3 →ₗ[ℝ] R3 :=
  e3coord.toLinearMap.comp (A.toLinearMap.comp e3coord.symm.toLinearMap)

theorem finrank_range_coordinateLinearMap
    (A : EuclideanThree →L[ℝ]
      EuclideanThree) :
    Module.finrank ℝ (LinearMap.range (coordinateLinearMap A)) =
      Module.finrank ℝ (LinearMap.range A.toLinearMap) := by
  rw [coordinateLinearMap, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e3coord.symm.toLinearEquiv),
    LinearEquiv.finrank_map_eq]


noncomputable def euclideanAdjugateNormal
    (A : EuclideanThree →L[ℝ]
      EuclideanThree)
    (x : EuclideanThree) :
      EuclideanThree :=
  e3coord.symm (adjugateNormal (coordinateLinearMap A) (e3coord x))

theorem euclideanAdjugateNormal_ne_zero
    (A : EuclideanThree →L[ℝ]
      EuclideanThree)
    (x : EuclideanThree)
    (hx : x ≠ 0) (hxker : A x = 0)
    (hrank : Module.finrank ℝ (LinearMap.range A.toLinearMap) = 2) :
    euclideanAdjugateNormal A x ≠ 0 := by
  apply e3coord.symm.injective.ne
  apply adjugateNormal_ne_zero_of_rank_two_of_mem_ker
  · exact e3coord.injective.ne hx
  · simp [coordinateLinearMap, hxker]
  · rw [finrank_range_coordinateLinearMap]
    exact hrank

theorem euclideanAdjugateNormal_mem_orthogonal_range
    (A : EuclideanThree →L[ℝ]
      EuclideanThree)
    (x : EuclideanThree)
    (hxker : A x = 0) :
    euclideanAdjugateNormal A x ∈
      Submodule.orthogonal (LinearMap.range A.toLinearMap) := by
  by_cases hx : x = 0
  · subst x
    simp [euclideanAdjugateNormal, adjugateNormal, matrixAdjugateNormal]
  rw [Submodule.mem_orthogonal]
  rintro w ⟨u, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [euclideanAdjugateNormal, e3coord,
    PiLp.continuousLinearEquiv_symm_apply, WithLp.ofLp_toLp, star_trivial]
  rw [dotProduct_comm]
  change coordinateLinearMap A (e3coord u) ⬝ᵥ
    adjugateNormal (coordinateLinearMap A) (e3coord x) = 0
  apply adjugateNormal_orthogonal
  by_contra hdet
  let M := LinearMap.toMatrix' (coordinateLinearMap A)
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero hdet
  have hcoordker : M *ᵥ e3coord x = 0 := by
    rw [LinearMap.toMatrix'_mulVec]
    simp [coordinateLinearMap, hxker]
  have hxzero : e3coord x = 0 := hinj (by simpa using hcoordker)
  exact hx (e3coord.injective (by simpa using hxzero))

noncomputable def sphereTwoBasepoint :
  SphereTwo :=
  ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩


noncomputable def radialProjection
    (y : EuclideanThree) :
    SphereTwo :=
    if hy : y = 0 then sphereTwoBasepoint else
    ⟨NormedSpace.normalize y,
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hy)⟩

@[simp] theorem coe_radialProjection_of_ne_zero
    (y : EuclideanThree) (hy : y ≠ 0) :
    (radialProjection y : EuclideanThree) =
      NormedSpace.normalize y := by
  simp [radialProjection, hy]

@[simp] theorem radialProjection_coe_sphere
    (x : SphereTwo) :
    radialProjection x = x := by
  apply Subtype.ext
  rw [coe_radialProjection_of_ne_zero x (ne_zero_of_mem_unit_sphere x)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (norm_eq_of_mem_sphere x)

theorem contDiffAt_normalize
    (y : EuclideanThree) (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ NormedSpace.normalize y := by
  change ContDiffAt ℝ ∞ (fun z ↦ ‖z‖⁻¹ • z) y
  exact ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).smul
    contDiffAt_id

theorem contDiffAt_coe_radialProjection
    (y : EuclideanThree) (hy : y ≠ 0) :
    ContDiffAt ℝ ∞
      (fun z ↦ (radialProjection z :
        EuclideanThree)) y := by
  apply (contDiffAt_normalize y hy).congr_of_eventuallyEq
  filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton hy] with z hz
  exact coe_radialProjection_of_ne_zero z hz


noncomputable def puncturedEuclideanThree : TopologicalSpace.Opens
    EuclideanThree :=
  ⟨{y | y ≠ 0}, isOpen_compl_singleton⟩


noncomputable def puncturedRadialProjection
    (y : puncturedEuclideanThree) :
    SphereTwo :=
  ⟨NormedSpace.normalize (y :
      EuclideanThree),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize y.property)⟩

theorem contMDiff_punctured_normalize :
    ContMDiff (modelWithCornersSelf ℝ
      EuclideanThree)
      (modelWithCornersSelf ℝ
        EuclideanThree) ∞
      (fun y : puncturedEuclideanThree ↦
        NormedSpace.normalize (y :
          EuclideanThree)) := by
  intro y
  exact (contDiffAt_normalize y y.property).contMDiffAt.comp y
    (contMDiff_subtype_val.contMDiffAt)

theorem contMDiff_puncturedRadialProjection :
    ContMDiff (modelWithCornersSelf ℝ
      EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      puncturedRadialProjection := by
  let _ : Fact (Module.finrank ℝ
      EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree,
      Module.finrank_fin_fun]⟩
  exact contMDiff_punctured_normalize.codRestrict_sphere _


noncomputable def puncturedRadialExtension
    (e : SphereTwo →
      EuclideanThree) :
    puncturedEuclideanThree →
      EuclideanThree :=
  e ∘ puncturedRadialProjection

theorem contMDiff_puncturedRadialExtension
    {e : SphereTwo →
      EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ
        EuclideanThree) ∞ e) :
    ContMDiff (modelWithCornersSelf ℝ
      EuclideanThree)
      (modelWithCornersSelf ℝ
        EuclideanThree) ∞
      (puncturedRadialExtension e) := by
  exact he.contMDiff.comp contMDiff_puncturedRadialProjection


noncomputable def spherePointInPunctured
    (x : SphereTwo) :
    puncturedEuclideanThree :=
  ⟨x, ne_zero_of_mem_unit_sphere x⟩

@[simp] theorem puncturedRadialExtension_spherePoint
    (e : SphereTwo →
      EuclideanThree)
    (x : SphereTwo) :
    puncturedRadialExtension e (spherePointInPunctured x) = e x := by
  simp [puncturedRadialExtension, puncturedRadialProjection,
    spherePointInPunctured, NormedSpace.normalize_eq_self_of_norm_eq_one,
    norm_eq_of_mem_sphere]


noncomputable def radialExtensionDerivative
    (e : SphereTwo →
      EuclideanThree)
    (x : SphereTwo) :
    EuclideanThree →L[ℝ]
      EuclideanThree :=
  mvfderiv (modelWithCornersSelf ℝ
    EuclideanThree)
    (puncturedRadialExtension e) (spherePointInPunctured x)


noncomputable def embeddedSphereAdjugateNormal
    (e : SphereTwo →
      EuclideanThree)
    (x : SphereTwo) :
    EuclideanThree :=
  euclideanAdjugateNormal (radialExtensionDerivative e x) x

theorem embeddedSphereAdjugateNormal_spec
    (e : SphereTwo →
      EuclideanThree)
    (x : SphereTwo)
    (hker : radialExtensionDerivative e x x = 0)
    (hrank : Module.finrank ℝ
      (LinearMap.range (radialExtensionDerivative e x).toLinearMap) = 2)
    (hrange : LinearMap.range (radialExtensionDerivative e x).toLinearMap =
      embeddedSphereTangentPlane e x) :
    embeddedSphereAdjugateNormal e x ≠ 0 ∧
      embeddedSphereAdjugateNormal e x ∈
        embeddedSphereNormalLine e x := by
  constructor
  · exact euclideanAdjugateNormal_ne_zero _ _
      (ne_zero_of_mem_unit_sphere x) hker hrank
  · rw [embeddedSphereNormalLine, ← hrange]
    exact euclideanAdjugateNormal_mem_orthogonal_range _ _ hker

end Poincare.Topology.SphereSeparation
