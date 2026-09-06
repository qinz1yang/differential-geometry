import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem linearIsometryEquiv_exists_eigenvector_one_or_neg_one
    (e : E ≃ₗᵢ[ℝ] E) (hfinrank : finrank ℝ E = 3) :
    ∃ v : E, v ≠ 0 ∧ (e v = v ∨ e v = -v) := by
  let b := stdOrthonormalBasis ℝ E
  let f : Module.End ℝ E := e.toLinearEquiv.toLinearMap
  let A : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis f
  have horth : A ∈ Matrix.orthogonalGroup (Fin (finrank ℝ E)) ℝ := by
    exact e.toMatrix_mem_unitaryGroup b b
  have hAtA : A.transpose * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin (finrank ℝ E)) ℝ).mp horth
  have hcard : Fintype.card (Fin (finrank ℝ E)) = 3 := by
    simpa using hfinrank
  have hdet : A.det = 1 ∨ A.det = -1 := by
    rw [← sq_eq_one_iff]
    simpa [unitary, sq] using! Matrix.det_of_mem_unitary horth
  rcases hdet with hdet | hdet
  · have hdet_sub : (A - 1).det = 0 := by
      have hneg : (A - 1).det = -(A - 1).det := by
        calc
          (A - 1).det = A.transpose.det * (A - 1).det := by
            rw [Matrix.det_transpose, hdet, one_mul]
          _ = (A.transpose * (A - 1)).det := (Matrix.det_mul _ _).symm
          _ = (1 - A.transpose).det := by rw [Matrix.mul_sub, hAtA, Matrix.mul_one]
          _ = (-(A - 1).transpose).det := by
            congr 1
            ext i j
            simp
          _ = -(A - 1).det := by
            rw [Matrix.det_neg, hcard, Matrix.det_transpose]
            norm_num
      linarith
    have hfdet : LinearMap.det (f - 1) = 0 := by
      rw [← LinearMap.det_toMatrix b.toBasis]
      simpa only [A, map_sub, LinearMap.toMatrix_one] using hdet_sub
    obtain ⟨v, hv, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hfdet)
    refine ⟨v, hv_ne, Or.inl ?_⟩
    change e v - v = 0 at hv
    exact sub_eq_zero.mp hv
  · have hdet_add : (A + 1).det = 0 := by
      have hneg : (A + 1).det = -(A + 1).det := by
        calc
          (A + 1).det = -(A.transpose.det * (A + 1).det) := by
            rw [Matrix.det_transpose, hdet]
            ring
          _ = -(A.transpose * (A + 1)).det := by rw [Matrix.det_mul]
          _ = -(1 + A.transpose).det := by rw [Matrix.mul_add, hAtA, Matrix.mul_one]
          _ = -((A + 1).transpose).det := by
            congr 2
            ext i j
            simp [Matrix.one_apply, eq_comm, add_comm]
          _ = -(A + 1).det := by rw [Matrix.det_transpose]
      linarith
    have hfdet : LinearMap.det (f + 1) = 0 := by
      rw [← LinearMap.det_toMatrix b.toBasis]
      simpa only [A, map_add, LinearMap.toMatrix_one] using hdet_add
    obtain ⟨v, hv, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hfdet)
    refine ⟨v, hv_ne, Or.inr ?_⟩
    change e v + v = 0 at hv
    exact eq_neg_of_add_eq_zero_left hv

section Three

variable [Fact (finrank ℝ E = 3)]

theorem sphereDiffeo_exists_fixed_or_antipodal_point
    (e : E ≃ₗᵢ[ℝ] E) :
    (∃ x : sphere (0 : E) 1, sphereDiffeo (n := 2) e x = x) ∨
      ∃ x : sphere (0 : E) 1, sphereDiffeo (n := 2) e x = -x := by
  obtain ⟨v, hv_ne, hv⟩ :=
    linearIsometryEquiv_exists_eigenvector_one_or_neg_one e Fact.out
  let x : sphere (0 : E) 1 :=
    ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hv_ne]⟩
  rcases hv with hv | hv
  · left
    refine ⟨x, Subtype.ext ?_⟩
    change e (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    rw [map_smul, hv]
  · right
    refine ⟨x, Subtype.ext ?_⟩
    change e (‖v‖⁻¹ • v) = -(‖v‖⁻¹ • v)
    rw [map_smul, hv, smul_neg]

end Three

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem sphereDiffeo_eq_neg_of_sq_eq_one_of_fixed_point_free
    (e : E ≃ₗᵢ[ℝ] E) (hsq : e * e = 1)
    (hfree : ∀ x : sphere (0 : E) 1, sphereDiffeo (n := n) e x ≠ x) :
    e = LinearIsometryEquiv.neg ℝ := by
  apply LinearIsometryEquiv.ext
  intro v
  have hee : e (e v) = v := by
    have h := congrArg (fun a : E ≃ₗᵢ[ℝ] E => a v) hsq
    simpa using h
  have hsum : e v + v = 0 := by
    by_contra hne
    let x : sphere (0 : E) 1 :=
      ⟨‖e v + v‖⁻¹ • (e v + v), by
        rw [mem_sphere_zero_iff_norm, norm_smul]
        simp [hne]⟩
    apply hfree x
    apply Subtype.ext
    change e (‖e v + v‖⁻¹ • (e v + v)) =
      ‖e v + v‖⁻¹ • (e v + v)
    rw [map_smul, map_add, hee, add_comm]
  change e v = -v
  exact eq_neg_of_add_eq_zero_left hsum

section FreeAction

variable {Γ : Type*} [Group Γ]

theorem orth_rep_injective_of_free_sphere_action
    (ρ : Γ →* (E ≃ₗᵢ[ℝ] E))
    (hfree : ∀ (γ : Γ) (x : sphere (0 : E) 1),
      sphereDiffeo (n := n) (ρ γ) x = x → γ = 1) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hfinrank : 0 < finrank ℝ E := by
    rw [show finrank ℝ E = n + 1 from Fact.out]
    omega
  let : Nontrivial E := Module.nontrivial_of_finrank_pos hfinrank
  let x : sphere (0 : E) 1 :=
    Classical.choice
      (NormedSpace.sphere_nonempty_rclike ℝ
        (E := E) (r := (1 : ℝ)) zero_le_one)
  apply hfree γ x
  apply Subtype.ext
  change ρ γ (x : E) = (x : E)
  rw [hγ]
  rfl

variable [Fact (finrank ℝ E = 3)]

theorem orth_rep_apply_eq_one_or_neg_of_free_sphere_action
    (ρ : Γ →* (E ≃ₗᵢ[ℝ] E))
    (hfree : ∀ (γ : Γ) (x : sphere (0 : E) 1),
      sphereDiffeo (n := 2) (ρ γ) x = x → γ = 1)
    (γ : Γ) :
    ρ γ = 1 ∨ ρ γ = LinearIsometryEquiv.neg ℝ := by
  by_cases hγ : γ = 1
  · left
    subst γ
    exact ρ.map_one
  have hfixedPointFree : ∀ x : sphere (0 : E) 1,
      sphereDiffeo (n := 2) (ρ γ) x ≠ x := by
    intro x hx
    exact hγ (hfree γ x hx)
  rcases sphereDiffeo_exists_fixed_or_antipodal_point (ρ γ) with
    ⟨x, hfixed⟩ | ⟨x, hantipodal⟩
  · exact (hfixedPointFree _ hfixed).elim
  right
  have hambient : ρ γ (x : E) = -(x : E) := by
    simpa using congrArg Subtype.val hantipodal
  have hsquareFixed : sphereDiffeo (n := 2) (ρ (γ * γ)) x = x := by
    apply Subtype.ext
    change ρ (γ * γ) (x : E) = (x : E)
    rw [ρ.map_mul]
    calc
      (ρ γ * ρ γ) (x : E) = ρ γ (ρ γ (x : E)) := rfl
      _ = ρ γ (-(x : E)) := by rw [hambient]
      _ = -ρ γ (x : E) := map_neg (ρ γ) (x : E)
      _ = -(-(x : E)) := by rw [hambient]
      _ = (x : E) := neg_neg _
  have hsqGroup : γ * γ = 1 := hfree (γ * γ) x hsquareFixed
  have hsq : ρ γ * ρ γ = 1 := by
    rw [← ρ.map_mul, hsqGroup, ρ.map_one]
  exact sphereDiffeo_eq_neg_of_sq_eq_one_of_fixed_point_free
    (ρ γ) hsq hfixedPointFree

end FreeAction

end DifferentialGeometry.Geometry
