import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.Tensor.Alternating.Basis

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ E)).finiteDimensional_of_finite

private def musicalInverse (k : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ⋀[ℝ]^k E := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (alternatingMapLinearEquiv.toLinearMap.comp
        (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))))

private theorem musicalInverse_injective (k : ℕ) :
    Function.Injective (musicalInverse (E := E) k) := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.injective.comp
    (LinearMap.toContinuousLinearMap.injective.comp
      (alternatingMapLinearEquiv.injective.comp
        ContinuousAlternatingMap.toAlternatingMap_injective))

def musicalEquiv (k : ℕ) : (⋀[ℝ]^k E) ≃L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ :=
  (LinearEquiv.ofInjectiveOfFinrankEq (musicalInverse k) (musicalInverse_injective k)
    (by rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap,
      exteriorPower.finrank_eq])).symm.toContinuousLinearEquiv

theorem inner_musicalEquiv_symm_ιMulti (k : ℕ)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ⟪(musicalEquiv k).symm a, ιMulti ℝ k v⟫ = a v := by
  let _ : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  change ⟪(InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm
    (LinearMap.toContinuousLinearMap (alternatingMapLinearEquiv a.toAlternatingMap)),
      ιMulti ℝ k v⟫ = a v
  rw [InnerProductSpace.toDual_symm_apply]
  exact alternatingMapLinearEquiv_apply_ιMulti a.toAlternatingMap v

theorem musicalEquiv_apply (k : ℕ) (u : ⋀[ℝ]^k E) (v : Fin k → E) :
    musicalEquiv k u v = ⟪u, ιMulti ℝ k v⟫ := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    (inner_musicalEquiv_symm_ιMulti k (musicalEquiv k u) v).symm

theorem musicalEquiv_ιMulti_apply (k : ℕ) (u v : Fin k → E) :
    musicalEquiv k (ιMulti ℝ k u) v =
      Matrix.det (Matrix.of fun i j => ⟪u j, v i⟫) := by
  rw [musicalEquiv_apply, inner_ιMulti_ιMulti]

theorem alternatingMapLinearEquiv_musicalEquiv (k : ℕ) (u v : ⋀[ℝ]^k E) :
    alternatingMapLinearEquiv (musicalEquiv k u).toAlternatingMap v = ⟪u, v⟫ := by
  have h : alternatingMapLinearEquiv (musicalEquiv k u).toAlternatingMap =
      innerₗ (⋀[ℝ]^k E) u := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro w
    exact (alternatingMapLinearEquiv_apply_ιMulti _ w).trans (musicalEquiv_apply k u w)
  exact LinearMap.congr_fun h v

omit [FiniteDimensional ℝ E] in
private theorem sum_mul_prod_inner {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) *
      ∏ i, ⟪v i, e (j i)⟫) = a v := by
  classical
  have h := a.toContinuousMultilinearMap.map_sum
    (fun i j => ⟪v i, e j⟫ • e j)
  have he : (fun i => ∑ j, ⟪v i, e j⟫ • e j) = v := by
    funext i
    simpa only [real_inner_comm] using e.sum_repr' (v i)
  rw [he] at h
  simpa only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap] using h.symm

private theorem sum_mul_musicalEquiv_ιMulti {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) *
      musicalEquiv k (ιMulti ℝ k v) (fun i => e (j i))) =
        (k.factorial : ℝ) * a v := by
  classical
  have hdet (j : Fin k → ι) :
      musicalEquiv k (ιMulti ℝ k v) (fun i => e (j i)) =
        Matrix.det (Matrix.of fun i l => ⟪v i, e (j l)⟫) := by
    rw [musicalEquiv_ιMulti_apply, ← Matrix.det_transpose]
    rfl
  simp only [hdet, Matrix.det_apply, Matrix.of_apply,
    Finset.mul_sum, Units.smul_def, zsmul_eq_mul]
  rw [Finset.sum_comm]
  have hterm (σ : Equiv.Perm (Fin k)) :
      (∑ j : Fin k → ι, a (fun i => e (j i)) *
        ((σ.sign : ℝ) * ∏ i, ⟪v (σ i), e (j i)⟫)) = a v := by
    calc
      _ = (σ.sign : ℝ) *
          ∑ j : Fin k → ι, a (fun i => e (j i)) *
            ∏ i, ⟪v (σ i), e (j i)⟫ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (σ.sign : ℝ) * a (v ∘ σ) :=
        congrArg ((σ.sign : ℝ) * ·) (sum_mul_prod_inner k e a (v ∘ σ))
      _ = a v := by
        change (σ.sign : ℝ) * a.toAlternatingMap (v ∘ σ) = a.toAlternatingMap v
        rw [a.toAlternatingMap.map_perm v σ]
        simp only [Units.smul_def, zsmul_eq_mul, ← mul_assoc]
        norm_cast
        rw [Int.units_mul_self]
        simp
  calc
    _ = ∑ _σ : Equiv.Perm (Fin k), a v :=
      Finset.sum_congr rfl (fun σ _ => hterm σ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]

theorem sum_mul_eq_factorial_mul_inner {ι : Type*} [Fintype ι]
    (k : ℕ) (e : OrthonormalBasis ι ℝ E)
    (a b : E [⋀^Fin k]→L[ℝ] ℝ) :
    (∑ j : Fin k → ι, a (fun i => e (j i)) * b (fun i => e (j i))) =
      (k.factorial : ℝ) * ⟪(musicalEquiv k).symm a, (musicalEquiv k).symm b⟫ := by
  classical
  let L : (⋀[ℝ]^k E) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ j : Fin k → ι,
        a (fun i => e (j i)) * musicalEquiv k w (fun i => e (j i))
      map_add' := fun w z => by
        simp only [map_add, ContinuousAlternatingMap.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c w => by
        simp only [map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  let R : (⋀[ℝ]^k E) →ₗ[ℝ] ℝ :=
    (k.factorial : ℝ) • innerₗ (⋀[ℝ]^k E) ((musicalEquiv k).symm a)
  have h : L = R := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (∑ j : Fin k → ι, a (fun i => e (j i)) *
      musicalEquiv k (ιMulti ℝ k v) (fun i => e (j i))) =
        (k.factorial : ℝ) * ⟪(musicalEquiv k).symm a, ιMulti ℝ k v⟫
    rw [inner_musicalEquiv_symm_ιMulti]
    exact sum_mul_musicalEquiv_ιMulti k e a v
  have heval := LinearMap.congr_fun h ((musicalEquiv k).symm b)
  simpa only [L, R, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
    ContinuousLinearEquiv.apply_symm_apply] using heval

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem inner_map_linearIsometry (k : ℕ) (f : E →ₗᵢ[ℝ] F)
    (u v : ⋀[ℝ]^k E) :
    ⟪exteriorPower.map k f.toLinearMap u,
      exteriorPower.map k f.toLinearMap v⟫ = ⟪u, v⟫ := by
  let m : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k F) := exteriorPower.map k f.toLinearMap
  have h_for (u : Fin k → E) :
      (innerₗ (⋀[ℝ]^k F) (m (ιMulti ℝ k u))).comp m =
        innerₗ (⋀[ℝ]^k E) (ιMulti ℝ k u) := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro v
    change ⟪m (ιMulti ℝ k u), m (ιMulti ℝ k v)⟫ =
      ⟪ιMulti ℝ k u, ιMulti ℝ k v⟫
    rw [map_apply_ιMulti, map_apply_ιMulti, inner_ιMulti_ιMulti,
      inner_ιMulti_ιMulti]
    apply congrArg Matrix.det
    funext i j
    change ⟪f (u j), f (v i)⟫ = ⟪u j, v i⟫
    exact f.inner_map_map _ _
  let B : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E →ₗ[ℝ] ℝ) :=
    { toFun := fun x => (innerₗ (⋀[ℝ]^k F) (m x)).comp m
      map_add' := by intros; ext y; simp
      map_smul' := by intros; ext y; simp [smul_eq_mul] }
  let C : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E →ₗ[ℝ] ℝ) :=
    { toFun := fun x => innerₗ (⋀[ℝ]^k E) x
      map_add' := by intros; ext y; simp
      map_smul' := by intros; ext y; simp [smul_eq_mul] }
  have hBC : B = C := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro u
    change (innerₗ (⋀[ℝ]^k F) (m (ιMulti ℝ k u))).comp m =
      innerₗ (⋀[ℝ]^k E) (ιMulti ℝ k u)
    exact h_for u
  exact LinearMap.congr_fun (LinearMap.congr_fun hBC u) v

theorem musicalEquiv_map_apply (k : ℕ) (f : E →ₗᵢ[ℝ] F)
    (u : ⋀[ℝ]^k E) (v : Fin k → E) :
    musicalEquiv k (E := F) (exteriorPower.map k f.toLinearMap u)
        (fun i => f (v i)) = musicalEquiv k (E := E) u v := by
  rw [musicalEquiv_apply, musicalEquiv_apply]
  have hm : exteriorPower.map k f.toLinearMap (ιMulti ℝ k v) =
      ιMulti ℝ k (fun i => f (v i)) := by
    rw [map_apply_ιMulti]
    rfl
  rw [← hm]
  exact inner_map_linearIsometry k f u (ιMulti ℝ k v)

theorem musicalEquiv_map (k : ℕ) (f : E ≃ₗᵢ[ℝ] F) (u : ⋀[ℝ]^k E) :
    musicalEquiv k (map k f.toLinearEquiv.toLinearMap u) =
      (musicalEquiv k u).compContinuousLinearMap
        f.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousAlternatingMap.ext
  intro v
  have h := musicalEquiv_map_apply k f.toLinearIsometry u (fun i => f.symm (v i))
  change musicalEquiv k (map k f.toLinearIsometry.toLinearMap u) v =
    musicalEquiv k u (fun i => f.symm (v i))
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply] using h

theorem map_musicalEquiv_symm (k : ℕ) (f : E ≃ₗᵢ[ℝ] F)
    (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    map k f.toLinearEquiv.toLinearMap ((musicalEquiv k).symm a) =
      (musicalEquiv k).symm (a.compContinuousLinearMap
        f.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply (musicalEquiv k).injective
  rw [musicalEquiv_map, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end exteriorPower
