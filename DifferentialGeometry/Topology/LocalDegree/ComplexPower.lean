import DifferentialGeometry.Topology.LocalDegree.FiniteAdditivity
import DifferentialGeometry.Topology.LocalDegree.Determinant
import DifferentialGeometry.Topology.LocalDegree.BallPerturbation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

set_option autoImplicit false

noncomputable section
open Set Metric
open scoped Topology

namespace DifferentialGeometry.LocalDegree

/-- The normalized complex power in the same standard real coordinates on
the source and target. -/
def normalizedComplexPower (a : ℂ) (n : ℕ) :
    C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)) :=
  let e := Complex.orthonormalBasisOneI.repr
  ⟨fun x => e ((e.symm x - a) ^ n / (n : ℂ)), by fun_prop⟩

private abbrev planeCoordinates : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

private theorem norm_coordinate_difference (a : ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖planeCoordinates.symm x - a‖ = ‖x - planeCoordinates a‖ := by
  simpa only [map_sub, LinearIsometryEquiv.apply_symm_apply] using
    (planeCoordinates.norm_map (planeCoordinates.symm x - a)).symm

private theorem normalizedComplexPower_boundary_norm (a : ℂ) (n : ℕ)
    {r : ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ sphere (planeCoordinates a) r) :
    ‖normalizedComplexPower a n x‖ = r ^ n / (n : ℝ) := by
  simp only [normalizedComplexPower, ContinuousMap.coe_mk,
    LinearIsometryEquiv.norm_map, norm_div, norm_pow, Complex.norm_natCast]
  rw [norm_coordinate_difference, mem_sphere_iff_norm.mp hx]

private def shiftedComplexPower (a : ℂ) (n : ℕ) (ρ : ℝ) :
    C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun x => planeCoordinates
    (((planeCoordinates.symm x - a) ^ n - (ρ : ℂ) ^ n) / (n : ℂ)), by fun_prop⟩

private theorem shiftedComplexPower_eq_zero_iff (a : ℂ) (n : ℕ)
    (hn : 0 < n) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    shiftedComplexPower a n ρ x = 0 ↔
      (planeCoordinates.symm x - a) ^ n = (ρ : ℂ) ^ n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  change planeCoordinates
    (((planeCoordinates.symm x - a) ^ n - (ρ : ℂ) ^ n) / (n : ℂ)) = 0 ↔ _
  simp only [LinearIsometryEquiv.map_eq_zero_iff, div_eq_zero_iff, hnC,
    or_false, sub_eq_zero]

private theorem shiftedComplexPower_root_norm (a : ℂ) (n : ℕ)
    (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : shiftedComplexPower a n ρ x = 0) :
    ‖planeCoordinates.symm x - a‖ = ρ := by
  have hp := congrArg norm ((shiftedComplexPower_eq_zero_iff a n hn ρ x).mp hx)
  rw [norm_pow, norm_pow, Complex.norm_of_nonneg hρ.le] at hp
  exact (pow_left_inj₀ (norm_nonneg _) hρ.le hn.ne').mp hp

private def shiftedComplexPowerRootEquiv (a : ℂ) (n : ℕ)
    (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) :
    rootsOfUnity n ℂ ≃ {x : EuclideanSpace ℝ (Fin 2) |
      shiftedComplexPower a n ρ x = 0} := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine
    { toFun := fun ζ => ⟨planeCoordinates (a + (ρ : ℂ) * ((ζ : ℂˣ) : ℂ)), ?_⟩
      invFun := fun x => rootsOfUnity.mkOfPowEq
        ((planeCoordinates.symm x.val - a) / (ρ : ℂ)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · apply (shiftedComplexPower_eq_zero_iff a n hn ρ _).mpr
    rw [LinearIsometryEquiv.symm_apply_apply, add_sub_cancel_left, mul_pow,
      (mem_rootsOfUnity' n ζ.val).mp ζ.property, mul_one]
  · rw [div_pow, (shiftedComplexPower_eq_zero_iff a n hn ρ x.val).mp x.property,
      div_self (pow_ne_zero _ hρC)]
  · intro ζ
    apply rootsOfUnity.coe_injective
    change (planeCoordinates.symm
      (planeCoordinates (a + (ρ : ℂ) * ((ζ : ℂˣ) : ℂ))) - a) / (ρ : ℂ) = _
    rw [LinearIsometryEquiv.symm_apply_apply, add_sub_cancel_left]
    field_simp [hρC]
  · intro x
    apply Subtype.ext
    apply planeCoordinates.symm.injective
    change planeCoordinates.symm
      (planeCoordinates (a + (ρ : ℂ) *
        ((planeCoordinates.symm x.val - a) / (ρ : ℂ)))) = planeCoordinates.symm x.val
    rw [LinearIsometryEquiv.symm_apply_apply]
    field_simp [hρC]
    ring

private def complexLinearInCoordinates (w : ℂ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  planeCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).comp
      planeCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem complexLinearInCoordinates_det (w : ℂ) :
    LinearMap.det (complexLinearInCoordinates w).toLinearMap = ‖w‖ ^ 2 := by
  change LinearMap.det
    ((planeCoordinates.toLinearEquiv : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
      ((ContinuousLinearMap.toSpanSingleton ℂ w).toLinearMap.restrictScalars ℝ) ∘ₗ
      (planeCoordinates.symm.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ)) = _
  rw [LinearIsometryEquiv.toLinearEquiv_symm,
    LinearMap.det_conj
      ((ContinuousLinearMap.toSpanSingleton ℂ w).toLinearMap.restrictScalars ℝ)
      planeCoordinates.toLinearEquiv,
    LinearMap.det_restrictScalars]
  change Algebra.norm ℝ (ContinuousLinearMap.toSpanSingleton ℂ w).det = _
  rw [ContinuousLinearMap.det_toSpanSingleton, Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq w

private theorem shiftedComplexPower_hasFDerivAt (a : ℂ) (n : ℕ)
    (hn : 0 < n) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (shiftedComplexPower a n ρ)
      (complexLinearInCoordinates ((planeCoordinates.symm x - a) ^ (n - 1))) x := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : HasDerivAt (fun z : ℂ => ((z - a) ^ n - (ρ : ℂ) ^ n) / (n : ℂ))
      ((planeCoordinates.symm x - a) ^ (n - 1)) (planeCoordinates.symm x) := by
    have hq : HasDerivAt (fun z : ℂ => z - a) 1 (planeCoordinates.symm x) :=
      (hasDerivAt_id' (planeCoordinates.symm x)).sub_const a
    have hp := hq.pow n
    change HasDerivAt (fun z : ℂ => (z - a) ^ n)
      ((n : ℂ) * (planeCoordinates.symm x - a) ^ (n - 1) * 1)
      (planeCoordinates.symm x) at hp
    simpa only [mul_one, mul_div_cancel_left₀ _ hnC] using
      (hp.sub_const ((ρ : ℂ) ^ n)).div_const (n : ℂ)
  exact planeCoordinates.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hd.hasFDerivAt.restrictScalars ℝ).comp x
      planeCoordinates.symm.toContinuousLinearEquiv.hasFDerivAt)

/-- The normalized power has degree `n` on every positive-radius ball about
its center. Boundary nonvanishing and the orientation of each regular root
are derived using the same real coordinates on both sides. -/
theorem euclideanBallDegree_normalizedComplexPower
    (a : ℂ) (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    let e := Complex.orthonormalBasisOneI.repr
    let f := (normalizedComplexPower a n).restrict (Metric.closedBall (e a) r)
    ∃ hb : ∀ x : Metric.closedBall (e a) r,
        x.val ∈ Metric.sphere (e a) r → f x ≠ 0,
      euclideanBallDegree (d := 1) hr f hb = (n : ℤ) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r := by dsimp [ρ]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let f := (normalizedComplexPower a n).restrict (closedBall (planeCoordinates a) r)
  let g0 := shiftedComplexPower a n ρ
  let g := g0.restrict (closedBall (planeCoordinates a) r)
  have hf : ∀ x : closedBall (planeCoordinates a) r,
      x.val ∈ sphere (planeCoordinates a) r → f x ≠ 0 := by
    intro x hx
    apply norm_pos_iff.mp
    change 0 < ‖normalizedComplexPower a n x.val‖
    rw [normalizedComplexPower_boundary_norm a n hx]
    exact div_pos (pow_pos hr _) hnR
  have hclose : ∀ x : closedBall (planeCoordinates a) r,
      x.val ∈ sphere (planeCoordinates a) r → ‖g x - f x‖ < ‖f x‖ := by
    intro x hx
    have heq : g x - f x = -planeCoordinates ((ρ : ℂ) ^ n / (n : ℂ)) := by
      change planeCoordinates
        (((planeCoordinates.symm x.val - a) ^ n - (ρ : ℂ) ^ n) / (n : ℂ)) -
        planeCoordinates ((planeCoordinates.symm x.val - a) ^ n / (n : ℂ)) = _
      rw [← map_sub, ← map_neg]
      congr 1
      ring
    rw [heq, norm_neg, LinearIsometryEquiv.norm_map, norm_div, norm_pow,
      Complex.norm_of_nonneg hρ.le, Complex.norm_natCast]
    change ρ ^ n / (n : ℝ) < ‖normalizedComplexPower a n x.val‖
    rw [normalizedComplexPower_boundary_norm a n hx]
    exact (div_lt_div_iff_of_pos_right hnR).mpr
      (pow_lt_pow_left₀ hρr hρ.le hn.ne')
  obtain ⟨hg, hdegrees⟩ := euclideanBallDegree_eq_of_norm_sub_lt hr f hf g hclose
  have hroot_mem : ∀ x, g0 x = 0 → x ∈ closedBall (planeCoordinates a) r := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, ← norm_coordinate_difference]
    exact (shiftedComplexPower_root_norm a n hn hρ hx).le.trans hρr.le
  let Z := {x : EuclideanSpace ℝ (Fin 2) |
    x ∈ closedBall (planeCoordinates a) r ∧ g0 x = 0}
  let eZ : {x : EuclideanSpace ℝ (Fin 2) | g0 x = 0} ≃ Z :=
    { toFun := fun x => ⟨x.val, hroot_mem x.val x.property, x.property⟩
      invFun := fun x => ⟨x.val, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eRoots : rootsOfUnity n ℂ ≃ Z :=
    (shiftedComplexPowerRootEquiv a n hn ρ hρ).trans eZ
  let : Finite Z := Finite.of_equiv (rootsOfUnity n ℂ) eRoots
  let : Fintype Z := Fintype.ofFinite Z
  have hfinite : {x ∈ closedBall (planeCoordinates a) r | g0 x = 0}.Finite :=
    Set.finite_coe_iff.mp inferInstance
  have hcard : Fintype.card Z = n := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr eRoots).symm.trans (Complex.card_rootsOfUnity n)
  have hboundary : ∀ x ∈ sphere (planeCoordinates a) r, g0 x ≠ 0 := by
    intro x hx
    exact hg ⟨x, sphere_subset_closedBall hx⟩ hx
  have hlocal (x : Z) :
      euclideanLocalDegree g0 x.val
        (isolatedZero_of_finite_closedBall_zeroSet g0.continuous.continuousOn
          hfinite hboundary x.property.1 x.property.2) = 1 := by
    have hq : planeCoordinates.symm x.val - a ≠ 0 := by
      apply norm_pos_iff.mp
      rw [shiftedComplexPower_root_norm a n hn hρ x.property.2]
      exact hρ
    have hd : HasFDerivAt g0
        (complexLinearInCoordinates ((planeCoordinates.symm x.val - a) ^ (n - 1)))
        x.val := shiftedComplexPower_hasFDerivAt a n hn ρ x.val
    have hdet : 0 < LinearMap.det (fderiv ℝ g0 x.val).toLinearMap := by
      rw [hd.fderiv, complexLinearInCoordinates_det]
      exact sq_pos_of_pos (norm_pos_iff.mpr (pow_ne_zero _ hq))
    rw [euclideanLocalDegree_eq_sign_det_fderiv _ hd.differentiableAt hdet.ne',
      sign_pos hdet]
    rfl
  refine ⟨hf, hdegrees.trans ?_⟩
  calc
    euclideanBallDegree hr g hg =
        ∑ᶠ x : Z, euclideanLocalDegree g0 x.val
          (isolatedZero_of_finite_closedBall_zeroSet g0.continuous.continuousOn
            hfinite hboundary x.property.1 x.property.2) :=
      euclideanBallDegree_eq_finsum_localDegrees hr g0.continuous.continuousOn
        hfinite hboundary
    _ = ∑ x : Z, (1 : ℤ) := by
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_congr rfl (fun x _ => hlocal x)
    _ = (n : ℤ) := by simp [hcard]

end DifferentialGeometry.LocalDegree
