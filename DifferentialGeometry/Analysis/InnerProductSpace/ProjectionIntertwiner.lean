import DifferentialGeometry.Analysis.InnerProductSpace.NearOneSquareRoot
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The orthogonal intertwiner of two close orthogonal projections

Lane CMS-BUN (S-BUNDLE, kernel and family G2). For orthogonal projections `P`, `Q` of a real
Hilbert space `F` put `T = Q P + (1 - Q)(1 - P)` (`intertwinerCore`). Then `T P = Q T`,
`T* T = 1 - (Q - P)²` and `‖T - 1‖ ≤ ‖Q - P‖`. With the smooth near-one square root `W` of
`T* T`, the whole-space operator `B = T W⁻¹` (`projIntertwiner`) is orthogonal (`B* B = B B* = 1`),
norm preserving, and intertwines: `B P = Q B`; it maps `range P` onto `range Q`, so the ranks agree.
This is the polar correction of the external review (finite soul, §7 S-BUNDLE, disposition D7);
it is NOT the polar decomposition of `L* L` read on all of `F`.

`B` is jointly `C^∞` in `(P, Q)` on the open set `‖(Q - P)²‖ < sqrtRadius`, hence `C^k` along any
`C^k` family of pairs over a manifold (`ContMDiffAt.projIntertwiner`).
-/

set_option autoImplicit false

noncomputable section

open Metric
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Analysis.ProjectionIntertwiner

open DifferentialGeometry.Analysis.NearOneSqrt

section RingAlgebra

variable {R : Type*} [Ring R] {P Q : R}

theorem core_mul_eq (hP : P * P = P) (hQ : Q * Q = Q) :
    (Q * P + (1 - Q) * (1 - P)) * P = Q * (Q * P + (1 - Q) * (1 - P)) := by
  have hQ' : ∀ X : R, Q * (Q * X) = Q * X := fun X => by rw [← mul_assoc, hQ]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc, hP, hQ, hQ']
  abel

theorem core_star_mul_core (hP : P * P = P) (hQ : Q * Q = Q) :
    (P * Q + (1 - P) * (1 - Q)) * (Q * P + (1 - Q) * (1 - P)) = 1 - (Q - P) * (Q - P) := by
  have hQ' : ∀ X : R, Q * (Q * X) = Q * X := fun X => by rw [← mul_assoc, hQ]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc, hP, hQ, hQ']
  abel

theorem commute_sub_mul_sub (hP : P * P = P) (hQ : Q * Q = Q) :
    Commute P ((Q - P) * (Q - P)) := by
  have hP' : ∀ X : R, P * (P * X) = P * X := fun X => by rw [← mul_assoc, hP]
  change P * ((Q - P) * (Q - P)) = ((Q - P) * (Q - P)) * P
  simp only [mul_sub, sub_mul, mul_assoc, hP, hQ, hP']
  abel

theorem core_sub_one_eq (hP : P * P = P) :
    Q * P + (1 - Q) * (1 - P) - 1 = (Q - P) * (P + P - 1) := by
  simp only [mul_add, mul_sub, sub_mul, one_mul, mul_one, hP]
  abel

theorem reflection_mul_self (hP : P * P = P) : (P + P - 1) * (P + P - 1) = 1 := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, hP]
  abel

end RingAlgebra

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- `T = Q P + (1 - Q)(1 - P)`. -/
def intertwinerCore (P Q : F →L[ℝ] F) : F →L[ℝ] F := Q * P + (1 - Q) * (1 - P)

/-- `B = T (T* T)^{-1/2}`, written with `T* T = 1 - (Q - P)²` for orthogonal projections. -/
def projIntertwiner (P Q : F →L[ℝ] F) : F →L[ℝ] F :=
  intertwinerCore P Q * Ring.inverse (sqrtNearOne (F →L[ℝ] F) (1 - (Q - P) * (Q - P)))

/-- An operator with `star U * U = 1` preserves norms. -/
theorem norm_apply_eq_of_star_mul_self_eq_one {U : F →L[ℝ] F} (hU : star U * U = 1) (v : F) :
    ‖U v‖ = ‖v‖ := by
  have hinner : inner ℝ (U v) (U v) = inner ℝ v v := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, hU, one_apply_eq_self]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hinner

theorem norm_le_one_of_star_mul_self_eq_one {U : F →L[ℝ] F} (hU : star U * U = 1) : ‖U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_apply_eq_of_star_mul_self_eq_one hU, one_mul]

variable {P Q : F →L[ℝ] F}

omit [CompleteSpace F] in
theorem intertwinerCore_comp (hP : P ∘L P = P) (hQ : Q ∘L Q = Q) :
    intertwinerCore P Q ∘L P = Q ∘L intertwinerCore P Q :=
  core_mul_eq hP hQ

theorem star_intertwinerCore (hPs : P.adjoint = P) (hQs : Q.adjoint = Q) :
    star (intertwinerCore P Q) = P * Q + (1 - P) * (1 - Q) := by
  have hP' : star P = P := by rw [ContinuousLinearMap.star_eq_adjoint, hPs]
  have hQ' : star Q = Q := by rw [ContinuousLinearMap.star_eq_adjoint, hQs]
  simp only [intertwinerCore, star_add, star_mul, star_sub, star_one, hP', hQ']

theorem adjoint_intertwinerCore_comp (hP : P ∘L P = P) (hPs : P.adjoint = P)
    (hQ : Q ∘L Q = Q) (hQs : Q.adjoint = Q) :
    (intertwinerCore P Q).adjoint ∘L intertwinerCore P Q = 1 - (Q - P) * (Q - P) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
    star_intertwinerCore hPs hQs]
  exact core_star_mul_core hP hQ

theorem norm_intertwinerCore_sub_one_le (hP : P ∘L P = P) (hPs : P.adjoint = P) :
    ‖intertwinerCore P Q - 1‖ ≤ ‖Q - P‖ := by
  have hP' : star P = P := by rw [ContinuousLinearMap.star_eq_adjoint, hPs]
  have hU : star (P + P - 1) * (P + P - 1) = 1 := by
    rw [star_sub, star_add, star_one, hP']
    exact reflection_mul_self hP
  rw [intertwinerCore, core_sub_one_eq hP]
  calc ‖(Q - P) * (P + P - 1)‖ ≤ ‖Q - P‖ * ‖P + P - 1‖ := norm_mul_le _ _
    _ ≤ ‖Q - P‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_le_one_of_star_mul_self_eq_one hU) (norm_nonneg _)
    _ = ‖Q - P‖ := mul_one _

theorem sub_mul_sub_mem_ball (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    1 - (Q - P) * (Q - P) ∈ ball (1 : F →L[ℝ] F) (sqrtRadius (F →L[ℝ] F)) := by
  rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact lt_of_le_of_lt ((norm_mul_le _ _).trans_eq (sq _).symm) hη

/-- The kernel: `B` is orthogonal and intertwines `P` and `Q`. -/
theorem projIntertwiner_spec (hP : P ∘L P = P) (hPs : P.adjoint = P) (hQ : Q ∘L Q = Q)
    (hQs : Q.adjoint = Q) (h1 : ‖Q - P‖ < 1) (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    projIntertwiner P Q ∘L P = Q ∘L projIntertwiner P Q ∧
      (projIntertwiner P Q).adjoint ∘L projIntertwiner P Q = 1 ∧
      projIntertwiner P Q ∘L (projIntertwiner P Q).adjoint = 1 ∧
      (∀ v, ‖projIntertwiner P Q v‖ = ‖v‖) ∧ IsUnit (projIntertwiner P Q) := by
  have hPs' : star P = P := by rw [ContinuousLinearMap.star_eq_adjoint, hPs]
  have hQs' : star Q = Q := by rw [ContinuousLinearMap.star_eq_adjoint, hQs]
  set X : F →L[ℝ] F := 1 - (Q - P) * (Q - P) with hXdef
  have hX : X ∈ ball (1 : F →L[ℝ] F) (sqrtRadius (F →L[ℝ] F)) := sub_mul_sub_mem_ball hη
  set W := sqrtNearOne (F →L[ℝ] F) X with hWdef
  set T := intertwinerCore P Q with hTdef
  have hWW : W * W = X := sqrtNearOne_mul_self hX
  have hWu : IsUnit W := isUnit_sqrtNearOne hX
  have hXs : star X = X := by
    rw [hXdef, star_sub, star_one, star_mul, star_sub, hPs', hQs']
  have hWs : star W = W := by
    refine eq_sqrtNearOne hX ?_ ?_
    · rw [← star_one, ← star_sub, norm_star]
      exact norm_sqrtNearOne_sub_one_lt hX
    · rw [← star_mul, hWW, hXs]
  have hPX : Commute P X := by
    rw [hXdef]
    exact (Commute.one_right P).sub_right (commute_sub_mul_sub hP hQ)
  have hPW : Commute P W := commute_sqrtNearOne hX hPX
  set Wi := Ring.inverse W with hWidef
  have hWWi : W * Wi = 1 := Ring.mul_inverse_cancel W hWu
  have hWiW : Wi * W = 1 := Ring.inverse_mul_cancel W hWu
  have hWis : star Wi = Wi := by
    calc star Wi = star Wi * (W * Wi) := by rw [hWWi, mul_one]
      _ = (star Wi * star W) * Wi := by rw [hWs, mul_assoc]
      _ = star (W * Wi) * Wi := by rw [star_mul]
      _ = Wi := by rw [hWWi, star_one, one_mul]
  have hPWi : P * Wi = Wi * P := by
    calc P * Wi = Wi * W * P * Wi := by rw [hWiW, one_mul]
      _ = Wi * (P * W) * Wi := by rw [hPW.eq]; simp only [mul_assoc]
      _ = Wi * P * (W * Wi) := by simp only [mul_assoc]
      _ = Wi * P := by rw [hWWi, mul_one]
  have hB : projIntertwiner P Q = T * Wi := rfl
  have hTP : T * P = Q * T := core_mul_eq hP hQ
  have hTT : star T * T = X := by
    rw [hTdef, star_intertwinerCore hPs hQs]
    exact core_star_mul_core hP hQ
  have hTu : IsUnit T := by
    have h : ‖1 - T‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (norm_intertwinerCore_sub_one_le hP hPs) h1
    simpa using isUnit_one_sub_of_norm_lt_one h
  have hWiu : IsUnit Wi := isUnit_iff_exists.mpr ⟨W, hWiW, hWWi⟩
  have hBu : IsUnit (projIntertwiner P Q) := by rw [hB]; exact hTu.mul hWiu
  have hBB : star (projIntertwiner P Q) * projIntertwiner P Q = 1 := by
    rw [hB, star_mul, hWis]
    calc Wi * star T * (T * Wi) = Wi * (star T * T) * Wi := by simp only [mul_assoc]
      _ = Wi * W * (W * Wi) := by rw [hTT, ← hWW]; simp only [mul_assoc]
      _ = 1 := by rw [hWiW, hWWi, one_mul]
  have hBB' : projIntertwiner P Q * star (projIntertwiner P Q) = 1 := by
    obtain ⟨u, hu⟩ := hBu
    have hstar : star (projIntertwiner P Q) = ↑u⁻¹ := by
      calc star (projIntertwiner P Q) = star (projIntertwiner P Q) * (↑u * ↑u⁻¹) := by
            rw [Units.mul_inv, mul_one]
        _ = (star (projIntertwiner P Q) * projIntertwiner P Q) * ↑u⁻¹ := by
            rw [hu, mul_assoc]
        _ = ↑u⁻¹ := by rw [hBB, one_mul]
    rw [hstar, ← hu, Units.mul_inv]
  refine ⟨?_, ?_, ?_, ?_, hBu⟩
  · change projIntertwiner P Q * P = Q * projIntertwiner P Q
    rw [hB, mul_assoc, ← hPWi, ← mul_assoc, hTP, mul_assoc]
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hBB
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hBB'
  · exact norm_apply_eq_of_star_mul_self_eq_one hBB

theorem projIntertwiner_mapsTo (hP : P ∘L P = P) (hPs : P.adjoint = P) (hQ : Q ∘L Q = Q)
    (hQs : Q.adjoint = Q) (h1 : ‖Q - P‖ < 1) (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F))
    {v : F} (hv : P v = v) : Q (projIntertwiner P Q v) = projIntertwiner P Q v := by
  have h := (projIntertwiner_spec hP hPs hQ hQs h1 hη).1
  have h' := congrArg (fun L : F →L[ℝ] F => L v) h
  simp only [ContinuousLinearMap.comp_apply, hv] at h'
  exact h'.symm

theorem exists_projIntertwiner_eq (hP : P ∘L P = P) (hPs : P.adjoint = P) (hQ : Q ∘L Q = Q)
    (hQs : Q.adjoint = Q) (h1 : ‖Q - P‖ < 1) (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F))
    {w : F} (hw : Q w = w) : ∃ v, P v = v ∧ projIntertwiner P Q v = w := by
  obtain ⟨hint, -, hBB', -, -⟩ := projIntertwiner_spec hP hPs hQ hQs h1 hη
  set B := projIntertwiner P Q
  have hadj : P ∘L B.adjoint = B.adjoint ∘L Q := by
    have h := congrArg ContinuousLinearMap.adjoint hint
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hPs, hQs] at h
    exact h
  refine ⟨B.adjoint w, ?_, ?_⟩
  · have h' := congrArg (fun L : F →L[ℝ] F => L w) hadj
    simp only [ContinuousLinearMap.comp_apply, hw] at h'
    exact h'
  · have h' := congrArg (fun L : F →L[ℝ] F => L w) hBB'
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h'

theorem range_eq_map_projIntertwiner (hP : P ∘L P = P) (hPs : P.adjoint = P) (hQ : Q ∘L Q = Q)
    (hQs : Q.adjoint = Q) (h1 : ‖Q - P‖ < 1) (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    LinearMap.range (Q : F →ₗ[ℝ] F) =
      Submodule.map (projIntertwiner P Q : F →ₗ[ℝ] F) (LinearMap.range (P : F →ₗ[ℝ] F)) := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    have hw : Q (Q u) = Q u := by
      change (Q ∘L Q) u = Q u
      rw [hQ]
    obtain ⟨v, hv, hBv⟩ := exists_projIntertwiner_eq hP hPs hQ hQs h1 hη hw
    exact ⟨v, ⟨v, hv⟩, hBv⟩
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    have hPu : P (P u) = P u := by
      change (P ∘L P) u = P u
      rw [hP]
    exact ⟨projIntertwiner P Q (P u),
      projIntertwiner_mapsTo hP hPs hQ hQs h1 hη hPu⟩

theorem finrank_range_eq_of_projIntertwiner (hP : P ∘L P = P) (hPs : P.adjoint = P)
    (hQ : Q ∘L Q = Q) (hQs : Q.adjoint = Q) (h1 : ‖Q - P‖ < 1)
    (hη : ‖Q - P‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    Module.finrank ℝ (LinearMap.range (Q : F →ₗ[ℝ] F)) =
      Module.finrank ℝ (LinearMap.range (P : F →ₗ[ℝ] F)) := by
  have hinj : Function.Injective (projIntertwiner P Q : F →ₗ[ℝ] F) := by
    intro a b hab
    have hn := (projIntertwiner_spec hP hPs hQ hQs h1 hη).2.2.2.1 (a - b)
    have h0 : projIntertwiner P Q (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hab
    rw [h0, norm_zero] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)
  rw [range_eq_map_projIntertwiner hP hPs hQ hQs h1 hη]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

/-- FAMILY form: `B` is jointly `C^∞` in the pair `(P, Q)` near any pair with
`‖Q - P‖² < sqrtRadius` (no projection hypothesis is needed for smoothness). -/
theorem contDiffAt_projIntertwiner {P₀ Q₀ : F →L[ℝ] F}
    (hη : ‖Q₀ - P₀‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    ContDiffAt ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) => projIntertwiner pq.1 pq.2) (P₀, Q₀) := by
  have hX := sub_mul_sub_mem_ball (P := P₀) (Q := Q₀) hη
  have hXc : ContDiff ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) =>
      1 - (pq.2 - pq.1) * (pq.2 - pq.1)) := by
    have hd : ContDiff ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) => pq.2 - pq.1) :=
      contDiff_snd.sub contDiff_fst
    exact contDiff_const.sub (hd.mul hd)
  have hTc : ContDiff ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) => intertwinerCore pq.1 pq.2) := by
    unfold intertwinerCore
    exact (contDiff_snd.mul contDiff_fst).add
      ((contDiff_const.sub contDiff_snd).mul (contDiff_const.sub contDiff_fst))
  have hS : ContDiffAt ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) =>
      sqrtNearOne (F →L[ℝ] F) (1 - (pq.2 - pq.1) * (pq.2 - pq.1))) (P₀, Q₀) :=
    (contDiffAt_sqrtNearOne hX).comp (P₀, Q₀) hXc.contDiffAt
  have hu := isUnit_sqrtNearOne hX
  have hinv : ContDiffAt ℝ ∞ Ring.inverse (sqrtNearOne (F →L[ℝ] F) (1 - (Q₀ - P₀) * (Q₀ - P₀))) := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rwa [IsUnit.unit_spec] at h
  have hI : ContDiffAt ℝ ∞ (fun pq : (F →L[ℝ] F) × (F →L[ℝ] F) =>
      Ring.inverse (sqrtNearOne (F →L[ℝ] F) (1 - (pq.2 - pq.1) * (pq.2 - pq.1)))) (P₀, Q₀) :=
    ContDiffAt.comp (g := Ring.inverse) (x := (P₀, Q₀)) hinv hS
  exact hTc.contDiffAt.mul hI

/-- FAMILY form over a manifold parameter: along `C^n` families `P`, `Q` with `‖Q - P‖²` below
`sqrtRadius`, the intertwiner is `C^n`. -/
theorem _root_.ContMDiffAt.projIntertwiner
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}
    {P Q : M → F →L[ℝ] F} {x : M} (hP : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) n P x)
    (hQ : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) n Q x)
    (hη : ‖Q x - P x‖ ^ 2 < sqrtRadius (F →L[ℝ] F)) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) n (fun y => projIntertwiner (P y) (Q y)) x := by
  have h := (contDiffAt_projIntertwiner hη).of_le (WithTop.coe_le_coe.mpr (le_top : n ≤ ⊤))
  exact ContDiffAt.comp_contMDiffAt (f := fun y => (P y, Q y)) h (hP.prodMk_space hQ)

end DifferentialGeometry.Analysis.ProjectionIntertwiner
