import DifferentialGeometry.Analysis.Sobolev.Nirenberg.Euclidean

/-!
# Smooth-test pairing functional for the duality identification of weak
partial derivatives

This module supplies the auxiliary integrability lemma and the
linear-in-test-function smooth-test pairing functional

  `smoothTestPairing Ω w k φ := -∫_Ω w · ∂_k φ`,

defined for `w ∈ L²(Ω)` and `φ` smooth compactly supported. This is the
candidate weak-partial pairing in the Riesz / duality argument: a
uniform `L²` bound on the difference quotients `D_h^k w` translates to a
uniform bound on `smoothTestPairing Ω w k φ` in terms of `‖φ‖_{L²}`,
the Cauchy–Schwarz / discrete-integration-by-parts route to
identifying a weak partial derivative.

## Main definitions and results

* `smoothTestPairing Ω w k φ`: the smooth-test linear functional
  `Λ_w(φ) := -∫_Ω w · ∂_k φ`.
* `integrable_w_partial_phi`: the integrand `w · ∂_k φ` is integrable on
  `Ω` for `w ∈ L²(Ω)` and `φ` smooth compactly supported.
* `smoothTestPairing_add`, `smoothTestPairing_smul`: linearity of the
  smooth-test pairing in the test argument.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
/-- For a smooth compactly supported `φ : E → ℝ` and `w : E → ℝ` in
`L²(volume.restrict Ω)`, the integrand `w · ∂_k φ` is integrable on `Ω`. -/
theorem integrable_w_partial_phi
    {Ω : Set E} {w : E → ℝ} (hw_l2 : MemLp w 2 (volume.restrict Ω))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (k : Fin d) :
    Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))
      (volume.restrict Ω) := by
  have h_partial_cont : Continuous
      (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have h_partial_supp :
      HasCompactSupport (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have h_partial_memLp :
      MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) 2
        (volume.restrict Ω) :=
    (h_partial_cont.memLp_of_hasCompactSupport h_partial_supp).restrict _
  exact MemLp.integrable_mul hw_l2 h_partial_memLp

omit [NeZero d] in
/-- The smooth-test pairing `Λ_w(φ) := -∫_Ω w · ∂_k φ`, for `w : E → ℝ` and
`φ` smooth compactly supported. The integrability hypothesis on `w` is not
imposed at the definition level so that the symbol can be applied to any
`w` of the appropriate type, with the relevant integrability lemma supplied
where needed (see `integrable_w_partial_phi`). -/
def smoothTestPairing
    (Ω : Set E) (w : E → ℝ) (k : Fin d) (φ : E → ℝ) : ℝ :=
  -∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)

omit [NeZero d] in
/-- The smooth-test pairing is additive in the test function. -/
theorem smoothTestPairing_add
    {Ω : Set E} {w : E → ℝ} (hw_l2 : MemLp w 2 (volume.restrict Ω))
    {k : Fin d} {φ ψ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_supp : HasCompactSupport ψ) :
    smoothTestPairing Ω w k (φ + ψ) =
      smoothTestPairing Ω w k φ + smoothTestPairing Ω w k ψ := by
  unfold smoothTestPairing
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have h_fderiv_sum : ∀ x : E,
      (fderiv ℝ (φ + ψ) x) (EuclideanSpace.single k 1) =
        (fderiv ℝ φ x) (EuclideanSpace.single k 1) +
          (fderiv ℝ ψ x) (EuclideanSpace.single k 1) := by
    intro x
    rw [show φ + ψ = (fun y => φ y + ψ y) from rfl]
    rw [fderiv_fun_add (hφ_diff.differentiableAt) (hψ_diff.differentiableAt)]
    simp
  have h_int_sum : ∀ x : E,
      w x * (fderiv ℝ (φ + ψ) x) (EuclideanSpace.single k 1) =
        w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) +
          w x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) := by
    intro x; rw [h_fderiv_sum x]; ring
  have h_int_eq :
      ∫ x in Ω, w x * (fderiv ℝ (φ + ψ) x) (EuclideanSpace.single k 1) =
        (∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)) +
          ∫ x in Ω, w x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) := by
    have hφ_int := integrable_w_partial_phi hw_l2 hφ hφ_supp k
    have hψ_int := integrable_w_partial_phi hw_l2 hψ hψ_supp k
    rw [show (fun x => w x * (fderiv ℝ (φ + ψ) x) (EuclideanSpace.single k 1)) =
      (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) +
        w x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1)) from by ext x; exact h_int_sum x]
    rw [integral_add hφ_int hψ_int]
  rw [h_int_eq]; ring

omit [NeZero d] in
/-- The smooth-test pairing is homogeneous in the test function. -/
theorem smoothTestPairing_smul
    {Ω : Set E} (w : E → ℝ) (k : Fin d) (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    smoothTestPairing Ω w k (c • φ) = c * smoothTestPairing Ω w k φ := by
  unfold smoothTestPairing
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h_fderiv_smul : ∀ x : E,
      (fderiv ℝ (c • φ) x) (EuclideanSpace.single k 1) =
        c * (fderiv ℝ φ x) (EuclideanSpace.single k 1) := by
    intro x
    have heq : (c • φ : E → ℝ) = fun y => c * φ y := by
      ext y; rfl
    rw [heq]
    rw [fderiv_const_mul (hφ_diff.differentiableAt) c]
    simp
  have h_int_smul : ∀ x : E,
      w x * (fderiv ℝ (c • φ) x) (EuclideanSpace.single k 1) =
        c * (w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)) := by
    intro x; rw [h_fderiv_smul x]; ring
  have h_int_eq :
      ∫ x in Ω, w x * (fderiv ℝ (c • φ) x) (EuclideanSpace.single k 1) =
        c * ∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) := by
    rw [show (fun x => w x * (fderiv ℝ (c • φ) x) (EuclideanSpace.single k 1)) =
      (fun x => c * (w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))) from by
        ext x; exact h_int_smul x]
    exact integral_const_mul _ _
  rw [h_int_eq]; ring

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
