import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness.MetricIsometry

open Filter Topology
open scoped ContDiff

variable {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace Real E0]

private noncomputable local instance finiteMetricBilinearNormedGroup :
    NormedAddCommGroup (E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance finiteMetricBilinearNormedSpace :
    NormedSpace Real (E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

open private isom_next_le isomEnvelope isomBudget isomBudget_le_of_le
  one_le_isomEnv isomBudget_succ postBilin preBilin raisedKoszulOp isom_second_on from
  DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds

section
variable [ContinuousDualEquiv E0] [CoerciveBilinInverse E0]

private theorem isom_deriv_le_finite
    [CompleteSpace E0]
    (N : Nat)
    (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (x : E0) (D : Real)
    (hBsm : ContDiffAt Real (N : WithTop ℕ∞) B x)
    (hCsm : ContDiffAt Real (N : WithTop ℕ∞) C (Phi x))
    (hPhi : ContDiffAt Real ((N + 1 : Nat) : WithTop ℕ∞) Phi x)
    (hBupper : ∀ q : E0, B x q q ≤ 2 * ‖q‖ ^ 2)
    (hmetric : ∀ q : E0,
      C (Phi x) (fderiv Real Phi x q) (fderiv Real Phi x q) = B x q q)
    (hBlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hClower : ∀ᶠ y in nhds (Phi x), ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q)
    (heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
      postBilin (fderiv Real Phi y)
          (raisedKoszulOp (B y) (fderiv Real B y)) -
        preBilin
          (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
          (fderiv Real Phi y))
    (hDB : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv Real i B x‖ ≤ D ^ i)
    (hDC : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv Real i C (Phi x)‖ ≤ D ^ i) :
    ∀ r, 1 ≤ r → r ≤ N + 1 →
      ‖iteratedFDeriv Real r Phi x‖ ≤ isomBudget (E0 := E0) D r := by
  intro r
  refine Nat.strong_induction_on r ?_
  intro r ih hr hrN
  rcases r with _ | n
  · omega
  rcases n with _ | m
  · change ‖iteratedFDeriv Real 1 Phi x‖ ≤ 2
    exact isom_first_bound (B x) (C (Phi x)) Phi x hBupper
      hClower.self_of_nhds hmetric
  · let P := isomEnvelope (E0 := E0) D (Nat.succ m)
    have hPjets : ∀ i, 1 ≤ i → i ≤ m + 1 →
        ‖iteratedFDeriv Real i Phi x‖ ≤ P ^ i := by
      intro i hi him
      have hprev := ih i (by omega) hi (by omega)
      have htoP : ‖iteratedFDeriv Real i Phi x‖ ≤ P :=
        hprev.trans (by simpa only [P] using
          isomBudget_le_of_le (E0 := E0) D (show i ≤ Nat.succ m by omega))
      exact htoP.trans
        (le_self_pow₀ (one_le_isomEnv (E0 := E0) D (Nat.succ m)) (by omega))
    have hstep := isom_next_le B C Phi x m D P
      (hBsm.of_le (by exact_mod_cast (show m + 1 ≤ N by omega)))
      (hCsm.of_le (by exact_mod_cast (show m + 1 ≤ N by omega)))
      (hPhi.of_le (by exact_mod_cast (show m + 2 ≤ N + 1 by omega)))
      hBlower hClower
      (fun i hi him => hDB i hi (by omega))
      (fun i hi him => hDC i hi (by omega)) hPjets heq
    simpa only [P, isomBudget_succ, Nat.succ_eq_add_one] using hstep

end

theorem exists_isometry_jet_bound_of_finite_metric_bounds
    [FiniteDimensional Real E0]
    (N : Nat) (D : Real) :
    ∃ M : Real, ∀ (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
      (Phi : E0 → E0) (U V : Set E0),
      IsOpen U → IsOpen V →
      ContDiffOn Real (N : WithTop ℕ∞) B U →
      ContDiffOn Real (N : WithTop ℕ∞) C V →
      ContDiffOn Real ((N + 1 : Nat) : WithTop ℕ∞) Phi U →
      Set.MapsTo Phi U V →
      (∀ x ∈ U, ∀ u v : E0,
        B x u v = C (Phi x) (fderiv Real Phi x u) (fderiv Real Phi x v)) →
      (∀ y ∈ V, ∀ a b : E0, C y a b = C y b a) →
      (∀ x ∈ U, ∀ q : E0,
        (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B x q q ∧ B x q q ≤ 2 * ‖q‖ ^ 2) →
      (∀ y ∈ V, ∀ q : E0,
        (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q) →
      (∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) →
      (∀ i, 1 ≤ i → i ≤ N → ∀ y ∈ V,
        ‖iteratedFDeriv Real i C y‖ ≤ D ^ i) →
      ∀ r, 1 ≤ r → r ≤ N + 1 → ∀ x ∈ U,
        ‖iteratedFDeriv Real r Phi x‖ ≤ M := by
  refine ⟨isomEnvelope (E0 := E0) D (N + 1), ?_⟩
  intro B C Phi U V hU hV hBsm hCsm hPhi hmap hiso hCsymm hBequiv hClower hDB hDC r hr hrN x hx
  have hPhiV : Phi x ∈ V := hmap hx
  by_cases hN : 1 ≤ N
  · have hB1 : ContDiffOn Real 1 B U := hBsm.of_le (by exact_mod_cast hN)
    have hC1 : ContDiffOn Real 1 C V := hCsm.of_le (by exact_mod_cast hN)
    have hPhi2 : ContDiffOn Real 2 Phi U := hPhi.of_le (by exact_mod_cast (show 2 ≤ N + 1 by omega))
    have hsecond := isom_second_on B C Phi U V hU hV hB1 hC1 hPhi2
      hmap hiso hCsymm (fun y hy q => (hBequiv y hy q).1)
        hClower
    have heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
        postBilin (fderiv Real Phi y)
            (raisedKoszulOp (B y) (fderiv Real B y)) -
          preBilin
            (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
            (fderiv Real Phi y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hsecond y hy
    have hbound := isom_deriv_le_finite N B C Phi x D
      ((hBsm x hx).contDiffAt (hU.mem_nhds hx))
      ((hCsm (Phi x) hPhiV).contDiffAt (hV.mem_nhds hPhiV))
      ((hPhi x hx).contDiffAt (hU.mem_nhds hx))
      (fun q => (hBequiv x hx q).2)
      (fun q => (hiso x hx q q).symm)
      (by filter_upwards [hU.mem_nhds hx] with y hy q; exact (hBequiv y hy q).1)
      (by filter_upwards [hV.mem_nhds hPhiV] with y hy q; exact hClower y hy q)
      heq (fun i hi hiN => hDB i hi hiN x hx)
        (fun i hi hiN => hDC i hi hiN (Phi x) hPhiV) r hr hrN
    exact hbound.trans (isomBudget_le_of_le (E0 := E0) D hrN)
  · have hrone : r = 1 := by omega
    subst r
    have hfirst := isom_first_bound (B x) (C (Phi x)) Phi x
      (fun q => (hBequiv x hx q).2) (hClower (Phi x) hPhiV)
      (fun q => (hiso x hx q q).symm)
    exact hfirst.trans (isomBudget_le_of_le (E0 := E0) D (show 1 ≤ N + 1 by omega))

end DifferentialGeometry.CheegerGromovCompactness.MetricIsometry
