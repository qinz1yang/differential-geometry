import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import Mathlib.Order.Filter.Finite

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter

private theorem eventually_forall_le_of_forall_eventually
    {P : ℕ → ℕ → Prop} (h : ∀ n : ℕ, ∀ᶠ k in atTop, P n k) :
    ∀ m : ℕ, ∀ᶠ k in atTop, ∀ n ≤ m, P n k := by
  intro m
  have h1 : ∀ᶠ k in atTop, ∀ n ∈ Finset.range (m + 1), P n k := by
    rw [eventually_all_finset]
    intro n _hn
    exact h n
  exact h1.mono fun k hk n hn => hk n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem exists_strictMono_forall_le_of_forall_eventually
    {P : ℕ → ℕ → Prop} (h : ∀ n : ℕ, ∀ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n m : ℕ, n ≤ m → P n (φ m) := by
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_eventually'
    (P := fun m k => ∀ n ≤ m, P n k)
    (fun m => (eventually_forall_le_of_forall_eventually h m).exists_forall_of_atTop)
  exact ⟨φ, hφ, fun n m hnm => hP m n hnm⟩

theorem exists_strictMono_forall_le_of_forall_ge
    {P : ℕ → ℕ → Prop} (h : ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n m : ℕ, n ≤ m → P n (φ m) :=
  exists_strictMono_forall_le_of_forall_eventually fun n => eventually_atTop.2 (h n)

theorem exists_strictMono_forall_le_cons_of_forall_eventually
    {Q : ℕ → Prop} {P : ℕ → ℕ → Prop}
    (hQ : ∀ᶠ k in atTop, Q k) (hP : ∀ n : ℕ, ∀ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ m : ℕ, Q (φ m)) ∧
      ∀ n m : ℕ, n ≤ m → P n (φ m) := by
  have hP' : ∀ m : ℕ, ∀ᶠ k in atTop, (∀ n ≤ m, P n k) ∧ Q k :=
    fun m => (eventually_forall_le_of_forall_eventually hP m).and hQ
  obtain ⟨φ, hφ, h⟩ := exists_strictMono_forall_le_of_forall_eventually hP'
  exact ⟨φ, hφ, fun m => (h 0 m (Nat.zero_le m)).2, fun n m hnm => (h n m hnm).1 n le_rfl⟩

open Bundle Set Manifold Metric
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_subsequence_curvDerivNorm_ball_le_of_local_jets_and_eventually
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    {Q : ℕ → Prop} (hQ : ∀ᶠ k in atTop, Q k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ m : ℕ, Q (φ m)) ∧
      ∃ C : ℕ → ℕ → ℝ, (∀ n p : ℕ, 0 ≤ C n p) ∧
        ∀ n p j : ℕ, n + p ≤ j →
          letI : TopologicalSpace (X.obj (φ j)).M := (X.obj (φ j)).topology
          letI : ChartedSpace H (X.obj (φ j)).M := (X.obj (φ j)).charted
          letI : IsManifold I ∞ (X.obj (φ j)).M := (X.obj (φ j)).smooth
          letI : T2Space (X.obj (φ j)).M := (X.obj (φ j)).t2
          letI : SigmaCompactSpace (X.obj (φ j)).M := (X.obj (φ j)).sigmaCompact
          ∀ x : (X.obj (φ j)).M,
            riemannianEDistOf (I := I) (X.obj (φ j)).metric (X.obj (φ j)).basepoint x ≤
              ENNReal.ofReal (n : ℝ) →
            curvDerivNorm (I := I) p (X.obj (φ j)).metric x ≤ C n p := by
  classical
  let C : ℕ → ℕ → ℝ := fun n p =>
    Classical.choose (hjets ((n : ℝ) + 1) (by positivity) p)
  have hC0 : ∀ n p : ℕ, 0 ≤ C n p := fun n p =>
    (Classical.choose_spec (hjets ((n : ℝ) + 1) (by positivity) p)).1
  have hCev : ∀ n p : ℕ, ∀ᶠ j in atTop,
      let _ : TopologicalSpace (X.obj j).M := (X.obj j).topology
      let _ : ChartedSpace H (X.obj j).M := (X.obj j).charted
      let _ : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      let _ : T2Space (X.obj j).M := (X.obj j).t2
      let _ : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
      ∀ x : (X.obj j).M,
        riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
          ENNReal.ofReal ((n : ℝ) + 1) →
            curvDerivNorm (I := I) p (X.obj j).metric x ≤ C n p :=
    fun n p => (Classical.choose_spec (hjets ((n : ℝ) + 1) (by positivity) p)).2
  let B : ℕ → ℕ → ℕ → Prop := fun n p j =>
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (X.obj j).M := (X.obj j).t2
    letI : SigmaCompactSpace (X.obj j).M := (X.obj j).sigmaCompact
    ∀ x : (X.obj j).M,
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
        ENNReal.ofReal (n : ℝ) → curvDerivNorm (I := I) p (X.obj j).metric x ≤ C n p
  have hB : ∀ n p : ℕ, ∀ᶠ j in atTop, B n p j := by
    intro n p
    refine (hCev n p).mono fun j hj x hx => ?_
    exact hj x (hx.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hP : ∀ m : ℕ, ∀ᶠ j in atTop, (∀ n p : ℕ, n + p ≤ m → B n p j) ∧ Q j := by
    intro m
    have h1 : ∀ᶠ j in atTop,
        ∀ np ∈ (Finset.range (m + 1)).product (Finset.range (m + 1)), B np.1 np.2 j := by
      rw [eventually_all_finset]
      intro np _
      exact hB np.1 np.2
    refine (h1.mono fun j hj n p hnp => ?_).and hQ
    exact hj (n, p) (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.le_add_right n p) hnp)),
       Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.le_add_left p n) hnp))⟩)
  obtain ⟨φ, hφ, h⟩ := exists_strictMono_forall_le_of_forall_eventually hP
  exact ⟨φ, hφ, fun m => (h 0 m (Nat.zero_le m)).2, C, hC0,
    fun n p j hnpj => (h (n + p) j hnpj).1 n p le_rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_subsequence_curvDerivNorm_ball_le_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ C : ℕ → ℕ → ℝ, (∀ n p : ℕ, 0 ≤ C n p) ∧
        ∀ n p j : ℕ, n + p ≤ j →
          letI : TopologicalSpace (X.obj (φ j)).M := (X.obj (φ j)).topology
          letI : ChartedSpace H (X.obj (φ j)).M := (X.obj (φ j)).charted
          letI : IsManifold I ∞ (X.obj (φ j)).M := (X.obj (φ j)).smooth
          letI : T2Space (X.obj (φ j)).M := (X.obj (φ j)).t2
          letI : SigmaCompactSpace (X.obj (φ j)).M := (X.obj (φ j)).sigmaCompact
          ∀ x : (X.obj (φ j)).M,
            riemannianEDistOf (I := I) (X.obj (φ j)).metric (X.obj (φ j)).basepoint x ≤
              ENNReal.ofReal (n : ℝ) →
            curvDerivNorm (I := I) p (X.obj (φ j)).metric x ≤ C n p := by
  obtain ⟨φ, hφ, _hT, C, hC0, hC⟩ :=
    exists_subsequence_curvDerivNorm_ball_le_of_local_jets_and_eventually X hjets
      (Q := fun _ => True) (Filter.Eventually.of_forall fun _ => trivial)
  exact ⟨φ, hφ, C, hC0, hC⟩

end CheegerGromovCompactness
end DifferentialGeometry
