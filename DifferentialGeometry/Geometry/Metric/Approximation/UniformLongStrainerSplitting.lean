import DifferentialGeometry.Geometry.Metric.Approximation.SequentialPrescribedSplitting
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u

theorem exists_prescribed_splitting_parameter {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (o : X)
        (aPlus aMinus : Fin k → X),
      (∀ a b : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
          eVariationOn c univ < ENNReal.ofReal (dist a b + η)) →
      dimH (ball o σ⁻¹) ≤ n →
      (∀ z ∈ ball o σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) →
      (∀ j, dist o (aPlus j) = σ⁻¹) → (∀ j, dist o (aMinus j) = σ⁻¹) →
      (∀ j, Real.pi - σ ≤ comparisonAngleNegCurvature σ
        (dist o (aPlus j)) (dist o (aMinus j)) (dist (aPlus j) (aMinus j))) →
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aPlus l))) →
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aMinus l))) →
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ (z : Z) (F : KleinerLottApprox o
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z)) δ),
          ∀ x : X, (F.toFun x).fst =
            WithLp.toLp 2 (fun j => dist o (aPlus j) - dist x (aPlus j)) := by
  classical
  let Bad (σ : ℝ) (k : ℕ) : Prop :=
    ∃ (X : Type u) (m : MetricSpace X), letI := m
      ∃ (_ : CompleteSpace X) (o : X) (aPlus aMinus : Fin k → X),
      (∀ a b : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
          eVariationOn c univ < ENNReal.ofReal (dist a b + η)) ∧
      dimH (ball o σ⁻¹) ≤ n ∧
      (∀ z ∈ ball o σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) ∧
      (∀ j, dist o (aPlus j) = σ⁻¹) ∧ (∀ j, dist o (aMinus j) = σ⁻¹) ∧
      (∀ j, Real.pi - σ ≤ comparisonAngleNegCurvature σ
        (dist o (aPlus j)) (dist o (aMinus j)) (dist (aPlus j) (aMinus j))) ∧
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aPlus l))) ∧
      (∀ j l, j ≠ l → Real.pi / 2 - σ ≤
        comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ (dist (aPlus j) (aMinus l))) ∧
      ¬ ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : KleinerLottApprox o
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z)) δ),
          ∀ x : X, (F.toFun x).fst =
            WithLp.toLp 2 (fun j => dist o (aPlus j) - dist x (aPlus j))
  by_contra hnone
  have hbad (σ : ℝ) (hσ : 0 < σ) (hσone : σ < 1) :
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ Bad σ k := by
    by_contra hb
    apply hnone
    refine ⟨σ, hσ, hσone, ?_⟩
    intro k hk hkn X m hcomplete o aPlus aMinus hcurves hdim hlocal hp hm hopp hcp hcm
    by_contra hfail
    apply hb
    exact ⟨k, hk, hkn, X, m, hcomplete, o, aPlus, aMinus,
      hcurves, hdim, hlocal, hp, hm, hopp, hcp, hcm, hfail⟩
  let σ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  have hσpos (i : ℕ) : 0 < σ i := by dsimp [σ]; positivity
  have hσone (i : ℕ) : σ i < 1 := by
    dsimp [σ]
    exact (div_lt_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hσzero : Tendsto σ atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [σ, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  choose k _hk hkn hb using fun i => hbad (σ i) (hσpos i) (hσone i)
  let rank (i : ℕ) : Fin (n + 1) := ⟨k i, Nat.lt_succ_iff.mpr (hkn i)⟩
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber rank
  have hinfinite : (rank ⁻¹' {r}).Infinite := Set.infinite_coe_iff.mp hr
  obtain ⟨φ, hφ, hφrank⟩ := Nat.exists_strictMono_subsequence (P := fun i => rank i = r) (by
    intro N
    obtain ⟨i, hi, hNi⟩ := hinfinite.exists_gt N
    exact ⟨i, hNi, hi⟩)
  have hkr (i : ℕ) : k (φ i) = r.val := congrArg Fin.val (hφrank i)
  have hb' (i : ℕ) : Bad (σ (φ i)) r.val := by
    simpa only [hkr i] using hb (φ i)
  choose X m hcomplete o aPlus aMinus hcurves hdim hlocal hp hm hopp hcp hcm hfail using hb'
  let : ∀ i, MetricSpace (X i) := m
  let : ∀ i, CompleteSpace (X i) := hcomplete
  obtain ⟨χ, _hχ, Z, mZ, z, _hproper, _hZcomplete, _hcomp, _hsegments, happrox⟩ :=
    exists_subsequence_prescribed_kleinerLott_approximations_of_reciprocal_local_geometry
      o hn hcurves hdim hlocal aPlus aMinus
      (fun i => hσpos (φ i)) (hσzero.comp hφ.tendsto_atTop) hp hm
      (fun j => Eventually.of_forall fun i => hopp i j)
      (fun j l hjl => Eventually.of_forall fun i => hcp i j l hjl)
      (fun j l hjl => Eventually.of_forall fun i => hcm i j l hjl)
  let := mZ
  obtain ⟨i, hi⟩ := (happrox δ hδ hδone).exists
  exact hfail (χ i) ⟨Z, mZ, z, hi⟩

end GC.MetricGeometry
