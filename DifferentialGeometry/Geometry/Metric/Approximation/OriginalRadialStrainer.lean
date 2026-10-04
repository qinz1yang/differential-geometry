import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialCompactness

/-!
# A uniform splitting parameter with the original radial coordinate

Compactness of growing local geometries turns calibrated opposite prefixes into a uniform
parameter. The prescribed first coordinate is the original centered distance at every point.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u

theorem exists_original_radial_strainer_parameter {n : ℕ} (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (o p aPlus aMinus : X),
      (∀ a b : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
          eVariationOn c univ < ENNReal.ofReal (dist a b + η)) →
      dimH (ball o σ⁻¹) ≤ n →
      (∀ z ∈ ball o σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) →
      dist o aPlus = σ⁻¹ → dist o aMinus = σ⁻¹ →
      (Real.pi - σ ≤ comparisonAngleNegCurvature σ
        (dist o aPlus) (dist o aMinus) (dist aPlus aMinus)) →
      (∀ w, dist o w + dist w aPlus = dist o aPlus →
        dist o w - σ * dist o w ≤ dist p w - dist p o) →
      dist o aMinus + dist aMinus p = dist o p →
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : KleinerLottApprox o
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) β),
          ∀ x : X, (F.toFun x).fst =
            WithLp.toLp 2 (Function.const (Fin 1) (dist p x - dist p o)) := by
  classical
  let Bad (σ : ℝ) : Prop :=
    ∃ (X : Type u) (m : MetricSpace X), letI := m
      ∃ hcomplete : CompleteSpace X, letI := hcomplete
      ∃ o p aPlus aMinus : X,
      (∀ a b : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
          eVariationOn c univ < ENNReal.ofReal (dist a b + η)) ∧
      dimH (ball o σ⁻¹) ≤ n ∧
      (∀ z ∈ ball o σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) ∧
      dist o aPlus = σ⁻¹ ∧ dist o aMinus = σ⁻¹ ∧
      (Real.pi - σ ≤ comparisonAngleNegCurvature σ
        (dist o aPlus) (dist o aMinus) (dist aPlus aMinus)) ∧
      (∀ w, dist o w + dist w aPlus = dist o aPlus →
        dist o w - σ * dist o w ≤ dist p w - dist p o) ∧
      dist o aMinus + dist aMinus p = dist o p ∧
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : KleinerLottApprox o
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) β),
          ∀ x : X, (F.toFun x).fst =
            WithLp.toLp 2 (Function.const (Fin 1) (dist p x - dist p o)))
  by_contra hnone
  have hbad (σ : ℝ) (hσ : 0 < σ) (hσone : σ < 1) : Bad σ := by
    by_contra hb
    apply hnone
    refine ⟨σ, hσ, hσone, ?_⟩
    intro X m hcomplete o p aPlus aMinus hcurves hdim hlocal hp hm hopp hrad hinward
    by_contra hfail
    exact hb ⟨X, m, hcomplete, o, p, aPlus, aMinus,
      hcurves, hdim, hlocal, hp, hm, hopp, hrad, hinward, hfail⟩
  let σ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  have hσpos (i : ℕ) : 0 < σ i := by dsimp [σ]; positivity
  have hσone (i : ℕ) : σ i < 1 := by
    dsimp [σ]
    exact (div_lt_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hσzero : Tendsto σ atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [σ, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  choose X m hcomplete o p aPlus aMinus hcurves hdim hlocal hp hm hopp hrad hinward hfail
    using fun i => hbad (σ i) (hσpos i) (hσone i)
  let : ∀ i, MetricSpace (X i) := m
  let : ∀ i, CompleteSpace (X i) := hcomplete
  obtain ⟨χ, hχ, Z, mZ, z, happrox⟩ := exists_subsequence_original_radial_splittings
    o p aPlus aMinus hn hcurves hdim hlocal hσpos hσzero hp hm hopp hrad hinward
  let := mZ
  obtain ⟨i, hi⟩ := (happrox β hβ hβone).exists
  exact hfail (χ i) ⟨Z, mZ, z, hi⟩

end GC.MetricGeometry
