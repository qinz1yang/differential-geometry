import DifferentialGeometry.Geometry.Metric.Approximation.ExactLimitApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.PointedFullProductLimits
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingCompatibilityTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Comparison.ExactSplittingCompatibility

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

theorem exists_splitting_compatibility_parameter {j k n : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n)
    {τ ν : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (X : Type u) [MetricSpace X] [CompleteSpace X] (p : X),
      (∀ x y : X, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
          eVariationOn c univ < ENNReal.ofReal (dist x y + η)) →
      dimH (ball p σ⁻¹) ≤ n →
      (∀ z ∈ ball p σ⁻¹, ∃ Ω : Set X,
        IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a : A) (b : B)
        (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) σ)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) σ),
        SplittingCompatible φ ψ τ := by
  classical
  let Bad (σ : ℝ) : Prop :=
    ∃ (X : Type u) (m : MetricSpace X), letI := m
      ∃ (_ : CompleteSpace X) (p : X)
        (A : Type u) (mA : MetricSpace A), letI := mA
        ∃ (B : Type u) (mB : MetricSpace B), letI := mB
          ∃ (a : A) (b : B)
            (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) σ)
            (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) σ),
            (∀ x y : X, ∀ η : ℝ, 0 < η →
              ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
                eVariationOn c univ < ENNReal.ofReal (dist x y + η)) ∧
            dimH (ball p σ⁻¹) ≤ n ∧
            (∀ z ∈ ball p σ⁻¹, ∃ Ω : Set X,
              IsOpen Ω ∧ fourPointComparison σ Ω ∧ z ∈ Ω) ∧
            (¬ ∃ (W : Type u) (mW : MetricSpace W), letI := mW
              ∃ w : W, Nonempty (KleinerLottApprox p
                (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) ∧
            ¬ SplittingCompatible φ ψ τ
  by_contra hnone
  have hbad (σ : ℝ) (hσ : 0 < σ) (hσone : σ < 1) : Bad σ := by
    by_contra hb
    apply hnone
    refine ⟨σ, hσ, hσone, ?_⟩
    intro X m hcomplete p hcurves hdim hlocal hno A B mA mB a b φ ψ
    by_contra hfail
    apply hb
    exact ⟨X, m, hcomplete, p, A, mA, B, mB, a, b, φ, ψ,
      hcurves, hdim, hlocal, hno, hfail⟩
  let σ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  have hσpos (i : ℕ) : 0 < σ i := by dsimp [σ]; positivity
  have hσone (i : ℕ) : σ i < 1 := by
    dsimp [σ]
    exact (div_lt_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hσzero : Tendsto σ atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [σ, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσzero, Eventually.of_forall hσpos⟩
  have hR : Tendsto (fun i => (σ i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hwithin
  choose X m hcomplete p A mA B mB a b Φ Ψ hcurves hdim hlocal hno hfail using
    fun i => hbad (σ i) (hσpos i) (hσone i)
  let : ∀ i, MetricSpace (X i) := m
  let : ∀ i, CompleteSpace (X i) := hcomplete
  let : ∀ i, MetricSpace (A i) := mA
  let : ∀ i, MetricSpace (B i) := mB
  obtain ⟨Y, mY, q, α, hα, hYcomplete, hYproper, hpointed, _hdimY, hYcomp,
      hYsegments, _hside, _hnets⟩ :=
    exists_pointed_limit_of_growing_local_geometry p ((hj.trans hjk).trans hkn)
      hcurves (fun i => (hσpos i).le) hσzero hR hdim hlocal
  let := mY
  let := hYcomplete
  let := hYproper
  have hmax := hpointed.not_exists_small_product_isometry_of_frequently_no_kleinerLott
    (0 : EuclideanSpace ℝ (Fin (k + 1))) hν hνone
    (Frequently.of_forall (fun i => hno (α i)))
  obtain ⟨W, mW, V, mV, w, v, χ, hχ, _hpW, _hcW, _hpV, _hcV,
      _hAconv, _hBconv, _hsubconv, eA, eB, heA, heB,
      R, ε, P, η, L, ζ, _hR, _hε, hP, hη, hL, hζ, f, g, h, hcontrol⟩ :=
    hpointed.exists_two_full_product_limits
      (fun i => Φ (α i)) (hσzero.comp hα.tendsto_atTop)
      (fun i => Ψ (α i)) (hσzero.comp hα.tendsto_atTop)
  let := mW
  let := mV
  obtain ⟨Q, H, hH, hfactor⟩ := exists_exact_compatibility_of_maximal_splitting
    hYcomp hjk hYsegments eA eB heA heB hmax
  have hgood := eventually_splittingCompatible_of_full_product_convergence
    (fun i => Φ (α (χ i))) (fun i => Ψ (α (χ i)))
    (hσzero.comp (hα.comp hχ).tendsto_atTop) (hσzero.comp (hα.comp hχ).tendsto_atTop)
    f g h hP hη hL hζ eA eB hcontrol Q H hH hfactor hτ hτone hjk
  obtain ⟨i, hi⟩ := hgood.exists
  exact hfail (α (χ i)) hi

end GC.MetricGeometry
