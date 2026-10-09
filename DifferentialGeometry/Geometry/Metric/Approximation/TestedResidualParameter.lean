import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalModels
import DifferentialGeometry.Geometry.Metric.Approximation.VanishingProductResidual

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w

theorem exists_tested_residual_parameter_of_nonnegative_models {n : ℕ} (hn : 1 ≤ n)
    (S r : ℝ) (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ n → fourPointComparison 0 (univ : Set C) →
      ∀ (A : Type w) [MetricSpace A] (a : A) (σ β : ℝ), σ ≤ η → β ≤ η →
        KleinerLottApprox z c σ →
        ∀ F : KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), a)) β,
          ∀ x : Z, dist x z ≤ S → dist (F.toFun x).snd a < r := by
  classical
  let Bad (η : ℝ) : Prop :=
    ∃ (Z : Type u) (mZ : MetricSpace Z), letI := mZ
      ∃ (z : Z) (C : Type v) (mC : MetricSpace C), letI := mC
        ∃ (_ : CompleteSpace C) (c : C) (A : Type w) (mA : MetricSpace A), letI := mA
          ∃ (a : A) (σ β : ℝ)
            (_ : KleinerLottApprox z c σ)
            (F : KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin n)), a)) β),
            σ ≤ η ∧ β ≤ η ∧
            (∀ x y : C, ∀ e : ℝ, 0 < e →
              ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
                eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) ∧
            dimH (univ : Set C) ≤ n ∧ fourPointComparison 0 (univ : Set C) ∧
            ∃ x : Z, dist x z ≤ S ∧ ¬ dist (F.toFun x).snd a < r
  by_contra hnone
  have hbad (η : ℝ) (hη : 0 < η) (hηsmall : η < 1 / 10) : Bad η := by
    by_contra hb
    apply hnone
    refine ⟨η, hη, hηsmall, ?_⟩
    intro Z mZ z C mC hc c hcurves hdim hcomp A mA a σ β hσ hβ f φ x hx
    by_contra hfail
    exact hb ⟨Z, mZ, z, C, mC, hc, c, A, mA, a, σ, β, f, φ,
      hσ, hβ, hcurves, hdim, hcomp, x, hx, hfail⟩
  let η : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 20)
  have hηpos (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hηsmall (i : ℕ) : η i < 1 / 10 := by
    dsimp [η]
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hηzero : Tendsto η atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 20) atTop atTop :=
      tendsto_atTop_add_const_right atTop (20 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [η, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  choose Z mZ z C mC hc c A mA a σ β f φ hση hβη hcurves hdim hcomp x hx hfail using
    fun i => hbad (η i) (hηpos i) (hηsmall i)
  let : ∀ i, MetricSpace (Z i) := mZ
  let : ∀ i, MetricSpace (C i) := mC
  let : ∀ i, CompleteSpace (C i) := hc
  let : ∀ i, MetricSpace (A i) := mA
  have hσzero : Tendsto σ atTop (𝓝 0) := squeeze_zero (fun i => (f i).error_pos.le) hση hηzero
  have hβzero : Tendsto β atTop (𝓝 0) := squeeze_zero (fun i => (φ i).error_pos.le) hβη hηzero
  obtain ⟨Y, mY, q, α, hα, hcY, hpY, _, hzconv, hdimY, hcompY, hsegY⟩ :=
    exists_common_pointed_limit_of_nonnegative_models c z hn hcurves hdim hcomp f hσzero
  let := mY
  let := hcY
  let := hpY
  obtain ⟨ψ, _, hsmall⟩ := hzconv.exists_subsequence_with_vanishing_tested_residual hn
    (fun i => φ (α i)) (hβzero.comp hα.tendsto_atTop) hsegY hcompY hdimY
  obtain ⟨i, hi⟩ := (hsmall S r hr).exists
  exact hfail (α (ψ i)) (hi (x (α (ψ i))) (hx (α (ψ i))))

end GC.MetricGeometry
