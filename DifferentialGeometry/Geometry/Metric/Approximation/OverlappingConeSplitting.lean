import DifferentialGeometry.Geometry.Metric.Approximation.VaryingKleinerLottConvergence
import DifferentialGeometry.Geometry.Comparison.TwoConeSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeConeCompactness
import DifferentialGeometry.Geometry.Metric.Approximation.ExactLimitApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.MovingPointedLimit

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v w

theorem exists_overlapping_cone_splitting_parameter {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (Z : Type u) [MetricSpace Z] (C : Type v) [MetricSpace C] [CompleteSpace C]
        (D : Type w) [MetricSpace D] (p q : Z) (o : C) (v : D),
      dist p q = 1 →
      (∀ x y : C, ∀ η : ℝ, 0 < η →
        ∃ c : unitInterval → C, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
          eVariationOn c univ < ENNReal.ofReal (dist x y + η)) →
      dimH (univ : Set C) ≤ n → fourPointComparison 0 (univ : Set C) →
      RadialConeData o → RadialConeData v →
      KleinerLottApprox p o ε → KleinerLottApprox q v ε →
      ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ a : W, Nonempty (KleinerLottApprox q
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), a)) δ) := by
  classical
  let Bad (ε : ℝ) : Prop :=
    ∃ (Z : Type u) (mZ : MetricSpace Z), letI := mZ
      ∃ (C : Type v) (mC : MetricSpace C), letI := mC
        ∃ (_ : CompleteSpace C) (D : Type w) (mD : MetricSpace D), letI := mD
          ∃ (p q : Z) (o : C) (v : D) (H : RadialConeData o) (K : RadialConeData v)
            (φ : KleinerLottApprox p o ε) (ψ : KleinerLottApprox q v ε),
            dist p q = 1 ∧
            (∀ x y : C, ∀ η : ℝ, 0 < η →
              ∃ c : unitInterval → C, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
                eVariationOn c univ < ENNReal.ofReal (dist x y + η)) ∧
            dimH (univ : Set C) ≤ n ∧ fourPointComparison 0 (univ : Set C) ∧
            ¬ ∃ (W : Type u) (mW : MetricSpace W), letI := mW
              ∃ a : W, Nonempty (KleinerLottApprox q
                (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), a)) δ)
  by_contra hnone
  have hbad (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) : Bad ε := by
    by_contra hb
    apply hnone
    refine ⟨ε, hε, hεone, ?_⟩
    intro Z mZ C mC hcomplete D mD p q o v hsep hcurves hdim hcomp H K φ ψ
    by_contra hfail
    exact hb ⟨Z, mZ, C, mC, hcomplete, D, mD, p, q, o, v, H, K, φ, ψ,
      hsep, hcurves, hdim, hcomp, hfail⟩
  let ε : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  have hεpos (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have hεone (i : ℕ) : ε i < 1 := by
    dsimp [ε]
    exact (div_lt_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  choose Z mZ C mC hcomplete D mD p q o v H K Φ Ψ hsep hcurves hdim hcomp hno using
    fun i => hbad (ε i) (hεpos i) (hεone i)
  let : ∀ i, MetricSpace (Z i) := mZ
  let : ∀ i, MetricSpace (C i) := mC
  let : ∀ i, CompleteSpace (C i) := hcomplete
  let : ∀ i, MetricSpace (D i) := mD
  obtain ⟨Y, mY, a, α, hα, hcompleteY, hproperY, hCconv, hconeY,
      _hdimY, hcompY, hsegmentsY, _hsideY, _hnetsY⟩ :=
    exists_pointed_cone_limit_of_nonnegative_geometry o hn hcurves hdim hcomp H
  let := mY
  let := hcompleteY
  let := hproperY
  have hZconv : PointedGHConverges (fun i => p (α i)) a :=
    (pointedGHConverges_iff_of_kleinerLott_sequence (fun i => Φ (α i))
      (hεzero.comp hα.tendsto_atTop)).mpr hCconv
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  let e : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hepos (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  have her (i : ℕ) : e i < r i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [e, r]
    linarith
  have hezero : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  obtain ⟨β, hβ, hf⟩ := extraction_forall_of_eventually
    (fun i => hZconv.eventually_approx (hepos i) (her i))
  let f (i : ℕ) : PointedBallApprox (p (α (β i))) a (r i) (e i) := Classical.choice (hf i)
  have hmarked (i : ℕ) : dist (q (α (β i))) (p (α (β i))) ≤ (1 : ℝ) := by
    rw [dist_comm, hsep]
  obtain ⟨b, χ, hχ, _hbball, _hbconv, hZqconv, hseplim⟩ :=
    exists_subsequence_moving_pointed_limit f hr hezero hmarked
  let γ : ℕ → ℕ := fun i => α (β (χ i))
  have hγ : StrictMono γ := hα.comp (hβ.comp hχ)
  have hab : dist b a = 1 := hseplim 1 (by
    have hh (i : ℕ) : dist (q (γ i)) (p (γ i)) = 1 := by rw [dist_comm, hsep]
    change Tendsto (fun i => dist (q (γ i)) (p (γ i))) atTop (𝓝 1)
    simpa only [hh] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hDconv : PointedGHConverges (fun i => v (γ i)) b :=
    (pointedGHConverges_iff_of_kleinerLott_sequence (fun i => Ψ (γ i))
      (hεzero.comp hγ.tendsto_atTop)).mp hZqconv
  obtain ⟨HY⟩ := hconeY
  obtain ⟨KY⟩ := hDconv.nonempty_radialConeData (fun i => K (γ i))
  have hne : a ≠ b := by intro hh; rw [← hh, dist_self] at hab; norm_num at hab
  obtain ⟨W, mW, w, eW, heW, _hpW, _hlineW, _hproperW, _hcompleteW,
      _hcompW, _hsegmentsW, _hdimW⟩ :=
    HY.exists_pointed_product_at_second_apex KY hne hcompY hsegmentsY
  let := mW
  have hmax := hZqconv.not_exists_small_product_isometry_of_frequently_no_kleinerLott
    (0 : EuclideanSpace ℝ (Fin 1)) hδ hδone (Frequently.of_forall (fun i => hno (γ i)))
  exact hmax ⟨W, mW, w, eW, heW⟩

end GC.MetricGeometry
