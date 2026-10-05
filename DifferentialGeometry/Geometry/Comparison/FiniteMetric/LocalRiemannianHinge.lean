import DifferentialGeometry.Geometry.Comparison.FiniteMetric.LocalHingeApproximants
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingArmConvergence
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.ApproximatingHingeComparison
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.HingeInnerLimit
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder

/-!
Local finite hinge comparison retains the original curvature ball and both exponential arms.
A fixed compact buffer controls the same smooth sequence, actual minimizing directions converge
at strict radial prefixes, and continuity restores the original endpoint lengths.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [groupE : NormedAddCommGroup E] [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E] [rankE : NeZero (Module.finrank ℝ E)]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [sigmaM : SigmaCompactSpace M] [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M] {r : ℕ∞}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem local_hinge_for_strict_prefixes
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y ∈ Metric.ball o R, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∀ {s t : ℝ}, 0 < s → s < a → 0 < t → t < b →
      comparisonAngle s t (dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨o, t • v⟩ : TangentBundle I M))) ≤ Real.arccos (g.inner o u v) := by
  intro s t hs hsa ht htb
  classical
  have hr1 : 1 ≤ r := (by norm_num : (1 : ℕ∞) ≤ 3).trans hr
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
    have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr1
    calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
      _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1
  obtain ⟨ρ, gSeq, φ, hρ0, hρ, hρR, hφ, hφ2, hbil, hconv, hsecφ⟩ :=
    exists_buffered_local_hinge_approximants g hn hnorm o (add_pos ha hb) hR hsec
  let A : M := g.expMap (⟨o, s • u⟩ : TangentBundle I M)
  let B : M := g.expMap (⟨o, t • v⟩ : TangentBundle I M)
  have hdA : dist o A = s :=
    (g.dist_expMap_smul_eq_of_dist_eq hr1 hnorm hu hminA).1 s ⟨hs.le, hsa.le⟩
  have hdB : dist o B = t :=
    (g.dist_expMap_smul_eq_of_dist_eq hr1 hnorm hv hminB).1 t ⟨ht.le, htb.le⟩
  have hA : A ≠ o := by
    intro hAo
    rw [hAo, dist_self] at hdA
    exact hs.ne' hdA.symm
  have hB : B ≠ o := by
    intro hBo
    rw [hBo, dist_self] at hdB
    exact ht.ne' hdB.symm
  have hδsmall (j : ℕ) : 1 / ((φ j : ℝ) + 2) < 1 / 3 := by
    have hφreal : (2 : ℝ) ≤ φ j := by exact_mod_cast hφ2 j
    exact lt_of_le_of_lt (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (by linarith : (4 : ℝ) ≤ (φ j : ℝ) + 2)) (by norm_num)
  have hU : ∀ j : ℕ, ∃ w : E, (gSeq (φ j)).inner o w w = 1 ∧
      (gSeq (φ j)).expMap
        (⟨o, (riemannianEDistOf (I := I) (gSeq (φ j)) o A).toReal • w⟩ :
          TangentBundle I M) = A := fun j =>
    exists_unit_smooth_approximant_arm g hnorm (gSeq (φ j))
      (one_div_nat_add_two_mem (φ j)).1 (hδsmall j) (hbil (φ j)) o A hA
  have hV : ∀ j : ℕ, ∃ w : E, (gSeq (φ j)).inner o w w = 1 ∧
      (gSeq (φ j)).expMap
        (⟨o, (riemannianEDistOf (I := I) (gSeq (φ j)) o B).toReal • w⟩ :
          TangentBundle I M) = B := fun j =>
    exists_unit_smooth_approximant_arm g hnorm (gSeq (φ j))
      (one_div_nat_add_two_mem (φ j)).1 (hδsmall j) (hbil (φ j)) o B hB
  choose U hUunit hUreach using hU
  choose V hVunit hVreach using hV
  obtain ⟨ψ1, hψ1, hUlimit⟩ := exists_subsequence_minimizingArmDirections_tendsto
    g hr hnorm gSeq hbil hconv φ hφ U hs hsa hu hminA hUunit hUreach
  obtain ⟨ψ2, hψ2, hVlimit⟩ := exists_subsequence_minimizingArmDirections_tendsto
    g hr hnorm gSeq hbil hconv (φ ∘ ψ1) (hφ.comp hψ1) (V ∘ ψ1)
      ht htb hv hminB (fun j => hVunit (ψ1 j)) (fun j => hVreach (ψ1 j))
  let τ : ℕ → ℕ := ψ1 ∘ ψ2
  have hτ : StrictMono τ := hψ1.comp hψ2
  have hUL : Tendsto (fun j => U (τ j)) atTop (𝓝 u) := hUlimit.comp hψ2.tendsto_atTop
  have hVL : Tendsto (fun j => V (τ j)) atTop (𝓝 v) := hVlimit
  have hindex : Tendsto (fun j => φ (τ j)) atTop atTop :=
    hφ.tendsto_atTop.comp hτ.tendsto_atTop
  have hδlimit : Tendsto (fun j => 1 / ((φ (τ j) : ℝ) + 2)) atTop (𝓝 0) := by
    have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
        fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    exact heps.comp hindex
  have hinner := tendsto_bilin_of_quadratic_bounds
    (B := (g.inner o : E →L[ℝ] E →L[ℝ] ℝ))
    (BSeq := fun j => ((gSeq (φ (τ j))).inner o : E →L[ℝ] E →L[ℝ] ℝ))
    (fun x y => g.symm o x y) (fun j x y => (gSeq (φ (τ j))).symm o x y)
    (fun j => 1 / ((φ (τ j) : ℝ) + 2)) hδlimit
    (fun j w => hbil (φ (τ j)) o w) (fun j => U (τ j)) (fun j => V (τ j))
    u v hUL hVL
  have hright := Real.continuous_arccos.continuousAt.tendsto.comp hinner
  have hd (x y : M) :
      Tendsto (fun j => (riemannianEDistOf (I := I) (gSeq (φ (τ j))) x y).toReal)
        atTop (𝓝 (dist x y)) :=
    (tendsto_toReal_riemannianEDistOf_of_bilipschitz g hnorm gSeq hbil x y).comp hindex
  have hκ : Tendsto (fun j => 1 / ((τ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hτ.tendsto_atTop
  have hleft := tendsto_comparisonAngleNegCurvature_zero hκ (hd o A) (hd o B) (hd A B)
    (Eventually.of_forall (fun j => by positivity)) (by rw [hdA]; exact hs)
      (by rw [hdB]; exact ht)
  have hstep (j : ℕ) :
      comparisonAngleNegCurvature (1 / ((τ j : ℝ) + 1))
        (riemannianEDistOf (I := I) (gSeq (φ (τ j))) o A).toReal
        (riemannianEDistOf (I := I) (gSeq (φ (τ j))) o B).toReal
        (riemannianEDistOf (I := I) (gSeq (φ (τ j))) A B).toReal ≤
      Real.arccos ((gSeq (φ (τ j))).inner o (U (τ j)) (V (τ j))) := by
    have hk : 0 < 1 / ((τ j : ℝ) + 1) := by positivity
    have hlocal : ∀ y ∈ Metric.closedBall o ρ,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt
          (gSeq (φ (τ j))) y (-(Real.sqrt (1 / ((τ j : ℝ) + 1))) ^ 2) := by
      intro y hy
      rw [Real.sq_sqrt hk.le]
      simpa only [neg_div] using hsecφ (τ j) y hy
    have hcompare := hyperbolic_hinge_of_bilipschitz_buffer g hnorm (gSeq (φ (τ j)))
      (one_div_nat_add_two_mem (φ (τ j))).1 (hδsmall (τ j)) (Real.sqrt_pos.mpr hk)
      (hbil (φ (τ j))) o A B (U (τ j)) (V (τ j)) hA hB
      (by rw [hdA, hdB]; linarith) (hUunit (τ j)) (hVunit (τ j))
      (hUreach (τ j)) (hVreach (τ j)) hlocal
    simpa only [comparisonAngleNegCurvature, ite_eq_right hk.ne',
      hyperbolicComparisonAngle, hyperbolicComparisonCosine] using hcompare
  have hfinal := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hstep)
  rwa [hdA, hdB] at hfinal

theorem comparisonAngle_le_arccos_inner_finite_of_sectional_nonneg_on_ball
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y ∈ Metric.ball o R, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    comparisonAngle a b (dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, b • v⟩ : TangentBundle I M))) ≤ Real.arccos (g.inner o u v) := by
  have hr1 : 1 ≤ r := (by norm_num : (1 : ℕ∞) ≤ 3).trans hr
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hε : Tendsto ε atTop (𝓝 0) := by
    refine (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
      fun n => ?_
    simp only [ε, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hεbounds (n : ℕ) : 0 < ε n ∧ ε n < 1 := by
    have h := one_div_nat_add_two_mem n
    exact ⟨h.1, by linarith [h.2]⟩
  let sa : ℕ → ℝ := fun n => a * (1 - ε n)
  let tb : ℕ → ℝ := fun n => b * (1 - ε n)
  have hsa (n : ℕ) : 0 < sa n ∧ sa n < a := by
    dsimp only [sa]
    constructor
    · exact mul_pos ha (sub_pos.mpr (hεbounds n).2)
    · nlinarith [(hεbounds n).1]
  have htb (n : ℕ) : 0 < tb n ∧ tb n < b := by
    dsimp only [tb]
    constructor
    · exact mul_pos hb (sub_pos.mpr (hεbounds n).2)
    · nlinarith [(hεbounds n).1]
  have hsaL : Tendsto sa atTop (𝓝 a) := by
    simpa only [sub_zero, mul_one] using
      (tendsto_const_nhds (x := a)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hε)
  have htbL : Tendsto tb atTop (𝓝 b) := by
    simpa only [sub_zero, mul_one] using
      (tendsto_const_nhds (x := b)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hε)
  have hcurve (w : E) (hw : g.inner o w w = 1) :
      Continuous (fun t : ℝ => g.expMap (⟨o, t • w⟩ : TangentBundle I M)) := by
    have hLip : LipschitzWith 1
        (fun t : ℝ => g.expMap (⟨o, t • w⟩ : TangentBundle I M)) :=
      LipschitzWith.of_dist_le_mul (fun s t => by
        have hbound := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm
          (x := o) (w : TangentSpace I o) s t
        change dist (g.expMap (⟨o, s • w⟩ : TangentBundle I M))
          (g.expMap (⟨o, t • w⟩ : TangentBundle I M)) ≤
            Real.sqrt (g.inner o w w) * |t - s| at hbound
        simpa only [hw, Real.sqrt_one, one_mul, NNReal.coe_one, Real.dist_eq,
          abs_sub_comm, mul_one] using hbound)
    exact hLip.continuous
  have hdL := ((hcurve u hu).tendsto a |>.comp hsaL).dist
    ((hcurve v hv).tendsto b |>.comp htbL)
  have hangle := tendsto_comparisonAngleNegCurvature_zero
    (κ := fun n : ℕ => (0 : ℝ)) tendsto_const_nhds hsaL htbL hdL
    (Eventually.of_forall (fun n => le_rfl)) ha hb
  simp only [comparisonAngleNegCurvature_zero] at hangle
  exact le_of_tendsto' hangle (fun n => local_hinge_for_strict_prefixes
    g hr hnorm o u v ha hb hR hu hv hminA hminB hsec
      (hsa n).1 (hsa n).2 (htb n).1 (htb n).2)

theorem sq_dist_expMap_le_finite_of_sectional_nonneg_on_ball
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y ∈ Metric.ball o R, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) ^ 2 ≤
        a ^ 2 + b ^ 2 - 2 * a * b * g.inner o u v := by
  have hangle := comparisonAngle_le_arccos_inner_finite_of_sectional_nonneg_on_ball
    g hr hnorm o u v ha hb hR hu hv hminA hminB hsec
  have hlower := abs_dist_sub_le (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
    (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) o
  rw [dist_comm _ o, dist_comm _ o, hminA, hminB] at hlower
  have hupper := dist_triangle (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) o
    (g.expMap (⟨o, b • v⟩ : TangentBundle I M))
  rw [dist_comm _ o, hminA, hminB] at hupper
  have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g o u v
  rw [hu, hv, Real.sqrt_one, one_mul] at hcs
  have hsquare := DifferentialGeometry.Toponogov.sq_le_cos_of_comparisonAngle_le ha hb hlower hupper
    (Real.arccos_le_pi (g.inner o u v)) hangle
  rwa [Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2] at hsquare

end DifferentialGeometry.Geometry.FiniteComparison
