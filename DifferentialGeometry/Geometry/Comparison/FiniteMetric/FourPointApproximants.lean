import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Distance
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

/-!
# Four-point comparison for a finite-regularity metric from smooth approximants

Lane CM-A, package CM5.c of the D-FOUND design (§C1): a pure distance statement, proved without
any geodesic theory of the finite metric.

* `fourPoint_le_two_pi_of_riemannianEDistOf`: the smooth eight-ball four-point bridge
  (`fourPointComparison_of_sectional_lower_bound_on_eight_ball`) stated for the length distance
  `riemannianEDistOf h` of a complete smooth metric `h` on a manifold that carries only its
  topology. The metric space structure is `inducedEMetricSpace h` (topology definitionally the
  given one), installed inside the proof.
* `tendsto_toReal_riemannianEDistOf_of_bilipschitz`: distances of `(1 ± 1/(k+2))`-bilipschitz
  smooth approximants converge to the finite-metric distance.
* `fourPointComparison_zero_ball_of_approximants` (kernel): if the finite metric `g` is the limit
  of such approximants whose sectional curvature is eventually `≥ κ - ε` on every compact set
  where `sec_g ≥ κ` (the output shape of CM5.a), and `sec_g ≥ 0` on `ball o (32 R)`, then the
  distance satisfies the four-point comparison at curvature `0` on `ball o R`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.FiniteComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- The smooth eight-ball four-point comparison for the length distance of a complete smooth
metric `h` on a manifold carrying only its topology. -/
theorem fourPoint_le_two_pi_of_riemannianEDistOf [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M] [SigmaCompactSpace M]
    (h : SmoothRiemannianMetric I M) (hfin : ∀ a b : M, riemannianEDistOf (I := I) h a b ≠ ⊤)
    (hcomplete : @CompleteSpace M (inducedEMetricSpace h).toPseudoEMetricSpace.toUniformSpace)
    (o : M) {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y : M, riemannianEDistOf (I := I) h o y < ENNReal.ofReal (8 * R) →
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt h y (-κ))
    (x a b c : M) (hx : riemannianEDistOf (I := I) h o x < ENNReal.ofReal R)
    (ha : riemannianEDistOf (I := I) h o a < ENNReal.ofReal R)
    (hb : riemannianEDistOf (I := I) h o b < ENNReal.ofReal R)
    (hc : riemannianEDistOf (I := I) h o c < ENNReal.ofReal R)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x) :
    comparisonAngleNegCurvature κ (riemannianEDistOf (I := I) h x a).toReal
        (riemannianEDistOf (I := I) h x b).toReal (riemannianEDistOf (I := I) h a b).toReal +
      comparisonAngleNegCurvature κ (riemannianEDistOf (I := I) h x b).toReal
        (riemannianEDistOf (I := I) h x c).toReal (riemannianEDistOf (I := I) h b c).toReal +
      comparisonAngleNegCurvature κ (riemannianEDistOf (I := I) h x c).toReal
        (riemannianEDistOf (I := I) h x a).toReal (riemannianEDistOf (I := I) h c a).toReal ≤
      2 * Real.pi := by
  let m : MetricSpace M := @EMetricSpace.toMetricSpace M (inducedEMetricSpace h) hfin
  have : CompleteSpace M := hcomplete
  have hmetric : ∀ a b : M, riemannianEDistOf (I := I) h a b = ENNReal.ofReal (dist a b) :=
    fun a b => edist_dist a b
  have hball : ∀ y : M, y ∈ Metric.ball o (8 * R) →
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt h y (-κ) :=
    fun y hy => hsec y (edist_lt_ofReal.mpr (Metric.mem_ball'.mp hy))
  exact fourPointComparison_of_sectional_lower_bound_on_eight_ball h hmetric o hκ hball
    x (Metric.mem_ball'.mpr (edist_lt_ofReal.mp hx)) a
    (Metric.mem_ball'.mpr (edist_lt_ofReal.mp ha)) b (Metric.mem_ball'.mpr (edist_lt_ofReal.mp hb))
    c (Metric.mem_ball'.mpr (edist_lt_ofReal.mp hc)) hax hbx hcx

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- The approximation parameter `1/(k+2)` lies in `(0, 1/2]`. -/
theorem one_div_nat_add_two_mem (k : ℕ) :
    0 < 1 / ((k : ℝ) + 2) ∧ 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
  refine ⟨by positivity, ?_⟩
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

omit [FiniteDimensional ℝ E] in
/-- Two-sided real distance comparison for a `(1 ± δ)`-bilipschitz smooth approximant. -/
theorem toReal_riemannianEDistOf_mem_Icc {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (h : SmoothRiemannianMetric I M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hbil : ∀ (x : M) (w : TangentSpace I x), (1 - δ) ^ 2 * g.inner x w w ≤ h.inner x w w ∧
      h.inner x w w ≤ (1 + δ) ^ 2 * g.inner x w w) (u v : M) :
    (1 - δ) * dist u v ≤ (riemannianEDistOf (I := I) h u v).toReal ∧
      (riemannianEDistOf (I := I) h u v).toReal ≤ (1 + δ) * dist u v := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 1 + δ := by linarith
  have hup := riemannianEDistOf_le_ofReal_mul_edist g hnorm h h2 (fun x w => (hbil x w).2) u v
  have hlow := ofReal_mul_edist_le_riemannianEDistOf g hnorm h h1 (fun x w => (hbil x w).1) u v
  rw [edist_dist, ← ENNReal.ofReal_mul h2.le] at hup
  rw [edist_dist, ← ENNReal.ofReal_mul h1.le] at hlow
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup)).mp hlow,
    ENNReal.toReal_le_of_le_ofReal (by positivity) hup⟩

omit [FiniteDimensional ℝ E] in
/-- Distances of `(1 ± 1/(k+2))`-bilipschitz smooth approximants converge to the distance. -/
theorem tendsto_toReal_riemannianEDistOf_of_bilipschitz {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbil : ∀ (k : ℕ) (x : M) (w : TangentSpace I x),
      (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
        (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w) (u v : M) :
    Tendsto (fun k => (riemannianEDistOf (I := I) (gSeq k) u v).toReal) atTop (𝓝 (dist u v)) := by
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    refine (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
      fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlo : Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2)) * dist u v) atTop (𝓝 (dist u v)) := by
    simpa using (h1.sub hδ).mul_const (dist u v)
  have hhi : Tendsto (fun k : ℕ => (1 + 1 / ((k : ℝ) + 2)) * dist u v) atTop (𝓝 (dist u v)) := by
    simpa using (h1.add hδ).mul_const (dist u v)
  have hb (k : ℕ) := toReal_riemannianEDistOf_mem_Icc g hnorm (gSeq k)
    (one_div_nat_add_two_mem k).1 (by linarith [(one_div_nat_add_two_mem k).2]) (hbil k) u v
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun k => (hb k).1) (fun k => (hb k).2)

/-- **Kernel of CM5.c (local four-point comparison).** Let `g` be a finite-regularity metric
whose length distance is the ambient complete distance, and let `gSeq` be smooth metrics,
`(1 ± 1/(k+2))`-bilipschitz to `g`, whose sectional curvature is eventually `≥ κ - ε` on every
compact set on which `sec_g ≥ κ` (the output of CM5.a). If `sec_g ≥ 0` on `ball o (32 R)`, the
distance satisfies the four-point comparison at curvature `0` on `ball o R`. -/
theorem fourPointComparison_zero_ball_of_approximants [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbil : ∀ (k : ℕ) (x : M) (w : TangentSpace I x),
      (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
        (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w)
    (hcurv : ∀ (C : Set M), IsCompact C → ∀ (κ ε : ℝ), 0 < ε →
      (∀ x ∈ C, ∀ v w : TangentSpace I x, κ ≤ g.sectionalCurvature x v w) →
      ∀ᶠ k in atTop, ∀ x ∈ C,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt (gSeq k) x (κ - ε))
    (o : M) (R : ℝ)
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ v w : TangentSpace I y,
      0 ≤ g.sectionalCurvature y v w) :
    fourPointComparison 0 (Metric.ball o R) := by
  rcases le_or_gt R 0 with hR | hR
  · intro x hx
    rw [Metric.ball_eq_empty.mpr hR] at hx
    exact absurd hx (notMem_empty x)
  have hδ := one_div_nat_add_two_mem
  have hlow (k : ℕ) (x : M) (w : TangentSpace I x) :
      (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w := (hbil k x w).1
  have hup (k : ℕ) (x : M) (w : TangentSpace I x) :
      (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w := (hbil k x w).2
  have hpos₁ (k : ℕ) : 0 < 1 - 1 / ((k : ℝ) + 2) := by linarith [(hδ k).2]
  have hpos₂ (k : ℕ) : 0 < 1 + 1 / ((k : ℝ) + 2) := by linarith [(hδ k).1]
  have : ProperSpace M :=
    properSpace_of_bilipschitz_smooth g hnorm (gSeq 0) (hpos₁ 0) (hpos₂ 0) (hlow 0) (hup 0)
  set C : Set M := Metric.closedBall o (24 * R) with hCdef
  have hC : IsCompact C := isCompact_closedBall o (24 * R)
  have hsecC : ∀ x ∈ C, ∀ v w : TangentSpace I x, 0 ≤ g.sectionalCurvature x v w := by
    intro x hx v w
    refine hsec x ?_ v w
    exact Metric.closedBall_subset_ball (by linarith) hx
  have hev : ∀ j : ℕ, ∀ᶠ k in atTop, 1 ≤ k ∧ ∀ x ∈ C,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt (gSeq k) x
        (0 - 1 / ((j : ℝ) + 1)) := fun j =>
    (eventually_ge_atTop 1).and (hcurv C hC 0 (1 / ((j : ℝ) + 1)) (by positivity) hsecC)
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually hev
  -- the comparison inequality for the `φ j`-th approximant at curvature `-1/(j+1)`
  have hstep : ∀ j : ℕ, ∀ x ∈ Metric.ball o R, ∀ a ∈ Metric.ball o R, ∀ b ∈ Metric.ball o R,
      ∀ c ∈ Metric.ball o R, a ≠ x → b ≠ x → c ≠ x →
      comparisonAngleNegCurvature (1 / ((j : ℝ) + 1))
          (riemannianEDistOf (I := I) (gSeq (φ j)) x a).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) x b).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) a b).toReal +
        comparisonAngleNegCurvature (1 / ((j : ℝ) + 1))
          (riemannianEDistOf (I := I) (gSeq (φ j)) x b).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) x c).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) b c).toReal +
        comparisonAngleNegCurvature (1 / ((j : ℝ) + 1))
          (riemannianEDistOf (I := I) (gSeq (φ j)) x c).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) x a).toReal
          (riemannianEDistOf (I := I) (gSeq (φ j)) c a).toReal ≤ 2 * Real.pi := by
    intro j x hx a ha b hb c hc hax hbx hcx
    set k := φ j with hk
    obtain ⟨hk1, hkC⟩ := hφP j
    have hδk : 1 / ((k : ℝ) + 2) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        linarith)
    have hin (y : M) (hy : y ∈ Metric.ball o R) :
        riemannianEDistOf (I := I) (gSeq k) o y < ENNReal.ofReal (2 * R) := by
      have h := riemannianEDistOf_le_ofReal_mul_edist g hnorm (gSeq k) (hpos₂ k) (hup k) o y
      rw [edist_dist, ← ENNReal.ofReal_mul (hpos₂ k).le] at h
      refine h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr ?_)
      have hoy : dist o y < R := Metric.mem_ball'.mp hy
      nlinarith [(hδ k).2, dist_nonneg (x := o) (y := y)]
    refine fourPoint_le_two_pi_of_riemannianEDistOf (gSeq k)
      (riemannianEDistOf_ne_top_of_le g hnorm (gSeq k) (hpos₂ k) (hup k))
      (completeSpace_inducedEMetricSpace_of_le g hnorm (gSeq k) (hpos₁ k) (hlow k)) o
      (R := 2 * R) (by positivity) (fun y hy => ?_) x a b c (hin x hx) (hin a ha) (hin b hb)
      (hin c hc) hax hbx hcx
    have hyC : y ∈ C := by
      have h := ofReal_mul_edist_le_riemannianEDistOf g hnorm (gSeq k) (hpos₁ k) (hlow k) o y
      rw [edist_dist, ← ENNReal.ofReal_mul (hpos₁ k).le] at h
      have h' := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp (h.trans_lt hy)
      rw [hCdef, Metric.mem_closedBall, dist_comm]
      nlinarith [dist_nonneg (x := o) (y := y)]
    have := hkC y hyC
    rwa [zero_sub] at this
  intro x hx a ha b hb c hc hax hbx hcx
  have hd (u v : M) : Tendsto (fun j => (riemannianEDistOf (I := I) (gSeq (φ j)) u v).toReal)
      atTop (𝓝 (dist u v)) :=
    (tendsto_toReal_riemannianEDistOf_of_bilipschitz g hnorm gSeq hbil u v).comp
      hφ.tendsto_atTop
  have hκ : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hκ0 : ∀ᶠ j : ℕ in atTop, 0 ≤ 1 / ((j : ℝ) + 1) := Eventually.of_forall fun j => by positivity
  have hpa : 0 < dist x a := dist_pos.mpr hax.symm
  have hpb : 0 < dist x b := dist_pos.mpr hbx.symm
  have hpc : 0 < dist x c := dist_pos.mpr hcx.symm
  have h1 := tendsto_comparisonAngleNegCurvature_zero hκ (hd x a) (hd x b) (hd a b) hκ0 hpa hpb
  have h2 := tendsto_comparisonAngleNegCurvature_zero hκ (hd x b) (hd x c) (hd b c) hκ0 hpb hpc
  have h3 := tendsto_comparisonAngleNegCurvature_zero hκ (hd x c) (hd x a) (hd c a) hκ0 hpc hpa
  simp only [comparisonAngleNegCurvature_zero]
  exact le_of_tendsto' ((h1.add h2).add h3) fun j =>
    hstep j x hx a ha b hb c hc hax hbx hcx

end DifferentialGeometry.Geometry.FiniteComparison
