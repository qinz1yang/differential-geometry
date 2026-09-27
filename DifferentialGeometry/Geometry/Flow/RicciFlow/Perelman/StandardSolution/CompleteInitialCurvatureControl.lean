import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Solution.MovingMetricDifferenceEnergy
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.Measure
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem initialControl_gram_continuous
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : {t : ℝ // t ∈ D.carrier} × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric q.1.1) x₀ q.2 i j)
        {q : {t : ℝ // t ∈ D.carrier} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} := by
  intro x₀ i j
  rw [continuousOn_iff_continuous_domRestrict]
  have hslot : ∀ k : Fin 2, Continuous
      (fun p : {q : {t : ℝ // t ∈ D.carrier} × M //
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) p.1.2
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (if k = 0 then i else j) p.1.2)) := by
    intro k
    exact (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) x₀ (if k = 0 then i else j)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p ↦ p.2)
  have hev := hS.smoothMetric.metricTensor_cont.eval_continuous
    (P := {q : {t : ℝ // t ∈ D.carrier} × M //
      q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
    (τ := fun p ↦ p.1.1.1) (b := fun p ↦ p.1.2)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p ↦ p.1.1.2) (continuous_snd.comp continuous_subtype_val) hslot
  refine hev.congr ?_
  intro p
  change metricTensorField (S.base.metric p.1.1.1) p.1.2
    (fun k : Fin 2 ↦ DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
      (if k = 0 then i else j) p.1.2) =
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1.1.1) x₀ p.1.2 i j
  rw [metricTensorField_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem initialControl_rmNormSq_continuousOn_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M ↦
      normSq0S (I := I) (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2))
      (D.carrier ×ˢ (univ : Set M)) := by
  have hnorm := DifferentialGeometry.Analysis.Spectral.normSq0S_family_continuousOn
    (I := I) S.base.metric (fun t x ↦ S.base.rm04 t x)
      (initialControl_gram_continuous S hS) hS.rm04Cont
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous (fun p : D.carrier ×ˢ (univ : Set M) ↦
      ((⟨p.1.1, p.2.1⟩ : D.carrier), p.1.2)) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  apply (hnorm.comp hmap).congr
  intro p
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem initialControl_rmNormSq_time_continuous
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hslab : Icc (0 : ℝ) T ⊆ D.carrier) (x : M) :
    ContinuousOn (fun r : ℝ ↦
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x)) (Icc (0 : ℝ) T) := by
  exact (initialControl_rmNormSq_continuousOn_carrier S hS).comp
    (f := fun r : ℝ ↦ (r, x))
    (continuous_id.prodMk continuous_const).continuousOn
    (fun r hr ↦ ⟨hslab hr, mem_univ x⟩)

private theorem initialControl_regular_slab
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 < T) (K : ℝ)
    (hcontrol : T ≤ compactCurvatureControlTime (Module.finrank ℝ E) K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B)
    (hinit : ∀ x : M,
      normSq0S (I := I) (S.base.metric 0) x 4 (S.base.rm04 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 2 * K ^ 2 + 1 := by
  let u := nablaKRm04NormSqIntrinsic (I := I) S 0
  let c := rmTowerCost (Module.finrank ℝ E) 0
  have hc : 0 ≤ c := rmTowerCost_nonneg _ _
  have hu : ContinuousOn (fun p : ℝ × M ↦ u p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    simpa only [u, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      (initialControl_rmNormSq_continuousOn_carrier S hS).mono
        (prod_mono hslab subset_rfl)
  have hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hp : 0 < t) : t ∈ D.regular :=
    hregular ⟨hp, ht.2⟩
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hp : 0 < t) (x : M) :
      DifferentiableWithinAt ℝ (fun r ↦ u r x) (Icc (0 : ℝ) T) t := by
    obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution S hS 0 ⟨t, hreg t ht hp⟩ x
    exact (hd.mono hslab).differentiableWithinAt
  have hheat (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hp : 0 < t) (x : M) :
      parabolicOperatorWithDrift (flowG S) T (fun _ _ ↦ 0) u t x ≤
        -2 * nablaKRm04NormSqIntrinsic S 1 t x + c * (u t x + 1) ^ 2 := by
    obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution S hS 0 ⟨t, hreg t ht hp⟩ x
    have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hT) t ht)
    rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
    change d - nablaKNormLap S 0 t x ≤ _
    have hnonneg : 0 ≤ u t x := nablaKRm04NormSqIntrinsic_nonneg S 0 t x
    have hs := Real.sq_sqrt hnonneg
    have hroot : Real.sqrt (u t x) ≤ u t x + 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith [sq_nonneg (u t x)]
    have hr : towerReactionSum (nablaKRm04NormSqIntrinsic S) c 0 t x =
        c * u t x * Real.sqrt (u t x) := by
      simp only [towerReactionSum, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.sub_zero]
      change c * Real.sqrt (u t x) * Real.sqrt (u t x) * Real.sqrt (u t x) = _
      calc
        _ = c * (Real.sqrt (u t x)) ^ 2 * Real.sqrt (u t x) := by ring
        _ = _ := by rw [hs]
    change d ≤ nablaKNormLap S 0 t x +
      (-2 * nablaKRm04NormSqIntrinsic S 1 t x +
        towerReactionSum (nablaKRm04NormSqIntrinsic S) c 0 t x) at hle
    rw [hr] at hle
    have hm := mul_le_mul_of_nonneg_left hroot (mul_nonneg hc hnonneg)
    nlinarith [mul_nonneg hc (show 0 ≤ u t x + 1 by linarith)]
  obtain ⟨B₀, hB₀⟩ := hbounded
  let B : ℝ := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : M) : u t x ≤ B :=
    (hB₀ t ht x).trans (le_max_right _ _)
  have hcut := nonempty_shi_barrier_cutoff_data_of_solution S hS hT hslab hregular
    hcomplete hB hbound
  have hb := DifferentialGeometry.Analysis.scalar_quadratic_reaction_bound_cutoffs
    (flowG S) T hT u (nablaKRm04NormSqIntrinsic S 1) c (K ^ 2) B
    hc (sq_nonneg K) hB
    (compactCurvatureControlTime_reaction_bound (Module.finrank ℝ E) K T hcontrol)
    hu htime (fun t _ _ ↦ nablaKNorm_smooth S t 0) hbound
    (fun t _ x ↦ nablaKRm04NormSqIntrinsic_nonneg S 1 t x)
    (fun t _ _ x ↦ towerNorm_grad_le S 0 t x) hheat hinit hcut
  exact hb

theorem curvature_normSq_bound_from_initial_complete
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ)
    (hcontrol : T ≤ compactCurvatureControlTime (Module.finrank ℝ E) K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioo (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B)
    (hinit : ∀ x : M,
      normSq0S (I := I) (S.base.metric 0) x 4 (S.base.rm04 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 2 * K ^ 2 + 1 := by
  by_cases hp : 0 < T
  · intro t ht x
    have hb : ∀ r ∈ Ico (0 : ℝ) T,
        normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x) ≤ 2 * K ^ 2 + 1 := by
      intro r hr
      let tau := (r + T) / 2
      have htau : 0 < tau := by dsimp only [tau]; linarith [hr.1]
      have htauT : tau < T := by dsimp only [tau]; linarith [hr.2]
      have hrtau : r ≤ tau := by dsimp only [tau]; linarith [hr.2]
      have hsub : Icc (0 : ℝ) tau ⊆ Icc (0 : ℝ) T :=
        fun q hq ↦ ⟨hq.1, hq.2.trans htauT.le⟩
      have hbounded' : ∃ B : ℝ, ∀ q ∈ Icc (0 : ℝ) tau, ∀ y : M,
          normSq0S (I := I) (S.base.metric q) y 4 (S.base.rm04 q y) ≤ B := by
        obtain ⟨B, hB⟩ := hbounded
        exact ⟨B, fun q hq y ↦ hB q (hsub hq) y⟩
      exact initialControl_regular_slab S hS tau htau K (htauT.le.trans hcontrol)
        hcomplete (hsub.trans hslab)
        (fun q hq ↦ hregular ⟨hq.1, hq.2.trans_lt htauT⟩)
        hbounded' hinit r ⟨hr.1, hrtau⟩ x
    have hc : ContinuousOn
        (fun r : ℝ ↦ normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x))
        (Icc (0 : ℝ) T) :=
      initialControl_rmNormSq_time_continuous S hS T hslab x
    have hclosure : closure (Ico (0 : ℝ) T) = Icc (0 : ℝ) T := closure_Ico hp.ne
    rw [← hclosure] at hc
    exact le_on_closure hb hc continuousOn_const (by rw [hclosure]; exact ht)
  · have hzero : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro t ht x
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact (hinit x).trans (by nlinarith [sq_nonneg K])

end DifferentialGeometry.PDE.RicciFlow

end
