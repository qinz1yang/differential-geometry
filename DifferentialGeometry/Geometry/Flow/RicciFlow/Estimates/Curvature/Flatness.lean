import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Solution.MovingMetricDifferenceEnergy
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set Manifold
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem normSq0S_eq_zero_of_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) {s : Nat} (hs : s ≠ 0)
    (A : Tensor0SSpace s I x) (h : Module.finrank ℝ E = 0) :
    normSq0S (I := I) g x s A = 0 := by
  have hx : Module.finrank ℝ (TangentSpace I x) = 0 := by
    have hfin : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [hfin, h]
  let b := Module.finBasis ℝ (TangentSpace I x)
  rw [hx] at b
  rw [normSq0S_eq_coord (I := I) g x s b (basisInvMetric (I := I) g x b)
    (basisInvMetric_isInverse (I := I) g x b) A]
  refine Finset.sum_eq_zero (fun I0 _ => Finset.sum_eq_zero (fun J0 _ => ?_))
  exact Fin.elim0 (I0 ⟨0, Nat.pos_of_ne_zero hs⟩)

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartGram_continuousOn_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : {t : ℝ // t ∈ D.carrier} × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (I := I) (S.base.metric q.1.1) x₀ q.2 i j)
        {q : {t : ℝ // t ∈ D.carrier} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} := by
  intro x₀ i j
  rw [continuousOn_iff_continuous_domRestrict]
  have hslot : ∀ k : Fin 2, Continuous
      (fun p : {q : {t : ℝ // t ∈ D.carrier} × M //
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) p.1.2
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
            (if k = 0 then i else j) p.1.2)) := by
    intro k
    exact (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn
        (I := I) x₀ (if k = 0 then i else j)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  have hev := hS.smoothMetric.metricTensor_cont.eval_continuous
    (P := {q : {t : ℝ // t ∈ D.carrier} × M //
      q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
    (τ := fun p => p.1.1.1) (b := fun p => p.1.2)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p => p.1.1.2) (continuous_snd.comp continuous_subtype_val) hslot
  refine hev.congr ?_
  intro p
  change metricTensorField (S.base.metric p.1.1.1) p.1.2
    (fun k : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
      (if k = 0 then i else j) p.1.2) =
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
      (I := I) (S.base.metric p.1.1.1) x₀ p.1.2 i j
  rw [metricTensorField_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem rmNormSq_continuousOn_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M =>
      normSq0S (I := I) (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2))
      (D.carrier ×ˢ (univ : Set M)) := by
  have hnorm := DifferentialGeometry.Analysis.Spectral.normSq0S_family_continuousOn
    (I := I) S.base.metric (fun t x => S.base.rm04 t x)
      (chartGram_continuousOn_carrier (I := I) S hS) hS.rm04Cont
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous (fun p : D.carrier ×ˢ (univ : Set M) =>
      ((⟨p.1.1, p.2.1⟩ : D.carrier), p.1.2)) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  apply (hnorm.comp hmap).congr
  intro p
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem rmNormSq_time_continuous
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (a b : ℝ) (hslab : Icc a b ⊆ D.carrier) (x : M) :
    ContinuousOn (fun r : ℝ =>
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x)) (Icc a b) := by
  exact (rmNormSq_continuousOn_carrier (I := I) S hS).comp
    (f := fun r : ℝ => (r, x))
    (continuous_id.prodMk continuous_const).continuousOn
    (fun r hr => ⟨hslab hr, mem_univ x⟩)

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaKRm04NormSqIntrinsic_timeShift
    (S : SolutionOn (I := I) (M := M) D) (a s : ℝ) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (S.timeShift a) 0 s x =
      normSq0S (I := I) (S.base.metric (s + a)) x 4 (S.base.rm04 (s + a) x) := by
  simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero,
    SolutionOn.timeShift_base_metric, SolutionFamily.rm04]

private theorem curvature_normSq_eq_zero_on_Icc_at_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hcarrier : Icc 0 T ⊆ D.carrier) (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ K)
    (hflat : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 0 x ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 t x = 0 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · intro t _ x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      normSq0S_eq_zero_of_finrank_eq_zero (I := I) (S.base.metric t) x
        (by norm_num) (S.base.rm04 t x) hdim
  · have : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let u := nablaKRm04NormSqIntrinsic (I := I) S 0
    let c : ℝ := rmTowerCost (Module.finrank ℝ E) 0
    have hc : 0 ≤ c := rmTowerCost_nonneg _ _
    let Λ : ℝ := c * Real.sqrt K
    have hΛ : 0 ≤ Λ := mul_nonneg hc (Real.sqrt_nonneg K)
    have hreg (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) : t ∈ D.regular :=
      hregular ⟨hp, ht.2⟩
    have hcont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ univ) := by
      simpa only [u, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
        (rmNormSq_continuousOn_carrier (I := I) S hS).mono (prod_mono hcarrier subset_rfl)
    have htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
        DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t := by
      intro t ht hp x
      obtain ⟨d, hd, _⟩ :=
        towerHeatBoundOn_of_solution (I := I) S hS 0 ⟨t, hreg t ht hp⟩ x
      exact (hd.mono hcarrier).differentiableWithinAt
    have hspace : ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := by
      intro t _ _
      simpa only [u] using nablaKNorm_smooth (I := I) S t 0
    have hbound : ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ K := hcurv
    have hw : ∀ t ∈ Icc 0 T, ∀ x : M,
        0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
      fun t _ x => nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
    have hgrad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
        (S.base.metric t).inner x (gradientFun (I := I) (S.base.metric t) (u t) x)
          (gradientFun (I := I) (S.base.metric t) (u t) x) ≤
        4 * K * nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
      intro t ht _ x _
      have h := towerNorm_grad_le (I := I) S 0 t x
      have h1 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
        nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
      nlinarith [hcurv t ht x]
    have hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
        parabolicOperatorWithDrift (flowG (I := I) S) T (fun _ _ => 0) u t x ≤
          -2 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x + Λ * u t x := by
      intro t ht hp x _
      obtain ⟨d, hd, hle⟩ :=
        towerHeatBoundOn_of_solution (I := I) S hS 0 ⟨t, hreg t ht hp⟩ x
      have hderiv := (hd.mono hcarrier).derivWithin ((uniqueDiffOn_Icc hT) t ht)
      rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
      change d - nablaKNormLap (I := I) S 0 t x ≤
        -2 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x + Λ * u t x
      have hnonneg : 0 ≤ u t x := nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x
      have hr : towerReactionSum (nablaKRm04NormSqIntrinsic (I := I) S) c 0 t x =
          c * u t x * Real.sqrt (u t x) := by
        simp only [towerReactionSum, Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add, Nat.sub_zero]
        change c * Real.sqrt (u t x) * Real.sqrt (u t x) * Real.sqrt (u t x) = _
        calc
          _ = c * (Real.sqrt (u t x)) ^ 2 * Real.sqrt (u t x) := by ring
          _ = _ := by rw [Real.sq_sqrt hnonneg]
      have hmul : c * u t x * Real.sqrt (u t x) ≤ Λ * u t x := by
        have hsqrt : Real.sqrt (u t x) ≤ Real.sqrt K := Real.sqrt_le_sqrt (hcurv t ht x)
        calc
          c * u t x * Real.sqrt (u t x) ≤ c * u t x * Real.sqrt K :=
            mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hc hnonneg)
          _ = Λ * u t x := by ring
      rw [hr] at hle
      linarith
    have hinit : ∀ x : M, u 0 x ≤ 0 := fun x => hflat x
    have hcut : ∀ O : M,
        Nonempty (ShiBarrierCutoffData (I := I) (flowG (I := I) S) T O) :=
      nonempty_shi_barrier_cutoff_data_of_solution (I := I) S hS hT hcarrier hregular
        hcomplete hK hcurv
    have hmain := DifferentialGeometry.Analysis.nonpositive_of_dissipation_and_cutoffs
      (flowG (I := I) S) T hT u
      (nablaKRm04NormSqIntrinsic (I := I) S 1) Λ K hΛ hK hcont htime hspace hinit
      hbound hw hgrad hheat hcut
    intro t ht x
    exact le_antisymm (hmain t ht x)
      (nablaKRm04NormSqIntrinsic_nonneg (I := I) S 0 t x)

theorem curvature_normSq_eq_zero_on_Icc_of_eq_zero_at_left
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ico a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hflat : ∀ x : M, normSq0S (I := I) (S.base.metric a) x 4 (S.base.rm04 a x) = 0) :
    ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) = 0 := by
  obtain ⟨K, hK, hcurvK⟩ := hcurv
  have hcurv' : ∀ t ∈ Icc a b, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ K := by
    intro t ht x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      hcurvK t ht x
  have hflat' : ∀ x : M, nablaKRm04NormSqIntrinsic (I := I) S 0 a x ≤ 0 := by
    intro x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      le_of_eq (hflat x)
  have hstep : ∀ b' : ℝ, a < b' → b' < b → ∀ t ∈ Icc a b', ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) = 0 := by
    intro b' hab' hb'b
    have hT : 0 < b' - a := sub_pos.mpr hab'
    let D' := D.timeShift a
    let S' := S.timeShift a
    have hS' : IsSolutionOn (I := I) S' := by
      simpa only [S'] using isSolutionOn_timeShift (I := I) hS a
    have hcarrier' : Icc 0 (b' - a) ⊆ D'.carrier := by
      intro s hs
      have hs' : s + a ∈ D.carrier :=
        hcarrier ⟨by linarith [hs.1], by linarith [hs.2, hb'b]⟩
      simpa only [D', RealTimeInterval.timeShift_carrier, Set.mem_ofPred_eq] using hs'
    have hregular' : Ioc 0 (b' - a) ⊆ D'.regular := by
      intro s hs
      have hs' : s + a ∈ D.regular :=
        hregular ⟨by linarith [hs.1], by linarith [hs.2, hb'b]⟩
      simpa only [D', RealTimeInterval.timeShift_regular, Set.mem_ofPred_eq] using hs'
    have hcomplete' : RiemannianMetricComplete (I := I) (S'.base.metric 0) := by
      simpa only [S', SolutionOn.timeShift_base_metric, zero_add] using hcomplete
    have hcurv'' : ∀ s ∈ Icc 0 (b' - a), ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I) S' 0 s y ≤ K := by
      intro s hs y
      rw [nablaKRm04NormSqIntrinsic_timeShift (I := I) S a s y]
      exact hcurvK (s + a) ⟨by linarith [hs.1], by linarith [hs.2, hb'b]⟩ y
    have hflat'' : ∀ y : M, nablaKRm04NormSqIntrinsic (I := I) S' 0 0 y ≤ 0 := by
      intro y
      rw [nablaKRm04NormSqIntrinsic_timeShift (I := I) S a 0 y, zero_add]
      exact hflat' y
    have hzero := curvature_normSq_eq_zero_on_Icc_at_zero (I := I) S' hS' hT hK
      hcarrier' hregular' hcomplete' hcurv'' hflat''
    intro t ht x
    have htmem : t - a ∈ Icc 0 (b' - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hz := hzero (t - a) htmem x
    rwa [nablaKRm04NormSqIntrinsic_timeShift (I := I) S a (t - a) x, sub_add_cancel] at hz
  have hclosed : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) = 0 := by
    intro t ht x
    have ht_lt_b' : t < (t + b) / 2 := by linarith [ht.2]
    have hb'_lt_b : (t + b) / 2 < b := by linarith [ht.2]
    have hab' : a < (t + b) / 2 := lt_of_le_of_lt ht.1 ht_lt_b'
    exact hstep ((t + b) / 2) hab' hb'_lt_b t ⟨ht.1, ht_lt_b'.le⟩ x
  intro t ht x
  have hclosure : closure (Ico a b) = Icc a b := closure_Ico hab.ne
  have hcont := rmNormSq_time_continuous (I := I) S hS a b hcarrier x
  have hle : normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 0 :=
    le_on_closure
      (f := fun r : ℝ => normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x))
      (g := fun _ : ℝ => (0 : ℝ))
      (fun r hr => le_of_eq (hclosed r hr x))
      (by rw [hclosure]; exact hcont)
      (by rw [hclosure]; exact continuousOn_const)
      (by rw [hclosure]; exact ht)
  exact le_antisymm hle (normSq0S_nonneg (I := I) (S.base.metric t) x 4 (S.base.rm04 t x))

end DifferentialGeometry.PDE.RicciFlow
