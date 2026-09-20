import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityHeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.BasepointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Smoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.DensityInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.WeakEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.RicciSoliton
import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceChart
import DifferentialGeometry.Geometry.Metric.Family.TimeComposition

noncomputable section
open Set Filter MeasureTheory
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure Entropy
open scoped _root_.Manifold ContDiff _root_.Topology NNReal ENNReal
universe u uH
variable {n : ℕ} {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
  (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem ancient_density_contDiffOn_in_chart_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c) (α : F.M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × EuclideanSpace ℝ (Fin n) => perelmanDensity n w.1
        (fun x => redLength F.S 0 p x w.1) ((extChartAt I α).symm w.2))
      (Ioo a b ×ˢ (extChartAt I α).target) := by
  let _ : NeZero n := ⟨by
    have hn := neZero_finrank_of_isAncientKappaSolution F hF
    simpa only [finrank_euclideanSpace_fin] using hn.out⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace F.M := ChartedSpace.locallyCompactSpace H F.M
  let Dr := RealTimeInterval.openInfinite 0 1 zero_lt_one
  have hGrev : MetricFamilySmoothOn Dr (fun t => F.S.base.metric (-t)) :=
    F.isSolution.smoothMetric.comp_time contDiff_id.neg.contDiffOn continuous_id.neg.continuousOn
      (fun t ht => show -t < 0 from neg_neg_of_pos ht)
      (fun t ht => show -t ≤ 0 from neg_nonpos.mpr ht.le)
  have hu := (ancient_perelmanDensity_locallyLipschitzOn_in_chart F hF p α).mono
    (show Ioo a b ×ˢ (extChartAt I α).target ⊆ Ioi 0 ×ˢ (extChartAt I α).target from
      fun _ hw => ⟨ha.trans hw.1.1, hw.2⟩)
  apply Analysis.Parabolic.contDiffOn_of_chart_weak_equation hGrev
    (fun t ht => ha.trans ht.1) α (isOpen_extChartAt_target (I := I) α)
    (by rw [(isOpen_extChartAt_target (I := I) α).interior_eq])
    (by simpa using hu)
  intro φ hφ hφc hφs
  simpa using (ancient_perelmanDensity_weak_eq_in_chart_of_constant_reducedVolume
    F hF p ha hab hmass α hφ hφc hφs).symm

theorem ancient_perelmanDensity_contMDiffOn_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun w : ℝ × F.M => perelmanDensity n w.1 (fun x => redLength F.S 0 p x w.1) w.2)
      (Ioo a b ×ˢ univ) := by
  intro w hw
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ]
  have hz : (w.1, extChartAt I w.2 w.2) ∈ Ioo a b ×ˢ (extChartAt I w.2).target :=
    ⟨hw.1, mem_extChartAt_target (I := I) w.2⟩
  have h := ((ancient_density_contDiffOn_in_chart_of_constant_reducedVolume F hF p ha hab hmass w.2).contDiffAt
      ((isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) w.2)).mem_nhds hz)).contMDiffAt
  simpa only [Function.comp_def, extChartAt_prod, PartialEquiv.prod_coe_symm,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    extChartAt_coe_symm, Function.id_def, PartialEquiv.prod_coe] using h

theorem ancient_redLength_contMDiffOn_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun w : ℝ × F.M => redLength F.S 0 p w.2 w.1) (Ioo a b ×ˢ univ) := by
  have hu := ancient_perelmanDensity_contMDiffOn_of_constant_reducedVolume F hF p ha hab hmass
  have ht (w : ℝ × F.M) (hw : w ∈ Ioo a b ×ˢ (univ : Set F.M)) : 0 < w.1 := ha.trans hw.1.1
  have hp (w : ℝ × F.M) (hw : w ∈ Ioo a b ×ˢ (univ : Set F.M)) :
      0 < perelmanDensity n w.1 (fun x => redLength F.S 0 p x w.1) w.2 :=
    mul_pos (prefactor_pos _ (ht w hw)) (Real.exp_pos _)
  have hf := contMDiffOn_perelmanPotential n
    (u := fun r => perelmanDensity n r (fun x => redLength F.S 0 p x r)) hu ht hp
  apply hf.congr
  intro w hw
  exact (congrFun (potential_density n (ht w hw) (fun x => redLength F.S 0 p x w.1)) w.2).symm

theorem ancient_perelmanDensity_isHeatPotOn_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c) :
    Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.openInterval a b ((a + b) / 2) ⟨by linarith, by linarith⟩)
      (reverseFamily (flowG F.S) 0) (fun r x => -F.S.scalar (-r) x)
      (fun r => perelmanDensity n r (fun x => redLength F.S 0 p x r)) := by
  have hu := ancient_perelmanDensity_contMDiffOn_of_constant_reducedVolume F hF p ha hab hmass
  refine ⟨hu, hu.continuousOn, ?_, ?_⟩
  · intro t ht
    have h := hu.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (s := (univ : Set F.M)) (fun y _ => ⟨ht, mem_univ y⟩)
    exact contMDiffOn_univ.mp h
  · intro t ht x
    have he := hasDerivAt_of_conjugate_heat_weak_equation F.S F.isSolution 0
      (u := fun r => perelmanDensity n r (fun x => redLength F.S 0 p x r)) isOpen_Ioo
      (fun r hr => show 0 - r < 0 from sub_neg.mpr (ha.trans hr.1)) hu (by
        intro α φ hφ hφc hφs
        simpa only [zero_sub, finrank_euclideanSpace_fin] using
          (ancient_perelmanDensity_weak_eq_in_chart_of_constant_reducedVolume
            F hF p ha hab hmass α hφ hφc hφs).symm) ht x
    simpa only [sub_eq_add_neg, zero_add, neg_mul] using he

theorem ancient_redLength_gradientRicciSoliton_and_hamiltonNormalized_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => redLength F.S 0 p x t),
      Geometry.gradientRicciSoliton (I := I) (F.S.base.metric (-t))
        ⟨fun x => redLength F.S 0 p x t, hf⟩ (1 / t) ∧
      Geometry.hamiltonNormalized (I := I) (F.S.base.metric (-t))
        ⟨fun x => redLength F.S 0 p x t, hf⟩ (1 / t) := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    neZero_finrank_of_isAncientKappaSolution F hF
  let Dr := RealTimeInterval.openInterval a b ((a + b) / 2) ⟨by linarith, by linarith⟩
  have hu := ancient_perelmanDensity_isHeatPotOn_of_constant_reducedVolume F hF p ha hab hmass
  have hpot := ancient_redLength_contMDiffOn_of_constant_reducedVolume F hF p ha hab hmass
  have hu' : Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (flowG F.S) 0) (fun r x => -F.S.scalar (0 - r) x)
      (fun r => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) r
        (fun x => redLength F.S 0 p x r)) := by
    simpa only [finrank_euclideanSpace_fin, zero_sub] using hu
  have h := gradientRicciSoliton_and_hamiltonNormalized_of_conjugate_density_and_hamilton_jacobi
    F.S F.isSolution 0 (fun r x => redLength F.S 0 p x r) hu' (show t ∈ Dr.regular from ht)
    (ha.trans ht.1) (show 0 - t ∈ ancientTimeInterval.regular by
      simpa only [zero_sub, ancientTimeInterval_regular, mem_Iio] using neg_neg_of_pos (ha.trans ht.1))
    (by
      intro r hr hrpos x
      have hnhds : Ioo a b ×ˢ (univ : Set F.M) ∈ 𝓝 (r, x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ x⟩
      have hmd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ)
          (fun w : ℝ × F.M => redLength F.S 0 p w.2 w.1) (r, x) :=
        (hpot.contMDiffAt hnhds).mdifferentiableAt
          (by simp)
      have hj := ancient_redLength_hamilton_jacobi_of_mdifferentiableAt_terminal F hF hrpos p x hmd
      change 2 * deriv (fun q => redLength F.S 0 p x q) r +
        (F.S.base.metric (0 - r)).inner x
          (gradientFun (F.S.base.metric (0 - r)) (fun y => redLength F.S 0 p y r) x)
          (gradientFun (F.S.base.metric (0 - r)) (fun y => redLength F.S 0 p y r) x) -
        F.S.scalar (0 - r) x + redLength F.S 0 p x r / r = 0
      simpa only [zero_sub] using hj)
  change ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => redLength F.S 0 p x t),
    Geometry.gradientRicciSoliton (I := I) (F.S.base.metric (0 - t))
      ⟨fun x => redLength F.S 0 p x t, hf⟩ (1 / t) ∧
    Geometry.hamiltonNormalized (I := I) (F.S.base.metric (0 - t))
      ⟨fun x => redLength F.S 0 p x t, hf⟩ (1 / t) at h
  simpa only [zero_sub] using h

theorem ancient_asymptoticReducedVolume_lt_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    asymptoticReducedVolume F.S 0 p < 1 := by
  apply lt_of_le_of_ne (ancient_asymptoticReducedVolume_le_one F hF p)
  intro heq
  have hmass (r : ℝ) (hr : 0 < r) : intrinsicReducedVolume F.S 0 p r = 1 := by
    apply le_antisymm (ancient_reducedVolume_le_one F hF le_rfl p hr)
    rw [← heq]
    exact asymptoticReducedVolume_le_redVolume F.S 0 p hr
  have hzero : F.S.scalar 0 p = 0 := by
    apply scalar_eq_zero_of_hamiltonNormalized_redLength F.S F.isSolution 0 p (delta := 1) zero_lt_one
      (fun s hs => show 0 - s ∈ ancientTimeInterval.carrier by
        simpa only [zero_sub, ancientTimeInterval_carrier, mem_Iic] using neg_nonpos.mpr hs.1)
      (fun s hs x => by
        simpa only [zero_sub] using ancientKappa_scalar_nonneg F hF (neg_nonpos.mpr hs.1) x)
    intro tau htau
    have ha : 0 < tau / 2 := half_pos htau.1
    have hab : tau / 2 < tau + 1 := by linarith
    have hvol : ∀ r ∈ Icc (tau / 2) (tau + 1), intrinsicReducedVolume F.S 0 p r = 1 :=
      fun r hr => hmass r (ha.trans_le hr.1)
    obtain ⟨hf, _, hn⟩ :=
      ancient_redLength_gradientRicciSoliton_and_hamiltonNormalized_of_constant_reducedVolume
        F hF p ha hab hvol (t := tau) ⟨half_lt_self htau.1, by linarith⟩
    exact ⟨hf, by simpa only [zero_sub] using hn⟩
  exact (ne_of_gt (ancientKappa_scalar_pos F hF le_rfl p)) hzero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
