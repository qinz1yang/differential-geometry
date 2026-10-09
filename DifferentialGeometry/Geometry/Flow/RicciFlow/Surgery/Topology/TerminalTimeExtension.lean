import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

noncomputable section

open Filter Set Bundle Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance terminalSigmaCompact : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
private local instance terminalC1 : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalC2 : IsManifold ThreeModel 2 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

def TerminalLimitMetric.extendedMetric (L : G.TerminalLimitMetric) (t : ℝ) :
    SmoothRiemannianMetric ThreeModel G.terminalRegularOpen :=
  if t < s then (G.flow.base.metric t).restrictOpen G.terminalRegularOpen else L.metric

@[simp] theorem TerminalLimitMetric.extendedMetric_terminal (L : G.TerminalLimitMetric) :
    L.extendedMetric s = L.metric := by simp [extendedMetric]

theorem TerminalLimitMetric.extendedMetric_before (L : G.TerminalLimitMetric)
    {t : ℝ} (ht : t < s) :
    L.extendedMetric t = (G.flow.base.metric t).restrictOpen G.terminalRegularOpen :=
  ite_eq_left ht

private theorem continuousWithinAt_terminal_of_uniform
    {Y Z : Type*} [TopologicalSpace Y] [PseudoMetricSpace Z]
    {F : ℝ → Y → Z} {W : Set Y} {b : ℝ} {y : Y}
    (hF : TendstoUniformlyOn F (F b) (𝓝[<] b) W)
    (hcont : ContinuousWithinAt (F b) W y) :
    ContinuousWithinAt (fun q : ℝ × Y => F q.1 q.2) (Iic b ×ˢ W) (b, y) := by
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ t in 𝓝[<] b, ∀ z ∈ W, dist (F t z) (F b z) < ε / 2 := by
    have h := Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (half_pos hε)
    exact h.mono fun t ht z hz => by simpa only [dist_comm] using ht z hz
  have hcloseLE : ∀ᶠ t in 𝓝[≤] b, ∀ z ∈ W, dist (F t z) (F b z) < ε / 2 := by
    rw [← Iio_insert, nhdsWithin_insert, eventually_sup, eventually_pure]
    exact ⟨fun z _ => by simpa only [dist_self] using half_pos hε, hclose⟩
  have hsmall : ∀ᶠ z in 𝓝[W] y, dist (F b z) (F b y) < ε / 2 :=
    Metric.tendsto_nhds.mp hcont (ε / 2) (half_pos hε)
  filter_upwards [hcloseLE.prod_mk (hsmall.and self_mem_nhdsWithin)] with q hq
  exact (dist_triangle (F q.1 q.2) (F b q.2) (F b y)).trans_lt
    ((add_lt_add (hq.1 q.2 hq.2.2) hq.2.1).trans_eq (add_halves ε))


theorem TerminalLimitMetric.chartGram_jets_tendsto_terminal
    (L : G.TerminalLimitMetric) (p x : G.terminalRegularOpen)
    (hxchart : x ∈ (chartAt ThreeSpace p).source) :
    ∃ W : Set ThreeSpace, IsOpen W ∧ extChartAt ThreeModel p x ∈ W ∧
      W ⊆ (extChartAt ThreeModel p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ ThreeSpace),
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartGramOnE (I := ThreeModel) (L.extendedMetric t) p i j))
          (iteratedFDeriv ℝ r (chartGramOnE (I := ThreeModel) L.metric p i j))
          (𝓝[<] s) W := by
  let _ : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  obtain ⟨K, hK, hxK, hKchart⟩ := exists_compact_between isCompact_singleton
    (chartAt ThreeSpace p).open_source (singleton_subset_iff.mpr hxchart)
  let W : Set ThreeSpace := (extChartAt ThreeModel p).target ∩
    (extChartAt ThreeModel p).symm ⁻¹' interior K
  have hW : IsOpen W := (continuousOn_extChartAt_symm (I := ThreeModel) p).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ThreeModel) p) isOpen_interior
  have hxs : x ∈ (extChartAt ThreeModel p).source := by
    simpa only [extChartAt_source] using hxchart
  have hxW : extChartAt ThreeModel p x ∈ W := by
    refine ⟨(extChartAt ThreeModel p).map_source hxs, ?_⟩
    change (extChartAt ThreeModel p).symm (extChartAt ThreeModel p x) ∈ interior K
    rw [(extChartAt ThreeModel p).left_inv hxs]
    exact hxK (mem_singleton x)
  refine ⟨W, hW, hxW, inter_subset_left, ?_⟩
  intro r i j
  obtain ⟨C, hC, hbound⟩ := chartJet_sub_le (I := ThreeModel) L.metric p hK hKchart r
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (2 * (C + 1) * ((r : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpoint (q : Fin (r + 1)) : ∀ᶠ t in 𝓝[<] s, ∀ y ∈ K,
      metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric L.metric y < δ := by
    obtain ⟨d, hd, hb⟩ := L.converges K hK q δ hδ
    have ht : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo d s := Ioo_mem_nhdsLT hd.2
    exact ht.mono fun t ht => hb t ht
  have hall := eventually_all.mpr hpoint
  have htime : ∀ᶠ t in 𝓝[<] s, t < s := self_mem_nhdsWithin
  filter_upwards [hall, htime] with t ht hts
  intro y hy
  let z := (extChartAt ThreeModel p).symm y
  have hzK : z ∈ K := interior_subset hy.2
  have hzy : extChartAt ThreeModel p z = y := (extChartAt ThreeModel p).right_inv hy.1
  have hsum : (∑ q ∈ Finset.range (r + 1), metricDerivNorm q
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric z) ≤
      ((r : ℝ) + 1) * δ := by
    calc
      _ ≤ ∑ _q ∈ Finset.range (r + 1), δ := Finset.sum_le_sum fun q hq =>
        (ht ⟨q, Finset.mem_range.mp hq⟩ z hzK).le
      _ = _ := by simp
  have hsmall : C * (((r : ℝ) + 1) * δ) < ε := by
    have hden : 0 < 2 * (C + 1) * ((r : ℝ) + 1) := by positivity
    have hprod : C * (((r : ℝ) + 1) * δ) ≤ ε / 2 := by
      dsimp [δ]
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) hε.le]
    linarith
  rw [L.extendedMetric_before hts, dist_comm, dist_eq_norm]
  have h := (hbound ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
    L.metric z hzK i j).trans (mul_le_mul_of_nonneg_left hsum hC)
  simpa only [hzy] using h.trans_lt hsmall


theorem TerminalLimitMetric.chartGram_jets_continuousOn_closed
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b)
    (p : G.terminalRegularOpen) (r : ℕ)
    (i j : Fin (Module.finrank ℝ ThreeSpace)) :
    ContinuousOn (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
      (chartGramOnE (I := ThreeModel) (L.extendedMetric q.1) p i j) q.2)
      (Icc b s ×ˢ (extChartAt ThreeModel p).target) := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  by_cases hts : t = s
  · subst t
    have hxchart : (extChartAt ThreeModel p).symm y ∈ (chartAt ThreeSpace p).source := by
      simpa only [extChartAt_source] using (extChartAt ThreeModel p).map_target hy
    obtain ⟨W, hW, hyW, _, hlim⟩ := L.chartGram_jets_tendsto_terminal
      p ((extChartAt ThreeModel p).symm y) hxchart
    rw [(extChartAt ThreeModel p).right_inv hy] at hyW
    have hspatial : ContinuousAt
        (iteratedFDeriv ℝ r (chartGramOnE (I := ThreeModel) L.metric p i j)) y :=
      ((chartGramOnE_contDiffOn (I := ThreeModel) L.metric p i j).contDiffAt
        ((isOpen_extChartAt_target (I := ThreeModel) p).mem_nhds hy)).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)
    have hlim' : TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
        (chartGramOnE (I := ThreeModel) (L.extendedMetric t) p i j))
        (iteratedFDeriv ℝ r (chartGramOnE (I := ThreeModel) (L.extendedMetric s) p i j))
        (𝓝[<] s) W := by simpa only [L.extendedMetric_terminal] using hlim r i j
    have hlocal := continuousWithinAt_terminal_of_uniform hlim'
      (by simpa only [L.extendedMetric_terminal] using hspatial.continuousWithinAt)
    have hfull : ContinuousWithinAt (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
        (chartGramOnE (I := ThreeModel) (L.extendedMetric q.1) p i j) q.2)
        (Iic s ×ˢ (univ : Set ThreeSpace)) (s, y) := by
      simpa only [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ,
        nhdsWithin_eq_nhds.mpr (hW.mem_nhds hyW)] using hlocal
    exact hfull.mono (fun q hq => ⟨hq.1.2, mem_univ _⟩)
  · have htreg : t ∈ Ico a s := ⟨hab.trans ht.1, lt_of_le_of_ne ht.2 hts⟩
    have hsmooth := chartGramOnE_joint_contDiffOn
      (fun t => (G.flow.base.metric t).restrictOpen G.terminalRegularOpen) (Ico a s)
      (G.smoothUpTo.restrictOpen_jointContMDiffOn G.terminalRegularOpen) p i j
    have hjet := DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn
      (G := fun t y => chartGramOnE (I := ThreeModel)
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) p i j y)
      (isOpen_extChartAt_target p) hsmooth r
    have hlocal := hjet.continuousOn (t, y) ⟨htreg, hy⟩
    have hregion : (Ico a s ×ˢ (extChartAt ThreeModel p).target) ∈
        𝓝[Icc b s ×ˢ (extChartAt ThreeModel p).target] (t, y) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (continuous_fst.continuousAt.preimage_mem_nhds
          (Iio_mem_nhds htreg.2))] with q hq htq
      exact ⟨⟨hab.trans hq.1.1, htq⟩, hq.2⟩
    apply (hlocal.mono_of_mem_nhdsWithin hregion).congr_of_eventuallyEq_of_mem _ ⟨ht, hy⟩
    filter_upwards [nhdsWithin_le_nhds (continuous_fst.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds htreg.2))] with q hq
    rw [L.extendedMetric_before hq]


theorem TerminalLimitMetric.extendedMetric_hasDerivAt
    (L : G.TerminalLimitMetric) {t : ℝ} (ht : t ∈ Ioo a s)
    (x : G.terminalRegularOpen) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => (L.extendedMetric u).inner x v w)
      (-2 * ricciTensor (L.extendedMetric t) x v w) t := by
  have hd := metricDerivAt G.flow G.equation ⟨t, ht⟩ x.1 v w
  have hric := metricRicciAt_apply_eq_ricciTensor (G.flow.base.metric t) x.1 v w
  dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
  erw [hric] at hd
  have hderiv : HasDerivAt
      (fun u => ((G.flow.base.metric u).restrictOpen G.terminalRegularOpen).inner x v w)
      (-2 * ricciTensor ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x v w) t := by
    simpa only [SolutionOn.family_metric, SmoothRiemannianMetric.restrictOpen_inner,
      DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
      DifferentialGeometry.mfderiv_subtype_val_apply] using hd
  rw [L.extendedMetric_before ht.2]
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht.2] with u hu
  rw [L.extendedMetric_before hu]

theorem TerminalLimitMetric.chartGram_contDiffOn_closed
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b) (hbs : b < s)
    (p : G.terminalRegularOpen) (i j : Fin (Module.finrank ℝ ThreeSpace)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ThreeSpace =>
      chartGramOnE (I := ThreeModel) (L.extendedMetric q.1) p i j q.2)
      (Icc b s ×ˢ (extChartAt ThreeModel p).target) := by
  have hpde := fun t (ht : t ∈ Ioo b s) x v w =>
    L.extendedMetric_hasDerivAt ⟨hab.trans_lt ht.1, ht.2⟩ x v w
  have hfull := chartGram_contDiffOn_of_spatialJets (I := ThreeModel) L.extendedMetric p hbs
    (isOpen_extChartAt_target p) Subset.rfl
    (fun r i j => L.chartGram_jets_continuousOn_closed hab p r i j) hpde
  exact contDiffOn_pi.mp (contDiffOn_pi.mp hfull i) j

theorem TerminalLimitMetric.extendedMetric_jointContMDiffOn
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b) (hbs : b < s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × G.terminalRegularOpen =>
        (⟨q.2, (L.extendedMetric q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ]
              TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc b s ×ˢ (univ : Set G.terminalRegularOpen)) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on L.extendedMetric (Icc b s)
  intro p i j
  have hgram := L.chartGram_contDiffOn_closed hab hbs p i j
  have hsource {y : G.terminalRegularOpen}
      (hy : y ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
      y ∈ (extChartAt ThreeModel p).source := by
    rwa [extChartAt_source_eq_chartAt_source,
      ← trivializationAt_baseSet_eq_chartAt_source (I := ThreeModel)]
  have harg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ × ThreeSpace)) ∞
      (fun q : ℝ × G.terminalRegularOpen => (q.1, extChartAt ThreeModel p q.2))
      (Icc b s ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_fst.prodMk
      ((contMDiffOn_extChartAt (I := ThreeModel) (x := p)).comp contMDiffOn_snd
        (fun q hq => by
          simpa only [Set.mem_preimage, trivializationAt_baseSet_eq_chartAt_source] using hq.2))
  have hh := hgram.contMDiffOn.comp harg (fun q hq =>
    ⟨hq.1, (extChartAt ThreeModel p).map_source (hsource hq.2)⟩)
  apply hh.congr
  intro q hq
  change chartGramMatrix (L.extendedMetric q.1) p q.2 i j =
    chartGramMatrix (L.extendedMetric q.1) p
      ((extChartAt ThreeModel p).symm (extChartAt ThreeModel p q.2)) i j
  rw [(extChartAt ThreeModel p).left_inv (hsource hq.2)]


theorem TerminalLimitMetric.chartGram_timeJets_contDiffOn_closed
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b) (hbs : b < s)
    (p : G.terminalRegularOpen) (i j : Fin (Module.finrank ℝ ThreeSpace)) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ThreeSpace => iteratedDerivWithin m
      (fun t => chartGramOnE (I := ThreeModel) (L.extendedMetric t) p i j q.2)
      (Icc b s) q.1) (Icc b s ×ˢ (extChartAt ThreeModel p).target) :=
  Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_iteratedDerivWithin_time
    (uniqueDiffOn_Icc hbs) (isOpen_extChartAt_target p)
    (L.chartGram_contDiffOn_closed hab hbs p i j) m

theorem TerminalLimitMetric.hasDerivWithinAt_chartGram_timeJet
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b) (hbs : b < s)
    (p : G.terminalRegularOpen) (i j : Fin (Module.finrank ℝ ThreeSpace)) (m : ℕ)
    {t : ℝ} (ht : t ∈ Icc b s) {y : ThreeSpace}
    (hy : y ∈ (extChartAt ThreeModel p).target) :
    HasDerivWithinAt (iteratedDerivWithin m
      (fun u => chartGramOnE (I := ThreeModel) (L.extendedMetric u) p i j y) (Icc b s))
      (iteratedDerivWithin (m + 1)
        (fun u => chartGramOnE (I := ThreeModel) (L.extendedMetric u) p i j y) (Icc b s) t)
      (Icc b s) t :=
  Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_iteratedDerivWithin_time
    (uniqueDiffOn_Icc hbs) (isOpen_extChartAt_target p)
    (L.chartGram_contDiffOn_closed hab hbs p i j) m ht hy

theorem TerminalLimitMetric.chartGram_mixedJets_contDiffOn_closed
    (L : G.TerminalLimitMetric) {b : ℝ} (hab : a ≤ b) (hbs : b < s)
    (p : G.terminalRegularOpen) (i j : Fin (Module.finrank ℝ ThreeSpace)) (r m : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
      (fun y => iteratedDerivWithin m
        (fun t => chartGramOnE (I := ThreeModel) (L.extendedMetric t) p i j y)
          (Icc b s) q.1) q.2) (Icc b s ×ˢ (extChartAt ThreeModel p).target) :=
  Perelman.KappaSolutions.spatial_iteratedFDeriv_contDiffOn
    (G := fun t y => iteratedDerivWithin m
      (fun u => chartGramOnE (I := ThreeModel) (L.extendedMetric u) p i j y) (Icc b s) t)
    (isOpen_extChartAt_target p) (L.chartGram_timeJets_contDiffOn_closed hab hbs p i j m) r

theorem TerminalLimitMetric.metricTensor_contDiffOn_time
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcb : c < s) (x : G.terminalRegularOpen) :
    ContDiffOn ℝ ∞ (fun t => metricTensorField (L.extendedMetric t) x) (Icc c s) := by
  classical
  let V := (extChartAt ThreeModel x).target
  have hxV : extChartAt ThreeModel x x ∈ V :=
    (extChartAt ThreeModel x).map_source (mem_extChartAt_source x)
  have hgram := L.chartGram_contDiffOn_closed hac hcb x
  have hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet :=
    mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) x
  let basis := chartBasisFamily (I := ThreeModel) x hx
  have hc (slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace)) :
      ContDiffOn ℝ ∞
        (fun t => component0S (I := ThreeModel) basis
          (metricTensorField (L.extendedMetric t) x) slots)
        (Icc c s) := by
    have hm := (hgram (slots 0) (slots 1)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hxV⟩)
    apply hm.congr
    intro t _ht
    simp only [Function.comp_def, id_eq, component0S_apply, metricTensorField_apply,
      basis, chartBasisFamily_apply, chartGramOnE, chartGramMatrix_apply]
    erw [(extChartAt ThreeModel x).left_inv (mem_extChartAt_source x)]
  have hsum : ContDiffOn ℝ ∞
      (fun t => ∑ slots, component0S (I := ThreeModel) basis
        (metricTensorField (L.extendedMetric t) x) slots •
        tensor0SBasis (I := ThreeModel) basis 2 slots) (Icc c s) :=
    ContDiffOn.sum fun slots _ => (hc slots).smul_const _
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

private theorem metric_timeJet_eval
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcb : c < s)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c s) (x : G.terminalRegularOpen)
    (v : Fin 2 → TangentSpace ThreeModel x) :
    iteratedDerivWithin q (fun s => (L.extendedMetric s).inner x (v 0) (v 1)) (Icc c s) t =
      (iteratedDerivWithin q (fun s => metricTensorField (L.extendedMetric s) x)
        (Icc c s) t) v := by
  have hq : (q : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hh := (tensor0SEvalCLM (I := ThreeModel) v).iteratedFDerivWithin_comp_left
    (L.metricTensor_contDiffOn_time hac hcb x t ht)
    (uniqueDiffOn_Icc hcb) ht hq
  have he := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin q => ℝ) ℝ =>
    A (fun _ => 1)) hh
  exact he

private theorem exists_field_of_chart_components
    (T : (x : G.terminalRegularOpen) →
      Bundle.continuousMultilinearMap ℝ 2 ThreeSpace (TangentSpace ThreeModel) x)
    (hT : ∀ p : G.terminalRegularOpen, ∀ slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace),
      ContMDiffAt ThreeModel 𝓘(ℝ) ∞
        (fun x => T x (fun k => chartBasisVecFiber (I := ThreeModel) p (slots k) x)) p) :
    ∃ B : Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) (n := ∞) 2,
      ∀ x, B x = T x := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (I := ThreeModel) (M := G.terminalRegularOpen) 2
  refine ⟨⟨T, ?_⟩, fun _ => rfl⟩
  let basis := chartModelBasis ThreeSpace
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace ThreeModel) ∞ basis T).mpr ?_
  intro slots p
  refine (hT p slots).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  let e := trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  have hrepr := continuousMultilinearMap_basis_repr (𝕜 := ℝ) basis 2
    ((trivializationAt (Tensor0SModel 2 ℝ ThreeSpace)
      (Bundle.continuousMultilinearMap ℝ 2 ThreeSpace (TangentSpace ThreeModel)) p)
        ⟨x, T x⟩).2 slots
  refine hrepr.trans ?_
  change (tensor0SSpaceFiberContinuousLinearEquiv (I := ThreeModel)
    (M := G.terminalRegularOpen) 2 x (T x)).compContinuousLinearMap
    (fun _ : Fin 2 => e.symmL ℝ x) (fun k => basis (slots k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact tensor0SSpaceFiberContinuousLinearEquiv_apply_apply (I := ThreeModel) 2 x (T x)
    (fun k => chartBasisVecFiber (I := ThreeModel) p (slots k) x)

private theorem exists_metric_timeJet_field
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcb : c < s)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c s) :
    ∃ B : Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) (n := ∞) 2,
      ∀ x, B x = iteratedDerivWithin q
        (fun s => metricTensorField (L.extendedMetric s) x) (Icc c s) t := by
  let T := fun x => iteratedDerivWithin q
    (fun s => metricTensorField (L.extendedMetric s) x) (Icc c s) t
  apply exists_field_of_chart_components T
  intro p slots
  let V := (extChartAt ThreeModel p).target
  have hV : IsOpen V := isOpen_extChartAt_target p
  have hpV : extChartAt ThreeModel p p ∈ V :=
    (extChartAt ThreeModel p).map_source (mem_extChartAt_source p)
  have hjets := fun q i j => L.chartGram_timeJets_contDiffOn_closed hac hcb p i j q
  have hmaps : MapsTo (fun y : ThreeSpace => (t, y)) V (Icc c s ×ˢ V) := fun _ hy => ⟨ht, hy⟩
  have hcoord : ContDiffOn ℝ ∞ (fun y => iteratedDerivWithin q
      (fun s => chartGramOnE (I := ThreeModel) (L.extendedMetric s) p (slots 0) (slots 1) y)
      (Icc c s) t) V :=
    (hjets q (slots 0) (slots 1)).comp (f := fun y : ThreeSpace => (t, y))
      (contDiffOn_const.prodMk contDiffOn_id) hmaps
  have hlocal : ContMDiffAt ThreeModel 𝓘(ℝ) ∞
      (fun x : G.terminalRegularOpen => iteratedDerivWithin q
      (fun s => chartGramOnE (I := ThreeModel) (L.extendedMetric s) p (slots 0) (slots 1)
        (extChartAt ThreeModel p x)) (Icc c s) t) p :=
    (hcoord.contDiffAt (hV.mem_nhds hpV)).contMDiffAt.comp p
      (contMDiffAt_extChartAt (I := ThreeModel) (x := p))
  refine hlocal.congr_of_eventuallyEq ?_
  let e := trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  filter_upwards [e.open_baseSet.mem_nhds hp] with x hx
  change (iteratedDerivWithin q (fun s => metricTensorField (L.extendedMetric s) x) (Icc c s) t)
    (fun k => chartBasisVecFiber (I := ThreeModel) p (slots k) x) = _
  rw [← metric_timeJet_eval L hac hcb q ht x
    (fun k => chartBasisVecFiber (I := ThreeModel) p (slots k) x)]
  have hxs : x ∈ (extChartAt ThreeModel p).source := by
    simpa only [e, trivializationAt_baseSet_eq_chartAt_source, extChartAt_source_eq_chartAt_source]
      using hx
  apply congrArg (fun f : ℝ → ℝ => iteratedDerivWithin q f (Icc c s) t)
  funext s
  simp only [chartGramOnE, chartGramMatrix_apply, (extChartAt ThreeModel p).left_inv hxs]


theorem TerminalLimitMetric.exists_time_derivative_fields
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcb : c < s) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      ∀ q t, t ∈ Icc c s → ∀ x,
        B q t x = iteratedDerivWithin q
          (fun s => metricTensorField (L.extendedMetric s) x) (Icc c s) t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c s) t := by
  classical
  choose C hC using fun q (t : Icc c s) =>
    exists_metric_timeJet_field L hac hcb (q + 1) t.property
  let B : ℕ → ℝ → Tensor0SField (I := ThreeModel)
      (M := G.terminalRegularOpen) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (L.extendedMetric t)
    | q + 1 => if ht : t ∈ Icc c s then C q ⟨t, ht⟩ else 0
  have hB (q : ℕ) (t : ℝ) (ht : t ∈ Icc c s) (x : G.terminalRegularOpen) :
      B q t x = iteratedDerivWithin q
        (fun s => metricTensorField (L.extendedMetric s) x) (Icc c s) t := by
    cases q with
    | zero => simp only [B, iteratedDerivWithin_zero]
    | succ q => simpa only [B, dite_eq_left ht] using hC q ⟨t, ht⟩ x
  refine ⟨B, fun _ => rfl, ?_⟩
  intro q t ht x
  refine ⟨hB q t ht x, ?_⟩
  have hq : (q : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top q)
  have hf := L.metricTensor_contDiffOn_time hac hcb x
  have hd := (hf.differentiableOn_iteratedDerivWithin hq
    (uniqueDiffOn_Icc hcb) t ht).hasDerivWithinAt
  rw [← iteratedDerivWithin_succ] at hd
  exact (hd.congr_deriv (hB (q + 1) t ht x).symm).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hB q s hs x) (hB q t ht x)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
