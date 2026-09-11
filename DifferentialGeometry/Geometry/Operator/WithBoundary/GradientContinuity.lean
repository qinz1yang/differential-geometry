import DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.ContinuousOn
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator


noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix BigOperators ENNReal

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
namespace DifferentialGeometry
namespace Geometry
namespace Operator
namespace WithBoundary

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure


private lemma partialDerivWithin_scalarOnE_continuousOn_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hpartial_target : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial_target.continuousOn


private lemma partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : M =>
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f) (extChartAt I α y))
      (chartAt H α).source := by
  have hpartial : ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_scalarOnE_continuousOn_target (I := I) α hf j
  have hchart : ContinuousOn (extChartAt I α : M → E) (chartAt H α).source := by
    have h1 : ContinuousOn (extChartAt I α : M → E) (extChartAt I α).source :=
      continuousOn_extChartAt (I := I) α
    refine h1.mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hmaps : Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
    intro x hx
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    exact (extChartAt I α).map_source hxsrc
  exact hpartial.comp hchart hmaps


private lemma gradChartCoeffWithin_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (gradChartCoeffWithin (I := I) g α f i) (chartAt H α).source := by
  classical
  have heq : ∀ y ∈ (chartAt H α).source,
      gradChartCoeffWithin (I := I) g α f i y =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α y i j *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α y) := by
    intro y _; rfl
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    have h2 : ContinuousOn
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet := h1.continuousOn
    refine h2.mono ?_
    intro y hy
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hy
  · exact partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
      (I := I) α hf j


private lemma chartGramMatrix_entry_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun y : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α y i j)
      (chartAt H α).source := by
  have h := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hcont : ContinuousOn (fun y : M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α y i j)
      (trivializationAt E (TangentSpace I) α).baseSet := h.continuousOn
  refine hcont.mono ?_
  intro y hy
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hy


private lemma g_inner_gradChartLocalWithin_expand
    (g : SmoothRiemannianMetric I M) (α : M) (f h : M → ℝ) (y : M) :
    g.inner y (gradChartLocalWithin (I := I) g α f y)
        (gradChartLocalWithin (I := I) g α h y) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            gradChartCoeffWithin (I := I) g α h j y *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α y i j := by
  classical
  unfold gradChartLocalWithin
  rw [show
        g.inner y (∑ i : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α f i y •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y)
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j y) =
        ∑ i : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            (g.inner y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y))
              (∑ j : Fin (Module.finrank ℝ E),
                gradChartCoeffWithin (I := I) g α h j y •
                  DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j y) from ?_]
  swap
  · rw [show g.inner y (∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y) =
            ∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                g.inner y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y) from ?_]
    · rw [sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (g.inner y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y))
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j y) =
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α h j y *
            g.inner y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i y)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j y) from ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
    ring
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul]
    rfl


private lemma g_inner_gradFun_gradFun_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ContinuousOn
      (fun y : M => g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y))
      (chartAt H α).source := by
  classical
  have h_rewrite : ∀ y ∈ (chartAt H α).source,
      g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y) =
        g.inner y (gradChartLocalWithin (I := I) g α f y)
          (gradChartLocalWithin (I := I) g α h y) := by
    intro y hy
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hf hy)]
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hh hy)]
  refine ContinuousOn.congr ?_ (fun y hy => h_rewrite y hy)
  refine ContinuousOn.congr (s := (chartAt H α).source) ?_
    (fun y _ => g_inner_gradChartLocalWithin_expand (I := I) g α f h y)
  refine continuousOn_finsetSum _ (fun i _ => ?_)
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hf i
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hh j
  · exact chartGramMatrix_entry_continuousOn_source (I := I) g α i j


theorem continuous_g_inner_gradFun_gradFun
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g h x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  have hcontOn :=
    g_inner_gradFun_gradFun_continuousOn_chart_source
      (I := I) (M := M) g x hf hh
  exact (hcontOn x hx_chart).continuousAt (hopen.mem_nhds hx_chart)

private lemma gradChartCoeffWithin_family_continuousOn_goodSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJreg : J ⊆ D.regular)
    (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M =>
        gradChartCoeffWithin (I := I) (G.metric p.1) α f i p.2)
      (J ×ˢ ((chartAt H α).source ∩ I.interior M)) := by
  classical
  let S : Set (ℝ × M) := J ×ˢ ((chartAt H α).source ∩ I.interior M)
  have hψ : ContinuousOn (fun p : ℝ × M => (p.1, extChartAt I α p.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun p hp => by
          rw [extChartAt_source_eq_chartAt_source (I := I)]
          exact hp.2.1)
  have hmaps : MapsTo (fun p : ℝ × M => (p.1, extChartAt I α p.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun p hp => ⟨hp.1,
      extChartAt_mem_interior_target_of_isInteriorPoint
        (I := I) α hp.2.1 hp.2.2⟩
  change ContinuousOn
    (fun p : ℝ × M =>
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (G.metric p.1) α p.2 i j *
          partialDerivWithin (E := E) (extChartAt I α).target j
            (scalarOnE (I := I) α f) (extChartAt I α p.2)) S
  refine continuousOn_finsetSum Finset.univ fun j _ => ?_
  have hinv :=
    (DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.chartInvGramOnE_continuousOn
      (I := I) hG hJreg α i j).comp hψ hmaps
  have hinv' : ContinuousOn
      (fun p : ℝ × M => chartInvGramMatrix (I := I) (G.metric p.1) α p.2 i j)
      S := by
    refine hinv.congr ?_
    intro p hp
    simp only [Function.comp_apply, chartInvGramOnE_def]
    rw [(extChartAt I α).left_inv
      (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hp.2.1)]
  have hpartial : ContinuousOn
      (fun p : ℝ × M =>
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f) (extChartAt I α p.2)) S :=
    (partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
      (I := I) α hf j).comp continuous_snd.continuousOn
        (fun p hp => hp.2.1)
  exact hinv'.mul hpartial

theorem gradient_inner_continuousOn_interior
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJreg : J ⊆ D.regular)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ContinuousOn
      (fun p : ℝ × M =>
        (G.metric p.1).inner p.2
          (gradFun (I := I) (G.metric p.1) f p.2)
          (gradFun (I := I) (G.metric p.1) h p.2))
      (J ×ˢ I.interior M) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let V : Set M := (chartAt H α).source ∩ I.interior M
  let U : Set (ℝ × M) := Set.univ ×ˢ V
  have hVopen : IsOpen V := (chartAt H α).open_source.inter
    (I.isOpen_interior (M := M) (n := ∞)
      (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0)))
  have hpU : p ∈ U := ⟨Set.mem_univ _, mem_chart_source H α, hp.2⟩
  refine ⟨U, isOpen_univ.prod hVopen, hpU, ?_⟩
  let S : Set (ℝ × M) := J ×ˢ V
  have hfcoeff : ∀ i, ContinuousOn
      (fun q : ℝ × M =>
        gradChartCoeffWithin (I := I) (G.metric q.1) α f i q.2) S :=
    fun i => gradChartCoeffWithin_family_continuousOn_goodSet
      (I := I) hG hJreg α hf i
  have hhcoeff : ∀ j, ContinuousOn
      (fun q : ℝ × M =>
        gradChartCoeffWithin (I := I) (G.metric q.1) α h j q.2) S :=
    fun j => gradChartCoeffWithin_family_continuousOn_goodSet
      (I := I) hG hJreg α hh j
  have hgram : ∀ i j, ContinuousOn
      (fun q : ℝ × M => chartGramMatrix (I := I) (G.metric q.1) α q.2 i j) S := by
    intro i j
    refine (hG.chartGramMatrix_continuousOn (I := I) hJreg α i j).mono ?_
    intro q hq
    refine ⟨hq.1, ?_⟩
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hq.2.1
  have hlocal : ContinuousOn
      (fun q : ℝ × M =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) (G.metric q.1) α f i q.2 *
              gradChartCoeffWithin (I := I) (G.metric q.1) α h j q.2 *
                chartGramMatrix (I := I) (G.metric q.1) α q.2 i j) S := by
    refine continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => ?_
    exact ((hfcoeff i).mul (hhcoeff j)).mul (hgram i j)
  refine (hlocal.congr ?_).mono ?_
  · intro q hq
    change (G.metric q.1).inner q.2
      (gradFun (I := I) (G.metric q.1) f q.2)
      (gradFun (I := I) (G.metric q.1) h q.2) = _
    rw [← gradChartLocalWithin_eq_gradFun (I := I) (G.metric q.1) α hf
      hq.2.1]
    rw [← gradChartLocalWithin_eq_gradFun (I := I) (G.metric q.1) α hh
      hq.2.1]
    exact g_inner_gradChartLocalWithin_expand
      (I := I) (G.metric q.1) α f h q.2
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

theorem gradient_inner_continuousOn_of_tsupport_subset_interior
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJreg : J ⊆ D.regular)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hfsupp : tsupport f ⊆ I.interior M) :
    ContinuousOn
      (fun p : ℝ × M =>
        (G.metric p.1).inner p.2
          (gradFun (I := I) (G.metric p.1) f p.2)
          (gradFun (I := I) (G.metric p.1) h p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  by_cases hpx : p.2 ∈ tsupport f
  · let U : Set (ℝ × M) := Set.univ ×ˢ I.interior M
    have hUopen : IsOpen U := isOpen_univ.prod
      (I.isOpen_interior (M := M) (n := ∞)
        (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0)))
    have hpU : p ∈ U := ⟨Set.mem_univ _, hfsupp hpx⟩
    refine ⟨U, hUopen, hpU, ?_⟩
    exact (gradient_inner_continuousOn_interior
      (I := I) hG hJreg hf hh).mono fun q hq => ⟨hq.1.1, hq.2.2⟩
  · let U : Set (ℝ × M) := Set.univ ×ˢ (tsupport f)ᶜ
    have hUopen : IsOpen U := isOpen_univ.prod (isClosed_tsupport f).isOpen_compl
    have hpU : p ∈ U := ⟨Set.mem_univ _, hpx⟩
    refine ⟨U, hUopen, hpU, ?_⟩
    have hzero : ContinuousOn (fun _ : ℝ × M => (0 : ℝ))
        ((J ×ˢ (Set.univ : Set M)) ∩ U) := continuousOn_const
    refine hzero.congr ?_
    intro q hq
    have hgrad : gradFun (I := I) (G.metric q.1) f q.2 = 0 := by
      by_contra hne
      exact hq.2.2 (support_gradFun_subset (I := I) (G.metric q.1) f hne)
    have hz : (G.metric q.1).inner q.2 (0 : TangentSpace I q.2) = 0 :=
      map_zero ((G.metric q.1).inner q.2)
    calc
      (G.metric q.1).inner q.2
          (gradFun (I := I) (G.metric q.1) f q.2)
          (gradFun (I := I) (G.metric q.1) h q.2) =
        (G.metric q.1).inner q.2 0
          (gradFun (I := I) (G.metric q.1) h q.2) := by rw [hgrad]
      _ = (0 : TangentSpace I q.2 →L[ℝ] ℝ)
          (gradFun (I := I) (G.metric q.1) h q.2) := by rw [hz]
      _ = 0 := rfl

end WithBoundary
end Operator
end Geometry
end DifferentialGeometry

namespace DifferentialGeometry
namespace Geometry
namespace Operator
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

theorem continuous_g_inner_gradFun_gradFun_euclideanHalfSpace
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
  continuous_g_inner_gradFun_gradFun
    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hf hh

theorem bddAbove_g_inner_gradFun_gradFun_of_compactSpace
    [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    BddAbove (Set.range (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))) := by
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun_euclideanHalfSpace (n := n) (M := M) g hf hh
  exact (isCompact_range hcont).bddAbove

private local instance instMeasurableSpaceM_gradContinuity :
    MeasurableSpace M := borel M
private local instance instBorelSpaceM_gradContinuity : BorelSpace M := ⟨rfl⟩

theorem integrable_g_inner_gradFun_gradFun
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Integrable (fun x : M =>
        g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
          (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  have : IsFiniteMeasure
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun_euclideanHalfSpace (n := n) (M := M) g hf hh
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end WithBoundary
end Operator
end Geometry
end DifferentialGeometry

end
