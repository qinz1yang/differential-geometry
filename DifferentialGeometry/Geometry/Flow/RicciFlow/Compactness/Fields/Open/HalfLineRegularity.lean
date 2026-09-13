import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineFlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Metric.Family.Continuity

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace HalfLineMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)] in
theorem gramSmooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (x₀ : P.M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Iio 0 ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro x₀ i j p hp
  have hp1 : p.1 < 0 := hp.1
  obtain ⟨n, hn⟩ := exists_nat_gt (-p.1)
  have hmemI : p.1 < p.1 / 2 := by linarith
  have hhalf : p.1 / 2 < 0 := by linarith
  have hβ : -(n : ℝ) < p.1 := by linarith
  have hwin : Set.Icc (-(n : ℝ)) (p.1 / 2) ⊆ X.D.regular :=
    fun s hs => hreg (lt_of_le_of_lt hs.2 hhalf)
  have hsub : Set.Icc (-(n : ℝ)) (p.1 / 2) ⊆ Set.Icc (-(n : ℝ)) 0 :=
    fun s hs => ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 hhalf)⟩
  have hlocal := FlowMetricConvergenceData.gramSmooth (I := I) (Φ := Φ) hwin
    (FlowMetricConvergenceData.restrict (Φ := Φ)
      (HalfLineMetricConvergenceData.atWindow Φ co n) hsub) x₀ i j p
    ⟨⟨hβ, hmemI⟩, hp.2⟩
  have hnhds : Set.Ioo (-(n : ℝ)) (p.1 / 2) ×ˢ
      (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 p :=
    prod_mem_nhds (Ioo_mem_nhds hβ hmemI)
      ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hp.2)
  exact (hlocal.contMDiffAt hnhds).contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCLMSection_smooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((co.gInf q.1).inner q.2))
      (Set.Iio 0 ×ˢ (Set.univ : Set P.M)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro q hq
  have hq1 : q.1 < 0 := hq.1
  obtain ⟨n, hn⟩ := exists_nat_gt (-q.1)
  have hmemI : q.1 < q.1 / 2 := by linarith
  have hhalf : q.1 / 2 < 0 := by linarith
  have hβ : -(n : ℝ) < q.1 := by linarith
  have hgram : ∀ (x₀ : P.M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo (-(n : ℝ)) (q.1 / 2) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (gramSmooth (I := I) (Φ := Φ) co hreg x₀ i j).mono
      (Set.prod_mono (fun s hs => lt_of_lt_of_le hs.2 hhalf.le) Set.Subset.rfl)
  have hlocal := metricCLMSection_jointContMDiffOn_of_chartGram_Ioo (I := I) co.gInf
    (-(n : ℝ)) (q.1 / 2) hgram
  have hnhds : Set.Ioo (-(n : ℝ)) (q.1 / 2) ×ˢ (Set.univ : Set P.M) ∈ 𝓝 q :=
    prod_mem_nhds (Ioo_mem_nhds hβ hmemI) Filter.univ_mem
  exact (hlocal.contMDiffAt hnhds).contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem metric_cont
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : Set.Iic 0 ⊆ X.D.carrier) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 (Set.Iic 0)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  refine tensor0SFamilyContinuousOnSet.of_locally (I := I) (M := P.M) (s := 2)
    (K := Set.Iic 0) (A := fun t x => Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x) ?_
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt (-t)
  have hβ : -(n : ℝ) < t := by linarith
  have ht0 : t ≤ (0 : ℝ) := ht
  refine ⟨Set.Ioo ((t - (n : ℝ)) / 2) 1, isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
  have hwin : Set.Icc (-(n : ℝ)) 0 ⊆ X.D.carrier :=
    fun s hs => hcarrier hs.2
  have hper := FlowMetricConvergenceData.metric_cont (I := I) (Φ := Φ) hwin
    (HalfLineMetricConvergenceData.atWindow Φ co n)
  have hsub : Set.Iic 0 ∩ Set.Ioo ((t - (n : ℝ)) / 2) 1 ⊆ Set.Icc (-(n : ℝ)) 0 := by
    intro s hs
    exact ⟨by linarith [hs.2.1, hβ], hs.1⟩
  exact hper.mono hsub

omit [NeZero (Module.finrank ℝ E)] in
theorem metricSmooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier = Set.Iic 0)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    MetricFamilySmoothOn (I := I) (M := P.M) X.D co.gInf := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hreg_le : X.D.regular ⊆ Set.Iio 0 := by
    have hsub : X.D.regular ⊆ Set.Iic 0 := by
      intro s hs
      rw [← hcarrier]
      exact X.D.regular_subset hs
    have h : X.D.regular ⊆ interior (Set.Iic (0 : ℝ)) := by
      rw [← X.D.regular_isOpen.interior_eq]
      exact interior_mono hsub
    rwa [interior_Iic] at h
  have hsec := metricCLMSection_smooth (I := I) (Φ := Φ) co hreg
  have hcontTensor : tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 X.D.carrier
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (co.gInf t) x) :=
    (metric_cont (I := I) (Φ := Φ) co (le_of_eq hcarrier.symm)).mono
      (le_of_eq hcarrier)
  refine ⟨?_, ?_, hcontTensor, ?_⟩
  · intro x v w
    have hψ' : ContMDiffOn 𝓘(ℝ, ℝ)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun t : ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
          ((co.gInf t).inner x)) X.D.regular :=
      hsec.comp (contMDiffOn_id.prodMk contMDiffOn_const)
        (fun t ht => ⟨hreg_le ht, Set.mem_univ x⟩)
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E
          (E := fun y => TangentSpace I y) x v) X.D.regular :=
      contMDiffOn_const
    have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E
          (E := fun y => TangentSpace I y) x w) X.D.regular :=
      contMDiffOn_const
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := P.M)) (E₂ := TangentSpace I (M := P.M))
      (E₃ := Bundle.Trivial P.M ℝ) (b := fun _ : ℝ => x)
      (ψ := fun t : ℝ => (co.gInf t).inner x)
      (v := fun _ : ℝ => v) (w := fun _ : ℝ => w) hψ' hv hw
    have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (co.gInf t).inner x v w) X.D.regular := by
      intro t ht
      have hpt := happ t ht
      rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
      exact hpt.2
    exact hscalar.contDiffOn
  · intro x v w
    have hbase : ContinuousOn
        (fun s : ℝ => Tensor0SBundle.metricTensorField (I := I) (co.gInf s) x (vec2 v w))
        X.D.carrier := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hcontTensor.eval_continuous
        (P := {s : ℝ // s ∈ X.D.carrier})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun p => p.2) continuous_const
        (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    refine hbase.congr (fun s _ => ?_)
    simp [metricTensorField_apply, vec2]
  · intro Idx _ frame u hframe i j
    refine contMDiffOn_of_locally_contMDiffOn (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ))
      (n := ∞) (s := X.D.regular ×ˢ u)
      (f := fun p : ℝ × P.M => (co.gInf p.1).inner p.2 (frame i p.2) (frame j p.2)) ?_
    intro p hp
    have hp1 : p.1 < 0 := hreg_le hp.1
    have hmemI : p.1 < p.1 / 2 := by linarith
    have hhalf : p.1 / 2 < 0 := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (-p.1)
    have hβ : -(n : ℝ) < p.1 := by linarith
    refine ⟨Set.Ioo (-(n : ℝ)) (p.1 / 2) ×ˢ (Set.univ : Set P.M),
      isOpen_Ioo.prod isOpen_univ, ⟨⟨hβ, hmemI⟩, Set.mem_univ _⟩, ?_⟩
    have hgram : ∀ (x₀ : P.M) (i j : Fin (Module.finrank Real E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × P.M =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
              (co.gInf q.1) x₀ q.2 i j)
          (Set.Ioo (-(n : ℝ)) (p.1 / 2) ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun x₀ i j => (gramSmooth (I := I) (Φ := Φ) co hreg x₀ i j).mono
        (Set.prod_mono (fun s hs => lt_of_lt_of_le hs.2 hhalf.le) Set.Subset.rfl)
    refine (metricFrameComp_jointContMDiffOn_of_chartGram (I := I) co.gInf
      (-(n : ℝ)) (p.1 / 2) hgram frame hframe i j).mono ?_
    rintro ⟨t, x⟩ ⟨⟨htR, hxu⟩, htI, _⟩
    exact ⟨htI, hxu⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem regular_subset_Iio
    (hcarrier : X.D.carrier = Set.Iic 0) :
    X.D.regular ⊆ Set.Iio 0 := by
  have hsub : X.D.regular ⊆ Set.Iic 0 := by
    intro s hs
    rw [← hcarrier]
    exact X.D.regular_subset hs
  have h : X.D.regular ⊆ interior (Set.Iic (0 : ℝ)) := by
    rw [← X.D.regular_isOpen.interior_eq]
    exact interior_mono hsub
  rwa [interior_Iic] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciCont_regular
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier = Set.Iic 0)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 X.D.regular
      (fun t x => metricRicciAt (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  exact (ricciCont_of_joint (I := I) co.gInf (Set.Iio 0) isOpen_Iio.uniqueDiffOn
    (gramSmooth (I := I) (Φ := Φ) co hreg)).mono
    (regular_subset_Iio (I := I) (X := X) hcarrier)

omit [NeZero (Module.finrank ℝ E)] in
theorem rm04Cont_regular
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier = Set.Iic 0)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 4 X.D.regular
      (fun t x => metricRm04At (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  exact (rm04Cont_of_joint (I := I) co.gInf (Set.Iio 0) isOpen_Iio.uniqueDiffOn
    (gramSmooth (I := I) (Φ := Φ) co hreg)).mono
    (regular_subset_Iio (I := I) (X := X) hcarrier)

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_regular
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier = Set.Iic 0)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn (fun q : ℝ × P.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
      (X.D.regular ×ˢ (Set.univ : Set P.M)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  exact (scalarCont_of_joint (I := I) co.gInf (Set.Iio 0) isOpen_Iio.uniqueDiffOn
    (gramSmooth (I := I) (Φ := Φ) co hreg)).mono
    (Set.prod_mono (regular_subset_Iio (I := I) (X := X) hcarrier) Set.Subset.rfl)

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTime_regular
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier = Set.Iic 0)
    (hreg : Set.Iio 0 ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ t ∈ X.D.regular, ∀ x : P.M,
      DifferentiableWithinAt Real
        (fun s : Real => metricScalarAt (I := I) (co.gInf s) x) X.D.regular t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro t ht x
  exact (scalarTime_of_joint (I := I) co.gInf (Set.Iio 0) isOpen_Iio.uniqueDiffOn
    (gramSmooth (I := I) (Φ := Φ) co hreg) t
    (regular_subset_Iio (I := I) (X := X) hcarrier ht) x).mono
    (regular_subset_Iio (I := I) (X := X) hcarrier)

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_carrier
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : Set.Iic 0 ⊆ X.D.carrier)
    (cLow : Nat → ℝ) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn (fun q : ℝ × P.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
      (Set.Iic 0 ×ˢ (Set.univ : Set P.M)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  refine continuousOn_of_locally_continuousOn (s := Set.Iic 0 ×ˢ (Set.univ : Set P.M))
    (f := fun q : ℝ × P.M => metricScalarAt (I := I) (co.gInf q.1) q.2) ?_
  intro p hp
  have hp1 : p.1 ≤ (0 : ℝ) := hp.1
  obtain ⟨n, hn⟩ := exists_nat_gt (-p.1)
  have hβ : -(n : ℝ) < p.1 := by linarith
  obtain ⟨K, hKc, hpKint, _⟩ :=
    exists_compact_subset (x := p.2) isOpen_univ (Set.mem_univ p.2)
  refine ⟨Set.Ioo (-(n : ℝ)) 1 ×ˢ interior K,
    isOpen_Ioo.prod isOpen_interior, ⟨⟨hβ, by linarith⟩, hpKint⟩, ?_⟩
  have hwin : Set.Icc (-(n : ℝ)) 0 ⊆ X.D.carrier := fun s hs => hcarrier hs.2
  have hsc := FlowMetricConvergenceData.continuousOn_scalar (I := I) (Φ := Φ) R bf hsrc htgt
    (-(n : ℝ)) 0 (cLow n) (hcLow n)
    (fun k t ht y v => hbound n k t ht y v)
    (fun q _ => hcovTail n q) (HalfLineMetricConvergenceData.atWindow Φ co n) K hKc hwin
  refine hsc.mono ?_
  rintro ⟨t, x⟩ ⟨⟨ht0, _⟩, ⟨htI, hxK⟩⟩
  exact ⟨⟨le_of_lt htI.1, ht0⟩, interior_subset hxK⟩

end HalfLineMetricConvergenceData

section HalfLineFlowLimitData

variable {Y : PointedFlowSeq (I := I)}

theorem exists_complete_smooth_flow_limit_subsequence_of_halfLine_metric_data
    (mc : MetricCompactLimit (I := I) (Y.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) Y mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SourceIsSigmaCompact (I := I) Φ₀)
    (htgt : TargetIsSigmaCompact (I := I) Φ₀)
    (co : HalfLineMetricConvergenceData (I := I) Φ₀ R bf hsrc htgt)
    (hzero : co.gInf 0 = mc.limit.metric)
    (hR : MetricComplete (I := I)
      ({ mc.limit with metric := R } : PointedRiemannianManifold (I := I)))
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ₀ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
                sourceDomCharted (I := I) Φ₀ k
            TangentSpace I y),
          cLow n * R.inner (y : mc.limit.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
              sourceDomCharted (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSmooth (I := I) Φ₀ k
            (sourceMetric (I := I) Φ₀ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : mc.limit.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ₀ R bf hsrc htgt k t) R z ≤ C)
    (hcarrier : Y.D.carrier = Set.Iic 0)
    (hregular : Y.D.regular = Set.Iio 0)
    (hscalarTime : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ t ∈ Y.D.carrier, ∀ x : mc.limit.M,
        DifferentiableWithinAt Real
          (fun s : Real => metricScalarAt (I := I) (co.gInf s) x) Y.D.carrier t)
    (hricciCont : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 2 Y.D.carrier
        (fun t x => metricRicciAt (I := I) (co.gInf t) x))
    (hrm04Cont : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 4 Y.D.carrier
        (fun t x => metricRm04At (I := I) (co.gInf t) x)) :
    ∃ d : SmoothFlowLimitSubsequence (I := I) Y mc,
      ∀ t ∈ Y.D.carrier, MetricComplete (I := I) (d.limit.L.atTime (I := I) t) := by
  let : TopologicalSpace mc.limit.M := mc.limit.topology
  let : ChartedSpace H mc.limit.M := mc.limit.charted
  let : T2Space mc.limit.M := mc.limit.t2
  let : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  let : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  have hsmooth : MetricFamilySmoothOn (I := I) (M := mc.limit.M) Y.D
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := mc.limit.M) Y.D).family.metric :=
    HalfLineMetricConvergenceData.metricSmooth (I := I) (Φ := Φ₀) co hcarrier
      (le_of_eq hregular.symm)
  have hscalarCont : ContinuousOn
      (fun q : Real × mc.limit.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
      (Y.D.carrier ×ˢ (Set.univ : Set mc.limit.M)) := by
    have h := HalfLineMetricConvergenceData.scalarCont_carrier (I := I) (Φ := Φ₀) co
      (le_of_eq hcarrier.symm) cLow hcLow hbound hcovTail
    simpa only [hcarrier] using h
  exact exists_complete_smooth_flow_limit_subsequence_of_halfLine_regularity (I := I) mc Φ₀ R
    bf hsrc htgt co hzero hR cLow hcLow hbound hcovTail (le_of_eq hcarrier) hregular hsmooth
    hscalarCont hscalarTime hricciCont hrm04Cont

end HalfLineFlowLimitData

end CheegerGromovCompactness
end DifferentialGeometry
