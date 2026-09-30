import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessMovingNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ShrinkingCylinderIsometries
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorRestriction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck

section
noncomputable section

open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance compactNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem eventually_strict_weighted_error_norm_on_compact
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    {K : Set M} (hK : IsCompact K)
    {J L : Set ℝ}
    (hregular : ∀ y ∈ K, ∃ V : Set E, IsOpen V ∧ extChartAt I y y ∈ V ∧
      V ⊆ (extChartAt I y).target ∧
      (∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) y i j z.2) (L ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => A z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2))) (J ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => B z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2))) (L ×ˢ V)))
    (t Q c alpha beta : ℕ → ℝ) {t₀ Q₀ c₀ alpha₀ beta₀ : ℝ}
    (hQ₀ : Q₀ ≠ 0) (hc : ∀ n, 0 < c n) (hc₀ : 0 < c₀)
    (htlim : Tendsto t atTop (𝓝 t₀)) (hQlim : Tendsto Q atTop (𝓝 Q₀))
    (hclim : Tendsto c atTop (𝓝 c₀)) (halim : Tendsto alpha atTop (𝓝 alpha₀))
    (hblim : Tendsto beta atTop (𝓝 beta₀))
    {lo hi eps : ℝ} (order : ℕ)
    (hsource : ∀ n s, s ∈ Icc lo hi → t n + s / Q n ∈ J)
    (hmodel : ∀ n s, s ∈ Icc lo hi → s / c n ∈ L)
    (hsource₀ : ∀ s ∈ Icc lo hi, t₀ + s / Q₀ ∈ J)
    (hmodel₀ : ∀ s ∈ Icc lo hi, s / c₀ ∈ L)
    (hstrict : ∀ s ∈ Icc lo hi,
      ∀ y ∈ K,
        tensor02CovDerivNormWith (I := I) order
          (alpha₀ • A (t₀ + s / Q₀) - beta₀ • B (s / c₀))
          (scaleMetric c₀ hc₀ (g (s / c₀))) (scaleMetric c₀ hc₀ (g (s / c₀))) y < eps) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
      ∀ y ∈ K,
        tensor02CovDerivNormWith (I := I) order
          (alpha n • A (t n + s / Q n) - beta n • B (s / c n))
          (scaleMetric (c n) (hc n) (g (s / c n)))
          (scaleMetric (c n) (hc n) (g (s / c n))) y < eps := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let f (n : ℕ) (s : ℝ) (y : M) := tensor02CovDerivNormWith (I := I) order
    (alpha n • A (t n + s / Q n) - beta n • B (s / c n))
    (scaleMetric (c n) (hc n) (g (s / c n))) (scaleMetric (c n) (hc n) (g (s / c n))) y
  change ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
    ∀ y ∈ K, f n s y < eps
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ (∀ s ∈ Icc lo hi,
      ∀ y ∈ K,
        f n s y < eps) := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hbad' (n : ℕ) : ∃ s ∈ Icc lo hi,
      ∃ y ∈ K,
        eps ≤ f (ns n) s y := by
    have hh := hbad n
    push Not at hh
    exact hh
  choose s hs y hy hbadnorm using hbad'
  obtain ⟨w, hw, phi, hphi, hwlim⟩ := (isCompact_Icc.prod hK).tendsto_subseq
    (x := fun n => (s n, y n)) (fun n => ⟨hs n, hy n⟩)
  let pick := ns ∘ phi
  have hpick : Tendsto pick atTop atTop := hns.comp hphi.tendsto_atTop
  have hslim : Tendsto (fun n => s (phi n)) atTop (𝓝 w.1) :=
    (continuous_fst.tendsto w).comp hwlim
  have hylim : Tendsto (fun n => y (phi n)) atTop (𝓝 w.2) :=
    (continuous_snd.tendsto w).comp hwlim
  obtain ⟨V, hV, hwV, hVt, hgram, hA, hB⟩ := hregular w.2 hw.2
  have hsourcelim : Tendsto (fun n => t (pick n) + s (phi n) / Q (pick n)) atTop
      (𝓝 (t₀ + w.1 / Q₀)) := (htlim.comp hpick).add (hslim.div (hQlim.comp hpick) hQ₀)
  have hmodellim : Tendsto (fun n => s (phi n) / c (pick n)) atTop (𝓝 (w.1 / c₀)) :=
    hslim.div (hclim.comp hpick) hc₀.ne'
  have hnorm := weighted_error_covariant_norm_tendsto_at_point g A B w.2 hV hwV hVt
    hgram hA hB (fun n => t (pick n) + s (phi n) / Q (pick n))
    (fun n => s (phi n) / c (pick n))
    (fun n => hsource (pick n) (s (phi n)) (hs (phi n)))
    (fun n => hmodel (pick n) (s (phi n)) (hs (phi n)))
    (hsource₀ w.1 hw.1) (hmodel₀ w.1 hw.1) hsourcelim hmodellim
    (fun n => c (pick n)) (fun n => alpha (pick n)) (fun n => beta (pick n))
    (fun n => hc (pick n)) hc₀ (hclim.comp hpick) (halim.comp hpick) (hblim.comp hpick)
    (fun n => y (phi n)) hylim order
  have hge := ge_of_tendsto hnorm (Filter.Eventually.of_forall (fun n => hbadnorm (phi n)))
  exact (not_le_of_gt (hstrict w.1 hw.1 w.2 hw.2)) hge

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
end

section
noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open Perelman.CanonicalNeighborhood.FiniteHorn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

private theorem metric_time_tower_chart_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) ∞ 2)
    (hzero : ∀ t ∈ Icc c b, A 0 t = metricTensorField (S.base.metric t))
    (hA : ∀ q t, t ∈ Icc c b → ∀ x,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t)
    (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧
      V ⊆ (extChartAt I p).target ∧
      ∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun z : ℝ × E => A q z.1 ((extChartAt I p).symm z.2)
          (fun j => chartBasisVecFiber (I := I) p (slots j)
            ((extChartAt I p).symm z.2))) (Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed S hS hac hcb hslab hreg p
  refine ⟨V, hV, hpV, hVt, ?_⟩
  intro q slots
  have hjet := contDiffOn_iteratedDerivWithin_time (uniqueDiffOn_Icc hcb) hV
    (hgram (slots 0) (slots 1)) q
  apply hjet.congr
  rintro ⟨t, z⟩ ⟨ht, hz⟩
  let x : M := (extChartAt I p).symm z
  let v : Fin 2 → TangentSpace I x := fun j => chartBasisVecFiber (I := I) p (slots j) x
  have hbase (s : ℝ) (hs : s ∈ Icc c b) :
      iteratedDerivWithin 0
        (fun r => chartGramOnE (I := I) (S.base.metric r) p (slots 0) (slots 1) z)
        (Icc c b) s = A 0 s x v := by
    rw [iteratedDerivWithin_zero, hzero s hs, metricTensorField_apply]
    rfl
  have heq := DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
    (uniqueDiffOn_Icc hcb)
    (fun r => chartGramOnE (I := I) (S.base.metric r) p (slots 0) (slots 1) z)
    (fun k s => A k s x v)
    (fun k s hs => (tensor0SEvalCLM (I := I) (M := M) (x := x) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hA k s hs x)) (fun s hs => by simpa only [iteratedDerivWithin_zero] using hbase s hs)
    q ht
  exact heq.symm

private theorem exists_metric_time_tower_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hreg : Ioo a b ⊆ D.regular) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) ∞ 2,
      (∀ t, A 0 t = metricTensorField (S.base.metric t)) ∧
      (∀ q t, t ∈ Icc c b → ∀ x,
        A q t x = iteratedDerivWithin q
          (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t ∧
        HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t) ∧
      ∀ p : M, ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧
        V ⊆ (extChartAt I p).target ∧
        ∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
          ContDiffOn ℝ ∞ (fun z : ℝ × E => A q z.1 ((extChartAt I p).symm z.2)
            (fun j => chartBasisVecFiber (I := I) p (slots j)
              ((extChartAt I p).symm z.2))) (Icc c b ×ˢ V) := by
  obtain ⟨A, hzero, hA⟩ := Perelman.KappaSolutions.exists_ordinary_metric_time_jets_on_closed_interval
    S hS hac hcb hcarrier hreg
  exact ⟨A, hzero, hA, metric_time_tower_chart_contDiffOn_closed
    S hS hac hcb (by rw [hcarrier]) hreg A (fun t _ => hzero t) (fun q t ht x => (hA q t ht x).2)⟩

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem metric_time_tower_sub_eq_iteratedDerivWithin
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (g h : ℝ → SmoothRiemannianMetric I M)
    (A B : ℕ → ℝ → Tensor0SField (I := I) (M := M) ∞ 2)
    (hA0 : ∀ t, A 0 t = metricTensorField (g t))
    (hB0 : ∀ t, B 0 t = metricTensorField (h t))
    (hA : ∀ q t, t ∈ J → ∀ x,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) J t)
    (hB : ∀ q t, t ∈ J → ∀ x,
      HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) J t)
    (q : ℕ) {t : ℝ} (ht : t ∈ J) (x : M) :
    A q t x - B q t x = iteratedDerivWithin q
      (fun s => metricTensorField (g s) x - metricTensorField (h s) x) J t := by
  apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt hJ
    _ (fun j s => A j s x - B j s x)
    (fun j s hs => (hA j s hs x).sub (hB j s hs x)) ?_ q ht).symm
  intro s _hs
  change metricTensorField (g s) x - metricTensorField (h s) x = A 0 s x - B 0 s x
  rw [hA0, hB0]


private theorem exists_metric_difference_time_towers_on_closed_interval
    {D₁ D₂ : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₁) (T : SolutionOn (I := I) (M := M) D₂)
    (hS : IsSolutionOn S) (hT : IsSolutionOn T)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrierS : Icc a b ⊆ D₁.carrier) (hregS : Ioo a b ⊆ D₁.regular)
    (hcarrierT : Icc a b ⊆ D₂.carrier) (hregT : Ioo a b ⊆ D₂.regular) :
    ∃ A B : ℕ → ℝ → Tensor0SField (I := I) (M := M) ∞ 2,
      (∀ t, A 0 t = metricTensorField (S.base.metric t)) ∧
      (∀ t, B 0 t = metricTensorField (T.base.metric t)) ∧
      (∀ q t, t ∈ Icc c b → ∀ x,
        HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t) ∧
      (∀ q t, t ∈ Icc c b → ∀ x,
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t) ∧
      (∀ q t, t ∈ Icc c b → ∀ x,
        A q t x - B q t x = iteratedDerivWithin q
          (fun s => metricTensorField (S.base.metric s) x -
            metricTensorField (T.base.metric s) x) (Icc c b) t) ∧
      ∀ p : M, ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧
        V ⊆ (extChartAt I p).target ∧
        (∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
          (fun z : ℝ × E => chartGramOnE (I := I) (T.base.metric z.1) p i j z.2)
          (Icc c b ×ˢ V)) ∧
        (∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
          ContDiffOn ℝ ∞ (fun z : ℝ × E => A q z.1 ((extChartAt I p).symm z.2)
            (fun j => chartBasisVecFiber (I := I) p (slots j)
              ((extChartAt I p).symm z.2))) (Icc c b ×ˢ V)) ∧
        (∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
          ContDiffOn ℝ ∞ (fun z : ℝ × E => B q z.1 ((extChartAt I p).symm z.2)
            (fun j => chartBasisVecFiber (I := I) p (slots j)
              ((extChartAt I p).symm z.2))) (Icc c b ×ˢ V)) := by
  let D := RealTimeInterval.closed a b (hac.le.trans hcb.le)
  let S' := S.timeRestrict D
  let T' := T.timeRestrict D
  have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS hcarrierS hregS
  have hT' : IsSolutionOn T' := isSolutionOn_timeRestrict hT hcarrierT hregT
  obtain ⟨A, hA0, hA, hAreg⟩ := exists_metric_time_tower_on_closed_interval
    S' hS' hac hcb rfl Subset.rfl
  obtain ⟨B, hB0, hB, hBreg⟩ := exists_metric_time_tower_on_closed_interval
    T' hT' hac hcb rfl Subset.rfl
  have hAd := fun q t ht x => (hA q t ht x).2
  have hBd := fun q t ht x => (hB q t ht x).2
  refine ⟨A, B, hA0, hB0, hAd, hBd, ?_, ?_⟩
  · intro q t ht x
    exact metric_time_tower_sub_eq_iteratedDerivWithin (uniqueDiffOn_Icc hcb)
      S.base.metric T.base.metric A B hA0 hB0 hAd hBd q ht x
  · intro p
    obtain ⟨V₁, hV₁, hp₁, ht₁, hAr⟩ := hAreg p
    obtain ⟨V₂, hV₂, hp₂, ht₂, hBr⟩ := hBreg p
    obtain ⟨V₃, hV₃, hp₃, ht₃, hgram⟩ :=
      solution_chartGram_contDiffOn_closed T hT hac hcb hcarrierT hregT p
    refine ⟨V₁ ∩ (V₂ ∩ V₃), hV₁.inter (hV₂.inter hV₃), ⟨hp₁, hp₂, hp₃⟩,
      (fun z hz => ht₁ hz.1), ?_, ?_, ?_⟩
    · intro i j
      exact (hgram i j).mono (prod_mono subset_rfl (fun z hz => hz.2.2))
    · intro q slots
      exact (hAr q slots).mono (prod_mono subset_rfl (fun z hz => hz.1))
    · intro q slots
      exact (hBr q slots).mono (prod_mono subset_rfl (fun z hz => hz.2.1))

end DifferentialGeometry.PDE.RicciFlow


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem neck_time_difference_field_eq_of_metric_towers
    {δ c : ℝ} (hc : c < 0)
    (g : ℝ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hA0 : ∀ t, A 0 t = metricTensorField (g t))
    (hB0 : ∀ t, B 0 t = metricTensorField
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ)))
    (hA : ∀ q t, t ∈ Icc c 0 → ∀ x,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c 0) t)
    (hB : ∀ q t, t ∈ Icc c 0 → ∀ x,
      HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c 0) t)
    (Z : ℕ → Icc c 0 → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v x, Z q v x = iteratedDerivWithin q (fun t =>
      metricTensorField (g t) x - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) x) (Icc c 0) v.1) :
    ∀ q v, Z q v = A q v.1 - B q v.1 := by
  intro q v
  ext x w
  have heq := metric_time_tower_sub_eq_iteratedDerivWithin
    (I := NeckCylinderModel) (uniqueDiffOn_Icc hc) g
    (fun t => (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
      (neckBuffer δ)) A B hA0 hB0 hA hB q v.2 x
  have hfield : Z q v x = A q v.1 x - B q v.1 x := by
    rw [hZ, heq]
    apply iteratedDerivWithin_congr _ v.2
    intro t ht
    simp only [min_eq_left ht.2, shrinkingCylinderMetric_eq_flow]
  exact congrArg (fun F => F w) hfield

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open Perelman.CanonicalNeighborhood.FiniteHorn

open private shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTimeJetConvergence

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem strict_tower_difference_bound
    {δ ε η c : ℝ} (hc : c < -1) (hη : η < ε)
    (A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (Z : ℕ → Icc c 0 → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZeq : ∀ q v, Z q v = A q v.1 - B q v.1) (r q : ℕ)
    (hbound : ∀ v : Icc c 0, ∀ x ∈ neckClosedTest δ,
      let g := (shrinkingCylinderMetric
        ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
      Real.sqrt (normSq0S g x (r + 2)
        (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) (x : neckBuffer δ)
    (hx : x ∈ neckClosedTest δ) :
    tensor02CovDerivNormWith r (A q t - B q t)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ)) x < ε := by
  let v : Icc c 0 := ⟨t, hc.le.trans ht.1, ht.2⟩
  have hh := hbound v x hx
  dsimp only at hh
  rw [cylinderTensorCovDeriv_eq_tensor02CovDeriv] at hh
  change tensor02CovDerivNormWith r (Z q v)
    ((shrinkingCylinderMetric ⟨t, ht.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
    ((shrinkingCylinderMetric ⟨t, ht.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x ≤ η at hh
  rw [hZeq q v, shrinkingCylinderMetric_eq_flow] at hh
  exact hh.trans_lt hη

private theorem exists_neck_metric_time_towers_with_strict_reparametrized_bounds
    {δ ε c a : ℝ} (hac : a < c) (hc : c < -1) (k : ℕ)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed a 0 (by linarith))) (hS : IsSolutionOn S)
    (Z : ℕ → Icc c 0 → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v x, Z q v x = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) x - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) x) (Icc c 0) v.1)
    (hbound : ∃ η : ℝ, η < ε ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
      ∀ v : Icc c 0, ∀ x ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g x (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η) :
    ∃ A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
      (∀ t, A 0 t = metricTensorField (S.base.metric t)) ∧
      (∀ t, B 0 t = metricTensorField
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
          (neckBuffer δ))) ∧
      (∀ q t, t ∈ Icc c 0 → ∀ x,
        HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c 0) t) ∧
      (∀ q t, t ∈ Icc c 0 → ∀ x,
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c 0) t) ∧
      (∀ q v, Z q v = A q v.1 - B q v.1) ∧
      ∀ time scale : ℕ → ℝ, Tendsto time atTop (𝓝 0) →
        Tendsto scale atTop (𝓝 1) →
        (∀ n, MapsTo (parabolicTime (time n) (scale n)) (Icc (-1 : ℝ) 0) (Icc c 0)) →
        ∀ᶠ n in atTop, ∀ r q : ℕ, r + 2 * q ≤ k →
          ∀ t ∈ Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
            let g := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)
            tensor02CovDerivNormWith r
              ((scale n * (scale n)⁻¹ ^ q) • A q (parabolicTime (time n) (scale n) t) - B q t)
              g g x < ε := by
  let _ : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)
  let C : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed a 0 (by linarith)) :=
    { base.metric := fun t =>
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ) }
  have hC : IsSolutionOn C := shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed
    δ a (by linarith)
  have hc0 : c < 0 := by linarith
  obtain ⟨A, B, hA0, hB0, hAd, hBd, hdiff, hregular⟩ :=
    exists_metric_difference_time_towers_on_closed_interval S C hS hC hac hc0
      Subset.rfl Subset.rfl Subset.rfl Subset.rfl
  have hZeq := neck_time_difference_field_eq_of_metric_towers hc0 S.base.metric
    A B hA0 hB0 hAd hBd Z hZ
  refine ⟨A, B, hA0, hB0, hAd, hBd, hZeq, ?_⟩
  intro time scale htime hscale hsource
  obtain ⟨η, hη, hbound⟩ := hbound
  have hscaleMetric (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)) :
      scaleMetric 1 zero_lt_one g = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner, one_mul]
  have hpair (r q : ℕ) (hrq : r + 2 * q ≤ k) :
      ∀ᶠ n in atTop, ∀ t ∈ Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
        tensor02CovDerivNormWith r
          ((scale n * (scale n)⁻¹ ^ q) • A q (parabolicTime (time n) (scale n) t) - B q t)
          (C.base.metric t) (C.base.metric t) x < ε := by
    have hcoef : Tendsto (fun n => scale n * (scale n)⁻¹ ^ q) atTop (𝓝 1) := by
      simpa only [inv_one, one_pow, one_mul] using
        hscale.mul ((hscale.inv₀ one_ne_zero).pow q)
    have hstrict (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) (x : neckBuffer δ)
        (hx : x ∈ neckClosedTest δ) :
        tensor02CovDerivNormWith r (A q t - B q t)
          (C.base.metric t) (C.base.metric t) x < ε :=
      strict_tower_difference_bound hc hη A B Z hZeq r q
        (hbound r q hrq) ht x hx
    have hlim := eventually_strict_weighted_error_norm_on_compact C.base.metric (A q) (B q)
      (isCompact_neckClosedTest δ)
      (J := Icc c 0) (L := Icc c 0) (fun y _hy => by
        obtain ⟨V, hV, hpV, hVt, hg, hA, hB⟩ := hregular y
        exact ⟨V, hV, hpV, hVt, hg, hA q, hB q⟩)
      time scale (fun _ => 1) (fun n => scale n * (scale n)⁻¹ ^ q) (fun _ => 1)
      (t₀ := 0) (Q₀ := 1) (c₀ := 1) (alpha₀ := 1) (beta₀ := 1)
      one_ne_zero (fun _ => zero_lt_one) zero_lt_one htime hscale
      tendsto_const_nhds hcoef tendsto_const_nhds (lo := (-1 : ℝ)) (hi := 0) (eps := ε) r
      (fun n t ht => hsource n ht)
      (fun n t ht => by simpa only [div_one] using
        (show t ∈ Icc c 0 from ⟨hc.le.trans ht.1, ht.2⟩))
      (fun t ht => by simpa only [div_one, zero_add] using
        (show t ∈ Icc c 0 from ⟨hc.le.trans ht.1, ht.2⟩))
      (fun t ht => by simpa only [div_one] using
        (show t ∈ Icc c 0 from ⟨hc.le.trans ht.1, ht.2⟩)) (by
        intro t ht x hx
        simpa only [div_one, zero_add, one_smul, hscaleMetric] using hstrict t ht x hx)
    simpa only [parabolicTime, div_one, one_smul, hscaleMetric] using hlim
  have hfinite : {ij : ℕ × ℕ | ij.1 + 2 * ij.2 ≤ k}.Finite := by
    apply ((Finset.range (k + 1)).product (Finset.range (k + 1))).finite_toSet.subset
    intro ij hij
    change ij.1 + 2 * ij.2 ≤ k at hij
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hall := (Filter.eventually_all_finite hfinite).mpr (fun ij hij => hpair ij.1 ij.2 hij)
  filter_upwards [hall] with n hn
  intro r q hrq t ht x hx
  exact hn (r, q) hrq t ht x hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section

open Set Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private local instance (U : Opens NeckCylinder) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel U.isOpen)

private theorem translated_buffer_subset {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) :
    cylinderAxialImage (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε) ≤ neckBuffer δ := by
  rintro q ⟨x, hx, rfl⟩
  change -δ⁻¹ - 1 < z.val.2 + 1 * x.2 ∧ z.val.2 + 1 * x.2 < δ⁻¹ + 1
  change -ε⁻¹ - 1 < x.2 ∧ x.2 < ε⁻¹ + 1 at hx
  constructor <;> linarith only [hx.1, hx.2, hfit, neg_abs_le z.val.2, le_abs_self z.val.2]

private def translatedBufferMap {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) : neckBuffer ε → neckBuffer δ :=
  Opens.inclusion (translated_buffer_subset z hfit) ∘
    cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε)

private theorem translatedBufferMap_val {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) (x : neckBuffer ε) :
    (translatedBufferMap z hfit x).val = (x.val.1, x.val.2 + z.val.2) := by
  change (x.val.1, z.val.2 + 1 * x.val.2) = (x.val.1, x.val.2 + z.val.2)
  simp only [one_mul, add_comm]

private theorem translatedBufferMap_smooth {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) :
    IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (translatedBufferMap z hfit) := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    NeckCylinderModel NeckCylinderModel (neckBuffer δ) (translatedBufferMap z hfit)
  change IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
    ((cylinderAxialDiffeomorph (I := 𝓡 2) (M := Sphere 2) z.val.2 1 (by norm_num)) ∘
      (Subtype.val : neckBuffer ε → NeckCylinder))
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    NeckCylinderModel NeckCylinderModel (Subtype.val : neckBuffer ε → NeckCylinder)
    (IsSmoothEmbedding.of_opens (neckBuffer ε)) _

private theorem translatedBufferMap_mfderiv {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) (x : neckBuffer ε)
    (v : TangentSpace NeckCylinderModel x) :
    mfderiv NeckCylinderModel NeckCylinderModel (translatedBufferMap z hfit) x v = v := by
  have hinc := (contMDiff_inclusion (I := NeckCylinderModel) (n := ∞)
    (translated_buffer_subset z hfit)).mdifferentiable (by simp)
  rw [translatedBufferMap, mfderiv_comp x (hinc _)
    ((cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num)
      (neckBuffer ε)).contMDiff.mdifferentiable (by simp) _), mfderiv_opens_incl]
  change mfderiv NeckCylinderModel NeckCylinderModel
    (cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε)) x v = v
  rw [cylinderAxialRestrict_mfderiv]
  simp only [one_mul]
  exact Prod.eta v

private theorem translatedBufferMap_local {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) :
    IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ (translatedBufferMap z hfit) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (translatedBufferMap_smooth z hfit).contMDiff
    (fun x v w h => by
      rw [translatedBufferMap_mfderiv, translatedBufferMap_mfderiv] at h
      change (v : EuclideanSpace ℝ (Fin 2) × ℝ) = w at h ⊢
      exact h) rfl

private theorem pullbackMetricCross_shrinkingCylinder_axial (ε a : ℝ) (s : Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric s).restrictOpen
        (cylinderAxialImage (I := 𝓡 2) a 1 (by norm_num) (neckBuffer ε)))
      (cylinderAxialRestrict (I := 𝓡 2) a 1 (by norm_num) (neckBuffer ε)) =
      (shrinkingCylinderMetric s).restrictOpen (neckBuffer ε) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    shrinkingCylinderMetric_eq_flow, PDE.RicciFlow.shrinkingCylinderMetric]
  exact pullback_cylinderMetric_cylinderAxialRestrict _ _ _ _ _

private theorem localPullMetric_shrinkingCylinder_translatedBufferMap {δ ε : ℝ}
    (z : neckBuffer δ) (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) (s : Iio (1 : ℝ)) :
    localPullMetric ((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ))
      (translatedBufferMap z hfit) (translatedBufferMap_local z hfit) =
      (shrinkingCylinderMetric s).restrictOpen (neckBuffer ε) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have h := congrArg (fun g => g.inner x v w)
    (pullbackMetricCross_shrinkingCylinder_axial ε z.val.2 s)
  rw [Diffeomorph.pullbackMetricCross_inner, cylinderAxialRestrict_mfderiv,
    cylinderAxialRestrict_mfderiv] at h
  simp only [one_mul] at h
  rw [localPullMetric_inner, translatedBufferMap_mfderiv, translatedBufferMap_mfderiv]
  exact h

private def translatedBufferTensor {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹)
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2 :=
  pullbackTensor02FieldCross
    (cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε))
    (restrictOpenTensor02FieldOfSubset (translated_buffer_subset z hfit) A)

private theorem translatedBufferTensor_apply {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹)
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (x : neckBuffer ε) (v : Fin 2 → TangentSpace NeckCylinderModel x) :
    translatedBufferTensor z hfit A x v = A (translatedBufferMap z hfit x) v := by
  rw [translatedBufferTensor, pullbackTensor02FieldCross_apply,
    restrictOpenTensor02FieldOfSubset_apply]
  change A (translatedBufferMap z hfit x)
    (fun j => mfderiv NeckCylinderModel NeckCylinderModel
      (cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε)) x (v j)) = _
  apply congrArg (fun slots => A (translatedBufferMap z hfit x) slots)
  funext j
  rw [cylinderAxialRestrict_mfderiv]
  simp only [one_mul]
  exact Prod.eta (v j)

private theorem translatedBufferTensor_norm {δ ε : ℝ} (z : neckBuffer δ)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹)
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (r : ℕ) (s t : Iio (1 : ℝ)) (x : neckBuffer ε) :
    tensor02CovDerivNormWith r (translatedBufferTensor z hfit A)
      ((shrinkingCylinderMetric s).restrictOpen (neckBuffer ε))
      ((shrinkingCylinderMetric t).restrictOpen (neckBuffer ε)) x =
    tensor02CovDerivNormWith r A
      ((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) (translatedBufferMap z hfit x) := by
  let hsub := translated_buffer_subset z hfit
  let Φ := cylinderAxialRestrict (I := 𝓡 2) z.val.2 1 (by norm_num) (neckBuffer ε)
  have h := tensor02CovDerivNormWith_pullbackTensor02FieldCross
    (((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ)).restrictOpenOfSubset hsub)
    (((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)).restrictOpenOfSubset hsub)
    Φ (restrictOpenTensor02FieldOfSubset hsub A) r x
  rw [SmoothRiemannianMetric.restrictOpen_flat, SmoothRiemannianMetric.restrictOpen_flat,
    pullbackMetricCross_shrinkingCylinder_axial, pullbackMetricCross_shrinkingCylinder_axial] at h
  have hrest := tensor02CovDerivNormWith_restrictOpenOfSubset hsub
    ((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ))
    ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) A r (Φ x)
  rw [SmoothRiemannianMetric.restrictOpen_flat, SmoothRiemannianMetric.restrictOpen_flat] at hrest
  exact h.trans hrest

private theorem exists_neckBuffer_translation_with_tensor_pullback {δ ε : ℝ} (hε : 0 < ε)
    (z : neckBuffer δ) (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) :
    ∃ (f : neckBuffer ε → neckBuffer δ)
      (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
      (∀ x : neckBuffer ε, (f x).val = (x.val.1, x.val.2 + z.val.2)) ∧
      f ⟨(z.val.1, 0), by
        have hi := inv_pos.mpr hε
        constructor <;> linarith⟩ = z ∧
      f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
      (∀ s : Iio (1 : ℝ),
        localPullMetric ((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ)) f hf =
          (shrinkingCylinderMetric s).restrictOpen (neckBuffer ε)) ∧
      ∃ pull : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2,
        (∀ A x v, pull A x v =
          A (f x) (fun j => mfderiv NeckCylinderModel NeckCylinderModel f x (v j))) ∧
        (∀ A x, pull A x = A (f x)) ∧
        ∀ A r (s t : Iio (1 : ℝ)) x,
          tensor02CovDerivNormWith r (pull A)
            ((shrinkingCylinderMetric s).restrictOpen (neckBuffer ε))
            ((shrinkingCylinderMetric t).restrictOpen (neckBuffer ε)) x =
          tensor02CovDerivNormWith r A
            ((shrinkingCylinderMetric s).restrictOpen (neckBuffer δ))
            ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) (f x) := by
  let f := translatedBufferMap z hfit
  refine ⟨f, translatedBufferMap_local z hfit, translatedBufferMap_smooth z hfit,
    translatedBufferMap_val z hfit, ?_, ?_,
    localPullMetric_shrinkingCylinder_translatedBufferMap z hfit,
    translatedBufferTensor z hfit, ?_, ?_, translatedBufferTensor_norm z hfit⟩
  · apply Subtype.ext
    rw [translatedBufferMap_val]
    simp only [zero_add]
  · rintro y ⟨x, hx, rfl⟩
    change -δ⁻¹ ≤ (f x).val.2 ∧ (f x).val.2 ≤ δ⁻¹
    rw [translatedBufferMap_val]
    change -ε⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ ε⁻¹ at hx
    constructor <;> linarith only [hx.1, hx.2, hfit, neg_abs_le z.val.2, le_abs_self z.val.2]
  · intro A x v
    change translatedBufferTensor z hfit A x v = A (translatedBufferMap z hfit x)
      (fun j => mfderiv NeckCylinderModel NeckCylinderModel (translatedBufferMap z hfit) x (v j))
    simp only [translatedBufferMap_mfderiv]
    exact translatedBufferTensor_apply z hfit A x v
  · intro A x
    ext v
    exact translatedBufferTensor_apply z hfit A x v

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

private theorem exists_rescaled_local_solution
    {δ ε : ℝ}
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (z : neckBuffer δ) {t : ℝ} (ht : t ≤ 0) (hq : 0 < S.scalar t z)
    (hwindow : MapsTo (parabolicTime t (S.scalar t z)) (Icc (-(9 / 8 : ℝ)) 0)
      (Ioc (-(5 / 4 : ℝ)) 0))
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f)
    (x : neckBuffer ε) (hcenter : f x = z) :
    ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
        (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
      IsSolutionOn T ∧
      (∀ r, T.base.metric r = localPullMetric
        (scaleMetric (S.scalar t z) hq (S.base.metric (t + r / S.scalar t z))) f hf) ∧
      T.scalar 0 x = 1 := by
  have htime : t ∈ (RealTimeInterval.closed (-2) 0 (by norm_num)).carrier := by
    have hh := hwindow (show (0 : ℝ) ∈ Icc (-(9 / 8 : ℝ)) 0 from ⟨by norm_num, le_rfl⟩)
    simp only [parabolicTime_zero] at hh
    exact ⟨by linarith [hh.1], ht⟩
  let U := (parabolicSolution S t (S.scalar t z) hq htime).localPullback f hf
  let T := U.timeRestrict (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num))
  have hT : IsSolutionOn T := by
    apply isSolutionOn_timeRestrict
      ((parabolicSolution_isSolutionOn S hS t (S.scalar t z) hq htime).localPullback f hf)
    · intro r hr
      have hh := hwindow hr
      exact ⟨by linarith [hh.1], hh.2⟩
    · intro r hr
      change (-2 : ℝ) < t + r / S.scalar t z ∧ t + r / S.scalar t z < 0
      have hh := hwindow ⟨hr.1.le, hr.2.le⟩
      constructor
      · have hlo : -(5 / 4 : ℝ) < t + r / S.scalar t z := hh.1
        linarith
      · exact add_neg_of_nonpos_of_neg ht (div_neg_of_neg_of_pos hr.2 hq)
  refine ⟨T, hT, fun _ => rfl, ?_⟩
  change U.scalar 0 x = 1
  rw [SolutionOn.localPullback_scalar, hcenter, parabolicSolution_scalar]
  simp only [parabolicTime_zero]
  exact inv_mul_cancel₀ hq.ne'

private theorem pull_metric_difference_eq {δ ε q : ℝ} (hq : 0 < q)
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f)
    (pull : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2)
    (hpull : ∀ A x v, pull A x v =
      A (f x) (fun j => mfderiv NeckCylinderModel NeckCylinderModel f x (v j)))
    (g cδ : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (cε : SmoothRiemannianMetric NeckCylinderModel (neckBuffer ε))
    (hc : localPullMetric cδ f hf = cε)
    (A B : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hA : A = metricTensorField g) (hB : B = metricTensorField cδ) :
    pull (q • A - B) = metricTensorField (localPullMetric (scaleMetric q hq g) f hf) -
      metricTensorField cε := by
  ext x v
  change pull (q • A - B) x v = _
  rw [hpull, hA, hB]
  change q * metricTensorField g (f x)
    (fun j => mfderiv NeckCylinderModel NeckCylinderModel f x (v j)) -
    metricTensorField cδ (f x) (fun j => mfderiv NeckCylinderModel NeckCylinderModel f x (v j)) =
    metricTensorField (localPullMetric (scaleMetric q hq g) f hf) x v - metricTensorField cε x v
  rw [metricTensorField_apply, metricTensorField_apply, metricTensorField_apply,
    metricTensorField_apply, localPullMetric_inner, scaleMetric_inner]
  have h := congrArg (fun c => c.inner x (v 0) (v 1)) hc
  rw [localPullMetric_inner] at h
  exact congrArg (fun u => _ - u) h

private theorem translated_error_time_deriv {δ ε t q : ℝ}
    (f : neckBuffer ε → neckBuffer δ)
    (pull : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2)
    (hpoint : ∀ A x, pull A x = A (f x))
    (A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hmap : MapsTo (parabolicTime t q) (Icc (-1 : ℝ) 0) (Icc (-(5 / 4 : ℝ)) 0))
    (hA : ∀ b s, s ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
      HasDerivWithinAt (fun r => A b r y) (A (b + 1) s y) (Icc (-(5 / 4 : ℝ)) 0) s)
    (hB : ∀ b s, s ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
      HasDerivWithinAt (fun r => B b r y) (B (b + 1) s y) (Icc (-(5 / 4 : ℝ)) 0) s)
    (b : ℕ) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : neckBuffer ε) :
    HasDerivWithinAt (fun r => pull ((q * q⁻¹ ^ b) • A b (t + r / q) - B b r) x)
      (pull ((q * q⁻¹ ^ (b + 1)) • A (b + 1) (t + s / q) - B (b + 1) s) x)
      (Icc (-1 : ℝ) 0) s := by
  have hsub : Icc (-1 : ℝ) 0 ⊆ Icc (-(5 / 4 : ℝ)) 0 := by
    intro r hr
    exact ⟨by linarith [hr.1], hr.2⟩
  let L : Tensor0SSpace 2 NeckCylinderModel (f x) ≃L[ℝ]
      Tensor0SSpace 2 NeckCylinderModel x :=
    (tensor0SSpaceContinuousLinearEquiv (I := NeckCylinderModel) 2 (f x)).trans
      (tensor0SSpaceContinuousLinearEquiv (I := NeckCylinderModel) 2 x).symm
  have hL (V : Tensor0SSpace 2 NeckCylinderModel (f x)) : L V = V := by
    ext v
    rfl
  have hdA := hasDerivWithinAt_rescaled_time_tower (fun b r => A b r (f x)) t q hmap
    (fun b r hr => hA b r hr (f x)) b s hs
  have hdB := (hB b s (hsub hs) (f x)).mono hsub
  have hd := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt s (hdA.sub hdB)
  have hfun : (fun r => pull ((q * q⁻¹ ^ b) • A b (t + r / q) - B b r) x) =
      L ∘ (fun r => (q * q⁻¹ ^ b) • A b (t + r / q) (f x) - B b r (f x)) := by
    funext r
    rw [Function.comp_apply, hL, hpoint]
    rfl
  rw [hfun]
  have hv : L ((q * q⁻¹ ^ (b + 1)) • A (b + 1) (t + s / q) (f x) - B (b + 1) s (f x)) =
      pull ((q * q⁻¹ ^ (b + 1)) • A (b + 1) (t + s / q) - B (b + 1) s) x := by
    rw [hL, hpoint]
    rfl
  rw [← hv]
  exact hd


private theorem exists_rebased_neckBuffer_solution_with_error_jets
    {δ ε : ℝ} (hε : 0 < ε)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (z : neckBuffer δ) {t : ℝ} (ht : t ≤ 0)
    (hfit : |z.val.2| + ε⁻¹ ≤ δ⁻¹) (hq : 0 < S.scalar t z)
    (hwindow : MapsTo (parabolicTime t (S.scalar t z)) (Icc (-(9 / 8 : ℝ)) 0)
      (Ioc (-(5 / 4 : ℝ)) 0))
    (A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hA₀ : ∀ s ∈ Icc (-(5 / 4 : ℝ)) 0, A 0 s = metricTensorField (S.base.metric s))
    (hB₀ : ∀ s ∈ Icc (-(5 / 4 : ℝ)) 0, B 0 s = metricTensorField
      ((shrinkingCylinderMetric ⟨min s 0, (min_le_right s 0).trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ)))
    (hA : ∀ b s, s ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
      HasDerivWithinAt (fun r => A b r y) (A (b + 1) s y) (Icc (-(5 / 4 : ℝ)) 0) s)
    (hB : ∀ b s, s ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
      HasDerivWithinAt (fun r => B b r y) (B (b + 1) s y) (Icc (-(5 / 4 : ℝ)) 0) s)
    (k : ℕ) (η : ℝ)
    (herror : ∀ a b, a + 2 * b ≤ k → ∀ s : Icc (-1 : ℝ) 0, ∀ y ∈ neckClosedTest δ,
      tensor02CovDerivNormWith a
        ((S.scalar t z * (S.scalar t z)⁻¹ ^ b) • A b (t + s.val / S.scalar t z) - B b s)
        ((shrinkingCylinderMetric ⟨s.val, s.property.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
        ((shrinkingCylinderMetric ⟨s.val, s.property.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) y ≤ η) :
    ∃ (f : neckBuffer ε → neckBuffer δ)
      (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
      (∀ x : neckBuffer ε, (f x).val = (x.val.1, x.val.2 + z.val.2)) ∧
      f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
      ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
        IsSolutionOn T ∧
        (∀ r, T.base.metric r = localPullMetric
          (scaleMetric (S.scalar t z) hq (S.base.metric (t + r / S.scalar t z))) f hf) ∧
        T.scalar 0 ⟨(z.val.1, 0), by
          have hi := inv_pos.mpr hε
          constructor <;> linarith⟩ = 1 ∧
        ∃ jet : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2,
          (∀ b s x v, jet b s x v =
            ((S.scalar t z * (S.scalar t z)⁻¹ ^ b) • A b (t + s / S.scalar t z) - B b s)
              (f x) (fun j => mfderiv NeckCylinderModel NeckCylinderModel f x (v j))) ∧
          (∀ s ∈ Icc (-1 : ℝ) 0, jet 0 s = metricTensorField (T.base.metric s) -
            metricTensorField ((shrinkingCylinderMetric
              ⟨min s 0, (min_le_right s 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))) ∧
          (∀ b s, s ∈ Icc (-1 : ℝ) 0 → ∀ x,
            HasDerivWithinAt (fun r => jet b r x) (jet (b + 1) s x) (Icc (-1 : ℝ) 0) s) ∧
          ∀ a b, a + 2 * b ≤ k → ∀ s : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest ε,
            tensor02CovDerivNormWith a (jet b s)
              ((shrinkingCylinderMetric ⟨s.val, s.property.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))
              ((shrinkingCylinderMetric ⟨s.val, s.property.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε)) x ≤ η := by
  obtain ⟨f, hf, hemb, hval, hcenter, hcapture, hcyl, pull, hpull, hpoint, hnorm⟩ :=
    exists_neckBuffer_translation_with_tensor_pullback hε z hfit
  obtain ⟨T, hT, hmetric, hbase⟩ := exists_rescaled_local_solution S hS z ht hq hwindow
    f hf _ hcenter
  let E := fun b s => (S.scalar t z * (S.scalar t z)⁻¹ ^ b) •
    A b (t + s / S.scalar t z) - B b s
  let jet := fun b s => pull (E b s)
  have hsub : Icc (-1 : ℝ) 0 ⊆ Icc (-(5 / 4 : ℝ)) 0 := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hmap : MapsTo (parabolicTime t (S.scalar t z)) (Icc (-1 : ℝ) 0)
      (Icc (-(5 / 4 : ℝ)) 0) := by
    intro s hs
    exact (hwindow ⟨by linarith [hs.1], hs.2⟩).imp_left le_of_lt
  refine ⟨f, hf, hemb, hval, hcapture, T, hT, hmetric, hbase, jet, ?_, ?_, ?_, ?_⟩
  · intro b s x v
    exact hpull (E b s) x v
  · intro s hs
    have hz := pull_metric_difference_eq hq f hf pull hpull
      (S.base.metric (t + s / S.scalar t z))
      ((shrinkingCylinderMetric ⟨min s 0, (min_le_right s 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric ⟨min s 0, (min_le_right s 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))
      (hcyl ⟨min s 0, (min_le_right s 0).trans_lt zero_lt_one⟩) (A 0 (t + s / S.scalar t z)) (B 0 s) (hA₀ _ (hmap hs)) (hB₀ _ (hsub hs))
    rw [← hmetric] at hz
    simpa only [jet, E, pow_zero, mul_one] using hz
  · intro b s hs x
    exact translated_error_time_deriv f pull hpoint A B hmap hA hB b s hs x
  · intro a b hab s x hx
    exact (hnorm (E b s) a ⟨s.val, s.property.2.trans_lt zero_lt_one⟩
      ⟨s.val, s.property.2.trans_lt zero_lt_one⟩ x).trans_le
        (herror a b hab s (f x) (hcapture ⟨x, hx, rfl⟩))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

private theorem eventually_scalar_normalized_time_window
    {δ : ℝ}
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (x : neckBuffer δ) (hscalar : S.scalar 0 x = 1) :
    ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iic 0] (x, 0),
      0 < S.scalar z.2 z.1 ∧
      MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
        (Ioc (-(5 / 4 : ℝ)) 0) := by
  have hscalarCont : ContinuousWithinAt (fun z : neckBuffer δ × ℝ => S.scalar z.2 z.1)
      (univ ×ˢ Icc (-2) 0) (x, 0) := by
    have hc := hS.scalarCont
    change ContinuousOn (fun z : ℝ × neckBuffer δ => S.scalar z.1 z.2)
      (Icc (-2 : ℝ) 0 ×ˢ univ) at hc
    have hf : ContinuousOn (fun z : neckBuffer δ × ℝ => (z.2, z.1))
        (univ ×ˢ Icc (-2 : ℝ) 0) :=
      (continuous_snd.prodMk continuous_fst).continuousOn
    have hm : MapsTo (fun z : neckBuffer δ × ℝ => (z.2, z.1))
        (univ ×ˢ Icc (-2 : ℝ) 0) (Icc (-2 : ℝ) 0 ×ˢ univ) := fun _ hz => ⟨hz.2, hz.1⟩
    exact (hc.comp hf hm) (x, 0) ⟨mem_univ x, by norm_num, le_rfl⟩
  have hnearDomain : univ ×ˢ Icc (-2 : ℝ) 0 ∈ 𝓝[univ ×ˢ Iic 0] (x, 0) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((continuous_snd.continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds (by norm_num : (-2 : ℝ) < 0)))] with z hz hlo
    exact ⟨hz.1, hlo.le, hz.2⟩
  have hscalarLim : Tendsto (fun z : neckBuffer δ × ℝ => S.scalar z.2 z.1)
      (𝓝[univ ×ˢ Iic 0] (x, 0)) (𝓝 1) := by
    rw [← hscalar]
    exact hscalarCont.mono_of_mem_nhdsWithin hnearDomain
  have htimeLim : Tendsto (fun z : neckBuffer δ × ℝ => z.2 - (9 / 8 : ℝ) / S.scalar z.2 z.1)
      (𝓝[univ ×ˢ Iic 0] (x, 0)) (𝓝 (-(9 / 8 : ℝ))) := by
    convert ((continuous_snd.tendsto (x, 0)).mono_left nhdsWithin_le_nhds).sub
      ((tendsto_const_nhds (x := (9 / 8 : ℝ))).div hscalarLim (by norm_num : (1 : ℝ) ≠ 0)) using 1; norm_num
  filter_upwards [hscalarLim.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)),
    htimeLim.eventually (eventually_gt_nhds (by norm_num : -(5 / 4 : ℝ) < -(9 / 8 : ℝ))),
    self_mem_nhdsWithin] with z hq hlo hz
  refine ⟨hq, ?_⟩
  intro r hr
  change -(5 / 4 : ℝ) < z.2 + r / S.scalar z.2 z.1 ∧
    z.2 + r / S.scalar z.2 z.1 ≤ 0
  have hlower := (div_le_div_iff_of_pos_right hq).mpr hr.1
  have hupper := div_nonpos_of_nonpos_of_nonneg hr.2 hq.le
  constructor
  · rw [neg_div] at hlower
    linarith
  · exact add_nonpos hz.2 hupper



end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


private local instance (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

private theorem eventually_strict_rebased_neck_time_tower_bounds
    {δ ε : ℝ} (k : ℕ)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (x : neckBuffer δ) (hscalar : S.scalar 0 x = 1)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < ε ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    ∃ A B : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
      (∀ t, A 0 t = metricTensorField (S.base.metric t)) ∧
      (∀ t, B 0 t = metricTensorField
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
          (neckBuffer δ))) ∧
      (∀ q t, t ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
        HasDerivWithinAt (fun s => A q s y) (A (q + 1) t y) (Icc (-(5 / 4 : ℝ)) 0) t) ∧
      (∀ q t, t ∈ Icc (-(5 / 4 : ℝ)) 0 → ∀ y,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) (Icc (-(5 / 4 : ℝ)) 0) t) ∧
      ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iic 0] (x, 0),
        ∀ r q : ℕ, r + 2 * q ≤ k → ∀ t ∈ Icc (-1 : ℝ) 0, ∀ y ∈ neckClosedTest δ,
          let g := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
            (neckBuffer δ)
          tensor02CovDerivNormWith r
            ((S.scalar z.2 z.1 * (S.scalar z.2 z.1)⁻¹ ^ q) •
              A q (parabolicTime z.2 (S.scalar z.2 z.1) t) - B q t) g g y < ε := by
  let : TopologicalSpace.MetrizableSpace (neckBuffer δ) := Manifold.metrizableSpace NeckCylinderModel _
  obtain ⟨A, B, hA0, hB0, hAd, hBd, _, hseq⟩ :=
    exists_neck_metric_time_towers_with_strict_reparametrized_bounds
      (by norm_num : (-2 : ℝ) < -(5 / 4 : ℝ)) (by norm_num) k S hS Z hZ hbound
  refine ⟨A, B, hA0, hB0, hAd, hBd, ?_⟩
  have hvalid := eventually_scalar_normalized_time_window S hS x hscalar
  let Good (z : neckBuffer δ × ℝ) : Prop := ∀ r q : ℕ, r + 2 * q ≤ k →
    ∀ t ∈ Icc (-1 : ℝ) 0, ∀ y ∈ neckClosedTest δ,
      let g := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ)
      tensor02CovDerivNormWith r
        ((S.scalar z.2 z.1 * (S.scalar z.2 z.1)⁻¹ ^ q) •
          A q (parabolicTime z.2 (S.scalar z.2 z.1) t) - B q t) g g y < ε
  change ∀ᶠ z in 𝓝[univ ×ˢ Iic 0] (x, 0), Good z
  by_contra hn
  have hfreq : ∃ᶠ z in 𝓝[univ ×ˢ Iic 0] (x, 0), ¬ Good z := by
    simpa only [Filter.Frequently, not_not] using hn
  obtain ⟨z, hz, hbad⟩ := Filter.exists_seq_forall_of_frequently
    ((hfreq.and_eventually hvalid).and_eventually self_mem_nhdsWithin)
  have htime : Tendsto (fun n => (z n).2) atTop (𝓝 0) :=
    ((continuous_snd.tendsto (x, 0)).mono_left nhdsWithin_le_nhds).comp hz
  have hscalarCont := hS.scalarCont
  change ContinuousOn (fun z : ℝ × neckBuffer δ => S.scalar z.1 z.2)
    (Icc (-2 : ℝ) 0 ×ˢ univ) at hscalarCont
  have hswap : ContinuousOn (fun z : neckBuffer δ × ℝ => (z.2, z.1))
      (univ ×ˢ Icc (-2 : ℝ) 0) := (continuous_snd.prodMk continuous_fst).continuousOn
  have hmaps : MapsTo (fun z : neckBuffer δ × ℝ => (z.2, z.1))
      (univ ×ˢ Icc (-2 : ℝ) 0) (Icc (-2 : ℝ) 0 ×ˢ univ) := fun _ hh => ⟨hh.2, hh.1⟩
  have hdom : univ ×ˢ Icc (-2 : ℝ) 0 ∈ 𝓝[univ ×ˢ Iic 0] (x, 0) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((continuous_snd.continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds (by norm_num : (-2 : ℝ) < 0)))] with z hz hlo
    exact ⟨hz.1, hlo.le, hz.2⟩
  have hlim : Tendsto (fun n => S.scalar (z n).2 (z n).1) atTop (𝓝 1) := by
    rw [← hscalar]
    exact (((hscalarCont.comp hswap hmaps) (x, 0)
      ⟨mem_univ x, by norm_num, le_rfl⟩).mono_of_mem_nhdsWithin hdom).tendsto.comp hz
  have hgood := hseq (fun n => (z n).2) (fun n => S.scalar (z n).2 (z n).1) htime hlim
    (fun n t ht => by
      have hh := (hbad n).1.2.2 (show t ∈ Icc (-(9 / 8 : ℝ)) 0 from
        ⟨by linarith [ht.1], ht.2⟩)
      exact ⟨hh.1.le, hh.2⟩)
  obtain ⟨n, hn⟩ := hgood.exists
  exact (hbad n).1.1 hn

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.KappaSolutions

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem strongNeckBackgroundMetric_eq_cylinder (ε s : ℝ) (hs : s ≤ 0) :
    strongNeckBackgroundMetric ε s =
      (shrinkingCylinderMetric ⟨s, hs.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε) := by
  rw [strongNeckBackgroundMetric_of_nonpos ε s hs, shrinkingCylinderMetric_eq_flow]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (scalarOneShrinkingCylinderMetric s (hs.trans_lt zero_lt_one)).inner x.val v w =
    (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) s).inner x.val v w
  exact (scalarOneShrinkingCylinderMetric_inner s (hs.trans_lt zero_lt_one) x.val.1 x.val.2 v.1 w.1 v.2 w.2).trans
    (PDE.RicciFlow.shrinkingCylinderMetric_inner (E := ThreeSpace)
      (hs.trans_lt zero_lt_one) x.val v w).symm

private theorem exists_strongNeckWitness_of_rebased_metric_and_jets
    {δ ε t η : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 ≤ η) (hηε : η < ε)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (z : neckBuffer δ) (hq : 0 < S.scalar t z)
    (hwindow : MapsTo (parabolicTime t (S.scalar t z)) (Icc (-(9 / 8 : ℝ)) 0)
      (Ioc (-(5 / 4 : ℝ)) 0))
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f)
    (hemb : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f)
    (hcenter : f (⟨(z.val.1, 0), by
      have hi := inv_pos.mpr hε
      constructor <;> linarith⟩ : neckBuffer ε) = z)
    (T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
      (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)))
    (hmetric : ∀ r, T.base.metric r = localPullMetric
      (scaleMetric (S.scalar t z) hq (S.base.metric (t + r / S.scalar t z))) f hf)
    (J : ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer ε) ∞ 2)
    (hJzero : ∀ r, ∀ hr : r ∈ Icc (-1 : ℝ) 0, ∀ x v, J 0 r x v =
      (T.base.metric r).inner x (v 0) (v 1) -
        ((shrinkingCylinderMetric ⟨r, hr.2.trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer ε)).inner x (v 0) (v 1))
    (hJderiv : ∀ b r, r ∈ Icc (-1 : ℝ) 0 → ∀ x v,
      HasDerivWithinAt (fun s => J b s x v) (J (b + 1) r x v) (Icc (-1 : ℝ) 0) r)
    (hJbound : ∀ a b, a + 2 * b ≤ ⌈ε⁻¹⌉₊ → ∀ r, ∀ hr : r ∈ Icc (-1 : ℝ) 0,
      ∀ x ∈ neckClosedTest ε,
        tensor02CovDerivNormWith a (J b r)
          ((shrinkingCylinderMetric ⟨r, hr.2.trans_lt zero_lt_one⟩).restrictOpen
            (neckBuffer ε))
          ((shrinkingCylinderMetric ⟨r, hr.2.trans_lt zero_lt_one⟩).restrictOpen
            (neckBuffer ε)) x ≤ η) :
    ∃ W : StrongNeckWitness S z.val.1 z t ε,
      (∀ x : neckBuffer ε, W.embedding x = f x) ∧ W.jet = J := by
  let F : C(spatialNeckBuffer ε, neckBuffer δ) := ⟨f, hemb.contMDiff.continuous⟩
  have hF : IsSmoothEmbedding SpatialNeckCylinderModel NeckCylinderModel ∞ F := by
    exact hemb
  have hnorm (r : ℝ) : strongNeckNormalizedMetric S z t hq (Phi := F) hF r = T.base.metric r := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hleft := strongNeckNormalizedMetric_inner S z t hq (Phi := F) hF r x v w
    have hright := congrArg (fun g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer ε) =>
      g.inner x v w) (hmetric r)
    have hpull := localPullMetric_inner (I := NeckCylinderModel) (J := NeckCylinderModel)
      (scaleMetric (S.scalar t z) hq (S.base.metric (t + r / S.scalar t z))) f hf x v w
    have hscale := scaleMetric_inner (S.scalar t z) hq (S.base.metric (t + r / S.scalar t z))
      (f x) (mfderiv NeckCylinderModel NeckCylinderModel f x v)
      (mfderiv NeckCylinderModel NeckCylinderModel f x w)
    exact hleft.trans (hright.trans (hpull.trans hscale)).symm
  refine ⟨{
    dimension_three := by simp
    isSolution := hS
    epsilon_pos := hε
    epsilon_lt_one := hε1
    scalar_pos := hq
    time_window := ?_
    embedding := F
    smooth_embedding := hF
    marked := hcenter
    jet := J
    jet_zero := ?_
    jet_succ := hJderiv
    closeness := ?_ }, fun _ => rfl, rfl⟩
  · intro v hv
    have hl := hwindow (show (-1 : ℝ) ∈ Icc (-(9 / 8 : ℝ)) 0 from ⟨by norm_num, by norm_num⟩)
    have hu := hwindow (show (0 : ℝ) ∈ Icc (-(9 / 8 : ℝ)) 0 from ⟨by norm_num, le_rfl⟩)
    change (-2 : ℝ) ≤ v ∧ v ≤ 0
    have hlo : -(5 / 4 : ℝ) < t - (S.scalar t z)⁻¹ := by
      simpa only [parabolicTime, neg_div, one_div, sub_eq_add_neg] using hl.1
    have hup : t ≤ 0 := by simpa only [parabolicTime_zero] using hu.2
    exact ⟨by linarith [hv.1], hv.2.trans hup⟩
  · intro r hr x v
    rw [hnorm, strongNeckBackgroundMetric_eq_cylinder ε r hr.2]
    exact hJzero r hr x v
  · refine ⟨η, hη, hηε, ?_⟩
    intro a b hab r hr x hx
    rw [strongNeckBackgroundMetric_eq_cylinder ε r hr.2]
    exact hJbound a b hab r hr x hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end

section
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.KappaSolutions

private local instance (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

theorem eventually_exists_strongNeckWitness_of_reserved_time_jets
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (x : neckBuffer δ) (haxial : x.val.2 = 0) (hscalar : S.scalar 0 x = 1)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iic 0] (x, 0),
      ∃ (hq : 0 < S.scalar z.2 z.1) (f : neckBuffer ε → neckBuffer δ)
        (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
        (∀ y : neckBuffer ε, (f y).val = (y.val.1, y.val.2 + z.1.val.2)) ∧
        f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
        MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
          (Ioc (-(5 / 4 : ℝ)) 0) ∧
        ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
          IsSolutionOn T ∧
          (∀ r, T.base.metric r = localPullMetric
            (scaleMetric (S.scalar z.2 z.1) hq
              (S.base.metric (z.2 + r / S.scalar z.2 z.1))) f hf) ∧
          T.scalar 0 ⟨(z.1.val.1, 0), by
            have hi := inv_pos.mpr (hδ.trans hδε)
            constructor <;> linarith⟩ = 1 ∧
          ∃ W : StrongNeckWitness S z.1.val.1 z.1 z.2 ε,
            (∀ y : neckBuffer ε, W.embedding y = f y) ∧
            ∀ r ∈ Icc (-1 : ℝ) 0, W.jet 0 r = metricTensorField (T.base.metric r) -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε)) := by
  have hε : 0 < ε := hδ.trans hδε
  have hfit : ε⁻¹ < δ⁻¹ := inv_strictAnti₀ hδ hδε
  let η := (δ + ε) / 2
  have hδη : δ < η := by dsimp [η]; linarith
  have hηε : η < ε := by dsimp [η]; linarith
  have hη : 0 ≤ η := (hδ.trans hδη).le
  have hboundη : ∃ b : ℝ, b < η ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ b := by
    obtain ⟨b, hb, hB⟩ := hbound
    exact ⟨b, hb.trans hδη, hB⟩
  obtain ⟨A, B, hA0, hB0, hAd, hBd, hstrict⟩ :=
    eventually_strict_rebased_neck_time_tower_bounds ⌈ε⁻¹⌉₊ S hS x hscalar Z hZ hboundη
  have hspaceCont : Continuous (fun z : neckBuffer δ × ℝ => |z.1.val.2| + ε⁻¹) :=
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).abs).add continuous_const
  have hspace : ∀ᶠ z : neckBuffer δ × ℝ in 𝓝 (x, 0), |z.1.val.2| + ε⁻¹ < δ⁻¹ :=
    hspaceCont.continuousAt.eventually (eventually_lt_nhds (by simpa only [haxial, abs_zero, zero_add] using hfit))
  filter_upwards [hstrict, eventually_scalar_normalized_time_window S hS x hscalar,
    nhdsWithin_le_nhds hspace, self_mem_nhdsWithin] with z hz hwindow hfitz hmem
  have hBzero (r : ℝ) (hr : r ∈ Icc (-(5 / 4 : ℝ)) 0) : B 0 r = metricTensorField
      ((shrinkingCylinderMetric ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ)) := by
    simpa only [shrinkingCylinderMetric_eq_flow, min_eq_left hr.2] using hB0 r
  obtain ⟨f, hf, hemb, hval, hcapture, T, hT, hmetric, hbase, jet, _, hzero, hderiv, hjet⟩ :=
    exists_rebased_neckBuffer_solution_with_error_jets hε S hS z.1 hmem.2 hfitz.le hwindow.1 hwindow.2
      A B (fun r _ => hA0 r) hBzero hAd hBd ⌈ε⁻¹⌉₊ η (by
        intro a b hab r y hy
        have hb := (hz a b hab r r.property y hy).le
        simpa only [shrinkingCylinderMetric_eq_flow, parabolicTime] using hb)
  have hcenter : f (⟨(z.1.val.1, 0), by
      have hi := inv_pos.mpr hε
      constructor <;> linarith⟩ : neckBuffer ε) = z.1 := by
    apply Subtype.ext
    exact (hval _).trans (by simp only [zero_add])
  obtain ⟨W, hembed, hWjet⟩ := exists_strongNeckWitness_of_rebased_metric_and_jets
    hε hε1 hη hηε S hS z.1 hwindow.1 hwindow.2 f hf hemb hcenter T hmetric jet
    (by
      intro r hr y v
      have he := congrArg (fun J => J y v) (hzero r hr)
      simpa only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
        metricTensorField_apply, min_eq_left hr.2] using he)
    (by
      intro b r hr y v
      exact (tensor0SEvalCLM (I := NeckCylinderModel) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        r (hderiv b r hr y))
    (by intro a b hab r hr y hy; exact hjet a b hab ⟨r, hr⟩ y hy)
  refine ⟨hwindow.1, f, hf, hemb, hval, hcapture, hwindow.2, T, hT, hmetric, hbase, W, hembed, ?_⟩
  intro r hr
  have hw := congrFun (congrFun hWjet 0) r
  exact hw.trans (hzero r hr)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
end
