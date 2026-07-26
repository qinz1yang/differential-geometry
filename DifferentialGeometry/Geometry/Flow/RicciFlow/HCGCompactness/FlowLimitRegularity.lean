import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldPDE
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Curvature.OpenSubtypeNaturality
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Analysis.Calculus.SpaceJet
import DifferentialGeometry.Analysis.Calculus.TimeSliceSwap
import DifferentialGeometry.Analysis.Calculus.TimeSliceBootstrap

/-!
# Joint continuity of the AA limit metric family (C⁰ layer of the `hsmooth` brick)

Toward `MetricFamilySmoothOn` for the Arzelà–Ascoli limit family `gInf` of
MSM135 Thm 3.10 ⇐ 3.9 (the `hsmooth` input of `isSolutionOn_of_reg`,
`FlowLimitBuild.lean`), this file provides the C⁰ half: joint `(t, x)` continuity
of the chart-Gram entries of `gInf` on window × base-set products, transferred
from the window-uniform order-0 covariant convergence produced by Brick 5
(`windowGInfAll_pt`) and the joint continuity of the approximating families.

* `chartGram_sub_le` — chart-Gram entry difference of two metrics at ANY point,
  bounded by `metricDerivNorm 0` times the `gRef`-norms of the chart frame
  vectors (pointwise Cauchy–Schwarz; anchor-free version of the single-point
  bound inside `RicciFromJets.lean`).
* `chartGramBound_contOn` — the Cauchy–Schwarz factor is continuous on the base
  set (it is built from `gRef`'s own chart-Gram diagonal).
* `chartGramLim_contOn` — the transfer: window-uniform order-0 convergence on
  compacts + per-`k` joint continuity ⟹ joint continuity of the limit's
  chart-Gram entries (locally-uniform-limit argument).
* `metricTensorContLim` — the endpoint consumed by `MetricFamilySmoothOn`'s
  `metricTensor_cont` field: the `Tensor0SFamilyContinuousOnSet` package for
  `gInf` on the window, via `metricTensorCont_of_chartGram`.

Route + the remaining (C^∞) half of the brick: `FlowLimitRegularity.md`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow (SolutionOn)
open Tensor0SBundle
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- The Cauchy–Schwarz factor of `chartGram_sub_le` is continuous on the trivialization
base set: it is built from the diagonal of `gRef`'s own chart-Gram matrix
(`chartGramMatrix_entry_contMDiffOn`). -/
theorem chartGramBound_contOn
    (gRef : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank Real E)) :
    ContinuousOn (fun x : M =>
      Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
          (chartBasisVecFiber (I := I) x₀ i x))
        * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
            (chartBasisVecFiber (I := I) x₀ j x)))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hii : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x i i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ i i).continuousOn
  have hjj : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x j j)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ j j).continuousOn
  exact (Real.continuous_sqrt.comp_continuousOn hii).mul
    (Real.continuous_sqrt.comp_continuousOn hjj)

variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Pointwise chart-Gram difference bound.**  The chart-Gram entry difference of two
metrics at any point `x` (any anchor `x₀`) is bounded by the order-0 covariant seminorm
`metricDerivNorm 0` times the `gRef`-norms of the two chart frame vectors.  Pointwise
Cauchy–Schwarz (`abs_apply_le_sqrt_normSq0S` at a `gRef`-orthonormal basis); no base-set
membership is needed — off the base set both sides use the same (junk) frame values. -/
theorem chartGram_sub_le
    (gRef u u' : SmoothRiemannianMetric I M) (x₀ x : M)
    (i j : Fin (Module.finrank Real E)) :
    |chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j|
      ≤ metricDerivNorm (I := I) 0 u u' gRef x
        * (Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ i x))
          * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
              (chartBasisVecFiber (I := I) x₀ j x))) := by
  classical
  have hentry : chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j
      = (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
          ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x] := by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    have hu := Tensor0SBundle.metricTensorField_apply (I := I) u x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    have hu' := Tensor0SBundle.metricTensorField_apply (I := I) u' x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    simp only [metricDiffCovDerivAt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hu'
    change u.inner x _ _ - u'.inner x _ _
      = (metricCovDeriv (I := I) u gRef 0 x) _ - (metricCovDeriv (I := I) u' gRef 0 x) _
    rw [show (metricCovDeriv (I := I) u gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u x from rfl,
      show (metricCovDeriv (I := I) u' gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u' x from rfl,
      hu, hu']
  rw [hentry]
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have h := abs_apply_le_sqrt_normSq0S (I := I) (g := gRef) (x := x) (s := 2)
    basis hON (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
    ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x]
  refine h.trans (le_of_eq ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- **Joint continuity of the limit chart-Gram entries (the C⁰ transfer).**  If the
chart-Gram entries of each `gSeq k` are jointly continuous on the window × base-set
product and `gSeq k → gInf` in the order-0 covariant seminorm, uniformly on
window × compacts (the Brick-5 `windowGInfAll_pt` shape), then the chart-Gram entries of
`gInf` are jointly continuous on the same product.  Locally-uniform-limit argument: near
each point pick a compact neighborhood inside the base set, bound the Cauchy–Schwarz
factor there, and apply `TendstoUniformlyOn.continuousOn`. -/
theorem chartGramLim_contOn
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (x₀ : M) (i j : Fin (Module.finrank Real E))
    (hkcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  intro p₀ hp₀
  obtain ⟨hp₀t, hp₀x⟩ := hp₀
  -- a compact neighborhood of `p₀.2` inside the base set
  obtain ⟨K, hKc, hKint, hKsub⟩ := exists_compact_subset
    (trivializationAt E (TangentSpace I) x₀).open_baseSet hp₀x
  have hKne : K.Nonempty := ⟨p₀.2, interior_subset hKint⟩
  -- the Cauchy–Schwarz factor and its sup on `K`
  set c : M → ℝ := fun x =>
    Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ i x))
      * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
          (chartBasisVecFiber (I := I) x₀ j x)) with hc
  have hcnonneg : ∀ x : M, 0 ≤ c x := fun x =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨z, hzK, hz⟩ := hKc.exists_isMaxOn hKne
    ((chartGramBound_contOn (I := I) gRef x₀ i j).mono hKsub)
  set Cb : ℝ := c z with hCb
  have hCb0 : 0 ≤ Cb := hcnonneg z
  have hzle : ∀ x ∈ K, c x ≤ Cb := fun x hx => isMaxOn_iff.mp hz x hx
  -- uniform convergence of the chart-Gram entries on `Icc β ψ ×ˢ K`
  have htu : TendstoUniformlyOn
      (fun (k : ℕ) (p : ℝ × M) => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      atTop (Set.Icc β ψ ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv K hKc (ε / (Cb + 1)) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hd : metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x ≤ ε / (Cb + 1) :=
      (hk0 k hk t ht x hx).le
    have hcs := chartGram_sub_le (I := I) gRef (gSeq k t) (gInf t) x₀ x i j
    calc dist (chartGramMatrix (I := I) (gInf t) x₀ x i j)
          (chartGramMatrix (I := I) (gSeq k t) x₀ x i j)
        = |chartGramMatrix (I := I) (gSeq k t) x₀ x i j
            - chartGramMatrix (I := I) (gInf t) x₀ x i j| := by
          rw [Real.dist_eq, abs_sub_comm]
      _ ≤ metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x * c x := hcs
      _ ≤ (ε / (Cb + 1)) * Cb := by
          exact mul_le_mul hd (hzle x hx) (hcnonneg x) (by positivity)
      _ < (ε / (Cb + 1)) * (Cb + 1) := by
          have hpos : 0 < ε / (Cb + 1) := by positivity
          exact mul_lt_mul_of_pos_left (by linarith) hpos
      _ = ε := div_mul_cancel₀ ε (by positivity)
  -- continuity of the limit on the smaller product, then within the full set
  have hcOn : ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ K) :=
    htu.continuousOn (Filter.Eventually.of_forall (fun k =>
      (hkcont k).mono (Set.prod_mono le_rfl hKsub))).frequently
  have hmem : Set.Icc β ψ ×ˢ K
      ∈ 𝓝[Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet] p₀ := by
    have hnhds : (Set.univ ×ˢ interior K : Set (ℝ × M)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hKint)
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hxK⟩
    exact ⟨ht, interior_subset hxK⟩
  exact (hcOn.continuousWithinAt
    ⟨hp₀t, interior_subset hKint⟩).mono_of_mem_nhdsWithin hmem

set_option maxHeartbeats 1000000 in
/-- **`metricTensor_cont` endpoint for the AA limit.**  The joint total-space continuity
package (`Tensor0SFamilyContinuousOnSet`) for `gInf` on the window `Icc β ψ`, from the
Brick-5-shaped order-0 uniform convergence and the joint chart-Gram continuity of the
approximating families.  This is the `metricTensor_cont` field of `MetricFamilySmoothOn`
(and `coeff_cont` follows from it by evaluation) for the limit flow. -/
theorem metricTensorContLim
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (hkcont : ∀ (k : ℕ) (x₀ : M) (i j : Fin (Module.finrank Real E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 (Set.Icc β ψ)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (gInf t) x) := by
  apply metricTensorCont_of_chartGram (I := I) (K := Set.Icc β ψ) gInf
  intro x₀ i j
  have hlim := chartGramLim_contOn (I := I) gSeq gInf gRef β ψ hconv x₀ i j
    (fun k => hkcont k x₀ i j)
  have hincl : ContinuousOn
      (fun q : {t : ℝ // t ∈ Set.Icc β ψ} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ Set.Icc β ψ} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  exact hlim.comp hincl (fun q hq => ⟨q.1.2, hq⟩)

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem metricCLMSection_Ioo
    [NeZero (Module.finrank Real E)]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ Set.univ) := by
  set gsh : ℝ → SmoothRiemannianMetric I M := fun s => g (s + a) with hgsh
  have haddC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 + a, p.2)) :=
    (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
  have hsubC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 - a, p.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have hgram_sh : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (gsh p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1 + a, p.2))
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      rintro ⟨s, m⟩ ⟨hs, hm⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hm⟩
    exact (hgram x₀ i j).comp haddC.contMDiffOn hmaps
  have hsh := metricCLMSection_jointContMDiffOn_of_chartGram
    (I := I) gsh (b - a) hgram_sh
  have hmaps2 : Set.MapsTo (fun p : ℝ × M => (p.1 - a, p.2))
      (Set.Ioo a b ×ˢ (Set.univ : Set M))
      (Set.Ioo (0 : ℝ) (b - a) ×ˢ (Set.univ : Set M)) := by
    rintro ⟨t, m⟩ ⟨ht, _⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Set.mem_univ _⟩
  have hcomp := hsh.comp hsubC.contMDiffOn hmaps2
  refine hcomp.congr ?_
  rintro ⟨t, m⟩ _
  simp only [Function.comp_apply, hgsh, sub_add_cancel]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem metricFrameComp_Ioo
    [NeZero (Module.finrank Real E)]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (Set.Ioo a b ×ˢ u) := by
  have hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ u) :=
    (metricCLMSection_Ioo (I := I) g a b hgram).mono
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × M => p.2) (s := Set.Ioo a b ×ˢ u)
    (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    (v := fun p : ℝ × M => frame i p.2)
    (w := fun p : ℝ × M => frame j p.2) hψ hv hw
  intro p hp
  have hpx := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

section OpenInterval

variable [NeZero (Module.finrank Real E)]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace ConvOut

variable [I.Boundaryless]

private theorem gSeqJet_contOn
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (k r : Nat) (x₀ : P.M) (i j : Fin (Module.finrank Real E))
    {C : Set E}
    (hCtarget : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      C ⊆ (extChartAt I x₀).target)
    (hCgrow : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      (extChartAt I x₀).symm '' C ⊆ bf.grow k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j) p.2)
      (Set.Icc β ψ ×ˢ C) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  rintro q hq
  obtain ⟨hqt, hqy⟩ := hq
  set y : E := q.2 with hy
  have hytarget : y ∈ (extChartAt I x₀).target := hCtarget hqy
  set x : P.M := (extChartAt I x₀).symm y with hx
  have hxchart : x ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hytarget
  have hxy : extChartAt I x₀ x = y := by
    simpa only [x] using (extChartAt I x₀).right_inv hytarget
  have hxgrow : x ∈ bf.grow k := hCgrow ⟨y, hqy, rfl⟩
  have hxsource : x ∈ Φ.source k := bf.grow_subset k hxgrow
  obtain ⟨σi, hσi⟩ := exists_section_eqOn_compact (I := I) x₀
    ((chartModelBasis E) i) isCompact_singleton
    (Set.singleton_subset_iff.mpr (by simpa only [extChartAt_source] using hxchart))
  obtain ⟨σj, hσj⟩ := exists_section_eqOn_compact (I := I) x₀
    ((chartModelBasis E) j) isCompact_singleton
    (Set.singleton_subset_iff.mpr (by simpa only [extChartAt_source] using hxchart))
  let sourceSigma : SigmaCompactSpace ↑(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↑(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  let Vi := @Integral.Connection.restrictOpenTangentSection E inferInstance inferInstance
    inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.t2 P.smooth
    P.sigmaCompact (sourceOpen (I := I) Φ k) sourceSigma sourceT2 σi
  let Vj := @Integral.Connection.restrictOpenTangentSection E inferInstance inferInstance
    inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.t2 P.smooth
    P.sigmaCompact (sourceOpen (I := I) Φ k) sourceSigma sourceT2 σj
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : SourceDomain (I := I) Φ k → Type _) := ![Vi, Vj]
  let xU : SourceDomain (I := I) Φ k := ⟨x, hxsource⟩
  let core : E → SourceDomain (I := I) Φ k := fun z =>
    if hz : (extChartAt I x₀).symm z ∈ Φ.source k then
      ⟨(extChartAt I x₀).symm z, hz⟩
    else xU
  have htend : Filter.Tendsto (extChartAt I x₀).symm (𝓝 y) (𝓝 x) := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (x := x₀) hytarget).tendsto
    rwa [show (extChartAt I x₀).symm y = x by rfl] at h
  have hevSource : ∀ᶠ z in 𝓝 y, (extChartAt I x₀).symm z ∈ Φ.source k :=
    htend.eventually ((Φ.source_open k).mem_nhds hxsource)
  have hcoreEq : (fun z : E => ((core z : SourceDomain (I := I) Φ k) : P.M)) =ᶠ[𝓝 y]
      (extChartAt I x₀).symm := by
    filter_upwards [hevSource] with z hz
    simp only [core, dif_pos hz]
  have hsymm : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hytarget)
  have hcoreVal : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (fun z : E => ((core z : SourceDomain (I := I) Φ k) : P.M)) y :=
    hsymm.congr_of_eventuallyEq hcoreEq
  have hcore : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞) core y := by
    rw [contMDiffAt_iff] at hcoreVal ⊢
    obtain ⟨hcont, hdiff⟩ := hcoreVal
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (by simpa [Function.comp_def] using hcont), ?_⟩
    convert hdiff using 2
  have hmap : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
      (𝓘(Real, Real).prod I) (∞ : WithTop ℕ∞)
      (fun p : Real × E => (p.1, core p.2)) q := by
    exact contMDiffAt_fst.prodMk (hcore.comp q contMDiffAt_snd)
  let S := sourceFlow (I := I) Φ k (hsrc k) (htgt k)
  have hsrcSmooth := solnMetricJointAt (I := I) (x := core y) S
    (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
    (X.D.regular_isOpen.mem_nhds (hwin hqt)) V
  have hlocalMD := hsrcSmooth.comp q hmap
  let G : Real × E → Real := fun p =>
    (srcMetric (I := I) Φ hsrc htgt k p.1).inner (core p.2)
      (V 0 (core p.2)) (V 1 (core p.2))
  have hlocal : ContDiffAt Real (∞ : WithTop ℕ∞) G q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    simpa only [G, S, srcMetric, solnMetricField,
      Tensor0SBundle.metricTensorField_apply] using hlocalMD
  obtain ⟨W, hWopen, hgrowW, hWone⟩ := bf.chi_one k
  have hσi0 : ∀ᶠ z in 𝓝 x,
      σi z = TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
        x₀ ((chartModelBasis E) i) z :=
    hσi.filter_mono (nhds_le_nhdsSet (Set.mem_singleton x))
  have hσj0 : ∀ᶠ z in 𝓝 x,
      σj z = TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
        x₀ ((chartModelBasis E) j) z :=
    hσj.filter_mono (nhds_le_nhdsSet (Set.mem_singleton x))
  have hevY : ∀ᶠ z in 𝓝 y,
      z ∈ (extChartAt I x₀).target ∧
      (extChartAt I x₀).symm z ∈ Φ.source k ∧
      (extChartAt I x₀).symm z ∈ W ∧
      σi ((extChartAt I x₀).symm z) =
        TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
          x₀ ((chartModelBasis E) i)
          ((extChartAt I x₀).symm z) ∧
      σj ((extChartAt I x₀).symm z) =
        TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
          x₀ ((chartModelBasis E) j)
          ((extChartAt I x₀).symm z) := by
    filter_upwards [
      (isOpen_extChartAt_target (I := I) x₀).mem_nhds hytarget,
      hevSource, htend.eventually (hWopen.mem_nhds (hgrowW hxgrow)),
      htend.eventually hσi0, htend.eventually hσj0] with z hzt hzs hzW hzi hzj
    exact ⟨hzt, hzs, hzW, hzi, hzj⟩
  let F : Real × E → Real := fun p =>
    chartGramOnE (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j p.2
  have hFG : F =ᶠ[𝓝 q] G := by
    filter_upwards [(continuous_snd.tendsto q).eventually hevY] with p hp
    rcases hp with ⟨hpt, hps, hpW, hpi, hpj⟩
    set z : P.M := (extChartAt I x₀).symm p.2 with hz
    have hcorez : core p.2 = (⟨z, hps⟩ : SourceDomain (I := I) Φ k) := by
      simp only [core, dif_pos hps, z]
    have hViz : Vi (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σi z := by
      exact @Integral.Connection.restrictOpenTangentSection_apply E inferInstance
        inferInstance inferInstance inferInstance H inferInstance I P.M P.topology P.charted
        P.t2 P.smooth P.sigmaCompact (sourceOpen (I := I) Φ k) sourceSigma sourceT2 σi
        ⟨z, hps⟩
    have hVjz : Vj (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σj z := by
      exact @Integral.Connection.restrictOpenTangentSection_apply E inferInstance
        inferInstance inferInstance inferInstance H inferInstance I P.M P.topology P.charted
        P.t2 P.smooth P.sigmaCompact (sourceOpen (I := I) Φ k) sourceSigma sourceT2 σj
        ⟨z, hps⟩
    have hV0 : V 0 (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σi z := by
      simpa only [V, Matrix.cons_val_zero] using hViz
    have hV1 : V 1 (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σj z := by
      simpa only [V, Matrix.cons_val_one] using hVjz
    simp only [F, G, chartGramOnE_def, chartGramMatrix_apply]
    rw [hcorez]
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k p.1 z hps
      (chartBasisVecFiber (I := I) x₀ i z) (chartBasisVecFiber (I := I) x₀ j z),
      hWone z hpW, hV0, hV1]
    simp only [one_smul, sub_self, zero_smul, add_zero]
    rw [hpi, hpj]
    rfl
  have hF : ContDiffAt Real (∞ : WithTop ℕ∞) F q :=
    hlocal.congr_of_eventuallyEq hFG
  have hjet := DifferentialGeometry.Analysis.spaceJet_contAt hF r
    (WithTop.coe_le_coe.2 (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞)))
  simpa only [F] using hjet.continuousWithinAt

/-- Every finite spatial chart jet of the fixed-window limit metric is jointly
continuous in time and chart position.  This is the locally uniform limit of
the corresponding finite-stage jets; the conversion from covariant metric
convergence to chart jets is provided by `chartJet_sub_le`. -/
theorem gramJets
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (r : Nat) (x₀ : P.M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × E =>
          iteratedFDeriv Real r
            (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2)
        (Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  intro r x₀ i j p₀ hp₀
  obtain ⟨C, hCc, hCint, hCsub⟩ :=
    exists_compact_subset isOpen_interior hp₀.2
  have hCtgt : C ⊆ (extChartAt I x₀).target := hCsub.trans interior_subset
  let K : Set P.M := (extChartAt I x₀).symm '' C
  have hKc : IsCompact K := by
    dsimp only [K]
    exact hCc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) x₀).mono hCtgt)
  have hKchart : K ⊆ (chartAt H x₀).source := by
    rintro y ⟨z, hz, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (hCtgt hz)
  obtain ⟨Cjet, hCjet0, hjet⟩ :=
    chartJet_sub_le (I := I) R x₀ hKc hKchart r
  let A : Real := Cjet * ((r + 1 : Nat) : Real)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < A + 1 := by linarith
  have htu : TendstoUniformlyOn
      (fun (k : Nat) (p : Real × E) =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) p.1) x₀ i j) p.2)
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2)
      atTop (Set.Icc β ψ ×ˢ C) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let δ : Real := ε / (A + 1)
    have hδ : 0 < δ := by
      dsimp only [δ]
      positivity
    obtain ⟨k₀, hk₀⟩ := co.convPt K hKc r δ hδ
    filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    let y : P.M := (extChartAt I x₀).symm z
    have hzTarget : z ∈ (extChartAt I x₀).target := hCtgt hz
    have hyK : y ∈ K := ⟨z, hz, rfl⟩
    have hright : extChartAt I x₀ y = z :=
      (extChartAt I x₀).right_inv hzTarget
    have hsum :
        (∑ q ∈ Finset.range (r + 1),
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)
            (co.gInf t) R y) ≤ ((r + 1 : Nat) : Real) * δ := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (r + 1), δ := by
          apply Finset.sum_le_sum
          intro q hq
          exact (hk₀ k hk t ht q
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) y hyK).le
        _ = ((r + 1 : Nat) : Real) * δ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hbound := hjet
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) (co.gInf t) y hyK i j
    rw [hright] at hbound
    calc
      dist
          (iteratedFDeriv Real r
            (chartGramOnE (I := I) (co.gInf t) x₀ i j) z)
          (iteratedFDeriv Real r
            (chartGramOnE (I := I)
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀ i j) z) =
          ‖iteratedFDeriv Real r
              (chartGramOnE (I := I)
                (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀ i j) z -
            iteratedFDeriv Real r
              (chartGramOnE (I := I) (co.gInf t) x₀ i j) z‖ := by
            rw [dist_eq_norm, norm_sub_rev]
      _ ≤ Cjet * ∑ q ∈ Finset.range (r + 1),
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)
            (co.gInf t) R y := hbound
      _ ≤ Cjet * (((r + 1 : Nat) : Real) * δ) :=
        mul_le_mul_of_nonneg_left hsum hCjet0
      _ = A * δ := by
        simp only [A]
        ring
      _ < (A + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := by
        rw [mul_comm]
        simpa only [δ] using div_mul_cancel₀ ε hden.ne'
  have hkcont : ∀ᶠ k : Nat in atTop, ContinuousOn
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) p.1) x₀ i j) p.2)
      (Set.Icc β ψ ×ˢ C) := by
    obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hKc
    filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
    apply gSeqJet_contOn (Φ := Φ) (R := R) (bf := bf) (hsrc := hsrc) (htgt := htgt)
      hwin (co.φ k) r x₀ i j hCtgt
    exact hkgrow (co.φ k) (hk.trans (co.hφ.id_le k))
  have hcOn : ContinuousOn
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2)
      (Set.Icc β ψ ×ˢ C) :=
    htu.continuousOn hkcont.frequently
  have hmem : Set.Icc β ψ ×ˢ C ∈
      𝓝[Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target] p₀ := by
    have hnhds : (Set.univ ×ˢ interior C : Set (Real × E)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hCint)
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, _⟩, _, hzC⟩
    exact ⟨ht, interior_subset hzC⟩
  exact (hcOn.continuousWithinAt
    ⟨hp₀.1, interior_subset hCint⟩).mono_of_mem_nhdsWithin hmem

/-- The matrix-valued spatial chart jets of the limit metric are jointly
continuous on the fixed time window and the interior chart target. -/
private theorem gramPiJets
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (r : Nat) (x₀ : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun p : Real × E => iteratedFDeriv Real r
        (chartGramPi (I := I) (co.gInf p.1) x₀) p.2)
      (Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  let L₁ :
      (∀ _ : Fin (Module.finrank Real E), E [×r]→L[Real] Real) ≃ₗᵢ[Real]
        E [×r]→L[Real] (Fin (Module.finrank Real E) → Real) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  let L₂ :
      (∀ _ : Fin (Module.finrank Real E),
          E [×r]→L[Real] (Fin (Module.finrank Real E) → Real)) ≃ₗᵢ[Real]
        E [×r]→L[Real]
          (Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  have hentry (i j : Fin (Module.finrank Real E)) :
      ContinuousOn
        (fun p : Real × E => iteratedFDeriv Real r
          (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2)
        (Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target) :=
    gramJets (I := I) (Φ := Φ) hwin co r x₀ i j
  have hrows : ContinuousOn
      (fun p i => L₁ (fun j => iteratedFDeriv Real r
        (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2))
      (Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target) := by
    refine continuousOn_pi.2 fun i => ?_
    exact L₁.continuous.comp_continuousOn
      (continuousOn_pi.2 fun j => hentry i j)
  have hmatrix : ContinuousOn
      (fun p => L₂ (fun i => L₁ (fun j => iteratedFDeriv Real r
        (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2)))
      (Set.Icc β ψ ×ˢ interior (extChartAt I x₀).target) :=
    L₂.continuous.comp_continuousOn hrows
  refine hmatrix.congr fun p hp => ?_
  have hrTop : (r : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hentryCD (i j : Fin (Module.finrank Real E)) :
      ContDiffAt Real (r : WithTop ℕ∞)
        (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2 :=
    ((chartGramOnE_contDiffOn (I := I) (co.gInf p.1) x₀ i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds
        (interior_subset hp.2))).of_le hrTop
  have hrowCD (i : Fin (Module.finrank Real E)) :
      ContDiffAt Real (r : WithTop ℕ∞)
        (fun z j => chartGramOnE (I := I) (co.gInf p.1) x₀ i j z) p.2 :=
    contDiffAt_pi' fun j => hentryCD i j
  rw [show chartGramPi (I := I) (co.gInf p.1) x₀ =
        (fun z i j => chartGramOnE (I := I) (co.gInf p.1) x₀ i j z) from rfl,
      iteratedFDeriv_pi hrowCD le_rfl]
  simp only [L₁, L₂, ContinuousMultilinearMap.piₗᵢ_apply]
  change ContinuousMultilinearMap.pi
      (fun i => iteratedFDeriv Real r
        (fun z j => chartGramOnE (I := I) (co.gInf p.1) x₀ i j z) p.2) =
    ContinuousMultilinearMap.pi
      (fun i => ContinuousMultilinearMap.pi (fun j =>
        iteratedFDeriv Real r
          (chartGramOnE (I := I) (co.gInf p.1) x₀ i j) p.2))
  apply congrArg ContinuousMultilinearMap.pi
  funext i
  exact iteratedFDeriv_pi (fun j => hentryCD i j) le_rfl

private theorem gramPiJet_contOn
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (r : Nat) (x₀ : P.M) {y : E}
    (hy : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      y ∈ interior (extChartAt I x₀).target) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContinuousOn
      (fun t => iteratedFDeriv Real r
        (chartGramPi (I := I) (co.gInf t) x₀) y)
      (Set.Icc β ψ) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  simpa only [Function.comp_apply] using
    (gramPiJets (I := I) (Φ := Φ) hwin co r x₀).comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, hy⟩)

private theorem uniform_comp_cpt
    {ι X₀ Y Z : Type*} [UniformSpace Y] [UniformSpace Z]
    {F : ι → X₀ → Y} {f : X₀ → Y} {l : Filter ι} {K : Set X₀}
    {g : Y → Z}
    (h : TendstoUniformlyOn F f l K)
    (hK : IsCompact (f '' K))
    (hg : ∀ y ∈ f '' K, ContinuousAt g y) :
    TendstoUniformlyOn (fun i x => g (F i x)) (fun x => g (f x)) l K := by
  intro r hr
  have hlocal := hK.uniformContinuousAt_of_continuousAt g hg hr
  filter_upwards [h _ hlocal] with i hi x hx
  exact hi x hx ⟨x, hx, rfl⟩

set_option synthInstance.maxHeartbeats 100000 in
private theorem gramJet_tendsto
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (x₀ : P.M) {y : E}
    (hy : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      y ∈ interior (extChartAt I x₀).target) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    TendstoUniformlyOn
      (fun k t => Analysis.jet2
        (chartGramPi (I := I)
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀) y)
      (fun t => Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y)
      atTop (Set.Icc β ψ) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  set x : P.M := (extChartAt I x₀).symm y with hx
  have hyt : y ∈ (extChartAt I x₀).target := interior_subset hy
  have hxsrc : x ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hyt
  have hxchart : x ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hxy : extChartAt I x₀ x = y := by
    simpa only [x] using (extChartAt I x₀).right_inv hyt
  obtain ⟨C, hC, hjet⟩ := chartJet2_sub_le (I := I) R x₀
    isCompact_singleton (Set.singleton_subset_iff.mpr hxchart)
  let A : Real := C * 3
  have hA : 0 ≤ A := mul_nonneg hC (by norm_num)
  have hden : 0 < A + 1 := by linarith
  let jetNorm : NormedAddCommGroup
      (Analysis.MatJet E (Module.finrank Real E)) := inferInstance
  let jetSemi : SeminormedAddCommGroup
      (Analysis.MatJet E (Module.finrank Real E)) :=
    @NormedAddCommGroup.toSeminormedAddCommGroup _ jetNorm
  letI : SeminormedAddCommGroup
      (Analysis.MatJet E (Module.finrank Real E)) := jetSemi
  letI : SeminormedAddGroup
      (Analysis.MatJet E (Module.finrank Real E)) :=
    @SeminormedAddCommGroup.toSeminormedAddGroup _ jetSemi
  letI : MetricSpace (Analysis.MatJet E (Module.finrank Real E)) :=
    jetNorm.toMetricSpace
  letI : PseudoMetricSpace (Analysis.MatJet E (Module.finrank Real E)) :=
    jetSemi.toPseudoMetricSpace
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : Real := ε / (A + 1)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨k₀, hk₀⟩ := co.convPt {x} isCompact_singleton 2 δ hδ
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  intro t ht
  have hsum :
      (∑ q ∈ Finset.range 3,
        metricDerivNorm (I := I) q
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)
          (co.gInf t) R x) ≤ 3 * δ := by
    calc
      _ ≤ ∑ _q ∈ Finset.range 3, δ := by
        apply Finset.sum_le_sum
        intro q hq
        exact (hk₀ k hk t ht q
          (Nat.le_of_lt_succ (Finset.mem_range.mp hq)) x (Set.mem_singleton x)).le
      _ = 3 * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
  have hbound := hjet
    (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) (co.gInf t)
    x (Set.mem_singleton x)
  rw [hxy] at hbound
  calc
    dist
        (Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y)
        (Analysis.jet2
          (chartGramPi (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀) y) =
        ‖Analysis.jet2
            (chartGramPi (I := I)
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀) y -
          Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y‖ := by
            rw [dist_eq_norm, norm_sub_rev]
    _ ≤ C * ∑ q ∈ Finset.range 3,
        metricDerivNorm (I := I) q
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)
          (co.gInf t) R x := hbound
    _ ≤ C * (3 * δ) := mul_le_mul_of_nonneg_left hsum hC
    _ = A * δ := by simp only [A]; ring
    _ < (A + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by
      rw [mul_comm]
      simpa only [δ] using div_mul_cancel₀ ε hden.ne'

private theorem gramRHS_tendsto
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (x₀ : P.M) (i j : Fin (Module.finrank Real E)) {y : E}
    (hy : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      y ∈ interior (extChartAt I x₀).target) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    TendstoUniformlyOn
      (fun k t =>
        (Analysis.jetRicciFlow (chartModelBasis E)
          (Analysis.jet2
            (chartGramPi (I := I)
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀) y)) i j)
      (fun t =>
        (Analysis.jetRicciFlow (chartModelBasis E)
          (Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y)) i j)
      atTop (Set.Icc β ψ) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  set x : P.M := (extChartAt I x₀).symm y with hx
  have hyt : y ∈ (extChartAt I x₀).target := interior_subset hy
  have hxsrc : x ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hyt
  have hxchart : x ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hxchart
  have hJcont : ContinuousOn
      (fun t => Analysis.jet2
        (chartGramPi (I := I) (co.gInf t) x₀) y)
      (Set.Icc β ψ) :=
    Analysis.jet2_contOn
      (gramPiJet_contOn (I := I) (Φ := Φ) hwin co 0 x₀ hy)
      (gramPiJet_contOn (I := I) (Φ := Φ) hwin co 1 x₀ hy)
      (gramPiJet_contOn (I := I) (Φ := Φ) hwin co 2 x₀ hy)
  let J : Nat → Real → Analysis.MatJet E (Module.finrank Real E) := fun k t =>
    Analysis.jet2
      (chartGramPi (I := I)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) x₀) y
  let Jinf : Real → Analysis.MatJet E (Module.finrank Real E) := fun t =>
    Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y
  let op : Analysis.MatJet E (Module.finrank Real E) → Real := fun p =>
    (Analysis.jetRicciFlow (chartModelBasis E) p) i j
  have hJ : TendstoUniformlyOn J Jinf atTop (Set.Icc β ψ) := by
    simpa only [J, Jinf] using gramJet_tendsto (I := I) (Φ := Φ) co x₀ hy
  have hJinf : ContinuousOn Jinf (Set.Icc β ψ) := by
    simpa only [Jinf] using hJcont
  have hop : ∀ p ∈ Jinf '' Set.Icc β ψ, ContinuousAt op p := by
    intro p hp
    rcases hp with ⟨t, ht, rfl⟩
    have hval : Matrix.of (Jinf t).1 =
        chartGramMatrix (I := I) (co.gInf t) x₀ x := by
      ext a b
      rfl
    have hdet : (Matrix.of (Jinf t).1).det ≠ 0 := by
      rw [hval]
      exact (chartGramMatrix_det_pos (I := I) (co.gInf t) x₀ hxbase).ne'
    have hΦ := Analysis.contDiffAt_jetRicciFlow (chartModelBasis E) hdet
    simpa only [op, Function.comp_apply] using
      (continuousAt_apply j _).comp
        ((continuousAt_apply i _).comp hΦ.continuousAt)
  have hcomp := uniform_comp_cpt (g := op) hJ
    (isCompact_Icc.image_of_continuousOn hJinf) hop
  simpa only [J, Jinf, op] using hcomp

/-- The fixed-window limit chart-Gram entries satisfy the Ricci-flow equation
on the closed convergence window. -/
theorem gramPDE
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (x₀ : P.M) (i j : Fin (Module.finrank Real E))
    {t : Real} (ht : t ∈ Set.Icc β ψ) {y : E}
    (hy : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      y ∈ interior (extChartAt I x₀).target) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    HasDerivWithinAt
      (fun s => chartGramOnE (I := I) (co.gInf s) x₀ i j y)
      ((Analysis.jetRicciFlow (chartModelBasis E)
        (Analysis.jet2 (chartGramPi (I := I) (co.gInf t) x₀) y)) i j)
      (Set.Icc β ψ) t := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  set x : P.M := (extChartAt I x₀).symm y with hx
  have hyt : y ∈ (extChartAt I x₀).target := interior_subset hy
  have hxsrc : x ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hyt
  have hxy : extChartAt I x₀ x = y := by
    simpa only [x] using (extChartAt I x₀).right_inv hyt
  have hxchart : x ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hxchart
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x₀ := by
    rw [mem_chartLeviCivitaGoodSet_iff]
    exact ⟨hxsrc, hxbase, hxy ▸ hy⟩
  let f : Nat → Real → Real := fun k s =>
    chartGramOnE (I := I)
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) s) x₀ i j y
  let f' : Nat → Real → Real := fun k u =>
    (Analysis.jetRicciFlow (chartModelBasis E)
      (Analysis.jet2
        (chartGramPi (I := I)
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) u) x₀) y)) i j
  let g : Real → Real := fun s =>
    chartGramOnE (I := I) (co.gInf s) x₀ i j y
  let h : Real → Real := fun u =>
    (Analysis.jetRicciFlow (chartModelBasis E)
      (Analysis.jet2 (chartGramPi (I := I) (co.gInf u) x₀) y)) i j
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover {x} isCompact_singleton
  have hderiv : ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k →
      ∀ u ∈ Set.Icc β ψ, HasDerivWithinAt (f k) (f' k u)
        (Set.Icc β ψ) u := by
    refine ⟨kgrow, ?_⟩
    intro k hk u hu
    have hxgrow : x ∈ bf.grow (co.φ k) :=
      hkgrow (co.φ k) (hk.trans (co.hφ.id_le k)) (Set.mem_singleton x)
    have hmpde := gSeqExt_pde (I := I) Φ R bf hsrc htgt (co.φ k)
      β ψ u hwin hu x hxgrow
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)
    have hentry := chartGramEntryPDE_of_metricPDE (I := I)
      (fun s => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) s)
      x₀ hxgood hxy i j hmpde
    let gu : SmoothRiemannianMetric I P.M :=
      gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) u
    have hStatic : ContDiffOn Real ∞ (chartGramPi (I := I) gu x₀)
        (interior (extChartAt I x₀).target) := by
      refine contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => ?_
      exact (chartGramOnE_contDiffOn (I := I) gu x₀ a b).mono interior_subset
    have hAt : ContDiffAt Real ∞ (chartGramPi (I := I) gu x₀) y :=
      hStatic.contDiffAt (isOpen_interior.mem_nhds hy)
    have hG : DifferentiableAt Real (chartGramPi (I := I) gu x₀) y :=
      hAt.differentiableAt (by simp)
    have hG1 : ∀ᶠ z in nhds y,
        DifferentiableAt Real (chartGramPi (I := I) gu x₀) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact (hStatic.contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt
        (by simp)
    have hG2 : DifferentiableAt Real
        (fun z => fderiv Real (chartGramPi (I := I) gu x₀) z) y :=
      (hAt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
    have hjet := jetRicciFlow_chartGram (I := I) gu x₀ hy hG hG1 hG2 i j
    simpa only [f, f', gu] using hentry.congr_deriv hjet.symm
  have hfg : ∀ u ∈ Set.Icc β ψ,
      Filter.Tendsto (fun k => f k u) atTop (nhds (g u)) := by
    intro u hu
    have hconv : ∀ ε : Real, 0 < ε → ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k →
        metricDerivNorm (I := I) 0
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) u)
          (co.gInf u) R x < ε := by
      intro ε hε
      obtain ⟨k₀, hk₀⟩ := co.convPt {x} isCompact_singleton 0 ε hε
      exact ⟨k₀, fun k hk => hk₀ k hk u hu 0 le_rfl x (Set.mem_singleton x)⟩
    have hinner := metricInner_tendsto (I := I)
      (fun k => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) u)
      (co.gInf u) R x hconv
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)
    simpa only [f, g, chartGramOnE_def, chartGramMatrix_apply, x] using hinner
  have hRHS := gramRHS_tendsto (I := I) (Φ := Φ) hwin co x₀ i j hy
  rw [Metric.tendstoUniformlyOn_iff] at hRHS
  have hunif : ∀ ε : Real, 0 < ε → ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k →
      ∀ u ∈ Set.Icc β ψ, |f' k u - h u| < ε := by
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 (hRHS ε hε)
    refine ⟨k₀, fun k hk u hu => ?_⟩
    have hd := hk₀ k hk u hu
    rw [Real.dist_eq] at hd
    simpa only [f', h, abs_sub_comm] using hd
  exact hasDeriv_lim_tail (convex_Icc β ψ) ht f f' g h hderiv hfg hunif

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] in
/-- Transfer a jointly smooth scalar chart-Gram readout on the model chart
back to the corresponding manifold chart-Gram entry. -/
private theorem gramModel_to_mfld
    (g : Real → letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    {β ψ : Real} (x₀ : P.M) (i j : Fin (Module.finrank Real E))
    (hmodel : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ContDiffOn Real ∞
        (fun p : Real × E => chartGramOnE (I := I) (g p.1) x₀ i j p.2)
        (Set.Ioo β ψ ×ˢ interior (extChartAt I x₀).target)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
      (fun p : Real × P.M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Set.Ioo β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  let S : Set (Real × P.M) :=
    Set.Ioo β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
  let U : Set (Real × E) :=
    Set.Ioo β ψ ×ˢ interior (extChartAt I x₀).target
  let f : Real × P.M → Real × E := fun p => (p.1, extChartAt I x₀ p.2)
  have hf : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real × E) ∞ f S := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)).comp
      contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
  have hmaps : Set.MapsTo f S U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hxsrc : x ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
    exact ⟨ht, extChartAt_target_subset_interior_of_boundaryless (I := I) x₀
      ((extChartAt I x₀).map_source hxsrc)⟩
  have hcomp : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
      (fun p : Real × P.M =>
        chartGramOnE (I := I) (g p.1) x₀ i j (extChartAt I x₀ p.2)) S :=
    hmodel.contMDiffOn.comp hf hmaps
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ ⟨_, hx⟩
  have hxsrc : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using hx
  change chartGramMatrix (I := I) (g t) x₀ x i j =
    chartGramMatrix (I := I) (g t) x₀
      ((extChartAt I x₀).symm (extChartAt I x₀ x)) i j
  rw [(extChartAt I x₀).left_inv hxsrc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Fixed-window joint spacetime smoothness of the limit metric in the
trivialization-based chart-Gram readout. This is the remaining analytic
regularity frontier. -/
theorem gramSmooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  let MatRow := Fin (Module.finrank Real E) → Real
  let MatVal := Fin (Module.finrank Real E) → MatRow
  let MatD1 := E →L[Real] MatVal
  let MatD2 := E →L[Real] MatD1
  letI : NormedAddCommGroup MatRow := Pi.normedAddCommGroup
  letI : NormedSpace Real MatRow := Pi.normedSpace
  letI : NormedAddCommGroup MatVal := Pi.normedAddCommGroup
  letI : NormedSpace Real MatVal := Pi.normedSpace
  letI : NormedAddCommGroup MatD1 := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real MatD1 := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup MatD2 := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real MatD2 := ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (MatD1 × MatD2) := Prod.normedAddCommGroup
  letI : NormedSpace Real (MatD1 × MatD2) := Prod.normedSpace
  letI : NormedAddCommGroup (MatVal × (MatD1 × MatD2)) := Prod.normedAddCommGroup
  letI : NormedSpace Real (MatVal × (MatD1 × MatD2)) := Prod.normedSpace
  intro x₀ i j
  let G : Real → E →
      (Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real) :=
    fun t => chartGramPi (I := I) (co.gInf t) x₀
  let J : Set Real := Set.Ioo β ψ
  let V : Set E := interior (extChartAt I x₀).target
  let U : Set (Real × E) := J ×ˢ V
  let RHS : Real → E →
      (Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real) :=
    fun t y => Analysis.jetRicciFlow (chartModelBasis E) (Analysis.jet2 (G t) y)
  let Ω : Set (Analysis.MatJet E (Module.finrank Real E)) :=
    {p | (Matrix.of p.1).det ≠ 0}
  have hJ : IsOpen J := isOpen_Ioo
  have hV : IsOpen V := isOpen_interior
  have hU : IsOpen U := hJ.prod hV
  have hGs : ∀ t ∈ J, ContDiffOn Real ∞ (G t) V := by
    intro t ht
    refine contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => ?_
    exact (chartGramOnE_contDiffOn (I := I) (co.gInf t) x₀ a b).mono interior_subset
  have hG₁s : ∀ t ∈ J,
      ContDiffOn Real ∞ (fun y => fderiv Real (G t) y) V := by
    intro t ht y hy
    have hAt : ContDiffAt Real ∞ (G t) y :=
      (hGs t ht y hy).contDiffAt (hV.mem_nhds hy)
    exact (hAt.fderiv_right (m := ∞)
      (by rw [ENat.coe_top_add_one])).contDiffWithinAt
  have hG₂s : ∀ t ∈ J,
      ContDiffOn Real ∞
        (fun y => fderiv Real (fun z => fderiv Real (G t) z) y) V := by
    intro t ht y hy
    have hAt : ContDiffAt Real ∞ (fun z => fderiv Real (G t) z) y :=
      (hG₁s t ht y hy).contDiffAt (hV.mem_nhds hy)
    exact (hAt.fderiv_right (m := ∞)
      (by rw [ENat.coe_top_add_one])).contDiffWithinAt
  have hJetSlices : ∀ t ∈ J,
      ContDiffOn Real ∞ (fun y => Analysis.jet2 (G t) y) V := by
    intro t ht
    simpa only [Analysis.jet2] using
      (hGs t ht).prodMk ((hG₁s t ht).prodMk (hG₂s t ht))
  have hdet : Continuous
      (fun p : Analysis.MatJet E (Module.finrank Real E) => (Matrix.of p.1).det) :=
    (Analysis.contDiff_det_of_entries
      (fun p : Analysis.MatJet E (Module.finrank Real E) => Matrix.of p.1)
      (fun a b => Analysis.contDiff_jetVal a b)).continuous
  have hΩ : IsOpen Ω := by
    simpa only [Ω, Set.mem_setOf_eq] using
      (isOpen_ne_fun hdet (continuous_const : Continuous
        (fun _ : Analysis.MatJet E (Module.finrank Real E) => (0 : Real))))
  have hΦ : ContDiffOn Real ∞
      (Analysis.jetRicciFlow (chartModelBasis E)) Ω := by
    intro p hp
    exact (Analysis.contDiffAt_jetRicciFlow (chartModelBasis E) hp).contDiffWithinAt
  have hJetMaps : Set.MapsTo
      (Function.uncurry (fun t y => Analysis.jet2 (G t) y)) U Ω := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    change (Matrix.of (Analysis.jet2 (G t) y).1).det ≠ 0
    set x : P.M := (extChartAt I x₀).symm y with hx
    have hyt : y ∈ (extChartAt I x₀).target := interior_subset hy
    have hxsrc : x ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hyt
    have hxbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source,
        ← extChartAt_source_eq_chartAt_source (I := I)]
      exact hxsrc
    have hmat : Matrix.of (Analysis.jet2 (G t) y).1 =
        chartGramMatrix (I := I) (co.gInf t) x₀ x := by
      ext a b
      simp only [Analysis.jet2, G, Matrix.of_apply, chartGramPi_apply,
        chartGramOnE_def, hx]
    rw [hmat]
    exact (chartGramMatrix_det_pos (I := I) (co.gInf t) x₀ hxbase).ne'
  have hRhsSlices : ∀ t ∈ J, ContDiffOn Real ∞ (RHS t) V := by
    intro t ht
    have hmaps : Set.MapsTo (fun y => Analysis.jet2 (G t) y) V Ω := by
      intro y hy
      have hty : (t, y) ∈ U := ⟨ht, hy⟩
      exact hJetMaps hty
    simpa only [RHS, Function.comp_apply] using
      hΦ.comp (hJetSlices t ht) hmaps
  have hpde : ∀ t ∈ J, ∀ y ∈ V,
      HasDerivAt (fun s => G s y) (RHS t y) t := by
    intro t ht y hy
    refine hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b => ?_
    have hab := gramPDE (I := I) (Φ := Φ) hwin co x₀ a b
      (t := t) (Set.Ioo_subset_Icc_self ht) (y := y) hy
    have hab' := hab.hasDerivAt (Icc_mem_nhds_iff.mpr ht)
    simpa only [G, RHS, chartGramPi_apply] using hab'
  have hbase : Analysis.SpaceJetDiff 0 G J V := by
    intro r
    apply contDiffOn_zero.2
    exact (gramPiJets (I := I) (Φ := Φ) hwin co r x₀).mono
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  have hAll : ∀ q : Nat, Analysis.SpaceJetDiff q G J V := by
    intro q
    induction q with
    | zero => exact hbase
    | succ q ih =>
        have hJetQ : Analysis.SpaceJetDiff q
            (fun t y => Analysis.jet2 (G t) y) J V :=
          ih.jet2 hV hGs
        have hRhsQ : Analysis.SpaceJetDiff q RHS J V := by
          simpa only [RHS] using
            Analysis.spaceJet_comp
              (Φ := Analysis.jetRicciFlow (chartModelBasis E))
              (u := fun t y => Analysis.jet2 (G t) y)
              hJ hV hΩ hJetMaps hΦ hJetSlices hJetQ
        intro r
        have hpdeR : ∀ p ∈ U,
            HasDerivAt
              (fun s => iteratedFDeriv Real r (G s) p.2)
              (iteratedFDeriv Real r (RHS p.1) p.2) p.1 := by
          intro p hp
          exact Analysis.hasDerivAt_iterF (G := G) (R := RHS) hJ hV r
            hGs hRhsSlices hpde (fun m _ => (hRhsQ m).continuousOn)
            (t := p.1) hp.1 (x := p.2) hp.2
        have hslice : ∀ p ∈ U,
            HasFDerivAt
              (fun y => iteratedFDeriv Real r (G p.1) y)
              (fderiv Real (iteratedFDeriv Real r (G p.1)) p.2) p.2 := by
          intro p hp
          have hAt : ContDiffAt Real ∞ (G p.1) p.2 :=
            (hGs p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2)
          have hJetAt : ContDiffAt Real 1
              (iteratedFDeriv Real r (G p.1)) p.2 :=
            hAt.iteratedFDeriv_right (m := 1) (i := r)
              (by exact_mod_cast le_top)
          exact (hJetAt.differentiableAt (by norm_num)).hasFDerivAt
        have hstep := Analysis.contDiffOn_succ_of_pde (q := q) hU hpdeR hslice
          (hRhsQ r) (ih.jet_fderiv r)
        simpa only [Nat.succ_eq_add_one] using hstep
  have hGinf : ContDiffOn Real ∞ (Function.uncurry G) U := by
    rw [contDiffOn_infty]
    intro q
    have hraw :=
      (continuousMultilinearCurryFin0 Real E
        (Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real)).contDiff.comp_contDiffOn
        (hAll q 0)
    exact hraw.congr fun p _ => by
      rcases p with ⟨t, y⟩
      rfl
  have hrow : ContDiffOn Real ∞
      (fun p : Real × E => (Function.uncurry G p) i) U :=
    (contDiffOn_pi.mp hGinf) i
  have hentry : ContDiffOn Real ∞
      (fun p : Real × E => (Function.uncurry G p) i j) U :=
    (contDiffOn_pi.mp hrow) j
  have hmodel : ContDiffOn Real ∞
      (fun p : Real × E => chartGramOnE (I := I) (co.gInf p.1) x₀ i j p.2)
      (Set.Ioo β ψ ×ˢ interior (extChartAt I x₀).target) := by
    refine hentry.congr fun p _ => ?_
    rcases p with ⟨t, y⟩
    rfl
  exact gramModel_to_mfld (I := I) (g := co.gInf) x₀ i j hmodel

end ConvOut

namespace OpenConvOut

set_option maxHeartbeats 1600000 in
/-- Assemble joint smoothness of the open-interval limit metric from joint
chart-Gram smoothness on every canonical compact window. -/
theorem smoothMetric
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (hgramWin : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
          (Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
              (RealTimeInterval.openWindowRight b t₀ n) ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    MetricFamilySmoothOn (I := I) (M := P.M)
      (RealTimeInterval.openInterval a b t₀ ht₀)
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M)
          (RealTimeInterval.openInterval a b t₀ ht₀)).family := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  have hgram : ∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j p hp
    obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ hp.1
    have htn : p.1 ∈ Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
        (RealTimeInterval.openWindowRight b t₀ n) := Icc_mem_nhds_iff.mp hn
    have hlocal := hgramWin n x₀ i j p ⟨htn, hp.2⟩
    have hnhds : Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
          (RealTimeInterval.openWindowRight b t₀ n) ×ˢ
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 p :=
      prod_mem_nhds (Ioo_mem_nhds htn.1 htn.2)
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hp.2)
    exact (hlocal.contMDiffAt hnhds).contMDiffWithinAt
  have hcontTensor : Tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2
      (Set.Ioo a b) (fun t x => metricTensorField (I := I) (co.gInf t) x) := by
    apply metricTensorCont_of_chartGram (I := I) (K := Set.Ioo a b) co.gInf
    intro x₀ i j
    have hincl : ContinuousOn
        (fun q : {t : ℝ // t ∈ Set.Ioo a b} × P.M => ((q.1 : ℝ), q.2))
        {q : {t : ℝ // t ∈ Set.Ioo a b} × P.M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    exact (hgram x₀ i j).continuousOn.comp hincl (fun q hq => ⟨q.1.2, hq⟩)
  refine ⟨?_, ?_, hcontTensor, ?_⟩
  · intro x X Y
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun t : ℝ => (t, x)) (Set.Ioo a b) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hψ' : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun t : ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
          ((co.gInf t).inner x)) (Set.Ioo a b) :=
      (metricCLMSection_Ioo (I := I) co.gInf a b hgram).comp
        hcurve (fun t ht => ⟨ht, Set.mem_univ _⟩)
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x X)
        (Set.Ioo a b) := contMDiffOn_const
    have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x Y)
        (Set.Ioo a b) := contMDiffOn_const
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := P.M)) (E₂ := TangentSpace I (M := P.M))
      (E₃ := Bundle.Trivial P.M ℝ) (b := fun _ : ℝ => x)
      (ψ := fun t : ℝ => (co.gInf t).inner x)
      (v := fun _ : ℝ => X) (w := fun _ : ℝ => Y) hψ' hv hw
    have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (co.gInf t).inner x X Y) (Set.Ioo a b) := by
      intro t ht
      have hpt := happ t ht
      rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
      exact hpt.2
    exact hscalar.contDiffOn
  · intro x X Y
    have hbase : ContinuousOn
        (fun s : ℝ => metricTensorField (I := I) (co.gInf s) x (vec2 X Y))
        (Set.Ioo a b) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hcontTensor.eval_continuous (P := {s : ℝ // s ∈ Set.Ioo a b})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun p => p.2) continuous_const
        (v := fun i _ => vec2 X Y i) (fun _ => continuous_const)
    refine hbase.congr (fun s _ => ?_)
    simp [metricTensorField_apply, vec2]
  · intro Idx _ frame u hframe i j
    exact metricFrameComp_Ioo (I := I) co.gInf a b hgram frame hframe i j

variable [I.Boundaryless]

/-- Joint chart-Gram smoothness of the glued limit metric on the ambient open
time interval. -/
theorem gramSmooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro x₀ i j p hp
  obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ hp.1
  have htn : p.1 ∈ Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n) := Icc_mem_nhds_iff.mp hn
  have hwin : RealTimeInterval.openWindow a b t₀ n ⊆ X.D.regular := by
    intro t ht
    have htOpen := RealTimeInterval.openWindow_subset ht₀ n ht
    simpa only [hD, RealTimeInterval.openInterval] using htOpen
  have hlocal := ConvOut.gramSmooth (I := I) (Φ := Φ) hwin
    (OpenConvOut.at_window Φ co n) x₀ i j p ⟨htn, hp.2⟩
  have hnhds : Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
        (RealTimeInterval.openWindowRight b t₀ n) ×ˢ
      (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 p :=
    prod_mem_nhds (Ioo_mem_nhds htn.1 htn.2)
      ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hp.2)
  exact (hlocal.contMDiffAt hnhds).contMDiffWithinAt

/-- The fixed-window analytic theorem supplies the open-interval metric
regularity package on the one subsequence carried by `OpenConvOut`. -/
theorem smoothMetric_of_conv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    MetricFamilySmoothOn (I := I) (M := P.M)
      (RealTimeInterval.openInterval a b t₀ ht₀)
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M)
          (RealTimeInterval.openInterval a b t₀ ht₀)).family := by
  apply OpenConvOut.smoothMetric (Φ := Φ) ht₀ co
  intro n
  apply ConvOut.gramSmooth (Φ := Φ) (co := OpenConvOut.at_window Φ co n)
  intro t ht
  have htOpen := RealTimeInterval.openWindow_subset ht₀ n ht
  simpa only [hD, RealTimeInterval.openInterval] using htOpen

end OpenConvOut

end OpenInterval

end HCGCompactness
end DifferentialGeometry
