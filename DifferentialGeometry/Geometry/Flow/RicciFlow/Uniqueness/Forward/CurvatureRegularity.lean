import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.DensityRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.TensorLifts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.RegularityWithin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

omit [T2Space M] [CompactSpace M] in
private theorem prod_open_nhds {S U : Set M} (hS : IsOpen S) {x₀ : M} (hx₀ : x₀ ∈ S)
    (hSU : S ⊆ U) (J : Set Real) (t : Real) :
    J ×ˢ S ∈ 𝓝[J ×ˢ U] ((t, x₀) : Real × M) := by
  have hset :
      (J ×ˢ U) ∩ ((fun p : Real × M => p.2) ⁻¹' S) = J ×ˢ S := by
    ext p
    constructor
    · rintro ⟨⟨hpJ, -⟩, hpS⟩
      exact ⟨hpJ, hpS⟩
    · rintro ⟨hpJ, hpS⟩
      exact ⟨⟨hpJ, hSU hpS⟩, hpS⟩
  have hopen : ((fun p : Real × M => p.2) ⁻¹' S) ∈ 𝓝 ((t, x₀) : Real × M) :=
    (hS.preimage continuous_snd).mem_nhds hx₀
  have h := inter_mem_nhdsWithin
    (J ×ˢ U) (a := ((t, x₀) : Real × M)) hopen
  rwa [hset] at h

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private lemma local_frame_eq_chart
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank Real E)) :
    (trivializationAt E (TangentSpace I) α).localFrame (chartModelBasis E) i x =
      chartBasisVecFiber (I := I) α i x := by
  rw [(trivializationAt E (TangentSpace I) α).localFrame_apply_of_mem_baseSet
    (chartModelBasis E) hx]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma local_chr_eq_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j k : Fin (Module.finrank Real E)) :
    let e := trivializationAt E (TangentSpace I) α
    let frame := e.localFrame (chartModelBasis E)
    let hframe := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
      (chartModelBasis E)
    christoffelSymbolInFrame (metricCov (I := I) g) frame hframe x i j k =
      chartChristoffel (I := I) g α i j k (extChartAt I α x) := by
  dsimp
  let e := trivializationAt E (TangentSpace I) α
  let frame := e.localFrame (chartModelBasis E)
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
    (chartModelBasis E)
  have hxbase : x ∈ e.baseSet := by
    simpa only [e] using chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hcov :
      (metricCov (I := I) g) (frame j) x (frame i x) =
        ∑ l : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α i j l (extChartAt I α x) •
            frame l x := by
    have hframe_diff :=
      (hframe.contMDiffAt e.open_baseSet hxbase j).mdifferentiableAt (by simp)
    have hchart_diff :=
      chartBasisVec_alpha_mdifferentiableAt (I := I) α j hx
    have hev :
        (fun y : M => frame j y) =ᶠ[𝓝 x]
          (fun y : M => chartBasisVecFiber (I := I) α j y) := by
      filter_upwards [e.open_baseSet.mem_nhds hxbase] with y hy
      exact local_frame_eq_chart (I := I) α hy j
    have hcov_congr :
        (metricCov (I := I) g).toFun (frame j) x =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) α j y) x := by
      change
        (LeviCivita (I := I) g).toFun (frame j) x =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) α j y) x
      exact
        (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
          hframe_diff hchart_diff Filter.univ_mem hev
    calc
      (metricCov (I := I) g) (frame j) x (frame i x) =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) α j y) x
            (frame i x) :=
        congrArg (fun L => L (frame i x)) hcov_congr
      _ = (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) α j y) x
            (chartBasisVecFiber (I := I) α i x) := by
        have hi : frame i x = chartBasisVecFiber (I := I) α i x := by
          simpa only [frame, e] using local_frame_eq_chart (I := I) α hxbase i
        rw [hi]
      _ = ∑ l : Fin (Module.finrank Real E),
            chartChristoffel (I := I) g α i j l (extChartAt I α x) •
              chartBasisVecFiber (I := I) α l x :=
        LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α i j hx
      _ = ∑ l : Fin (Module.finrank Real E),
            chartChristoffel (I := I) g α i j l (extChartAt I α x) •
              frame l x := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have hl : frame l x = chartBasisVecFiber (I := I) α l x := by
          simpa only [frame, e] using local_frame_eq_chart (I := I) α hxbase l
        rw [hl]
  have hcoeff (l : Fin (Module.finrank Real E)) :
      hframe.coeff k x (frame l x) = if l = k then 1 else 0 := by
    rw [hframe.coeff_apply_of_mem hxbase]
    change
      ((hframe.toBasisAt hxbase).repr
        (e.localFrame (chartModelBasis E) l x)) k =
          if l = k then 1 else 0
    rw [← hframe.toBasisAt_coe hxbase l]
    rw [(hframe.toBasisAt hxbase).repr_self]
    simp [Finsupp.single_apply]
  change christoffelSymbolInFrame (metricCov (I := I) g) frame hframe x i j k =
    chartChristoffel (I := I) g α i j k (extChartAt I α x)
  rw [christoffelSymbolInFrame_eval, hcov, map_sum]
  simp only [map_smul, hcoeff]
  simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem nablaChartJoint
    {s : ℕ}
    (g : Real → SmoothRiemannianMetric I M)
    (A : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {J : Set Real}
    (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (L : Fin s → Fin (Module.finrank Real E)) {t : Real}, t ∈ J →
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          A p.1 p.2
            (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (L a) p.2))
        (J ×ˢ (Set.univ : Set M)) (t, x₀))
    (K : Fin (s + 1) → Fin (Module.finrank Real E))
    {t : Real} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        metricNabla0S (I := I) (g p.1) (A p.1) p.2
          (fun a : Fin (s + 1) =>
            chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let frame := e.localFrame (chartModelBasis E)
  let hframeInf := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
    (chartModelBasis E)
  let hframe₁ := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
    (chartModelBasis E)
  let chr : Real → M → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun r y => christoffelSymbolInFrame (metricCov (I := I) (g r))
      frame hframe₁ y
  have hxbase : x₀ ∈ e.baseSet := by
    simp [e]
  have hG := genGramOn_of_field (I := I) g x₀ hgram
  have hchr : ∀ i j l : Fin (Module.finrank Real E),
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chr p.1 p.2 i j l)
        (J ×ˢ e.baseSet) (t, x₀) := by
    intro i j l
    have hchart := christWithinM (I := I) g x₀ hG i j l ht
      (mem_chart_source H x₀)
    have hchart' :
        ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            chartChristoffel (I := I) (g p.1) x₀ i j l
              (extChartAt I x₀ p.2))
          (J ×ˢ e.baseSet) (t, x₀) := by
      simpa only [e, trivializationAt_baseSet_eq_chartAt_source] using hchart
    have hgood :
        J ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ∈
          𝓝[J ×ˢ e.baseSet] ((t, x₀) : Real × M) := by
      apply prod_open_nhds
        (chartLeviCivitaGoodSet_isOpen (I := I) x₀)
        (self_mem_chartLeviCivitaGoodSet (I := I) x₀)
      · intro y hy
        simpa [e] using chartLeviCivitaGoodSet_mem_baseSet (I := I) hy
    have heq :
        (fun p : Real × M => chr p.1 p.2 i j l) =ᶠ[
          𝓝[J ×ˢ e.baseSet] ((t, x₀) : Real × M)]
        (fun p : Real × M =>
          chartChristoffel (I := I) (g p.1) x₀ i j l
            (extChartAt I x₀ p.2)) := by
      filter_upwards [hgood] with p hp
      simpa [chr, frame, hframe₁] using
        (local_chr_eq_chart (I := I) (g p.1) x₀ hp.2 i j l)
    exact hchart'.congr_of_eventuallyEq heq
      (heq.self_of_nhdsWithin ⟨ht, hxbase⟩)
  have hbase : ∀ L : Fin s → Fin (Module.finrank Real E),
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => frameComp0S (I := I) (A p.1) frame p.2 L)
        (J ×ˢ e.baseSet) (t, x₀) := by
    intro L
    have hA' := (hA L ht).mono
      (Set.prod_mono (Set.Subset.refl J) (Set.subset_univ e.baseSet))
    apply hA'.congr
    · intro p hp
      simp only [frameComp0S]
      congr 1
      funext a
      exact local_frame_eq_chart (I := I) x₀ hp.2 (L a)
    · simp only [frameComp0S]
      congr 1
      funext a
      exact local_frame_eq_chart (I := I) x₀ hxbase (L a)
  have hext := prodExtDeriv_joint (I := I) e.open_baseSet ht hxbase
    (hF := hbase (Fin.tail K))
    (hX := hframeInf.contMDiffAt e.open_baseSet hxbase (K 0))
  have hsum :
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          ∑ q : Fin s, ∑ l : Fin (Module.finrank Real E),
            chr p.1 p.2 (K 0) (Fin.tail K q) l *
              frameComp0S (I := I) (A p.1) frame p.2
                (Function.update (Fin.tail K) q l))
        (J ×ˢ e.baseSet) (t, x₀) := by
    refine ContMDiffWithinAt.sum fun q _ =>
      ContMDiffWithinAt.sum fun l _ => ?_
    exact (hchr (K 0) (Fin.tail K q) l).mul
      (hbase (Function.update (Fin.tail K) q l))
  have hstep := hext.sub hsum
  have hcov :
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          covDerivStepComp
            (frameExtData (I := I) frame
              (fun y : M => frameComp0S (I := I) (A p.1) frame y) p.2)
            (chr p.1 p.2)
            (frameComp0S (I := I) (A p.1) frame p.2) K)
        (J ×ˢ e.baseSet) (t, x₀) := by
    simpa only [covDerivStepComp, frameExtData] using hstep
  have hintrinsic :
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          metricNabla0S (I := I) (g p.1) (A p.1) p.2
            (fun a : Fin (s + 1) =>
              chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (J ×ˢ e.baseSet) (t, x₀) := by
    apply hcov.congr
    · intro p hp
      have hbridge := covDerivStepComp_frameComp_eq
        (I := I) (metricCov (I := I) (g p.1)) (A p.1)
        (metricNabla0S (I := I) (g p.1) (A p.1))
        (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := M) s (metricCov (I := I) (g p.1)) (A p.1) _)
        frame hframe₁ e.open_baseSet hp.2 K
      calc
        metricNabla0S (I := I) (g p.1) (A p.1) p.2
            (fun a => chartBasisVecFiber (I := I) x₀ (K a) p.2) =
            metricNabla0S (I := I) (g p.1) (A p.1) p.2
              (frameTuple (I := I) frame p.2 K) := by
          congr 1
          funext a
          exact (local_frame_eq_chart (I := I) x₀ hp.2 (K a)).symm
        _ = covDerivStepComp
            (frameExtData (I := I) frame
              (fun y : M => frameComp0S (I := I) (A p.1) frame y) p.2)
            (chr p.1 p.2)
            (frameComp0S (I := I) (A p.1) frame p.2) K := by
          simpa only [chr] using hbridge.symm
    · have hbridge := covDerivStepComp_frameComp_eq
        (I := I) (metricCov (I := I) (g t)) (A t)
        (metricNabla0S (I := I) (g t) (A t))
        (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := M) s (metricCov (I := I) (g t)) (A t) _)
        frame hframe₁ e.open_baseSet hxbase K
      calc
        metricNabla0S (I := I) (g t) (A t) x₀
            (fun a => chartBasisVecFiber (I := I) x₀ (K a) x₀) =
            metricNabla0S (I := I) (g t) (A t) x₀
              (frameTuple (I := I) frame x₀ K) := by
          congr 1
          funext a
          exact (local_frame_eq_chart (I := I) x₀ hxbase (K a)).symm
        _ = covDerivStepComp
            (frameExtData (I := I) frame
              (fun y : M => frameComp0S (I := I) (A t) frame y) x₀)
            (chr t x₀)
            (frameComp0S (I := I) (A t) frame x₀) K := by
          simpa only [chr] using hbridge.symm
  exact hintrinsic.mono_of_mem_nhdsWithin
    (prod_open_nhds e.open_baseSet hxbase (Set.subset_univ e.baseSet) J t)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem crossRm1ChartJoint
    (gL gC gD : Real → SmoothRiemannianMetric I M) {J : Set Real}
    (x₀ : M)
    (hgramL : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 5 → Fin (Module.finrank Real E))
    {t : Real} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        metricNabla0S (I := I) (gD p.1)
          (CovariantDerivative.rm04Section (I := I) (gL p.1)
            (metricCov (I := I) (gC p.1))
            (metricCov_smooth (I := I) (gC p.1))) p.2
          (fun a : Fin 5 =>
            chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  apply nablaChartJoint (I := I) gD
    (fun r => CovariantDerivative.rm04Section (I := I) (gL r)
      (metricCov (I := I) (gC r)) (metricCov_smooth (I := I) (gC r)))
    x₀ hgramD
  · intro L r hr
    simpa only [CovariantDerivative.rm04Section_apply] using
      (rm04ChartJoint (I := I) gL gC x₀ hgramL hgramC L hr)
  · exact ht

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem crossRm2ChartJoint
    (gL gC gD : Real → SmoothRiemannianMetric I M) {J : Set Real}
    (x₀ : M)
    (hgramL : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 6 → Fin (Module.finrank Real E))
    {t : Real} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        metricNabla0S (I := I) (gD p.1)
          (metricNabla0S (I := I) (gD p.1)
            (CovariantDerivative.rm04Section (I := I) (gL p.1)
              (metricCov (I := I) (gC p.1))
              (metricCov_smooth (I := I) (gC p.1)))) p.2
          (fun a : Fin 6 =>
            chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  apply nablaChartJoint (I := I) gD
    (fun r => metricNabla0S (I := I) (gD r)
      (CovariantDerivative.rm04Section (I := I) (gL r)
        (metricCov (I := I) (gC r)) (metricCov_smooth (I := I) (gC r))))
    x₀ hgramD
  · intro L r hr
    exact crossRm1ChartJoint (I := I) gL gC gD x₀
      hgramL hgramC hgramD L hr
  · exact ht

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem nablaKRmChartJoint
    (g : Real → SmoothRiemannianMetric I M) {J : Set Real}
    (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank Real E),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (k : ℕ) (K : Fin (4 + k) → Fin (Module.finrank Real E))
    {t : Real} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        nablaKRm04Field (I := I)
          (solOfMetric (I := I)
            (D := RealTimeInterval.univ 0) g) p.1 k p.2
          (fun a : Fin (4 + k) =>
            chartBasisVecFiber (I := I) x₀ (K a) p.2))
      (J ×ˢ (Set.univ : Set M)) (t, x₀) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let frame := e.localFrame (chartModelBasis E)
  let hframeInf := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
    (chartModelBasis E)
  let hframe₁ := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
    (chartModelBasis E)
  let S := solOfMetric (I := I) (D := RealTimeInterval.univ 0) g
  let chr : Real → M → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe₁ y
  let base : Real → M → (Fin 4 → Fin (Module.finrank Real E)) → Real :=
    fun s => frameComp0S (I := I) (S.base.rm04 s) frame
  have hxbase : x₀ ∈ e.baseSet := by
    simp [e]
  have hG := genGramOn_of_field (I := I) g x₀ hgram
  have hchr : ∀ i j l : Fin (Module.finrank Real E),
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chr p.1 p.2 i j l)
        (J ×ˢ e.baseSet) (t, x₀) := by
    intro i j l
    have hchart := christWithinM (I := I) g x₀ hG i j l ht
      (mem_chart_source H x₀)
    have hchart' :
        ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            chartChristoffel (I := I) (g p.1) x₀ i j l
              (extChartAt I x₀ p.2))
          (J ×ˢ e.baseSet) (t, x₀) := by
      simpa only [e, trivializationAt_baseSet_eq_chartAt_source] using hchart
    have hgood :
        J ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ∈
          𝓝[J ×ˢ e.baseSet] ((t, x₀) : Real × M) := by
      apply prod_open_nhds
        (chartLeviCivitaGoodSet_isOpen (I := I) x₀)
        (self_mem_chartLeviCivitaGoodSet (I := I) x₀)
      · intro y hy
        simpa [e] using chartLeviCivitaGoodSet_mem_baseSet (I := I) hy
    have heq :
        (fun p : Real × M => chr p.1 p.2 i j l) =ᶠ[
          𝓝[J ×ˢ e.baseSet] ((t, x₀) : Real × M)]
        (fun p : Real × M =>
          chartChristoffel (I := I) (g p.1) x₀ i j l
            (extChartAt I x₀ p.2)) := by
      filter_upwards [hgood] with p hp
      simpa [chr, S, frame, hframe₁] using
        (local_chr_eq_chart (I := I) (g p.1) x₀ hp.2 i j l)
    exact hchart'.congr_of_eventuallyEq heq
      (heq.self_of_nhdsWithin ⟨ht, hxbase⟩)
  have hbase : ∀ m : Fin 4 → Fin (Module.finrank Real E),
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => base p.1 p.2 m)
        (J ×ˢ e.baseSet) (t, x₀) := by
    intro m
    have hrm := rm04ChartJoint (I := I) g g x₀ hgram hgram m ht
    have hrm' := hrm.mono
      (Set.prod_mono (Set.Subset.refl J) (Set.subset_univ e.baseSet))
    apply hrm'.congr
    · intro p hp
      simp only [base, frameComp0S, S, solOfMetric, SolutionFamily.rm04,
        metricRm04_apply]
      congr 1
      funext a
      exact local_frame_eq_chart (I := I) x₀ hp.2 (m a)
    · simp only [base, frameComp0S, S, solOfMetric, SolutionFamily.rm04,
        metricRm04_apply]
      congr 1
      funext a
      exact local_frame_eq_chart (I := I) x₀ hxbase (m a)
  have htower := iterRmComp_joint (I := I)
    frame hframeInf e.open_baseSet ht hxbase chr base hchr hbase k K
  have hintrinsic :
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          nablaKRm04Field (I := I) S p.1 k p.2
            (fun a : Fin (4 + k) =>
              chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (J ×ˢ e.baseSet) (t, x₀) := by
    apply htower.congr
    · intro p hp
      have hbridge := iterRmLF_eq_nabla (I := I) S p.1 frame hframe₁
        e.open_baseSet k hp.2 K
      calc
        nablaKRm04Field (I := I) S p.1 k p.2
            (fun a => chartBasisVecFiber (I := I) x₀ (K a) p.2) =
            nablaKRm04Field (I := I) S p.1 k p.2
              (frameTuple (I := I) frame p.2 K) := by
          congr 1
          funext a
          exact (local_frame_eq_chart (I := I) x₀ hp.2 (K a)).symm
        _ = iteratedRmComp (I := I) frame chr base k p.1 p.2 K := by
          simpa only [chr, base] using hbridge.symm
    · have hbridge := iterRmLF_eq_nabla (I := I) S t frame hframe₁
        e.open_baseSet k hxbase K
      calc
        nablaKRm04Field (I := I) S t k x₀
            (fun a => chartBasisVecFiber (I := I) x₀ (K a) x₀) =
            nablaKRm04Field (I := I) S t k x₀
              (frameTuple (I := I) frame x₀ K) := by
          congr 1
          funext a
          exact (local_frame_eq_chart (I := I) x₀ hxbase (K a)).symm
        _ = iteratedRmComp (I := I) frame chr base k t x₀ K := by
          simpa only [chr, base] using hbridge.symm
  exact hintrinsic.mono_of_mem_nhdsWithin
    (prod_open_nhds e.open_baseSet hxbase (Set.subset_univ e.baseSet) J t)

end DifferentialGeometry.PDE.RicciFlow
