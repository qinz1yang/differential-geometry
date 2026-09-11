import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessOpennessPreparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessOriginalError
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessRecenterConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessStrictNorm


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance strictStabilityC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem WindowedModelWitness.eventually_strict_of_regular_window
    (hS : IsSolutionOn S) {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (hwindow : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps) :
    ∀ᶠ q : M × ℝ in 𝓝 (x, t),
      Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
      ∃ W' : WindowedModelWitness eps kappa S q.1 q.2,
        ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
          ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint (modelRadius eps),
            tensor02CovDerivNormWith a (W'.comparison.jet b s)
              (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Good (q : M × ℝ) : Prop :=
    Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
    ∃ W' : WindowedModelWitness eps kappa S q.1 q.2,
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps
  change ∀ᶠ q in 𝓝 (x, t), Good q
  obtain ⟨a, c, b, hac, hclo, htb, hslab, hreg⟩ := W.exists_common_source_slab hwindow
  have hback : t - (eps * S.scalar t x)⁻¹ < t :=
    sub_lt_self _ (inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos))
  have hcb : c < b := (hclo.trans hback).trans htb
  let J := Icc c b
  let L := Icc (-2 * modelDepth eps - 1) 0
  let K := riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1)
  obtain ⟨U, A, B, hKU, hU, hA₀, hB₀, hA, hB⟩ :=
    W.exists_common_raw_time_towers hS hac hcb hslab hreg
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hvalid := W.eventually_admissible_recentering hS hac hclo htb hslab hreg
  obtain ⟨hx, hc₀, _hQ₀, _hbuff₀, _hcmp₀, _ht₀, _hwin₀, hSource₀, hModel₀⟩ := hvalid.self_of_nhds
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hinv : W.embedding.symm x = W.model.basepoint :=
    (congrArg (W.embedding.symm : M → W.model.M) W.base_map.symm).trans (W.embedding.left_inv' hp)
  have hcone : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hmodelSub : Icc (-modelDepth eps) 0 ⊆ L := by
    intro s hs
    simpa only [hinv, hcone, parabolicTime, zero_add, div_one] using hModel₀ hs
  have hsmallU : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) ⊆ U :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans hKU
  have hOld := W.strict_original_error_of_time_towers A B U hsmallU hA₀ hB₀ J L
    hA hB hSource₀ hmodelSub hstrict
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hK : IsCompact K := RiemannianMetricComplete.closedEBall_isCompact hcomplete _ _
  have hdepth : 0 < modelDepth eps := inv_pos.mpr W.eps_pos
  have hmodelSlab : Icc (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.carrier := fun _ hr => hr.2
  have hmodelReg : Ioo (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.regular := fun _ hr => hr.2
  let F := PartialDiffeomorph.refl (I := I3) W.model.M
  have hBzero (s : ℝ) (y : W.model.M) (_hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      B 0 s y v = (W.model.S.base.metric s).inner (F y)
        (mfderiv I3 I3 F y (v 0)) (mfderiv I3 I3 F y (v 1)) := by
    change B 0 s y v = (W.model.S.base.metric s).inner y
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 0))
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 1))
    simp only [hB₀, metricTensorField_apply, mfderiv_id, ContinuousLinearMap.id_apply]
  have hAreg := partial_pullback_time_tower_contDiffOn_closed S hS hac hcb hslab hreg
    W.embedding U hU A hA₀ (fun q s hs y _hy => hA q s hs y)
  have hBreg := partial_pullback_time_tower_contDiffOn_closed W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg F U (Set.subset_univ _) B hBzero
    (fun q s hs y _hy => hB q s hs y)
  have hscaleOne (g : SmoothRiemannianMetric I3 W.model.M) : scaleMetric 1 zero_lt_one g = g :=
    SmoothRiemannianMetric.ext_inner (fun y v w => by simp only [scaleMetric_inner, one_mul])
  by_contra hnot
  have hfreq : ∃ᶠ q in 𝓝 (x, t), ¬ Good q := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨q, hq, hbad⟩ := Filter.exists_seq_forall_of_frequently (hfreq.and_eventually hvalid)
  choose hc hQ hbuff hcmp htime hwindow' hsourceMap hmodelMap using fun n => (hbad n).2.2
  let center (n : ℕ) := W.embedding.symm (q n).1
  let time (n : ℕ) := (q n).2
  let Q (n : ℕ) := S.scalar (q n).2 (q n).1
  let C (n : ℕ) := W.model.S.scalar 0 (center n)
  have htimeLim : Tendsto time atTop (𝓝 t) := (continuous_snd.tendsto (x, t)).comp hq
  have hcenterLim : Tendsto center atTop (𝓝 W.model.basepoint) := by
    have hh := (W.embedding.symm.contMDiffOn_toFun.continuousOn.continuousAt
      (W.embedding.open_target.mem_nhds hx)).tendsto.comp ((continuous_fst.tendsto (x, t)).comp hq)
    rw [hinv] at hh
    exact hh
  have hswap : Continuous (fun z : M × ℝ => (z.2, z.1)) :=
    continuous_snd.prodMk continuous_fst
  have hwithin : Tendsto (fun n => ((q n).2, (q n).1)) atTop
      (𝓝[D.carrier ×ˢ (Set.univ : Set M)] (t, x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hswap.tendsto (x, t)).comp hq,
      Filter.Eventually.of_forall (fun n => ⟨htime n, mem_univ _⟩)⟩
  have hQlim : Tendsto Q atTop (𝓝 (S.scalar t x)) :=
    Filter.Tendsto.comp (g := fun z : ℝ × M => S.scalar z.1 z.2)
      (f := fun n => ((q n).2, (q n).1))
      (hS.scalarCont (t, x) ⟨W.time_mem, mem_univ x⟩) hwithin
  have hClim : Tendsto C atTop (𝓝 (1 : ℝ)) := by
    have hscalar : ContinuousAt (fun z => W.model.S.scalar 0 z) W.model.basepoint :=
      (metricScalar_smooth (W.model.S.base.metric 0)).continuous.continuousAt
    have hh := hscalar.tendsto.comp hcenterLim
    rw [hcone] at hh
    exact hh
  have hpair (i j : ℕ) (hij : i + 2 * j ≤ modelOrder eps) :
      ∀ᶠ n in atTop, ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (scaleMetric (C n) (hc n) (W.model.S.base.metric 0)) (center n) (modelRadius eps),
          tensor02CovDerivNormWith i
            (rescaledTensorTimeTower A (time n) (Q n) j s - rescaledTensorTimeTower B 0 (C n) j s)
            (rescaledMetric W.model.S 0 (C n) (hc n) s)
            (rescaledMetric W.model.S 0 (C n) (hc n) s) y < eps := by
    have hAlpha : Tendsto (fun n => Q n * (Q n)⁻¹ ^ j) atTop
        (𝓝 (S.scalar t x * (S.scalar t x)⁻¹ ^ j)) := hQlim.mul ((hQlim.inv₀ W.scalar_pos.ne').pow j)
    have hBeta : Tendsto (fun n => C n * (C n)⁻¹ ^ j) atTop (𝓝 (1 : ℝ)) := by
      simpa only [inv_one, one_pow, one_mul] using hClim.mul ((hClim.inv₀ one_ne_zero).pow j)
    have hh := eventually_strict_weighted_error_norm_on_scaled_ball
      (fun s => W.model.S.base.metric s) (A j) (B j) W.model.basepoint (modelRadius eps) hK
      (uniqueDiffOn_Icc hcb)
      (uniqueDiffOn_Icc (a := -2 * modelDepth eps - 1) (b := 0) (by linarith))
      (fun y hy => by
        obtain ⟨V₁, hV₁, hp₁, ht₁, hAc⟩ := hAreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₂, hV₂, hp₂, _ht₂, hBc⟩ := hBreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₃, hV₃, hp₃, _ht₃, hgc⟩ := solution_chartGram_contDiffOn_closed
          W.model.S W.model.isSolution (a := -2 * modelDepth eps - 2)
          (c := -2 * modelDepth eps - 1) (b := 0) (by linarith) (by linarith) hmodelSlab hmodelReg y
        refine ⟨V₁ ∩ (V₂ ∩ V₃), hV₁.inter (hV₂.inter hV₃), ⟨hp₁, hp₂, hp₃⟩,
          (fun z hz => ht₁ hz.1), ?_, ?_, ?_⟩
        · intro r s
          exact (hgc r s).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.2))
        · intro slots
          exact (hAc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.1))
        · intro slots
          exact (hBc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.1)))
      center hcenterLim time Q C (fun n => Q n * (Q n)⁻¹ ^ j) (fun n => C n * (C n)⁻¹ ^ j)
      W.scalar_pos hc zero_lt_one htimeLim hQlim hClim hAlpha hBeta i hcmp
      (fun n s hs => hsourceMap n hs)
      (fun n s hs => by simpa only [parabolicTime, zero_add] using hmodelMap n hs)
      (fun s hs => hSource₀ hs)
      (fun s hs => by simpa only [div_one] using hmodelSub hs)
      (fun s hs y hy => by
        have hy' : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) := by
          simpa only [hscaleOne] using hy
        simpa only [div_one, one_smul, hscaleOne] using hOld i j hij s hs y hy')
    simpa only [rescaledTensorTimeTower, rescaledMetric, parabolicTime, zero_add] using hh
  have hfinite : {ij : ℕ × ℕ | ij.1 + 2 * ij.2 ≤ modelOrder eps}.Finite := by
    apply ((Finset.range (modelOrder eps + 1)).product (Finset.range (modelOrder eps + 1))).finite_toSet.subset
    intro ij hij
    change ij.1 + 2 * ij.2 ≤ modelOrder eps at hij
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hall := (Filter.eventually_all_finite hfinite).mpr (fun ij hij => hpair ij.1 ij.2 hij)
  obtain ⟨n, hn⟩ := hall.exists
  have hright : W.embedding (center n) = (q n).1 := W.embedding.right_inv' (hbad n).2.1
  have hnew := W.exists_recentered_strict_of_time_towers (center n) (time n) (hc n)
    (by simpa only [hright] using hQ n) (htime n)
    (by simpa only [hright] using (hwindow' n).trans D.regular_subset)
    U hU (hbuff n) ((hcmp n).trans hKU) A B hA₀ hB₀ J L hA hB
    (by simpa only [hright] using hsourceMap n) (hmodelMap n)
    (fun i j hij s hs y hy => by
      have hh := hn (i, j) hij s hs y hy
      simpa only [hright] using hh)
  apply (hbad n).1
  refine ⟨hwindow' n, ?_⟩
  rw [hright] at hnew
  exact hnew


theorem isOpen_setOf_regular_strict_model_witness (hS : IsSolutionOn S) (eps kappa : ℝ) :
    IsOpen {q : M × ℝ |
      Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.regular ∧
      ∃ W : WindowedModelWitness eps kappa S q.1 q.2,
        ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
          ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
            tensor02CovDerivNormWith a (W.comparison.jet b s)
              (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨hwindow, W, hstrict⟩ := hq
  exact W.eventually_strict_of_regular_window hS hwindow hstrict

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
