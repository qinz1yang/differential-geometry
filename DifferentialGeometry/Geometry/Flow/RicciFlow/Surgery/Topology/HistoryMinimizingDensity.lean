import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutMultiNull
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.MinimizingMass
import DifferentialGeometry.Geometry.Measure.LocalIsometry

noncomputable section
open Set Bundle Manifold MeasureTheory TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {X : Type u}
  [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem exists_contMDiff_minimizer_of_minimizing_vector [PseudoMetrizableSpace X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) (x : X) (Z : TangentSpace ThreeModel x)
    {v : ℝ} (hv : 0 < v) (hmin : (Z, v ^ 2) ∈ lMinDomain S T x)
    (hbdd : BddBelow {r : ℝ | ∃ γ : ℝ → X,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ γ 0 = x ∧
        γ v = lExp S T x Z (v ^ 2) ∧ lRegularizedAction S T γ 0 v = r}) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      η v = lExp S T x Z (v ^ 2) ∧
      lRegularizedAction S T η 0 v = lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v ∧
      lRegularizedAction S T η 0 v = lCost S T x (lExp S T x Z (v ^ 2)) (v ^ 2) ∧
      ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ 0 = η 0 → γ v = η v →
        lRegularizedAction S T η 0 v ≤ lRegularizedAction S T γ 0 v := by
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  have hdom := ((mem_lMinDomain S T x Z (v ^ 2)).mp hmin).1
  have hvdom : v ∈ lRegularizedDomain S T x Z := by
    have hh := ((mem_lExpPosDom S T x Z (v ^ 2)).mp hdom).2.2
    simpa only [Real.sqrt_sq hv.le] using hh
  obtain ⟨ρ, hρ, hρid, _, hρrange⟩ := exists_lRegularizedDomain_smoothClamp S T x Z hv hvdom
  let η : ℝ → X := fun t => lRegularizedCurve S T x Z (ρ t)
  have hρsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := contMDiff_iff_contDiff.mpr hρ
  let z : ThreeSpace := Z
  have hpair : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ThreeSpace)).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (z, ρ t)) := contMDiff_const.prodMk hρsmooth
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ η := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞
      ((fun q : ThreeSpace × ℝ => lRegularizedCurve S T x q.1 q.2) ∘
        (fun t : ℝ => (z, ρ t))) univ
    exact (lRegularizedCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun t _ => by
        change ρ t ∈ lRegularizedDomain S T x Z
        exact hρrange t)
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η := hηsmooth.of_le (by norm_num)
  have heq : EqOn η (lRegularizedCurve S T x Z) (Icc 0 v) := by
    intro t ht
    change lRegularizedCurve S T x Z (ρ t) = lRegularizedCurve S T x Z t
    rw [hρid ht]
    rfl
  have h0 : η 0 = x := (heq ⟨le_rfl, hv.le⟩).trans (lRegularizedCurve_zero S T x Z)
  have hvend : η v = lExp S T x Z (v ^ 2) := by
    rw [heq ⟨hv.le, le_rfl⟩]
    change lRegularizedCurve S T x Z v = lRegularizedCurve S T x Z (Real.sqrt (v ^ 2))
    rw [Real.sqrt_sq hv.le]
  have haction : lRegularizedAction S T η 0 v =
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v := by
    apply lRegularizedAction_congr S T η _ 0 v
    rw [uIoo_of_le hv.le]
    exact heq.mono Ioo_subset_Icc_self
  have hcost : lRegularizedAction S T η 0 v =
      lCost S T x (lExp S T x Z (v ^ 2)) (v ^ 2) := by
    rw [haction]
    have hh := ((mem_lMinDomain S T x Z (v ^ 2)).mp hmin).2
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 (v ^ 2) = _ at hh
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T
      (lRegularizedCurve S T x Z) (v ^ 2) (sq_nonneg v)] at hh
    simpa only [Real.sqrt_sq hv.le] using hh
  refine ⟨η, hη, h0, hvend, haction, hcost, ?_⟩
  intro γ hγ hγ0 hγv
  rw [hcost, lCost_eq_regularity S T x _ _ (sq_nonneg v), Real.sqrt_sq hv.le]
  exact lRegularizedCostC1_le_bdd S T 0 v x _ hbdd γ hγ (hγ0.trans h0) (hγv.trans hvend)

theorem regularizedDensity_eq_redDensity_at_lExp_of_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric ThreeModel X) {T v μ B r : ℝ}
    (hv : 0 < v) (hμ : 0 ≤ μ) (hr : 0 < r)
    (hupper : T ∈ H.stageDomain last) (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ y : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) y)
    (x : X) (Z : TangentSpace ThreeModel x)
    (hmin : (Z, v ^ 2) ∈ lMinDomain S T x)
    (hpole : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (haction : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v ≤
      μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3) :
    H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x)
        (f ⟨first, le_rfl, hle⟩ (lExp S T x Z (v ^ 2))) =
      ENNReal.ofReal (redDensity S T x (lExp S T x Z (v ^ 2)) (v ^ 2)) := by
  let i : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hopen : _root_.Topology.IsOpenEmbedding (f i) :=
    .of_continuous_injective_isOpenMap (hf i).contMDiff.continuous (hinj i) (hf i).isOpenMap
  let _ : MetrizableSpace (H.stage first).Carrier := Manifold.metrizableSpace ThreeModel (H.stage first).Carrier
  let _ : PseudoMetrizableSpace X := hopen.isEmbedding.isInducing.pseudoMetrizableSpace
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  have hclock : ∀ t ∈ Icc (0 : ℝ) v, T - t ^ 2 ∈ D.carrier := by
    intro t ht
    apply D.regular_subset
    apply lExpPosDom_regularity S T x Z ((mem_lMinDomain S T x Z (v ^ 2)).mp hmin).1
    simpa only [Real.sqrt_sq hv.le] using ht
  have hbdd : BddBelow {r : ℝ | ∃ γ : ℝ → X,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ γ 0 = x ∧
        γ v = lExp S T x Z (v ^ 2) ∧ lRegularizedAction S T γ 0 v = r} := by
    refine ⟨-(2 * B / 3) * v ^ 3, ?_⟩
    rintro _ ⟨γ, hγ, hγ0, hγv, rfl⟩
    have hmem := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross
      S hS T (u := 0) (v := v) le_rfl hv.le
      (by
        simp only [zero_pow two_ne_zero, sub_zero]
        exact ⟨H.time_le_of_mem_stageDomain hupper,
          H.le_stageEndTime_of_mem_stageDomain hupper⟩) hlower hclock hmetric γ hγ
    have hl := H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T 0 v B hscalar _ _ hmem
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), sub_zero] using hl
  obtain ⟨η, hη, hη0, hηv, hηaction, hηcost, hηmin⟩ :=
    exists_contMDiff_minimizer_of_minimizing_vector S hS T x Z hv hmin hbdd
  have hcost := H.regularizedCost_eq_of_minimal_of_compact_barrier first last hle f hf hinj K hK
    hcross S hS g (u := 0) (v := v) (μ := μ) (B := B) (r := r)
    le_rfl hv.le hμ hr (by simpa using hupper) hlower hclock hmetric hcompare hscalar
    η hη hηmin (hη0.symm ▸ hpole) (by simpa only [hη0] using hfront) (by
      simpa only [hηaction, sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using haction)
  rw [hη0, hηv] at hcost
  rw [H.regularizedDensity_eq_exp_of_cost_eq first last hle T B hv hupper hscalar _ _ hcost]
  unfold redDensity redLength
  rw [← hηcost, Real.sqrt_sq hv.le]
  congr 2
  simp only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  ring


private local instance : MeasurableSpace X := borel X
private local instance : BorelSpace X := ⟨rfl⟩
private local instance (j : Fin (H.eventCount + 1)) : MeasurableSpace (H.stage j).Carrier :=
  borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) : BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem lintegral_regularizedDensity_image_lExp_le_one_of_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric ThreeModel X) {T v σ μ B r : ℝ}
    (hv : 0 < v) (hvσ : v ^ 2 < σ) (hμ : 0 ≤ μ) (hr : 0 < r)
    (hupper : T ∈ H.stageDomain last) (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hendmetric : S.base.metric (T - v ^ 2) =
      localPullMetric (H.stageMetric first (T - v ^ 2)) (f ⟨first, le_rfl, hle⟩) (hf ⟨first, le_rfl, hle⟩))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ y : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) y)
    (x : X) {U A : Set ThreeSpace} (hU : IsOpen U) (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hmin : ∀ Z ∈ U, (Z, σ) ∈ lMinDomain S T x)
    (hbdd : ∀ Z ∈ U, BddBelow {r : ℝ | ∃ γ : ℝ → X,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ γ 0 = x ∧
        γ (Real.sqrt σ) = lExp S T x Z σ ∧ lRegularizedAction S T γ 0 (Real.sqrt σ) = r})
    (hpole : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (haction : ∀ Z ∈ A, lRegularizedAction S T (lRegularizedCurve S T x Z) 0 v ≤
      μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3) :
    (∫⁻ q in (fun Z : ThreeSpace => f ⟨first, le_rfl, hle⟩ (lExp S T x Z (v ^ 2))) '' A,
      H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x) q
      ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier (H.stageMetric first (T - v ^ 2))) ≤ 1 := by
  let i : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hopen : _root_.Topology.IsOpenEmbedding (f i) :=
    .of_continuous_injective_isOpenMap (hf i).contMDiff.continuous (hinj i) (hf i).isOpenMap
  let _ : SecondCountableTopology (H.stage first).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage first).Carrier
  let _ : SecondCountableTopology X := hopen.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let _ : SigmaCompactSpace X := inferInstance
  let _ : MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  have hAborel : @MeasurableSet ThreeSpace (borel ThreeSpace) A := by
    rwa [← BorelSpace.measurable_eq (α := ThreeSpace)]
  let V : Set X := (fun Z : ThreeSpace => lExp S T x Z (v ^ 2)) '' A
  have hVmeas : MeasurableSet V := by
    obtain ⟨Φ, hsource, _, hEq⟩ := exists_lExpPartial_on_open_minimizing_family_of_bdd
      S hS T x (sq_pos_of_pos hv) hvσ hU hmin hbdd
    let Ψ : PartialDiffeomorph 𝓘(ℝ, ThreeSpace) ThreeModel ThreeSpace X 1 :=
      { Φ.toPartialEquiv with
        open_source := Φ.open_source
        open_target := Φ.open_target
        contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
        contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
    have himage : Ψ '' A = V := image_congr (fun Z hZ => hEq (hAU hZ))
    rw [← himage]
    exact DifferentialGeometry.Integral.Measure.measurableSet_image_param_global Ψ hAborel
      (by change A ⊆ Φ.source; rwa [hsource])
  have hV : (f i) '' V =
      (fun Z : ThreeSpace => f ⟨first, le_rfl, hle⟩ (lExp S T x Z (v ^ 2))) '' A := by
    exact image_image _ _ _
  have htransport := Geometry.Measure.setLIntegral_image_of_injective_local_isometry
    (S.base.metric (T - v ^ 2)) (H.stageMetric first (T - v ^ 2)) (f i) (hf i) (hinj i)
    (fun y v w => by rw [hendmetric, localPullMetric_inner]) V
    (H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x))
  rw [hV] at htransport
  rw [htransport]
  have heq : ∀ y ∈ V,
      H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x) (f i y) =
        ENNReal.ofReal (redDensity S T x y (v ^ 2)) := by
    rintro y ⟨Z, hZ, rfl⟩
    have hm := lMinDomain_down_of_bdd S hS T x Z (hmin Z (hAU hZ)) (sq_pos_of_pos hv) hvσ.le
      (lRegularizedCosts_prefix_bdd_of_min S hS T x Z (hmin Z (hAU hZ))
        (sq_pos_of_pos hv) hvσ.le (hbdd Z (hAU hZ))) (hbdd Z (hAU hZ))
    exact H.regularizedDensity_eq_redDensity_at_lExp_of_compact_barrier first last hle f hf hinj K hK
      hcross S hS g hv hμ hr hupper hlower hmetric hcompare hscalar x Z hm hpole hfront (haction Z hZ)
  calc
    _ = ∫⁻ y in V, ENNReal.ofReal (redDensity S T x y (v ^ 2))
        ∂riemannianVolumeMeasure ThreeModel X (S.base.metric (T - v ^ 2)) := by
      apply lintegral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hVmeas] with y hy
      exact heq y hy
    _ ≤ 1 := lintegral_redDensity_image_lExp_le_one_on_minimizing_family_of_bdd S hS T x
      (sq_pos_of_pos hv) hvσ hU hmin hbdd hAborel hAU

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) {X : Type u}
 [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] [SigmaCompactSpace X]
private local instance : MeasurableSpace X := borel X
private local instance : BorelSpace X := ⟨rfl⟩

theorem exists_open_regularizedCost_eq_lCost_and_ae_unique_minimizer_of_action_lt_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hreg : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ D.regular)
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (y : X) (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ 0 = x) (hend : γ v = y)
    (hact : lRegularizedAction S T γ 0 v <
      μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3) :
    ∃ U : Set X, IsOpen U ∧ y ∈ U ∧
      (∀ p : X, LocallyLipschitzOn ((extChartAt ThreeModel p).target ∩ (extChartAt ThreeModel p).symm ⁻¹' U)
        ((fun z : X => lCost S T x z (v ^ 2)) ∘ (extChartAt ThreeModel p).symm)) ∧
      (∀ z ∈ U, H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ z) =
          (lCost S T x z (v ^ 2) : WithTop ℝ)) ∧
      ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure ThreeModel X (S.base.metric (T - v ^ 2))).restrict U,
        (∃! Z : TangentSpace ThreeModel x, (Z, v ^ 2) ∈ lMinDomain S T x ∧ lExp S T x Z (v ^ 2) = z) ∧
        ∀ Z : TangentSpace ThreeModel x, (Z, v ^ 2) ∈ lMinDomain S T x → lExp S T x Z (v ^ 2) = z →
          ¬ IsLConjugate S T x Z (v ^ 2) := by
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jfirst) :=
    .of_continuous_injective_isOpenMap (hf jfirst).contMDiff.continuous (hinj jfirst) (hf jfirst).isOpenMap
  let _ : SecondCountableTopology (H.stage first).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage first).Carrier
  let _ : SecondCountableTopology X := hemb.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let _ : MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  have htime : ∀ t ∈ Icc (0 : ℝ) v, T - t ^ 2 ∈ D.carrier := fun t ht => D.regular_subset (hreg t ht)
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hupper' : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper0, H.le_stageEndTime_of_mem_stageDomain hupper0⟩
  obtain ⟨A, hγA, hA⟩ := exists_between hact
  obtain ⟨U, hU, hγU, α, hα, hα0, hαv, _, hαact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T hv htime γ hγ hγA
  have hy : y ∈ U := hend ▸ hγU
  have hbdd (z : X) : BddBelow {a : ℝ | ∃ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ ∧
      δ 0 = x ∧ δ v = z ∧ lRegularizedAction S T δ 0 v = a} := by
    refine ⟨-(2 * B / 3) * v ^ 3, ?_⟩
    rintro _ ⟨δ, hδ, _, _, rfl⟩
    have hm := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross S hS T
      le_rfl hv.le hupper' hlower htime hmetric δ hδ
    have hh := H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T 0 v B hscalar _ _ hm
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), sub_zero] using hh
  have hconf (δ : ℝ → X) (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ)
      (hδ0 : δ 0 = x) (hδact : lRegularizedAction S T δ 0 v ≤ A) : MapsTo δ (Icc 0 v) K :=
    H.mapsTo_of_lRegularizedAction_lt_history_escape_barrier first last hle f hf hinj K hK hcross
      le_rfl hv.le hupper' hlower S hS htime g hμ hr hmetric hcompare
      (fun j t ht z => hscalar j t ht (f j z)) x hx hfront δ hδ hδ0
      (by simpa only [sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hδact.trans_lt hA)
  have hLip : ∀ p : X, LocallyLipschitzOn
      ((extChartAt ThreeModel p).target ∩ (extChartAt ThreeModel p).symm ⁻¹' U)
      ((fun z : X => lCost S T x z (v ^ 2)) ∘ (extChartAt ThreeModel p).symm) := by
    intro p
    apply DifferentialGeometry.PDE.RicciFlow.lCost_chart_locallyLipschitzOn_of_compact_action_sublevel
      S hS T x (tau := v ^ 2) (A := A) (sq_pos_of_pos hv) ?_ K hK U hU ?_ ?_ ?_ p
    · intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hle' : T - t ≤ v ^ 2 := by linarith [ht.1]
      have hc := hreg (Real.sqrt (T - t)) ⟨Real.sqrt_nonneg _, by
        exact (Real.sqrt_le_sqrt hle').trans_eq (Real.sqrt_sq hv.le)⟩
      simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hc
    · simpa only [Real.sqrt_sq hv.le] using hbdd
    · intro z hz
      exact ⟨α z, hα z hz, (hα0 z hz).trans hstart, by simpa only [Real.sqrt_sq hv.le] using hαv z hz,
        by simpa only [Real.sqrt_sq hv.le] using (hαact z hz).le⟩
    · intro δ hδ hδ0 _ hδact
      simpa only [Real.sqrt_sq hv.le] using hconf δ hδ hδ0 (by simpa only [Real.sqrt_sq hv.le] using hδact)
  have hident : ∀ z ∈ U, H.regularizedCost first last hle T B 0 v
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ z) =
        (lCost S T x z (v ^ 2) : WithTop ℝ) ∧
      ∃ Z : TangentSpace ThreeModel x, (Z, v ^ 2) ∈ lMinDomain S T x ∧ lExp S T x Z (v ^ 2) = z := by
    intro z hz
    obtain ⟨η, hη, hη0, hηv, _, hmin⟩ := exists_lRegularizedMinC1_of_compact_action_sublevel
      S hS T hv hreg x z (α z) (hα z hz) ((hα0 z hz).trans hstart) (hαv z hz) K hK
      (fun δ hδ hδ0 _ hδact => hconf δ hδ hδ0 (hδact.trans (hαact z hz).le))
    have hm : ∀ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ → δ 0 = η 0 → δ v = η v →
        lRegularizedAction S T η 0 v ≤ lRegularizedAction S T δ 0 v :=
      fun δ hδ hδ0 hδv => hmin δ hδ (hδ0.trans hη0) (hδv.trans hηv)
    have heq := H.regularizedCost_eq_of_minimal_of_compact_barrier first last hle f hf hinj K hK hcross
      S hS g le_rfl hv.le hμ hr hupper0 hlower htime hmetric hcompare hscalar η hη hm
      (hη0.symm ▸ hx) (by simpa only [hη0] using hfront) (by
        have hb := (hmin (α z) (hα z hz) ((hα0 z hz).trans hstart) (hαv z hz)).trans (hαact z hz).le
        simpa only [sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hb.trans hA.le)
    have hcost : lRegularizedAction S T η 0 v = lCost S T x z (v ^ 2) := by
      rw [lCost_eq_regularity S T x z (v ^ 2) (sq_nonneg v), Real.sqrt_sq hv.le]
      let costs : Set ℝ := {a | ∃ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ ∧
        δ 0 = x ∧ δ v = z ∧ lRegularizedAction S T δ 0 v = a}
      have hmem : lRegularizedAction S T η 0 v ∈ costs := ⟨η, hη, hη0, hηv, rfl⟩
      change lRegularizedAction S T η 0 v = sInf costs
      apply le_antisymm
      · apply le_csInf (s := costs) ⟨_, hmem⟩
        rintro _ ⟨δ, hδ, hδ0, hδv, rfl⟩
        exact hmin δ hδ hδ0 hδv
      · exact csInf_le (hbdd z) hmem
    refine ⟨by simpa only [hη0, hηv, hcost] using heq, ?_⟩
    cases hη0
    obtain ⟨Z, hZ, hZend, _, _⟩ := exists_lMinimizingVector_of_minimal S hS T hv hreg η hη hm
    exact ⟨Z, hZ, hZend.trans hηv⟩
  refine ⟨U, hU, hy, hLip, (fun z hz => (hident z hz).1), ?_⟩
  have hmulti := DifferentialGeometry.PDE.RicciFlow.lMinimizingVector_nonunique_image_null_on_of_locallyLipschitz
    S hS T x (v ^ 2) hU hLip (fun Z _ _ => Filter.Eventually.of_forall (fun z => by
      simpa only [Real.sqrt_sq hv.le] using hbdd z)) (S.base.metric (T - v ^ 2))
  have hconj := lConjugateImage_null S hS T x (v ^ 2) (S.base.metric (T - v ^ 2))
  have hamulti := ae_restrict_of_ae (s := U) (measure_eq_zero_iff_ae_notMem.mp hmulti)
  have haconj := ae_restrict_of_ae (s := U) (measure_eq_zero_iff_ae_notMem.mp hconj)
  filter_upwards [ae_restrict_mem hU.measurableSet, hamulti, haconj] with z hz hzm hzc
  obtain ⟨Z, hZ, hZz⟩ := (hident z hz).2
  refine ⟨⟨Z, ⟨hZ, hZz⟩, ?_⟩, ?_⟩
  · intro W hW
    by_contra hWZ
    exact hzm ⟨hz, Z, W, (fun h => hWZ h.symm), hZ, hW.1, hZz, hW.2⟩
  · intro W _ hWz hWconj
    exact hzc ⟨W, hWconj, hWz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Bundle Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) {X : Type u}
 [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] [SigmaCompactSpace X]
private local instance : MeasurableSpace X := borel X
private local instance : BorelSpace X := ⟨rfl⟩
private local instance (j : Fin (H.eventCount + 1)) : MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) : BorelSpace (H.stage j).Carrier := ⟨rfl⟩

omit [SigmaCompactSpace X] in
theorem exists_open_regularizedDensity_mass_le_one_of_action_lt_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hreg : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ D.regular)
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hendmetric : S.base.metric (T - v ^ 2) =
      localPullMetric (H.stageMetric first (T - v ^ 2)) (f ⟨first, le_rfl, hle⟩) (hf ⟨first, le_rfl, hle⟩))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (y : X) (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hstart : γ 0 = x) (hend : γ v = y)
    (hact : lRegularizedAction S T γ 0 v <
      μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3) :
    ∃ U : Set X, IsOpen U ∧ y ∈ U ∧
      (∀ z ∈ U, H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ z) = (lCost S T x z (v ^ 2) : WithTop ℝ)) ∧
      0 < riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (T - v ^ 2)) (f ⟨first, le_rfl, hle⟩ '' U) ∧
      (∫⁻ q in f ⟨first, le_rfl, hle⟩ '' U,
        H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x) q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier (H.stageMetric first (T - v ^ 2))) ≤ 1 := by
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jfirst) :=
    .of_continuous_injective_isOpenMap (hf jfirst).contMDiff.continuous (hinj jfirst) (hf jfirst).isOpenMap
  let _ : SecondCountableTopology (H.stage first).Carrier := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage first).Carrier
  let _ : SecondCountableTopology X := hemb.isEmbedding.secondCountableTopology
  let _ : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let _ : SigmaCompactSpace X := inferInstance
  let _ : MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let _ : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  obtain ⟨U, hU, hyU, _, hcost, _⟩ :=
    H.exists_open_regularizedCost_eq_lCost_and_ae_unique_minimizer_of_action_lt_compact_barrier
      first last hle f hf hinj K hK hcross hv hupper hlower S hS hreg g hμ hr hmetric hcompare hscalar
      x hx hfront y γ hγ hstart hend hact
  have htime : ∀ t ∈ Icc (0 : ℝ) v, T - t ^ 2 ∈ D.carrier := fun t ht => D.regular_subset (hreg t ht)
  obtain ⟨A, hγA, hA⟩ := exists_between hact
  obtain ⟨V, hV, hyV, α, hα, hα0, hαv, _, hαact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T hv htime γ hγ hγA
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hyW : y ∈ W := ⟨hyU, hend ▸ hyV⟩
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simp only [zero_pow two_ne_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hbdd (z : X) : BddBelow {a : ℝ | ∃ δ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ ∧
      δ 0 = x ∧ δ v = z ∧ lRegularizedAction S T δ 0 v = a} := by
    refine ⟨-(2 * B / 3) * v ^ 3, ?_⟩
    rintro _ ⟨δ, hδ, _, _, rfl⟩
    have hm := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross S hS T
      le_rfl hv.le hupper0 hlower htime hmetric δ hδ
    have hh := H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T 0 v B hscalar _ _ hm
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), sub_zero] using hh
  have hmass : (∫⁻ z in W, ENNReal.ofReal (redDensity S T x z (v ^ 2))
      ∂riemannianVolumeMeasure ThreeModel X (S.base.metric (T - v ^ 2))) ≤ 1 := by
    apply lintegral_redDensity_le_one_of_compact_action_sublevel S hS T x (τ := v ^ 2) (A := A)
      (sq_pos_of_pos hv) ?_ K hK W hW ?_ ?_ ?_
    · intro t ht
      have hn : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hh : T - t ≤ v ^ 2 := by linarith [ht.1]
      have hc := hreg (Real.sqrt (T - t)) ⟨Real.sqrt_nonneg _,
        (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq hv.le)⟩
      simpa only [Real.sq_sqrt hn, sub_sub_cancel] using hc
    · simpa only [Real.sqrt_sq hv.le] using hbdd
    · intro z hz
      exact ⟨α z, hα z hz.2, (hα0 z hz.2).trans hstart,
        by simpa only [Real.sqrt_sq hv.le] using hαv z hz.2,
        by simpa only [Real.sqrt_sq hv.le] using hαact z hz.2⟩
    · intro δ hδ hδ0 _ hδact
      rw [Real.sqrt_sq hv.le] at hδact ⊢
      apply H.mapsTo_of_lRegularizedAction_lt_history_escape_barrier first last hle f hf hinj K hK hcross
        le_rfl hv.le hupper0 hlower S hS htime g hμ hr hmetric hcompare
        (fun j t ht z => hscalar j t ht (f j z)) x hx hfront δ hδ hδ0
      simpa only [sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hδact.trans_lt hA
  refine ⟨W, hW, hyW, (fun z hz => hcost z hz.1), ?_, ?_⟩
  · let _ : (riemannianVolumeMeasure ThreeModel (H.stage first).Carrier (H.stageMetric first (T - v ^ 2))).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure _
    exact ((hf jfirst).isOpenMap W hW).measure_pos _ ⟨f jfirst y, y, hyW, rfl⟩
  · rw [DifferentialGeometry.Geometry.Measure.setLIntegral_image_of_injective_local_isometry
      (S.base.metric (T - v ^ 2)) (H.stageMetric first (T - v ^ 2)) (f jfirst) (hf jfirst) (hinj jfirst)
      (fun z V W => by rw [hendmetric, localPullMetric_inner]) W]
    have heq : ∀ z ∈ W, H.regularizedDensity first last hle T B v (f ⟨last, hle, le_rfl⟩ x) (f jfirst z) =
        ENNReal.ofReal (redDensity S T x z (v ^ 2)) := by
      intro z hz
      rw [H.regularizedDensity_eq_exp_of_cost_eq first last hle T B hv hupper hscalar _ _ (hcost z hz.1)]
      unfold redDensity redLength
      rw [Real.sqrt_sq hv.le]
      congr 2
      simp only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      ring
    rw [setLIntegral_congr_fun hW.measurableSet heq]
    exact hmass

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end
