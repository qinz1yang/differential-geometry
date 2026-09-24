import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CylinderBackwardConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.CoefficientExtension
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private theorem stage_index_eq_of_backward_window
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (hleft : N.scale⁻¹ ≤ H.time i.succ - H.time i.castSucc)
    (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - N.scale⁻¹ < H.time j.succ) : j = i := by
  apply Fin.ext
  by_contra heq
  have hlt : j.val < i.val := lt_of_le_of_ne hj heq
  have ht : H.time j.succ ≤ H.time i.castSucc :=
    H.time_strictMono.monotone (by change j.val + 1 ≤ i.val; omega)
  linarith

private abbrev cylinderJet (δ : ℝ) (q : ℕ) (v : ℝ) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
  shrinkingCylinderTimeJet δ q v

private theorem background_eq_surgery_metric (δ v : ℝ) :
    strongNeckBackgroundMetric δ v =
      (shrinkingCylinderMetric ⟨min v 0, (min_le_right v 0).trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z V W
  have hs := scalarOneShrinkingCylinderMetric_inner (min v 0)
    ((min_le_right v 0).trans_lt zero_lt_one) z.1.1 z.1.2 V.1 W.1 V.2 W.2
  have hmodel := (Classical.choose_spec (exists_unique_shrinkingCylinderMetric
    (⟨min v 0, (min_le_right v 0).trans_lt zero_lt_one⟩ : Iio (1 : ℝ)))).1 z.1 V W
  have hround : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner z.1.1 V.1 W.1 =
      inner ℝ (show ThreeSpace from mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 V.1)
        (show ThreeSpace from mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 W.1) := rfl
  apply hs.trans
  apply Eq.trans _ hmodel.symm
  rw [hround]
  unfold shrinkingCylinderInner
  have hp (A : TangentSpace NeckCylinderModel z) :
      mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) z.1 A =
      mfderiv (𝓡 2) ThreeModel (fun y : Sphere 2 => y.1) z.1.1 A.1 := by
    change mfderiv NeckCylinderModel ThreeModel
      ((fun y : Sphere 2 => (y.1 : ThreeSpace)) ∘ Prod.fst) z.1 A = _
    have hh := mfderiv_comp_apply z.1
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).mdifferentiableAt (by simp))
      mdifferentiableAt_fst (show TangentSpace NeckCylinderModel z.1 from A)
    exact hh.trans (by rw [mfderiv_fst]; rfl)
  rw [hp V, hp W, mfderiv_snd]
  rfl

theorem eventually_nonempty_incomingBackwardNeck
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] H.time i.succ))
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : 0 < metricScalarAt (H.event i).terminal.metric x)
    {eps δ : ℝ} (hδ : δ < 1 / 4) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (nk : ∀ n, StrongNeck (H.event i).incoming.flow eps x.1 (τ n))
    (N : ℕ → NormalizedNeck (H.event i).terminal.metric δ k)
    (hcenter : ∀ n, (N n).center = x) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hmap : ∀ n, ∀ z : neckBuffer δ, ((N n).chart z).1 = (nk n).map z.1)
    {K : Set (H.event i).incoming.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ, (N n).chart z ∈ K)
    (hbudget : 2 * Real.sqrt ((3 : ℝ) ^ (k + 2)) * eps < δ) :
    ∀ᶠ n in atTop, Nonempty (IncomingBackwardNeck H i (N n)
      (Real.sqrt ((N n).scale⁻¹))) := by
  let G := (H.event i).incoming
  let L := (H.event i).terminal
  obtain ⟨B, hzero, hB, η, hη, hbound⟩ :=
    L.exists_historical_neck_error_bound hτ x hx hδ k hk nk N hcenter hfit hmap hK hcapture hbudget
  have hscale (n : ℕ) : (N n).scale = metricScalarAt L.metric x := by
    rw [(N n).scale_scalar, hcenter n]
  have hleft (n : ℕ) : (N n).scale⁻¹ ≤ H.time i.succ - H.time i.castSucc := by
    rw [hscale]
    exact L.inv_scalar_le_time_length_of_strongNecks hτ x hx nk
  filter_upwards [hbound] with n hn
  let r := Real.sqrt ((N n).scale⁻¹)
  have hr : 0 < r := Real.sqrt_pos.mpr (inv_pos.mpr (N n).scale_pos)
  have hrsq : r ^ 2 = (N n).scale⁻¹ := Real.sq_sqrt (inv_nonneg.mpr (N n).scale_pos.le)
  have hQ : (r ^ 2)⁻¹ = (N n).scale := by rw [hrsq, inv_inv]
  let chart : (j : Fin H.eventCount) → j.val ≤ i.val →
      H.time i.succ - r^2 < H.time j.succ → C(neckBuffer δ, (H.stage j.castSucc).Carrier) :=
    fun j hj ha => by
      have hji := stage_index_eq_of_backward_window (N n) (hleft n) j hj (by rwa [← hrsq])
      subst j
      exact ⟨fun z => ((N n).chart z).1, continuous_subtype_val.comp (N n).chart.continuous⟩
  let metric := L.neckMetric (N n)
  let jets := fun q (v : Icc (-1 : ℝ) 0) =>
    ((N n).scale * (N n).scale⁻¹ ^ q) •
      (N n).tensorPullback (B q (H.time i.succ + v.1 / (N n).scale)) - cylinderJet δ q v.1
  refine ⟨{ radius_pos := hr
            left_nonneg := (H.time_nonneg i.castSucc).trans (by linarith [hleft n, hrsq])
            stageChart := chart
            stageChart_smooth := ?_
            terminal_chart := ?_
            crossing := ?_
            metric := metric
            terminal_metric := L.neckMetric_zero (N n)
            metric_on_slab := ?_
            timeDifferenceJet := jets
            timeDifferenceJet_eq := ?_
            parabolic_closeness := ?_
            metric_smooth := L.neckMetric_smooth (N n) (hleft n) }⟩
  · intro j hj ha
    have hji := stage_index_eq_of_backward_window (N n) (hleft n) j hj (by rwa [← hrsq])
    subst j
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel G.terminalRegularOpen (N n).chart (N n).chart_smooth
  · intro ha z
    rfl
  · intro j hj next ha
    have ht := H.time_strictMono.monotone (show j.succ ≤ i.castSucc from by
      change j.val + 1 ≤ i.val; omega)
    have hcontr : False := by linarith [hleft n, hrsq]
    exact hcontr.elim
  · intro j hj ha v hv htlo hthi z V W
    have hji := stage_index_eq_of_backward_window (N n) (hleft n) j hj (by rwa [← hrsq])
    subst j
    rw [hQ]
    have htime : H.time i.succ + r ^ 2 * v = H.time i.succ + v / (N n).scale := by
      rw [hrsq, div_eq_mul_inv, mul_comm]
    rw [htime]
    have hh := L.neckMetric_inner_before (N n) hv.2 z V W
    have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := NeckCylinderModel)
      (J := ThreeModel) (N n).chart z
    have hchart : (chart i hj ha : neckBuffer δ → (H.stage i.castSucc).Carrier) =
        fun z => ((N n).chart z).1 := rfl
    have hde : mfderiv NeckCylinderModel ThreeModel (chart i hj ha) z =
        mfderiv NeckCylinderModel ThreeModel (N n).chart z := by rw [hchart]; exact hd
    exact hh.trans (congrArg₂ (fun (V W : ThreeSpace) => (N n).scale *
      ((H.event i).incoming.flow.base.metric (H.time i.succ + v / (N n).scale)).inner
        ((N n).chart z).1 V W) (DFunLike.congr_fun hde.symm V)
          (DFunLike.congr_fun hde.symm W))
  · intro q v z
    exact L.neckMetric_timeJets (N n) (hleft n) B hzero
      (fun q t ht y => (hB q t ht y).2) q v z
  · refine ⟨η, hη, ?_⟩
    intro a b hab v z hz
    have hh := hn a b hab v.1 v.2 z hz
    have hbg := background_eq_surgery_metric δ v.1
    have hbg' : strongNeckBackgroundMetric δ v.1 =
        (shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ) := by
      simpa only [min_eq_left v.2.2] using hbg
    change Real.sqrt (normSq0S
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      z (a + 2)
      (cylinderTensorCovDeriv
        ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) (jets b v) a z)) ≤ η
    rw [cylinderTensorCovDeriv_eq_tensor02CovDeriv]
    change tensor02CovDerivNormWith a (jets b v)
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ)) z ≤ η
    have hs := hscale n
    rw [← hbg']
    dsimp [jets]
    rw [hs]
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace F] {I : ModelWithCorners ℝ E F}
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M] [T2Space M]
  (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
  (K : Set (H.event i).incoming.terminalRegularOpen)
  (G : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorFootprintInterior first i hle K))
  (Q : ℝ) (hQ : 0 < Q)
  (Phi : M → H.backwardSurvivorFootprintInterior first i hle K)
  (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)

private theorem localPullMetric_scale_backwardSurvivorSlabMetric_inner
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc)
    {t : ℝ} (ht : t < H.time j.succ)
    (hGt : G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
      (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (scaleMetric Q hQ (G t)) Phi hPhi).inner x v w =
      Q * ((H.event j).incoming.flow.base.metric t).inner
        (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf
          (j.castSucc_lt_succ.le.trans hl) (Phi x).val.val)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first i.castSucc hle
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x v)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first i.castSucc hle
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x w) := by
  erw [localPullMetric_inner, scaleMetric_inner, hGt,
    SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner,
    H.backwardSurvivorSlabMetric_before first i.castSucc hle j hf hl ht,
    localPullMetric_inner]
  let psi : M → H.backwardSurvivorDomain first i.castSucc hle := fun y => (Phi y).val.val
  have hpsi : MDifferentiable I ThreeModel psi :=
    ((contMDiff_subtype_val.comp contMDiff_subtype_val).comp hPhi.contMDiff).mdifferentiable
      (by decide)
  have hdp : mfderiv I ThreeModel psi x = mfderiv I ThreeModel Phi x := by
    exact (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
      (fun y => (Phi y).val) x).trans
        (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel) Phi x)
  have hd := mfderiv_comp x
    ((H.backwardSurvivorMap_isLocalDiffeomorph first i.castSucc hle j.castSucc hf
      (j.castSucc_lt_succ.le.trans hl)).mdifferentiable (by decide) (psi x))
    (hpsi x)
  rw [hdp] at hd
  change mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first i.castSucc hle
    j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x = _ at hd
  rw [hd]
  rfl

private theorem localPullMetric_scale_backwardSurvivorTerminalFaceMetric_inner
    {t : ℝ} (ht : t < H.time i.succ)
    (hGt : G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
      (H.backwardSurvivorFootprintInterior first i hle K))
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (scaleMetric Q hQ (G t)) Phi hPhi).inner x v w =
      Q * ((H.event i).incoming.flow.base.metric t).inner
        (H.backwardSurvivorMap first i.castSucc hle i.castSucc hle le_rfl (Phi x).val.val)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first i.castSucc hle
          i.castSucc hle le_rfl (Phi y).val.val) x v)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first i.castSucc hle
          i.castSucc hle le_rfl (Phi y).val.val) x w) := by
  erw [localPullMetric_inner, scaleMetric_inner, hGt,
    H.backwardSurvivorTerminalFaceMetric_before first i hle ht]
  erw [SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have he : H.backwardSurvivorMap first i.castSucc hle i.castSucc hle le_rfl =
      Subtype.val := by
    funext z
    exact H.backwardSurvivorMap_last first i.castSucc hle z
  rw [he]
  have hd : mfderiv I ThreeModel (fun y => (Phi y).val.val.val) x =
      mfderiv I ThreeModel Phi x := by
    exact (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
      (fun y => (Phi y).val.val) x).trans
      ((mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
        (fun y => (Phi y).val) x).trans
          (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel) Phi x))
  rw [hd]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {i : Fin H.eventCount} {hle : first ≤ i.castSucc}

private theorem first_le_stage_of_time_lt {a : ℝ}
    (hstart : H.time first ≤ a) (j : Fin H.eventCount)
    (ha : a < H.time j.succ) : first ≤ j.castSucc := by
  by_contra hn
  have hj : j.succ ≤ first := by
    apply Fin.le_iff_val_le_val.mpr
    have hh := Fin.lt_def.mp (lt_of_not_ge hn)
    change j.val + 1 ≤ first.val
    exact hh
  exact (not_lt_of_ge ((H.time_strictMono.monotone hj).trans hstart)) ha

private theorem footprint_lift_isSmoothEmbedding
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (Φ : neckBuffer δ → H.backwardSurvivorFootprintInterior first i hle K)
    (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hmap : H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ := by
  apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hΦ
  intro x y hxy
  apply N.chart_smooth.isEmbedding.injective
  rw [← hmap]
  exact congrArg (H.backwardSurvivorFootprintMap first i hle K) hxy

private theorem footprint_lift_to_domain_isSmoothEmbedding
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (Φ : neckBuffer δ → H.backwardSurvivorFootprintInterior first i hle K)
    (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hmap : H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (fun x => (Φ x).val.val : neckBuffer δ → H.backwardSurvivorDomain first i.castSucc hle) := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
    NeckCylinderModel ThreeModel (H.backwardSurvivorTerminalFace first i hle)
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
    NeckCylinderModel ThreeModel (H.backwardSurvivorFootprintInterior first i hle K)
      Φ (footprint_lift_isSmoothEmbedding N K Φ hΦ hmap)


theorem NormalizedNeck.exists_incomingBackwardNeck_of_historical_solution
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (Φ : neckBuffer δ → H.backwardSurvivorFootprintInterior first i hle K)
    (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hmap : H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    {θ : ℝ} (hθ : 1 < θ)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θ) 0 (by linarith)))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric 0 = N.normalizedMetric)
    (hmetric : ∀ t ∈ Ico (-1 : ℝ) 0, S.base.metric t = localPullMetric
      (scaleMetric N.scale N.scale_pos (G (H.time i.succ + t / N.scale))) Φ hΦ)
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (hstart : H.time first ≤ H.time i.succ - N.scale⁻¹)
    (Z : (b : ℕ) → (v : Icc (-1 : ℝ) 0) →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ b v x, Z b v x = iteratedDerivWithin b
      (fun t => metricTensorField (S.base.metric t) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x)
      (Icc (-1 : ℝ) 0) v.1)
    (hclose : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2*b ≤ k →
      ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g x (a + 2) (cylinderTensorCovDeriv g (Z b v) a x)) ≤ η) :
    ∃ B : IncomingBackwardNeck H i N (Real.sqrt N.scale⁻¹),
      B.metric = S.base.metric ∧ B.timeDifferenceJet = Z ∧
      ∀ (j : Fin H.eventCount) (hj : j.val ≤ i.val)
        (ha : H.time i.succ - (Real.sqrt N.scale⁻¹)^2 < H.time j.succ)
        (hf : first ≤ j.castSucc) (x : neckBuffer δ),
        B.stageChart j hj ha x =
          H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hj (Φ x).val.val := by
  let r := Real.sqrt N.scale⁻¹
  have hrsq : r ^ 2 = N.scale⁻¹ := Real.sq_sqrt (inv_nonneg.mpr N.scale_pos.le)
  have hf (j : Fin H.eventCount) (ha : H.time i.succ - r^2 < H.time j.succ) :
      first ≤ j.castSucc :=
    first_le_stage_of_time_lt (by rwa [hrsq]) j ha
  let Ψ : neckBuffer δ → H.backwardSurvivorDomain first i.castSucc hle := fun x => (Φ x).val.val
  have hΨ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Ψ :=
    footprint_lift_to_domain_isSmoothEmbedding N K Φ hΦ hmap
  let chart : (j : Fin H.eventCount) → j.val ≤ i.val →
      H.time i.succ - r^2 < H.time j.succ → C(neckBuffer δ, (H.stage j.castSucc).Carrier) :=
    fun j hj ha => ⟨H.backwardSurvivorMap first i.castSucc hle j.castSucc (hf j ha) hj ∘ Ψ,
      ((H.backwardSurvivorMap_isSmoothEmbedding first i.castSucc hle j.castSucc (hf j ha) hj).contMDiff.comp
        hΨ.contMDiff).continuous⟩
  refine ⟨{
    radius_pos := Real.sqrt_pos.mpr (inv_pos.mpr N.scale_pos)
    left_nonneg := (H.time_nonneg first).trans (by rwa [hrsq])
    stageChart := chart
    stageChart_smooth := ?_
    terminal_chart := ?_
    crossing := ?_
    metric := S.base.metric
    terminal_metric := hterminal
    metric_on_slab := ?_
    timeDifferenceJet := Z
    timeDifferenceJet_eq := hZ
    parabolic_closeness := hclose
    metric_smooth := ?_ }, rfl, rfl, ?_⟩
  · intro j hj ha
    exact (H.backwardSurvivorMap_isSmoothEmbedding first i.castSucc hle j.castSucc (hf j ha) hj).comp
      hΨ (by decide)
  · intro ha x
    change H.backwardSurvivorMap first i.castSucc hle i.castSucc (hf i ha) le_rfl (Ψ x) = _
    rw [H.backwardSurvivorMap_last]
    exact congrArg Subtype.val (congrFun hmap x)
  · intro j hj next ha hn x
    exact H.backwardSurvivorMap_crossing first i.castSucc hle j (hf j ha)
      (by change j.val + 1 ≤ i.val; omega) (Ψ x)
  · intro j hj ha v hv htlo hthi x V W
    have htime : H.time i.succ + r ^ 2 * v = H.time i.succ + v / N.scale := by
      rw [hrsq, div_eq_mul_inv, mul_comm]
    have hscale : (r ^ 2)⁻¹ = N.scale := by rw [hrsq, inv_inv]
    rw [hmetric v hv, hscale, htime]
    rw [htime] at htlo hthi
    by_cases he : j = i
    · subst j
      exact H.localPullMetric_scale_backwardSurvivorTerminalFaceMetric_inner first i hle K G
        N.scale N.scale_pos Φ hΦ hthi (hlast _ ⟨htlo, hthi.le⟩) x V W
    · have hl : j.succ ≤ i.castSucc := by
        have hlt := lt_of_le_of_ne hj (fun h => he (Fin.ext h))
        change j.val + 1 ≤ i.val
        omega
      exact H.localPullMetric_scale_backwardSurvivorSlabMetric_inner first i hle K G
        N.scale N.scale_pos Φ hΦ j (hf j ha) hl hthi
        (hslabs j (hf j ha) hl _ ⟨htlo, hthi.le⟩) x V W
  · let _ : SigmaCompactSpace (neckBuffer δ) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
    intro p t ht
    have hg := solution_metricCLMSection_contMDiffOn_closed S hS
      (show -θ < (-1 : ℝ) by linarith) (show (-1 : ℝ) < 0 by norm_num)
      (show Icc (-θ) 0 ⊆ (RealTimeInterval.closed (-θ) 0 (by linarith)).carrier from Subset.rfl)
      (show Ioo (-θ) 0 ⊆ (RealTimeInterval.closed (-θ) 0 (by linarith)).regular from Subset.rfl)
    obtain ⟨U, hU, hp, hUb, A, hA, hEq⟩ :=
      Geometry.Metric.exists_local_metric_coefficient_extension S.base.metric
        (by norm_num : (-1 : ℝ) < 0) hg p
    exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
      fun s hs x hx v w => hEq s hs.2 x hx v w⟩
  · intro j hj ha hfj x
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem eventually_exists_incomingBackwardNeck_of_historical_spatial_convergence
    (H : ℕ → ObservedHistory.{u}) (i : ∀ n, Fin (H n).eventCount)
    (first : ∀ n, Fin ((H n).eventCount + 1)) (hle : ∀ n, first n ≤ (i n).castSucc)
    {δ θ : ℝ} {k : ℕ} (hθ : 1 < θ)
    (N : ∀ n, NormalizedNeck ((H n).event (i n)).terminal.metric δ k)
    (K : ∀ n, Set ((H n).event (i n)).incoming.terminalRegularOpen)
    (Φ : ∀ n, neckBuffer δ → (H n).backwardSurvivorFootprintInterior
      (first n) (i n) (hle n) (K n))
    (hΦ : ∀ n, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Φ n))
    (hmap : ∀ n, (H n).backwardSurvivorFootprintMap (first n) (i n) (hle n) (K n) ∘ Φ n =
      (N n).chart)
    (G : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel
      ((H n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)))
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θ) 0 (by linarith)))
    (hS : ∀ n, IsSolutionOn (S n))
    (hterminal : ∀ n, (S n).base.metric 0 = (N n).normalizedMetric)
    (hmetric : ∀ n t, t ∈ Ico (-1 : ℝ) 0 → (S n).base.metric t = localPullMetric
      (scaleMetric (N n).scale (N n).scale_pos
        (G n ((H n).time (i n).succ + t / (N n).scale))) (Φ n) (hΦ n))
    (hslabs : ∀ n (j : Fin (H n).eventCount) (hf : first n ≤ j.castSucc)
      (hl : j.succ ≤ (i n).castSucc), ∀ t ∈ Icc ((H n).time j.castSucc) ((H n).time j.succ),
        G n t = (((H n).backwardSurvivorSlabMetric (first n) (i n).castSucc (hle n) j hf hl t).restrictOpen
          ((H n).backwardSurvivorTerminalFace (first n) (i n) (hle n))).restrictOpen
            ((H n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)))
    (hlast : ∀ n t, t ∈ Icc ((H n).time (i n).castSucc) ((H n).time (i n).succ) →
      G n t = ((H n).backwardSurvivorTerminalFaceMetric (first n) (i n) (hle n) t).restrictOpen
        ((H n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)))
    (hstart : ∀ n, (H n).time (first n) ≤ (H n).time (i n).succ - (N n).scale⁻¹)
    (hconv : ∀ A : Set (neckBuffer δ), IsCompact A → ∀ r : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (-1 : ℝ) 0,
        metricDerivNormSupOn A r ((S n).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) < ε) :
    ∀ᶠ n in atTop,
      ∃ B : IncomingBackwardNeck (H n) (i n) (N n) (Real.sqrt (N n).scale⁻¹),
        B.metric = (S n).base.metric ∧
        ∀ (j : Fin (H n).eventCount) (hj : j.val ≤ (i n).val)
          (ha : (H n).time (i n).succ - (Real.sqrt (N n).scale⁻¹)^2 < (H n).time j.succ)
          (hf : first n ≤ j.castSucc) (x : neckBuffer δ),
          B.stageChart j hj ha x =
            (H n).backwardSurvivorMap (first n) (i n).castSucc (hle n) j.castSucc hf hj
              (Φ n x).val.val := by
  have hδ : 0 < δ := (N 0).delta_pos
  have hjets := eventually_exists_neck_time_difference_jets_of_spatial_convergence
    hδ (by linarith : -θ < (-1 : ℝ)) k S hS Subset.rfl Subset.rfl hconv
  filter_upwards [hjets] with n hn
  obtain ⟨Z, hZ, hclose⟩ := hn
  obtain ⟨B, hB, _, hchart⟩ := (N n).exists_incomingBackwardNeck_of_historical_solution
    (K n) (Φ n) (hΦ n) (hmap n) (G n) hθ (S n) (hS n) (hterminal n)
      (hmetric n) (hslabs n) (hlast n) (hstart n) Z hZ hclose
  exact ⟨B, hB, hchart⟩

open scoped NNReal in
theorem exists_subsequence_incomingBackwardNeck_of_historical_scalar_bounds
    (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
    (first : ∀ i, Fin ((H i).eventCount + 1))
    (hle : ∀ i, first i ≤ (event i).castSucc)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {k : ℕ} (N : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (δ 0) k)
    (K : ∀ i, Set ((H i).event (event i)).incoming.terminalRegularOpen)
    (Phi : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorFootprintInterior
      (first i) (event i) (hle i) (K i))
    (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
    (hmap : ∀ i, (H i).backwardSurvivorFootprintMap (first i) (event i) (hle i) (K i) ∘ Phi i =
      (N i).chart)
    (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
      ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i)))
    (S : ∀ n, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n))
      (RealTimeInterval.closed (-2) 0 (by norm_num)))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (hzero : ∀ i, (S 0 i).base.metric 0 = (N i).normalizedMetric)
    (hmetric : ∀ i t, t ∈ Ico (-1 : ℝ) 0 → (S 0 i).base.metric t = localPullMetric
      (scaleMetric (N i).scale (N i).scale_pos
        (G i ((H i).time (event i).succ + t / (N i).scale))) (Phi i) (hPhi i))
    (hslabs : ∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc)
      (hl : j.succ ≤ (event i).castSucc),
      ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
        G i t = (((H i).backwardSurvivorSlabMetric (first i) (event i).castSucc
          (hle i) j hf hl t).restrictOpen
          ((H i).backwardSurvivorTerminalFace (first i) (event i) (hle i))).restrictOpen
            ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i)))
    (hlast : ∀ i t, t ∈ Icc ((H i).time (event i).castSucc) ((H i).time (event i).succ) →
      G i t = ((H i).backwardSurvivorTerminalFaceMetric (first i) (event i) (hle i) t).restrictOpen
        ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i)))
    (hstart : ∀ i, (H i).time (first i) ≤ (H i).time (event i).succ - (N i).scale⁻¹)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (offset : ℕ → ℕ) (hoffset : offset 0 = 0)
    (hcompat : ∀ n m t, t ∈ Icc (-2 : ℝ) 0 →
      (fun i => ((S n (i - offset n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m (i - offset m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    (C : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hscale : Tendsto (fun i => (N i).scale) atTop atTop)
    (hderiv : ∀ n, ∀ A : Set (neckBuffer (δ n)), IsCompact A → ∀ᶠ i in atTop,
      ∀ x ∈ A, ∀ t ∈ Ioo (-2 : ℝ) 0,
        q (i + offset n) < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C * (S n i).scalar t x ^ 2)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, Perelman.PhiAlmostNonnegative (S n i)
      (Icc (-2 : ℝ) 0) (Perelman.rescalePinchingFunction (N (i + offset n)).scale phi)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ᶠ i in atTop,
      ∃ B : IncomingBackwardNeck (H (rho i)) (event (rho i)) (N (rho i))
          (Real.sqrt (N (rho i)).scale⁻¹),
        B.metric = (S 0 (rho i)).base.metric ∧
        ∀ (j : Fin (H (rho i)).eventCount) (hj : j.val ≤ (event (rho i)).val)
          (ha : (H (rho i)).time (event (rho i)).succ - (Real.sqrt (N (rho i)).scale⁻¹)^2 <
            (H (rho i)).time j.succ)
          (hf : first (rho i) ≤ j.castSucc) (x : neckBuffer (δ 0)),
          B.stageChart j hj ha x =
            (H (rho i)).backwardSurvivorMap (first (rho i)) (event (rho i)).castSucc
              (hle (rho i)) j.castSucc hf hj (Phi (rho i) x).val.val := by
  obtain ⟨rho,hrho,hconv⟩ :=
    exists_subsequence_converges_to_shrinkingCylinder_on_subinterval_of_scalar_deriv_bound
      hδ hδlim S hS (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) < 2) Subset.rfl Subset.rfl hterminal offset hcompat
      C q (fun i => (N i).scale) hq (fun i => (N i).scale_pos) hscale hderiv hphi hpinch
  refine ⟨rho,hrho,?_⟩
  apply eventually_exists_incomingBackwardNeck_of_historical_spatial_convergence
    (fun i => H (rho i)) (fun i => event (rho i)) (fun i => first (rho i))
    (fun i => hle (rho i)) (by norm_num : (1 : ℝ) < 2)
    (fun i => N (rho i)) (fun i => K (rho i)) (fun i => Phi (rho i))
    (fun i => hPhi (rho i)) (fun i => hmap (rho i)) (fun i => G (rho i))
    (fun i => S 0 (rho i)) (fun i => hS 0 (rho i)) (fun i => hzero (rho i))
    (fun i => hmetric (rho i)) (fun i => hslabs (rho i)) (fun i => hlast (rho i))
    (fun i => hstart (rho i)) ?_
  intro A hA r epsilon hepsilon
  obtain ⟨i0,hi0⟩ := hconv 0 A hA r epsilon hepsilon
  refine ⟨i0,fun i hi t ht => ?_⟩
  have hh := hi0 i hi t ⟨by norm_num at *; linarith [ht.1],ht.2⟩
  simpa only [hoffset,Nat.sub_zero] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
