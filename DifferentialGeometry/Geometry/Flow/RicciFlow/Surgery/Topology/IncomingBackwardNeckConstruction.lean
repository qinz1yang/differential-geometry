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

private theorem cylinderTensorCovDeriv_eq_tensor02CovDeriv {δ : ℝ}
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2) (r : ℕ) :
    cylinderTensorCovDeriv g A r = tensor02CovDeriv A g r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [cylinderTensorCovDeriv, ih]
      rfl

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
