import DifferentialGeometry.Geometry.Neck.NormalizedFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CylinderBackwardConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckIncomingAdapter
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance terminal_regular_sigmaCompact (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

section
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {s : ℝ} {J : (H.stage last).IncomingSlab (H.time last) s} {L : J.TerminalLimitMetric}

private theorem prospective_historical_normalized_pullback_overlap
    {δ₀ δ₁ δ₂ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ₀ k)
    (hδ₁ : δ₀ ≤ δ₁) (hδ₂ : δ₀ ≤ δ₂) (hδ₁' : δ₁ < 1) (hδ₂' : δ₂ < 1)
    (K₁ K₂ : Set J.terminalRegularOpen)
    (Φ₁ : neckBuffer δ₁ → H.backwardSurvivorIncomingFootprint first last hle J K₁)
    (Φ₂ : neckBuffer δ₂ → H.backwardSurvivorIncomingFootprint first last hle J K₂)
    (hΦ₁ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ₁)
    (hΦ₂ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ₂)
    (hmap₁ : H.backwardSurvivorIncomingFootprintMap first last hle J K₁ ∘ Φ₁ = (N.monoDelta hδ₁ hδ₁').chart)
    (hmap₂ : H.backwardSurvivorIncomingFootprintMap first last hle J K₂ ∘ Φ₂ = (N.monoDelta hδ₂ hδ₂').chart)
    (G₁ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingFootprint first last hle J K₁))
    (G₂ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingFootprint first last hle J K₂))
    (hslabs₁ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₁ t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle J)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle J K₁))
    (hslabs₂ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₂ t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle J)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle J K₂))
    (hlast₁ : ∀ t ∈ Icc (H.time last) (s), G₁ t =
      (H.backwardSurvivorIncomingMetric first last hle J L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle J K₁))
    (hlast₂ : ∀ t ∈ Icc (H.time last) (s), G₂ t =
      (H.backwardSurvivorIncomingMetric first last hle J L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle J K₂))
    {t : ℝ} (ht : t ∈ Icc (H.time first) (s)) :
    (localPullMetric (scaleMetric N.scale N.scale_pos (G₁ t)) Φ₁ hΦ₁).restrictOpenOfSubset
        (inf_le_left : neckBuffer δ₁ ⊓ neckBuffer δ₂ ≤ neckBuffer δ₁) =
      (localPullMetric (scaleMetric N.scale N.scale_pos (G₂ t)) Φ₂ hΦ₂).restrictOpenOfSubset
        (inf_le_right : neckBuffer δ₁ ⊓ neckBuffer δ₂ ≤ neckBuffer δ₂) := by
  let U := neckBuffer δ₁ ⊓ neckBuffer δ₂
  let ι₁ : U → neckBuffer δ₁ := TopologicalSpace.Opens.inclusion inf_le_left
  let ι₂ : U → neckBuffer δ₂ := TopologicalSpace.Opens.inclusion inf_le_right
  have hι₁ : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ ι₁ :=
    fun x => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun y : U => (inf_le_left : U ≤ neckBuffer δ₁) y.property)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U x)
  have hι₂ : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ ι₂ :=
    fun x => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (fun y : U => (inf_le_right : U ≤ neckBuffer δ₂) y.property)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U x)
  have hcomp : H.backwardSurvivorIncomingFootprintMap first last hle J K₁ ∘ (Φ₁ ∘ ι₁) =
      H.backwardSurvivorIncomingFootprintMap first last hle J K₂ ∘ (Φ₂ ∘ ι₂) := by
    funext x
    have h₁ := congrFun hmap₁ (ι₁ x)
    have h₂ := congrFun hmap₂ (ι₂ x)
    exact h₁.trans h₂.symm
  have heq := H.localPullMetric_backwardSurvivorIncomingFootprint_eq K₁ K₂ G₁ G₂
    hslabs₁ hslabs₂ hlast₁ hlast₂ (Φ₁ ∘ ι₁) (Φ₂ ∘ ι₂)
    (DifferentialGeometry.isLocalDiffeomorph_comp hΦ₁ hι₁)
    (DifferentialGeometry.isLocalDiffeomorph_comp hΦ₂ hι₂) hcomp ht
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hh := congrArg (fun g => g.inner x v w) heq
  have hd₁ (v : TangentSpace NeckCylinderModel x) :
      mfderiv NeckCylinderModel ThreeModel (Φ₁ ∘ ι₁) x v =
        mfderiv NeckCylinderModel ThreeModel Φ₁ (ι₁ x) v := by
    rw [mfderiv_comp_apply x (hΦ₁.contMDiff.mdifferentiableAt (by decide))
      (hι₁.contMDiff.mdifferentiableAt (by decide))]
    change (mfderiv NeckCylinderModel ThreeModel Φ₁ (ι₁ x))
      ((mfderiv NeckCylinderModel NeckCylinderModel
        (TopologicalSpace.Opens.inclusion inf_le_left : U → neckBuffer δ₁) x) v) = _
    rw [DifferentialGeometry.mfderiv_opens_incl]
    rfl
  have hd₂ (v : TangentSpace NeckCylinderModel x) :
      mfderiv NeckCylinderModel ThreeModel (Φ₂ ∘ ι₂) x v =
        mfderiv NeckCylinderModel ThreeModel Φ₂ (ι₂ x) v := by
    rw [mfderiv_comp_apply x (hΦ₂.contMDiff.mdifferentiableAt (by decide))
      (hι₂.contMDiff.mdifferentiableAt (by decide))]
    change (mfderiv NeckCylinderModel ThreeModel Φ₂ (ι₂ x))
      ((mfderiv NeckCylinderModel NeckCylinderModel
        (TopologicalSpace.Opens.inclusion inf_le_right : U → neckBuffer δ₂) x) v) = _
    rw [DifferentialGeometry.mfderiv_opens_incl]
    rfl
  simp only [localPullMetric_inner, hd₁, hd₂] at hh
  change N.scale * _ = N.scale * _
  exact congrArg (N.scale * ·) hh


end

variable (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (hoffset : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  {k : ℕ} (hk : ∀ i, k ≤ order i)
  (N : ∀ i, NormalizedNeck (L i).metric (δ 0) k)
  (hN : ∀ i, N i = ((O i).monoDelta
    (by simpa only [hoffset, Nat.add_zero] using hprecision 0 i) (hδ1 0)).lowerOrder (hk i))
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (htrace : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (hstart2 : ∀ i, (H i).time (first i) ≤ s i - 2 / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    qPhysical i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)

include heps horder hprecision hN htrace hinside hstart2 hinit hderivative hfinal hphi hpinching hpinchFinal in
private theorem exists_same_chart_prospective_historical_rows_from_survivor_footprints :
    ∃ (K : ∀ i, Set (J i).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i)))
      (S : ∀ n, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n))
        (RealTimeInterval.closed (-2) 0 (by norm_num))),
      (∀ i, (H i).backwardSurvivorIncomingFootprintMap (first i) (last i) (hle i) (J i) (K i) ∘ Phi i =
        (N i).chart) ∧
      (∀ n i, IsSolutionOn (S n i)) ∧
      (∀ i, (S 0 i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S 0 i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos
          (G i (s i + t / (N i).scale))) (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc)
        (hl : j.succ ≤ (last i)),
        ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
          G i t = (((H i).backwardSurvivorSlabMetric (first i) (last i)
            (hle i) j hf hl t).restrictOpen
            ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (J i))).restrictOpen
              ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ i t, t ∈ Icc ((H i).time (last i)) (s i) →
        G i t = ((H i).backwardSurvivorIncomingMetric (first i) (last i) (hle i) (J i) (L i) t).restrictOpen
          ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ i, (H i).time (first i) ≤ s i - (N i).scale⁻¹) ∧
      (∀ n, MetricCInfConvergenceOnCompacts
        (fun i => (S n i).base.metric 0)
        (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
        (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))) ∧
      (∀ n m t, t ∈ Icc (-2 : ℝ) 0 →
        (fun i => ((S n (i - offset n)).base.metric t).restrictOpenOfSubset
          (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
        (fun i => ((S m (i - offset m)).base.metric t).restrictOpenOfSubset
          (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m)))) ∧
      (∀ n, ∀ A : Set (neckBuffer (δ n)), IsCompact A → ∀ᶠ i in atTop,
        ∀ x ∈ A, ∀ t ∈ Ioo (-2 : ℝ) 0,
          qPhysical (i + offset n) / (O (i + offset n)).scale < (S n i).scalar t x →
          |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
            C * (S n i).scalar t x ^ 2) ∧
      (∀ n, ∀ᶠ i in atTop, Perelman.PhiAlmostNonnegative (S n i)
        (Icc (-2 : ℝ) 0) (Perelman.rescalePinchingFunction (N (i + offset n)).scale phi)) := by
  classical
  obtain ⟨tail, rfl⟩ : ∃ tail : ℕ → ℕ, offset = fun n => Nat.casesOn n 0 tail := by
    refine ⟨fun n => offset (n + 1), funext ?_⟩
    intro n
    cases n with
    | zero => exact hoffset
    | succ n => rfl
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 tail
  have hrow (n j : ℕ) := (H (j + offset n)).exists_historical_pullback_solution_from_incoming_slab_with_scalar_bounds
    (first (j + offset n)) (last (j + offset n)) (hle (j + offset n))
    (J (j + offset n)) (L (j + offset n)) (hinit (j + offset n))
    ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n))
    (Footprint n j) (htrace n j) (hinside n j) (by norm_num : (0 : ℝ) ≤ 2)
    (hstart2 (j + offset n)) (hderivative (j + offset n)) (hfinal (j + offset n))
    hphi.contDiff.continuous (hpinching (j + offset n)) (hpinchFinal (j + offset n))
  choose F hF GG SS hmap hS hzero hmetric hslabs hlast hderiv hpinch using hrow
  have hNscale (i : ℕ) : (N i).scale = (O i).scale := by rw [hN]; rfl
  have hNchart (i : ℕ) : (N i).chart =
      ((O i).monoDelta (by simpa only [hoffset,Nat.add_zero] using hprecision 0 i) (hδ1 0)).chart := by
    rw [hN]
    rfl
  have hNmetric (i : ℕ) : (N i).normalizedMetric =
      ((O i).monoDelta (by simpa only [hoffset,Nat.add_zero] using hprecision 0 i) (hδ1 0)).normalizedMetric := by
    rw [hN]
    rfl
  let K : ∀ i, Set (J i).terminalRegularOpen := fun i => Footprint 0 i
  let F0 : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i) := fun i => F 0 i
  have hF0 : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F0 i) := fun i => hF 0 i
  let G0 : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
      ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i)) := fun i => GG 0 i
  refine ⟨K,F0,hF0,G0,SS,?_,hS,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hNchart]
    exact hmap 0 i
  · intro i
    rw [hNmetric]
    exact hzero 0 i
  · intro i t
    rw [hN]
    exact hmetric 0 i t
  · intro i j hf hl t ht
    exact hslabs 0 i j hf hl t ht
  · intro i t ht
    exact hlast 0 i t ht
  · intro i
    rw [hNscale,inv_eq_one_div]
    have hleDiv : 1 / (O i).scale ≤ 2 / (O i).scale :=
      div_le_div_of_nonneg_right (by norm_num) (O i).scale_pos.le
    exact (hstart2 i).trans (sub_le_sub_left hleDiv _)
  · intro n A hA
    have htail : Tendsto (fun j : ℕ => j + offset n) atTop atTop := tendsto_add_atTop_nat _
    have hc := NormalizedNeck.metricCInfConvergenceOn_restrict_of_precision_tendsto_zero
      (fun j => O (j + offset n)) (hprecision n) (heps.comp htail) (horder.comp htail) A
    intro p eta heta
    obtain ⟨j0,hj0⟩ := hc p eta heta
    refine ⟨j0,fun j hj => ?_⟩
    change metricDerivNormSupOn A p ((SS n j).base.metric 0) _ _ < eta
    rw [hzero n j]
    exact hj0 j hj
  · intro n m t ht
    filter_upwards [eventually_ge_atTop (max (offset n) (offset m))] with j hj
    have hjn : offset n ≤ j := (le_max_left _ _).trans hj
    have hjm : offset m ≤ j := (le_max_right _ _).trans hj
    have hn : j - offset n + offset n = j := Nat.sub_add_cancel hjn
    have hm : j - offset m + offset m = j := Nat.sub_add_cancel hjm
    rw [hmetric n (j - offset n) t, hmetric m (j - offset m) t]
    let jn := j - offset n
    let jm := j - offset m
    have htime : s j + t / (O j).scale ∈
        Icc ((H j).time (first j)) (s j) := by
      have hlo : -2 / (O j).scale ≤ t / (O j).scale :=
        div_le_div_of_nonneg_right ht.1 (O j).scale_pos.le
      have hhi : t / (O j).scale ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht.2 (O j).scale_pos.le
      have hstart := hstart2 j
      rw [neg_div] at hlo
      constructor <;> linarith
    have hrowsame : ∀ (an am : ℕ) (hpn : eps an ≤ δ n) (hpm : eps am ≤ δ m),
        an = j → am = j →
        ∀ (Kn : Set (J an).terminalRegularOpen)
          (Km : Set (J am).terminalRegularOpen)
          (Fn : neckBuffer (δ n) → (H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)
          (Fm : neckBuffer (δ m) → (H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)
          (hFn : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fn)
          (hFm : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fm)
          (Gn : ℝ → SmoothRiemannianMetric ThreeModel
            ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn))
          (Gm : ℝ → SmoothRiemannianMetric ThreeModel
            ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)),
          ((H an).backwardSurvivorIncomingFootprintMap (first an) (last an) (hle an) (J an) Kn ∘ Fn =
            ((O an).monoDelta hpn (hδ1 n)).chart) →
          ((H am).backwardSurvivorIncomingFootprintMap (first am) (last am) (hle am) (J am) Km ∘ Fm =
            ((O am).monoDelta hpm (hδ1 m)).chart) →
          (∀ (r : Fin (H an).eventCount) (hf : first an ≤ r.castSucc)
            (hl : r.succ ≤ (last an)), ∀ u ∈ Icc ((H an).time r.castSucc) ((H an).time r.succ),
              Gn u = (((H an).backwardSurvivorSlabMetric (first an) (last an)
                (hle an) r hf hl u).restrictOpen ((H an).backwardSurvivorIncomingDomain (first an) (last an) (hle an) (J an))).restrictOpen
                  ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)) →
          (∀ (r : Fin (H am).eventCount) (hf : first am ≤ r.castSucc)
            (hl : r.succ ≤ (last am)), ∀ u ∈ Icc ((H am).time r.castSucc) ((H am).time r.succ),
              Gm u = (((H am).backwardSurvivorSlabMetric (first am) (last am)
                (hle am) r hf hl u).restrictOpen ((H am).backwardSurvivorIncomingDomain (first am) (last am) (hle am) (J am))).restrictOpen
                  ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)) →
          (∀ u ∈ Icc ((H an).time (last an)) (s an),
            Gn u = ((H an).backwardSurvivorIncomingMetric (first an) (last an) (hle an) (J an) (L an) u).restrictOpen
              ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)) →
          (∀ u ∈ Icc ((H am).time (last am)) (s am),
            Gm u = ((H am).backwardSurvivorIncomingMetric (first am) (last am) (hle am) (J am) (L am) u).restrictOpen
              ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)) →
          (localPullMetric (scaleMetric (O an).scale (O an).scale_pos
              (Gn (s an + t / (O an).scale))) Fn hFn).restrictOpenOfSubset
                (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n)) =
            (localPullMetric (scaleMetric (O am).scale (O am).scale_pos
              (Gm (s am + t / (O am).scale))) Fm hFm).restrictOpenOfSubset
                (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m)) := by
      intro an am hpn hpm han ham
      subst an
      subst am
      intro Kn Km Fn Fm hFn hFm Gn Gm hmapn hmapm hslabn hslabm hlastn hlastm
      exact prospective_historical_normalized_pullback_overlap (O j) hpn hpm (hδ1 n) (hδ1 m)
        Kn Km Fn Fm hFn hFm hmapn hmapm Gn Gm hslabn hslabm hlastn hlastm htime
    exact hrowsame (jn + offset n) (jm + offset m) (hprecision n jn) (hprecision m jm)
      hn hm (Footprint n jn) (Footprint m jm) (F n jn) (F m jm) (hF n jn) (hF m jm)
      (GG n jn) (GG m jm) (hmap n jn) (hmap m jm) (hslabs n jn) (hslabs m jm)
      (hlast n jn) (hlast m jm)
  · intro n A hA
    exact Eventually.of_forall fun j x hx t ht hh => hderiv n j t ht x hh
  · intro n
    apply Eventually.of_forall
    intro j
    rw [hNscale]
    exact hpinch n j


include hδ hδlim heps horder hprecision hN htrace hinside hstart2 hinit hderivative hfinal
  hphi hpinching hpinchFinal hq hscale in
private theorem exists_subsequence_prospective_historical_neck_recognition :
    ∃ (K : ∀ i, Set (J i).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorIncomingFootprint
        (first i) (last i) (hle i) (J i) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i)))
      (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ 0))
        (RealTimeInterval.closed (-2) 0 (by norm_num)))
      (rho : ℕ → ℕ),
      StrictMono rho ∧
      (∀ i, (H i).backwardSurvivorIncomingFootprintMap
        (first i) (last i) (hle i) (J i) (K i) ∘ Phi i = (N i).chart) ∧
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (S i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos (G i (s i + t / (N i).scale)))
        (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc) (hl : j.succ ≤ last i),
        ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
          G i t = (((H i).backwardSurvivorSlabMetric (first i) (last i)
            (hle i) j hf hl t).restrictOpen
            ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (J i))).restrictOpen
              ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ i t, t ∈ Icc ((H i).time (last i)) (s i) →
        G i t = ((H i).backwardSurvivorIncomingMetric
          (first i) (last i) (hle i) (J i) (L i) t).restrictOpen
          ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ A : Set (neckBuffer (δ 0)), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn A p ((S (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer (δ 0))) (roundCylinderMetric.restrictOpen (neckBuffer (δ 0))) < η) ∧
      ∀ᶠ i in atTop,
        ∃ Z : (b : ℕ) → Icc (-1 : ℝ) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer (δ 0)) ∞ 2,
          (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
            metricTensorField ((S (rho i)).base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer (δ 0))) x) (Icc (-1 : ℝ) 0) v.1) ∧
          ∃ η : ℝ, η < δ 0 ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest (δ 0),
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer (δ 0))
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  obtain ⟨K,Phi,hPhi,G,S,hmap,hS,hzero,hmetric,hslabs,hlast,hstart,hterminal,hcompat,hderiv,hpinch⟩ :=
    exists_same_chart_prospective_historical_rows_from_survivor_footprints H last first hle s J L
      hinit δ hδ1 eps order O heps horder offset hoffset hprecision hk N hN Footprint htrace
      hinside hstart2 C qPhysical hderivative hfinal hphi hpinching hpinchFinal
  have hNscale (i : ℕ) : (N i).scale = (O i).scale := by rw [hN]; rfl
  have hscaleN : Tendsto (fun i => (N i).scale) atTop atTop := by
    simpa only [hNscale] using hscale
  obtain ⟨rho,hrho,hconv⟩ :=
    exists_subsequence_converges_to_shrinkingCylinder_on_subinterval_of_scalar_deriv_bound
      hδ hδlim S hS (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) < 2) Subset.rfl Subset.rfl hterminal offset hcompat
      C (fun i => qPhysical i / (O i).scale) (fun i => (N i).scale) hq
      (fun i => (N i).scale_pos) hscaleN hderiv hphi hpinch
  have hc : ∀ A : Set (neckBuffer (δ 0)), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
        metricDerivNormSupOn A p ((S 0 (rho i)).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
            (neckBuffer (δ 0))) (roundCylinderMetric.restrictOpen (neckBuffer (δ 0))) < η := by
    simpa only [hoffset, Nat.sub_zero] using hconv 0
  refine ⟨K,Phi,hPhi,G,S 0,rho,hrho,hmap,hS 0,hzero,hmetric,hslabs,hlast,hc,?_⟩
  apply eventually_exists_neck_time_difference_jets_of_spatial_convergence
    (hδ 0) (by norm_num : (-2 : ℝ) < -1) k (fun i => S 0 (rho i))
    (fun i => hS 0 (rho i)) Subset.rfl Subset.rfl
  intro A hA r eta heta
  obtain ⟨j,hj⟩ := hc A hA r eta heta
  refine ⟨j,fun i hi t ht => hj i hi t ⟨?_,ht.2⟩⟩
  linarith [ht.1]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] terminal_regular_sigmaCompact

theorem exists_prospective_neck_convergence_of_growing_source_traces
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (hprecision0 : ∀ i, eps i ≤ δ)
  {k : ℕ} (hk : ∀ i, k ≤ order i)
  (N : ∀ i, NormalizedNeck (L i).metric δ k)
  (hN : ∀ i, N i = ((O i).monoDelta
    (hprecision0 i) hδ1).lowerOrder (hk i))
  (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
  (hfit0 : ∀ i, δ⁻¹ + 1 ≤ radius i)
  (htrace : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
    Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) x.val))
  (hstart2 : ∀ i, (H i).time (first i) ≤ s i - 2 / (O i).scale)
  (C : ℝ≥0) (q : ℝ)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi) :
    ∃ (K : ∀ i, Set (J i).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer δ → (H i).backwardSurvivorIncomingFootprint
        (first i) (last i) (hle i) (J i) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i)))
      (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-2) 0 (by norm_num)))
      (rho : ℕ → ℕ),
      StrictMono rho ∧
      (∀ i, (H i).backwardSurvivorIncomingFootprintMap
        (first i) (last i) (hle i) (J i) (K i) ∘ Phi i = (N i).chart) ∧
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (S i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos (G i (s i + t / (N i).scale)))
        (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc) (hl : j.succ ≤ last i),
        ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
          G i t = (((H i).backwardSurvivorSlabMetric (first i) (last i)
            (hle i) j hf hl t).restrictOpen
            ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (J i))).restrictOpen
              ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ i t, t ∈ Icc ((H i).time (last i)) (s i) →
        G i t = ((H i).backwardSurvivorIncomingMetric
          (first i) (last i) (hle i) (J i) (L i) t).restrictOpen
          ((H i).backwardSurvivorIncomingFootprint (first i) (last i) (hle i) (J i) (K i))) ∧
      (∀ A : Set (neckBuffer δ), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn A p ((S (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < η) ∧
      ∀ᶠ i in atTop,
        ∃ Z : (b : ℕ) → Icc (-1 : ℝ) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
            metricTensorField ((S (rho i)).base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-1 : ℝ) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  let d : ℕ → ℝ := fun n => Nat.casesOn n δ (fun m => δ / ((m : ℝ) + 2))
  have hd : ∀ n, 0 < d n := by
    intro n
    cases n with
    | zero => exact hδ
    | succ n => dsimp [d]; positivity
  have hd1 : ∀ n, d n < 1 := by
    intro n
    cases n with
    | zero => exact hδ1
    | succ n =>
      dsimp [d]
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    apply (hh.const_div_atTop δ).congr'
    apply Eventually.of_forall
    intro n
    cases n with
    | zero => simp [d]
    | succ n => dsimp [d]; congr 1; push_cast; ring
  have htail (n : ℕ) : ∃ m : ℕ, ∀ j, m ≤ j → eps j ≤ d n ∧ (d n)⁻¹ + 1 ≤ radius j := by
    have hp : ∀ᶠ j in atTop, eps j ≤ d n :=
      (heps.eventually (Iio_mem_nhds (hd n))).mono fun j hj => hj.le
    have hr : ∀ᶠ j in atTop, (d n)⁻¹ + 1 ≤ radius j :=
      hradius.eventually (eventually_ge_atTop _)
    exact eventually_atTop.1 (hp.and hr)
  choose tail htail using htail
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 (fun m => tail (m+1))
  have hoffset : offset 0 = 0 := rfl
  have hprecision : ∀ n j, eps (j + offset n) ≤ d n := by
    intro n j
    cases n with
    | zero => simpa [offset, d] using hprecision0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).1
  have hfit : ∀ n j, (d n)⁻¹ + 1 ≤ radius (j + offset n) := by
    intro n j
    cases n with
    | zero => simpa [offset, d] using hfit0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).2
  let K : ∀ n j, Set (J (j + offset n)).terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart ''
      {z | -(radius (j + offset n)) ≤ z.val.2 ∧ z.val.2 ≤ radius (j + offset n)}
  have hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hd1 n)).chart ⊆
      interior (K n j) := by
    intro n j x hx
    obtain ⟨z, rfl⟩ := hx
    dsimp [K]
    rw [(O (j + offset n)).interior_image_closedSlab]
    refine ⟨TopologicalSpace.Opens.inclusion
      (neckBuffer_le_of_le (O (j + offset n)).delta_pos (hprecision n j)) z, ?_, rfl⟩
    constructor <;> dsimp <;> linarith [z.property.1, z.property.2, hfit n j]
  have hqevent : ∀ᶠ i in atTop, q / (O i).scale ≤ 1 := by
    filter_upwards [hscale.eventually (eventually_gt_atTop q)] with i hi
    exact (div_le_iff₀ (O i).scale_pos).2 (by linarith)
  exact exists_subsequence_prospective_historical_neck_recognition H last first hle s J L hinit
    d hd hd1 hdlim eps order O heps horder offset hoffset hprecision hk N hN K
    (fun n j => htrace (j + offset n)) hinside hstart2 C (fun _ => q) hqevent hscale
    hderivative hfinal hphi hpinching hpinchFinal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
