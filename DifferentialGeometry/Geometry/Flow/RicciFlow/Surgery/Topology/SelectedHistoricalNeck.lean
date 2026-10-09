import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckFlow
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

section
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {i : Fin H.eventCount} {hle : first ≤ i.castSucc}

private theorem historical_normalized_pullback_overlap
    {δ₀ δ₁ δ₂ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hδ₁ : δ₀ ≤ δ₁) (hδ₂ : δ₀ ≤ δ₂) (hδ₁' : δ₁ < 1) (hδ₂' : δ₂ < 1)
    (K₁ K₂ : Set (H.event i).incoming.terminalRegularOpen)
    (Φ₁ : neckBuffer δ₁ → H.backwardSurvivorFootprintInterior first i hle K₁)
    (Φ₂ : neckBuffer δ₂ → H.backwardSurvivorFootprintInterior first i hle K₂)
    (hΦ₁ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ₁)
    (hΦ₂ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ₂)
    (hmap₁ : H.backwardSurvivorFootprintMap first i hle K₁ ∘ Φ₁ = (N.monoDelta hδ₁ hδ₁').chart)
    (hmap₂ : H.backwardSurvivorFootprintMap first i hle K₂ ∘ Φ₂ = (N.monoDelta hδ₂ hδ₂').chart)
    (G₁ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K₁))
    (G₂ : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K₂))
    (hslabs₁ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₁ t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K₁))
    (hslabs₂ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₂ t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K₂))
    (hlast₁ : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ), G₁ t =
      (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K₁))
    (hlast₂ : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ), G₂ t =
      (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K₂))
    {t : ℝ} (ht : t ∈ Icc (H.time first) (H.time i.succ)) :
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
  have hcomp : H.backwardSurvivorFootprintMap first i hle K₁ ∘ (Φ₁ ∘ ι₁) =
      H.backwardSurvivorFootprintMap first i hle K₂ ∘ (Φ₂ ∘ ι₂) := by
    funext x
    have h₁ := congrFun hmap₁ (ι₁ x)
    have h₂ := congrFun hmap₂ (ι₂ x)
    exact h₁.trans h₂.symm
  have heq := H.localPullMetric_backwardSurvivorFootprint_eq K₁ K₂ G₁ G₂
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

variable (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ (event i).castSucc)
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (hoffset : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  {k : ℕ} (hk : ∀ i, k ≤ order i)
  (N : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (δ 0) k)
  (hN : ∀ i, N i = ((O i).monoDelta
    (by simpa only [hoffset, Nat.add_zero] using hprecision 0 i) (hδ1 0)).lowerOrder (hk i))
  (Footprint : ∀ n j, Set ((H (j + offset n)).event (event (j + offset n))).incoming.terminalRegularOpen)
  (htrace : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (event (j + offset n)).castSucc
    (hle (j + offset n)) x.val))
  (hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (hstart2 : ∀ i, (H i).time (first i) ≤ (H i).time (event i).succ - 2 / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)

include heps horder hprecision hN htrace hinside hstart2 hderivative hphi hpinching in
private theorem exists_same_chart_historical_rows_from_survivor_footprints :
    ∃ (K : ∀ i, Set ((H i).event (event i)).incoming.terminalRegularOpen)
      (Phi : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorFootprintInterior
        (first i) (event i) (hle i) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (G : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i)))
      (S : ∀ n, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n))
        (RealTimeInterval.closed (-2) 0 (by norm_num))),
      (∀ i, (H i).backwardSurvivorFootprintMap (first i) (event i) (hle i) (K i) ∘ Phi i =
        (N i).chart) ∧
      (∀ n i, IsSolutionOn (S n i)) ∧
      (∀ i, (S 0 i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, t ∈ Ico (-1 : ℝ) 0 → (S 0 i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos
          (G i ((H i).time (event i).succ + t / (N i).scale))) (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H i).eventCount) (hf : first i ≤ j.castSucc)
        (hl : j.succ ≤ (event i).castSucc),
        ∀ t ∈ Icc ((H i).time j.castSucc) ((H i).time j.succ),
          G i t = (((H i).backwardSurvivorSlabMetric (first i) (event i).castSucc
            (hle i) j hf hl t).restrictOpen
            ((H i).backwardSurvivorTerminalFace (first i) (event i) (hle i))).restrictOpen
              ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i))) ∧
      (∀ i t, t ∈ Icc ((H i).time (event i).castSucc) ((H i).time (event i).succ) →
        G i t = ((H i).backwardSurvivorTerminalFaceMetric (first i) (event i) (hle i) t).restrictOpen
          ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i))) ∧
      (∀ i, (H i).time (first i) ≤ (H i).time (event i).succ - (N i).scale⁻¹) ∧
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
  have hrow (n j : ℕ) := ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).exists_historical_pullback_solution_with_scalar_bounds
    (Footprint n j) (htrace n j) (hinside n j) (by norm_num : (0 : ℝ) ≤ 2)
    (hstart2 (j + offset n)) (hderivative (j + offset n)) hphi.contDiff.continuous
    (hpinching (j + offset n))
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
  let K : ∀ i, Set ((H i).event (event i)).incoming.terminalRegularOpen := fun i => Footprint 0 i
  let F0 : ∀ i, neckBuffer (δ 0) → (H i).backwardSurvivorFootprintInterior
      (first i) (event i) (hle i) (K i) := fun i => F 0 i
  have hF0 : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F0 i) := fun i => hF 0 i
  let G0 : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
      ((H i).backwardSurvivorFootprintInterior (first i) (event i) (hle i) (K i)) := fun i => GG 0 i
  refine ⟨K,F0,hF0,G0,SS,?_,hS,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hNchart]
    exact hmap 0 i
  · intro i
    rw [hNmetric]
    exact hzero 0 i
  · intro i t _
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
    have htime : (H j).time (event j).succ + t / (O j).scale ∈
        Icc ((H j).time (first j)) ((H j).time (event j).succ) := by
      have hlo : -2 / (O j).scale ≤ t / (O j).scale :=
        div_le_div_of_nonneg_right ht.1 (O j).scale_pos.le
      have hhi : t / (O j).scale ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht.2 (O j).scale_pos.le
      have hstart := hstart2 j
      rw [neg_div] at hlo
      constructor <;> linarith
    have hrowsame : ∀ (an am : ℕ) (hpn : eps an ≤ δ n) (hpm : eps am ≤ δ m),
        an = j → am = j →
        ∀ (Kn : Set ((H an).event (event an)).incoming.terminalRegularOpen)
          (Km : Set ((H am).event (event am)).incoming.terminalRegularOpen)
          (Fn : neckBuffer (δ n) → (H an).backwardSurvivorFootprintInterior
            (first an) (event an) (hle an) Kn)
          (Fm : neckBuffer (δ m) → (H am).backwardSurvivorFootprintInterior
            (first am) (event am) (hle am) Km)
          (hFn : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fn)
          (hFm : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fm)
          (Gn : ℝ → SmoothRiemannianMetric ThreeModel
            ((H an).backwardSurvivorFootprintInterior (first an) (event an) (hle an) Kn))
          (Gm : ℝ → SmoothRiemannianMetric ThreeModel
            ((H am).backwardSurvivorFootprintInterior (first am) (event am) (hle am) Km)),
          ((H an).backwardSurvivorFootprintMap (first an) (event an) (hle an) Kn ∘ Fn =
            ((O an).monoDelta hpn (hδ1 n)).chart) →
          ((H am).backwardSurvivorFootprintMap (first am) (event am) (hle am) Km ∘ Fm =
            ((O am).monoDelta hpm (hδ1 m)).chart) →
          (∀ (r : Fin (H an).eventCount) (hf : first an ≤ r.castSucc)
            (hl : r.succ ≤ (event an).castSucc), ∀ u ∈ Icc ((H an).time r.castSucc) ((H an).time r.succ),
              Gn u = (((H an).backwardSurvivorSlabMetric (first an) (event an).castSucc
                (hle an) r hf hl u).restrictOpen ((H an).backwardSurvivorTerminalFace
                  (first an) (event an) (hle an))).restrictOpen
                  ((H an).backwardSurvivorFootprintInterior (first an) (event an) (hle an) Kn)) →
          (∀ (r : Fin (H am).eventCount) (hf : first am ≤ r.castSucc)
            (hl : r.succ ≤ (event am).castSucc), ∀ u ∈ Icc ((H am).time r.castSucc) ((H am).time r.succ),
              Gm u = (((H am).backwardSurvivorSlabMetric (first am) (event am).castSucc
                (hle am) r hf hl u).restrictOpen ((H am).backwardSurvivorTerminalFace
                  (first am) (event am) (hle am))).restrictOpen
                  ((H am).backwardSurvivorFootprintInterior (first am) (event am) (hle am) Km)) →
          (∀ u ∈ Icc ((H an).time (event an).castSucc) ((H an).time (event an).succ),
            Gn u = ((H an).backwardSurvivorTerminalFaceMetric (first an) (event an) (hle an) u).restrictOpen
              ((H an).backwardSurvivorFootprintInterior (first an) (event an) (hle an) Kn)) →
          (∀ u ∈ Icc ((H am).time (event am).castSucc) ((H am).time (event am).succ),
            Gm u = ((H am).backwardSurvivorTerminalFaceMetric (first am) (event am) (hle am) u).restrictOpen
              ((H am).backwardSurvivorFootprintInterior (first am) (event am) (hle am) Km)) →
          (localPullMetric (scaleMetric (O an).scale (O an).scale_pos
              (Gn ((H an).time (event an).succ + t / (O an).scale))) Fn hFn).restrictOpenOfSubset
                (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n)) =
            (localPullMetric (scaleMetric (O am).scale (O am).scale_pos
              (Gm ((H am).time (event am).succ + t / (O am).scale))) Fm hFm).restrictOpenOfSubset
                (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m)) := by
      intro an am hpn hpm han ham
      subst an
      subst am
      intro Kn Km Fn Fm hFn hFm Gn Gm hmapn hmapm hslabn hslabm hlastn hlastm
      exact historical_normalized_pullback_overlap (O j) hpn hpm (hδ1 n) (hδ1 m)
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


include hδ heps horder hprecision hN htrace hinside hstart2 hderivative hphi hpinching
  hδlim hq hscale in
theorem exists_subsequence_selected_backward_neck_from_survivor_footprints :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ᶠ i in atTop,
      Nonempty (IncomingBackwardNeck (H (rho i)) (event (rho i)) (N (rho i))
        (Real.sqrt (N (rho i)).scale⁻¹)) := by
  obtain ⟨K,Phi,hPhi,G,S,hmap,hS,hzero,hmetric,hslabs,hlast,hstart,hterminal,hcompat,hderiv,hpinch⟩ :=
    exists_same_chart_historical_rows_from_survivor_footprints H event first hle δ hδ1
      eps order O heps horder offset hoffset hprecision hk N hN Footprint htrace hinside hstart2
      C qPhysical hderivative hphi hpinching
  have hscales : ∀ i, (N i).scale = (O i).scale := by intro i; rw [hN]; rfl
  have hscaleN : Tendsto (fun i => (N i).scale) atTop atTop := by
    simpa only [hscales] using hscale
  obtain ⟨rho,hrho,hB⟩ := exists_subsequence_incomingBackwardNeck_of_historical_scalar_bounds
    H event first hle δ hδ hδlim N K Phi hPhi hmap G S hS hzero hmetric hslabs hlast hstart
    hterminal offset hoffset hcompat C (fun i => qPhysical i / (O i).scale) hq hscaleN
    hderiv hphi hpinch
  exact ⟨rho,hrho,hB.mono fun i hi => ⟨hi.choose⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

private theorem selected_backward_neck_of_growing_source_traces_and_buffers
    (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
    (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ (event i).castSucc)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (eps : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (eps i) (order i))
    (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
    (hprecision0 : ∀ i, eps i ≤ δ 0)
    {k : ℕ} (hk : ∀ i, k ≤ order i)
    (N : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (δ 0) k)
    (hN : ∀ i, N i = ((O i).monoDelta (hprecision0 i) (hδ1 0)).lowerOrder (hk i))
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hfit0 : ∀ i, (δ 0)⁻¹ + 1 ≤ radius i)
    (htrace : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
      Nonempty (BackwardPointTrace (H i) (first i) (event i).castSucc (hle i) x.val))
    (hstart2 : ∀ i, (H i).time (first i) ≤ (H i).time (event i).succ - 2 / (O i).scale)
    (C : ℝ≥0) (q : ℝ)
    (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
    (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
      ∀ x : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q < ((H i).event j).incoming.flow.scalar t x →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * ((H i).event j).incoming.flow.scalar t x ^ 2)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ᶠ i in atTop,
      Nonempty (IncomingBackwardNeck (H (rho i)) (event (rho i)) (N (rho i))
        (Real.sqrt (N (rho i)).scale⁻¹)) := by
  classical
  have htail (n : ℕ) : ∃ m : ℕ, ∀ j, m ≤ j → eps j ≤ δ n ∧ (δ n)⁻¹ + 1 ≤ radius j := by
    have hp : ∀ᶠ j in atTop, eps j ≤ δ n :=
      (heps.eventually (Iio_mem_nhds (hδ n))).mono fun j hj => hj.le
    have hr : ∀ᶠ j in atTop, (δ n)⁻¹ + 1 ≤ radius j :=
      hradius.eventually (eventually_ge_atTop _)
    exact eventually_atTop.1 (hp.and hr)
  choose tail htail using htail
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 (fun m => tail (m+1))
  have hoffset : offset 0 = 0 := rfl
  have hprecision : ∀ n j, eps (j + offset n) ≤ δ n := by
    intro n j
    cases n with
    | zero => simpa [offset] using hprecision0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).1
  have hfit : ∀ n j, (δ n)⁻¹ + 1 ≤ radius (j + offset n) := by
    intro n j
    cases n with
    | zero => simpa [offset] using hfit0 j
    | succ n => exact (htail (n+1) (j + offset (n+1)) (by dsimp [offset]; omega)).2
  let K : ∀ n j, Set ((H (j + offset n)).event (event (j + offset n))).incoming.terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart '' {z | -(radius (j + offset n)) ≤ z.val.2 ∧ z.val.2 ≤ radius (j + offset n)}
  have hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
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
  exact exists_subsequence_selected_backward_neck_from_survivor_footprints
    H event first hle δ hδ hδ1 hδlim eps order O heps horder offset hoffset hprecision hk N hN
    K (fun n j => htrace (j + offset n)) hinside hstart2 C (fun _ => q) hqevent hscale
    hderivative hphi hpinching

theorem exists_subsequence_selected_backward_neck_of_growing_source_traces
    (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
    (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ (event i).castSucc)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (eps : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (eps i) (order i))
    (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
    (hprecision0 : ∀ i, eps i ≤ δ)
    {k : ℕ} (hk : ∀ i, k ≤ order i)
    (N : ∀ i, NormalizedNeck ((H i).event (event i)).terminal.metric (δ) k)
    (hN : ∀ i, N i = ((O i).monoDelta (hprecision0 i) (hδ1)).lowerOrder (hk i))
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hfit0 : ∀ i, (δ)⁻¹ + 1 ≤ radius i)
    (htrace : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
      Nonempty (BackwardPointTrace (H i) (first i) (event i).castSucc (hle i) x.val))
    (hstart2 : ∀ i, (H i).time (first i) ≤ (H i).time (event i).succ - 2 / (O i).scale)
    (C : ℝ≥0) (q : ℝ)
    (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
    (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
      ∀ x : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q < ((H i).event j).incoming.flow.scalar t x →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * ((H i).event j).incoming.flow.scalar t x ^ 2)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.castSucc ≤ (event i).castSucc →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ᶠ i in atTop,
      Nonempty (IncomingBackwardNeck (H (rho i)) (event (rho i)) (N (rho i))
        (Real.sqrt (N (rho i)).scale⁻¹)) := by
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
    | succ n =>
      dsimp [d]
      congr 1
      push_cast
      ring
  exact selected_backward_neck_of_growing_source_traces_and_buffers H event first hle d hd hd1
    hdlim eps order O heps horder hprecision0 hk N hN radius hradius hfit0 htrace
    hstart2 C q hscale hderivative hphi hpinching

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
