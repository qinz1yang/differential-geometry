import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SharpEvent_S117
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageGlue_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNegDefect_S56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakBootstrap_S93
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61

set_option autoImplicit false

/-!
# CH12-S132 / G3b (K-level): the `Ico` lift datum on `[t, 2t]` from `Weak (η/2)` on the whole window

`ico_datum_S132` : given `WeakAt_S85 K j0 J B (η/2) s` for every `s ∈ [t, 2t]` (`B = ball (2R)`, `J` smooth,
`ckErr_0 < δ'` at `t`) there is ONE lift datum `(last, a ≤ t, 2t < b, stages, φ)` of `J` with
the ckErr clause (`< ε`), the vector-defect clause (`≤ η₀`) for every `r ∈ [t, 2t]`, and the scalar clause at
`t` (the `hneg` input of `hlift_Ioo_core_S89`).  The per-`r` clauses are proved for an arbitrary index `j` with
`actS_S70 K r = j` (so that `subst` removes the `clamp`), then specialised to `K.activeStage r`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- ckErr (`< ε`) and defect (`≤ η₀`) at one time `r ∈ [t, 2t]` for the restriction of the `2t`-lift `φ`
to the stage `j` with `actS_S70 K r = j`. -/
theorem ck_def_at_S132 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier)
    {R t η η₀ ε₁ δ' ε : ℝ} (ht0 : 0 < t) (hj0 : actS_S70 K t = j0) (hη0 : 0 ≤ η)
    (hηη₀ : η / 2 ≤ η₀) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₁ε : ε₁ ≤ ε) (hη : 10 * (η / 2) ≤ ε₁)
    (hδ0 : 0 ≤ δ') (hδ : 10 * δ' ≤ ε₁)
    (hBne : (riemannianBallOf H.metric H.basepoint (2 * R)).Nonempty)
    (hJ : ContMDiffOn (𝓡 3) ThreeModel ∞ J (riemannianBallOf H.metric H.basepoint (2 * R)))
    (hck : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < δ')
    (hboot : ∀ s ∈ Icc t (2 * t),
      WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) (η / 2) s)
    {last : Fin (K.eventCount + 1)} (ordered : j0 ≤ last)
    (φ : H.Carrier → K.backwardSurvivorDomain j0 last ordered)
    (hφJ : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      K.backwardSurvivorMap j0 last ordered j0 le_rfl ordered (φ p) = J p)
    {r : ℝ} (hrI : r ∈ Icc t (2 * t)) (hrh : r ≤ K.horizon) {j : Fin (K.eventCount + 1)}
    (hj : actS_S70 K r = j) (hj1 : j0 ≤ j) (hj2 : j ≤ last) :
    (∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (K.stageMetric j r) r⁻¹
        (fun q => K.backwardSurvivorMap j0 last ordered j hj1 hj2 (φ q)) 0 p < ε) ∧
    (∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ∀ V : TangentSpace ThreeModel (K.backwardSurvivorMap j0 last ordered j hj1 hj2 (φ p)),
        |2 * r * ricciTensor (K.stageMetric j r)
            (K.backwardSurvivorMap j0 last ordered j hj1 hj2 (φ p)) V V +
          (K.stageMetric j r).inner (K.backwardSurvivorMap j0 last ordered j hj1 hj2 (φ p)) V V| ≤
          η₀ * (K.stageMetric j r).inner (K.backwardSurvivorMap j0 last ordered j hj1 hj2 (φ p)) V V) := by
  subst hj
  have hBopen : IsOpen (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    isOpen_riemannianBallOf_S61 H _
  have hWr := hboot r hrI
  obtain ⟨hle, φr, hφr, hφrall⟩ := exists_lift_of_surv_S93 H K j0 J
    ⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ hJ hBne hWr.1
  have hcmp := metric_compare_sharp_S117 H K j0 J ht0 hrI.1 hrI.2 hrh (by linarith) hδ0 hε₁ hε₁1 hη hδ
    hj0 (last := actS_S70 K r) rfl hle hBopen
    (fun r' hr' => (hboot r' ⟨hr'.1, hr'.2.trans hrI.2⟩).2) φr hφr (fun p hp => (hφrall p hp).1) hck
  have hfe : ∀ q ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      K.backwardSurvivorMap j0 last ordered (actS_S70 K r) hj1 hj2 (φ q) = (φr q).val := by
    intro q hq
    exact tracked_unique_S70 K hj1 J q (tracked_restrict_S70 K ordered hj1 hj2 J q (φ q) (hφJ q hq))
      (hφrall q hq).2
  refine ⟨fun p hp => ?_, fun p hp V => ?_⟩
  · rw [ckErr_congr_open_S110 H (K.stageMetric (actS_S70 K r) r)
      (fun q => K.backwardSurvivorMap j0 last ordered (actS_S70 K r) hj1 hj2 (φ q))
      (fun q => (φr q).val) ⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ hfe r⁻¹ 0 p hp]
    exact lt_of_lt_of_le (hcmp p hp) hε₁ε
  · exact defectAt_mono_S85 K _ _ V r hηη₀
      (defect_clause_of_weak_S93 K j0 J _ hWr last ordered hj1 hj2 φ p hp (hφJ p hp) V)

theorem ico_datum_S132 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier)
    {R t η η₀ ε₁ δ' ε : ℝ} (ht0 : 0 < t) (h2t : 2 * t < K.horizon) (hj0 : actS_S70 K t = j0)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hηη₀ : η / 2 ≤ η₀) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₁ε : ε₁ ≤ ε)
    (hη : 10 * (η / 2) ≤ ε₁) (hδ0 : 0 ≤ δ') (hδ : 10 * δ' ≤ ε₁)
    (hBne : (riemannianBallOf H.metric H.basepoint (2 * R)).Nonempty)
    (hJ : ContMDiffOn (𝓡 3) ThreeModel ∞ J (riemannianBallOf H.metric H.basepoint (2 * R)))
    (hck : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < δ')
    (hboot : ∀ s ∈ Icc t (2 * t),
      WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) (η / 2) s) :
    ∃ (last : Fin (K.eventCount + 1)) (ordered : j0 ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : 2 * t < b)
      (_ : b ≤ K.horizon)
      (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
        j0 ≤ K.activeStage r ∧ K.activeStage r ≤ last)
      (φ : H.Carrier → K.backwardSurvivorDomain j0 last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (2 * R)) ∧
      (∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
        K.backwardSurvivorMap j0 last ordered j0 le_rfl ordered (φ p) = J p) ∧
      (∀ (r : Icc (0 : ℝ) K.horizon) (hr : (r : ℝ) ∈ Ico a b), (r : ℝ) ∈ Icc t (2 * t) →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (K.stageMetric (K.activeStage r) r) r⁻¹
            (fun q => K.backwardSurvivorMap j0 last ordered (K.activeStage r) (stages r hr).1
              (stages r hr).2 (φ q)) 0 p < ε) ∧
      (∀ (r : Icc (0 : ℝ) K.horizon) (hr : (r : ℝ) ∈ Ico a b), (r : ℝ) ∈ Icc t (2 * t) →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ∀ V : TangentSpace ThreeModel (K.backwardSurvivorMap j0 last ordered (K.activeStage r)
              (stages r hr).1 (stages r hr).2 (φ p)),
            |2 * (r : ℝ) * ricciTensor (K.stageMetric (K.activeStage r) r)
                (K.backwardSurvivorMap j0 last ordered (K.activeStage r) (stages r hr).1
                  (stages r hr).2 (φ p)) V V +
              (K.stageMetric (K.activeStage r) r).inner (K.backwardSurvivorMap j0 last ordered
                (K.activeStage r) (stages r hr).1 (stages r hr).2 (φ p)) V V| ≤
              η₀ * (K.stageMetric (K.activeStage r) r).inner (K.backwardSurvivorMap j0 last ordered
                (K.activeStage r) (stages r hr).1 (stages r hr).2 (φ p)) V V) ∧
      (K.time j0 = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
        metricScalarAt (K.initialMetric j0)
          (K.backwardSurvivorMap j0 last ordered j0 le_rfl ordered (φ p)) ≤ 0) := by
  have hBopen : IsOpen (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    isOpen_riemannianBallOf_S61 H _
  have h2 : (2 * t) ∈ Icc t (2 * t) := ⟨by linarith, le_rfl⟩
  obtain ⟨hlast, φ, hφ, hφall⟩ := exists_lift_of_surv_S93 H K j0 J
    ⟨riemannianBallOf H.metric H.basepoint (2 * R), hBopen⟩ hJ hBne (hboot (2 * t) h2).1
  obtain ⟨a, b, hat, htb, hb, hwin⟩ := window_stages_S93 K ht0 h2t
  have hφJ : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      K.backwardSurvivorMap j0 (actS_S70 K (2 * t)) hlast j0 le_rfl hlast (φ p) = J p :=
    fun p hp => (hφall p hp).1
  have hstg : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      j0 ≤ K.activeStage r ∧ K.activeStage r ≤ actS_S70 K (2 * t) := by
    intro r hr
    have := hwin r r.2 hr
    rw [actS_eq_activeStage_S93 K r, hj0] at this
    exact this
  refine ⟨actS_S70 K (2 * t), hlast, a, b, hat, htb, hb, hstg, φ, hφ, hφJ, ?_, ?_, ?_⟩
  · intro r hr hrI p hp
    exact (ck_def_at_S132 H K j0 J ht0 hj0 hη0 hηη₀ hε₁ hε₁1 hε₁ε hη hδ0 hδ hBne hJ hck hboot hlast φ
      hφJ hrI r.2.2 (actS_eq_activeStage_S93 K r) (hstg r hr).1 (hstg r hr).2).1 p hp
  · intro r hr hrI p hp V
    exact (ck_def_at_S132 (ε := ε) H K j0 J ht0 hj0 hη0 hηη₀ hε₁ hε₁1 hε₁ε hη hδ0 hδ hBne hJ hck hboot hlast
      φ hφJ hrI r.2.2 (actS_eq_activeStage_S93 K r) (hstg r hr).1 (hstg r hr).2).2 p hp V
  · intro htime p hp
    rw [hφJ p hp]
    have hini := K.stageMetric_initial j0
    rw [htime] at hini
    rw [← hini]
    refine scalar_nonpos_of_quad_defect_S56 (η := η / 2) (K.stageMetric j0 t) (J p) ht0 (by linarith) ?_
    subst hj0
    have hself : TrackedAt_S70 K (le_refl (actS_S70 K t)) J p (J p) :=
      ⟨⟨J p, K.mem_backwardSurvivorDomain_self _ (J p)⟩, rfl,
        K.backwardSurvivorMap_last _ _ le_rfl ⟨J p, K.mem_backwardSurvivorDomain_self _ (J p)⟩⟩
    intro V
    exact (hboot t ⟨le_rfl, by linarith⟩).2 le_rfl p hp (J p) hself V

end GC.LongTime.Ch12
