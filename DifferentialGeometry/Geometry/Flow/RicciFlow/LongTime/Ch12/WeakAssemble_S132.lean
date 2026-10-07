import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HK03Bridge_S132
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.IcoDatum_S132
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HopenOpen_S103
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HeqStart_S93

set_option autoImplicit false

/-!
# CH12-S132 / G3b (F-level): the weak bootstrap on `[t, 2t]` for the `postStage` data of hWA, and the
`Ico` datum (hWA v3 clauses with `2t < b`, plus the scalar clause for the `Ioo` bridge)

`hico_S132`: constants `η := min (min η₀ (1/2)) (ε₁/10)`, `δ' := min (1/2) (η/5764)`, `a₀ := min (R/8) (1/14)`,
`v` (volume of `B(o, a₀/2)`); `h0` from `h0_defect_of_post_S103`, `hopen` from `hopen_S103`, `hev` from `hevS_S117`
at `2η`, `himprove` from `himprove_of_regular_S107` + `hreg_S117` + `hK03_bridge_S132`; then
`weak_bootstrap_S93` and `ico_datum_S132` at `K := (F.tower.history ⌈2t⌉₊+1).toHistory`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.LongTime GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hico_S132 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L)
    (H : FiniteVolumeHyperbolicModel.{u}) (R ε η₀ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hη₀ : 0 < η₀) :
    ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
      (U : TopologicalSpace.Opens H.Carrier)
      (f : H.Carrier → (postStage F.observation t).Carrier),
      riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
      (∀ j : ℕ, j ≤ 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δ') →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
        (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : 2 * t < b)
        (_ : b ≤ (F.tower.history n).horizon)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
          first ≤ (F.tower.history n).toHistory.activeStage r ∧
            (F.tower.history n).toHistory.activeStage r ≤ last)
        (φ : H.Carrier →
          (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (2 * R)) ∧
        (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
          (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
              (φ p)) (f p)) ∧
        (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
          (r : ℝ) ∈ Icc t (2 * t) →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
              ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
              (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ q)) 0 p < ε) ∧
        (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
          (r : ℝ) ∈ Icc t (2 * t) →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            ∀ V : TangentSpace ThreeModel
                ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)),
              |2 * (r : ℝ) * ricciTensor ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r)
                  ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) V V +
                ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r).inner
                  ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) V V| ≤
                η₀ * ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r).inner
                  ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) V V) ∧
        ((F.tower.history n).toHistory.time first = t →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            metricScalarAt ((F.tower.history n).toHistory.initialMetric first)
              ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered first le_rfl
                ordered (φ p)) ≤ 0) := by
  -- constants
  have hε₁ : 0 < min ε 1 := lt_min hε one_pos
  have hε₁1 : min ε 1 ≤ 1 := min_le_right _ _
  have hε₁ε : min ε 1 ≤ ε := min_le_left _ _
  have hη : 0 < min (min η₀ (1 / 2)) (min ε 1 / 10) :=
    lt_min (lt_min hη₀ (by norm_num)) (by positivity)
  have hηη₀ : min (min η₀ (1 / 2)) (min ε 1 / 10) ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hη12 : min (min η₀ (1 / 2)) (min ε 1 / 10) ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηε : min (min η₀ (1 / 2)) (min ε 1 / 10) ≤ min ε 1 / 10 := min_le_right _ _
  generalize min (min η₀ (1 / 2)) (min ε 1 / 10) = η at hη hηη₀ hη12 hηε
  generalize min ε 1 = ε₁ at hε₁ hε₁1 hε₁ε hηε
  have hδp : 0 < min (1 / 2 : ℝ) (η / 5764) := lt_min (by norm_num) (by positivity)
  have hδh : min (1 / 2 : ℝ) (η / 5764) ≤ 1 / 2 := min_le_left _ _
  have hδη : min (1 / 2 : ℝ) (η / 5764) ≤ η / 5764 := min_le_right _ _
  generalize min (1 / 2 : ℝ) (η / 5764) = δ' at hδp hδh hδη
  have ha₀ : 0 < min (R / 8) (1 / 14 : ℝ) := lt_min (by positivity) (by norm_num)
  have ha₀R : min (R / 8) (1 / 14 : ℝ) ≤ R / 8 := min_le_left _ _
  have ha₀14 : min (R / 8) (1 / 14 : ℝ) ≤ 1 / 14 := min_le_right _ _
  generalize min (R / 8) (1 / 14 : ℝ) = a₀ at ha₀ ha₀R ha₀14
  have ha₀1 : 189 * a₀ ^ 2 ≤ 1 := by nlinarith
  obtain ⟨v, hv0, hv⟩ := exists_v_S132 H ha₀
  obtain ⟨T₁, hT₁, hevS⟩ := hevS_S117 Hp hdec
  obtain ⟨T', hK⟩ := hK03_bridge_S132 Hp hdec hneg hLTF03 a₀ v (4 * R) (η / 2) ha₀ hv0
    (by positivity) (by positivity)
  refine ⟨δ', max (max T₁ T') 1, hδp, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro t ht0 htT U f hU hf hemb hck
  have hT₁t : T₁ ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans htT
  have hT't : T' ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans htT
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * t < (n : ℝ) := ⟨⌈2 * t⌉₊ + 1, by
    have := Nat.le_ceil (2 * t); push_cast; linarith⟩
  refine ⟨n, ?_⟩
  have hhor : (F.tower.history n).toHistory.horizon = (n : ℝ) := F.observation.horizon_eq n
  set K := (F.tower.history n).toHistory with hKdef
  have h2t : 2 * t < K.horizon := by rw [hhor]; exact hn
  have h2t' : 2 * t ≤ K.horizon := h2t.le
  let τ0 : Icc (0 : ℝ) K.horizon := ⟨t, ht0.le, by rw [hhor]; linarith⟩
  set j0 := K.activeStage τ0 with hj0def
  have hact : actS_S70 K t = j0 := actS_eq_activeStage_S93 K τ0
  have hP : postStage F.observation t = K.stage j0 := postStage_eq_stage_active_CPD2 F.observation n τ0
  have hm : HEq (postMetric F.observation t) (K.stageMetric j0 t) :=
    postMetric_heq_stageMetric_S65 F.observation n τ0
  obtain ⟨hJ, hJinj, hJo, hJp, hBne⟩ := jb_facts_S132 H hP f U hR hU hf hemb
  set J : H.Carrier → (K.stage j0).Carrier :=
    fun p => cast (congrArg OrientedThreeStage.Carrier hP) (f p) with hJdef
  have hck0 : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < δ' := by
    intro p hp
    have e := ckErr_S45_cast_stage_S103 H hP (postMetric F.observation t) (K.stageMetric j0 t) hm t⁻¹ f 0 p
    rw [e]
    exact hck 0 (by norm_num) p hp
  have h0 : WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) (η / 2) t :=
    ⟨survAt_start_S93 K j0 J _ hact,
      h0_defect_of_post_S103 F.observation H K j0 ht0 hact hP hm f U hf hemb _ hU (η := η / 2) (by linarith)
        (by linarith) hck⟩
  have hj0t : j0 ≤ actS_S70 K t := hact.symm.le
  have hopen := hopen_S103 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) hη ht0 h2t'
  have hevS' := fun (i : Fin K.eventCount) (hi : j0 ≤ i.castSucc) (t'' : ℝ) (h1 : t < t'')
    (h2 : t'' < K.time i.succ) (h3 : K.time i.succ ≤ 2 * t)
    (h4 : ∀ r ∈ Ico t'' (K.time i.succ),
      WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) (η / 2) r) =>
    hevS n j0 J _ hJo hJp hBne (η := η) (t := t) (by linarith) hT₁t i hi t'' h1 h2 h3 h4
  have hev : ∀ i : Fin K.eventCount, t < K.time i.succ → K.time i.succ ≤ 2 * t → j0 ≤ i.castSucc →
      (∀ r ∈ Ico t (K.time i.succ),
        WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) η r) →
      WeakAt_S85 K j0 J (riemannianBallOf H.metric H.basepoint (2 * R)) η (K.time i.succ) := by
    intro i h1 h2 hi hW
    have e : 2 * η / 2 = η := by ring
    have := hevS n j0 J _ hJo hJp hBne (η := 2 * η) (t := t) (by linarith) hT₁t i hi
      ((t + K.time i.succ) / 2) (by linarith) (by linarith) h2 (fun r hr => by
        rw [e]; exact hW r ⟨by linarith [hr.1], hr.2⟩)
    rw [e] at this
    exact this
  have hreg := hreg_S117 H K j0 J (R := R) (η := η) (t := t) (a₀ := a₀) (v := v) (T' := T') hR
    (by linarith) ht0 h2t' hact ha₀ ha₀R ha₀1 hv hJ hJinj
    (fun p hp => lt_of_lt_of_le (hck0 p hp) (by linarith)) hT't (hK n)
  have himprove := himprove_of_regular_S107 K j0 J _ ht0 h2t' hj0t h0 hreg hevS'
  have hboot := weak_bootstrap_S93 K j0 J _ hη.le ht0 h2t' hj0t h0 hev hopen himprove
  obtain ⟨last, ordered, a, b, hat, htb, hb, stages, φ, hφ, hφJ, hCK, hDEF, hNEG⟩ :=
    ico_datum_S132 (R := R) (η₀ := η₀) (ε := ε) (δ' := δ') H K j0 J ht0 h2t hact hη.le (by linarith) (by linarith) hε₁ hε₁1 hε₁ε
      (by linarith) hδp.le (by linarith) hBne hJ hck0 hboot
  refine ⟨j0, last, ordered, a, b, hat, htb, hb, stages, φ, hφ, ?_, hCK, hDEF, hNEG⟩
  intro r hr hrt p hp
  have hr' : r = τ0 := Subtype.ext hrt
  subst hr'
  exact heq_start_S93 n τ0 f last ordered φ p (hφJ p hp) (stages τ0 hr).1 (stages τ0 hr).2

end GC.LongTime.Ch12
