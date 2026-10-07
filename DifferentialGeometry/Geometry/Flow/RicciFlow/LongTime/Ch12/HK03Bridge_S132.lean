import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Vector_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RegularInterchange_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyThickCores_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HregS117
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrCast_S103
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakBootstrap_S93
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.FixedRadiusDisj_O44

set_option autoImplicit false

/-!
# CH12-S132 / G3a: the `hK03` input of `hreg_S117` from the late LTF03 threshold, and the `J`, `B` facts

* `mem_eventTimes_history_iff_S132`, `seed_transport_S132`: plumbing between a regular slice of
  `F.observation` at time `u ≤ n` and the active stage of the history `n`.
* `hK03_bridge_S132` : the `hK` binder of `hreg_S117` (all `n`, all regular `s' ≥ T'`) from
  `ltf03_vector_threshold_S45` (RegularSlice at `s'`, `postStage_regularSlice`, `postMetric_regularSlice`,
  `postMetric_heq_stageMetric_S65`).
* `jb_facts_S132`: `J = cast ∘ f` is smooth / injective / has open preconnected image on `B = ball (2R)`.
* `exists_v_S132`: the volume constant `v` of `hreg_S117`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.LongTime GC.LongTime.CuspP1
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

section Regular

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem mem_eventTimes_history_iff_S132 {T : ObservationTower P g} (n : ℕ) {u : ℝ} (hu0 : 0 < u)
    (hun : u ≤ (n : ℝ)) : u ∈ T.eventTimes ↔ u ∈ (T.history n).eventTimes := by
  have h1 := T.eventTimes_inter u hu0.le
  have h2 := (T.observe_eq_atIndex n u hu0.le hun).eventTimes_eq
  rw [T.atIndex_eventTimes] at h2
  have hm : u ∈ Ioc (0 : ℝ) u := ⟨hu0, le_rfl⟩
  constructor
  · intro h
    have h3 : u ∈ T.eventTimes ∩ Ioc 0 u := ⟨h, hm⟩
    rw [h1, h2] at h3
    exact h3.1
  · intro h
    have h3 : u ∈ (T.history n).eventTimes ∩ Ioc 0 u := ⟨h, hm⟩
    rw [← h2, ← h1] at h3
    exact h3.1

/-- The `hK`-shape statement transports along an equality of stages with `HEq` metrics. -/
theorem seed_transport_S132 {A B : OrientedThreeStage.{u}} (h : A = B) (gA : A.Metric) (gB : B.Metric)
    (hg : HEq gA gB) {c : ℝ} (hc : 0 < c) (a v L ε : ℝ)
    (HA : ∀ p : A.Carrier,
      (∀ q ∈ riemannianBallOf (scaleMetric c⁻¹ (inv_pos.mpr hc) gA) p a,
        SectionalBoundedBelowAt (scaleMetric c⁻¹ (inv_pos.mpr hc) gA) q (-(a ^ 2)⁻¹)) →
      ENNReal.ofReal (v * a ^ 3) ≤ ballVolume (scaleMetric c⁻¹ (inv_pos.mpr hc) gA) p a →
      ∀ q ∈ riemannianBallOf (scaleMetric c⁻¹ (inv_pos.mpr hc) gA) p L, ∀ V : TangentSpace ThreeModel q,
        |2 * c * ricciTensor gA q V V + gA.inner q V V| ≤ ε * gA.inner q V V) :
    ∀ p : B.Carrier,
      (∀ q ∈ riemannianBallOf (scaleMetric c⁻¹ (inv_pos.mpr hc) gB) p a,
        SectionalBoundedBelowAt (scaleMetric c⁻¹ (inv_pos.mpr hc) gB) q (-(a ^ 2)⁻¹)) →
      ENNReal.ofReal (v * a ^ 3) ≤ ballVolume (scaleMetric c⁻¹ (inv_pos.mpr hc) gB) p a →
      ∀ q ∈ riemannianBallOf (scaleMetric c⁻¹ (inv_pos.mpr hc) gB) p L, ∀ V : TangentSpace ThreeModel q,
        |2 * c * ricciTensor gB q V V + gB.inner q V V| ≤ ε * gB.inner q V V := by
  subst h
  have h' := eq_of_heq hg
  subst h'
  exact HA

variable {F : GC.Interface.RawSurgery P g}

/-- The `hK` binder of `hreg_S117` (all histories `n`, all regular times `s' ≥ T'`), from the late
LTF03 vector-defect threshold on regular slices. -/
theorem hK03_bridge_S132 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L)
    (a v L ε : ℝ) (ha : 0 < a) (hv : 0 < v) (hL : 0 < L) (hε : 0 < ε) :
    ∃ T' : ℝ, ∀ n : ℕ, ∀ s' : ℝ, T' ≤ s' → ∀ hs' : 0 < s', s' ≤ (F.tower.history n).toHistory.horizon →
      (F.tower.history n).toHistory.time (actS_S70 (F.tower.history n).toHistory s') < s' →
      ∀ p' : ((F.tower.history n).toHistory.stage
          (actS_S70 (F.tower.history n).toHistory s')).Carrier,
        (∀ q ∈ riemannianBallOf
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') ((F.tower.history n).toHistory.stageMetric
              (actS_S70 (F.tower.history n).toHistory s') s')) p' a,
          SectionalBoundedBelowAt
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') ((F.tower.history n).toHistory.stageMetric
              (actS_S70 (F.tower.history n).toHistory s') s')) q (-(a ^ 2)⁻¹)) →
        ENNReal.ofReal (v * a ^ 3) ≤
          ballVolume (scaleMetric s'⁻¹ (inv_pos.mpr hs') ((F.tower.history n).toHistory.stageMetric
            (actS_S70 (F.tower.history n).toHistory s') s')) p' a →
        ∀ q ∈ riemannianBallOf
            (scaleMetric s'⁻¹ (inv_pos.mpr hs') ((F.tower.history n).toHistory.stageMetric
              (actS_S70 (F.tower.history n).toHistory s') s')) p' L,
          ∀ V : TangentSpace ThreeModel q,
            |2 * s' * ricciTensor ((F.tower.history n).toHistory.stageMetric
                (actS_S70 (F.tower.history n).toHistory s') s') q V V +
                ((F.tower.history n).toHistory.stageMetric
                  (actS_S70 (F.tower.history n).toHistory s') s').inner q V V| ≤
              ε * ((F.tower.history n).toHistory.stageMetric
                (actS_S70 (F.tower.history n).toHistory s') s').inner q V V := by
  obtain ⟨T', hT'⟩ := ltf03_vector_threshold_S45 Hp hdec hneg hLTF03 a v L ε ha hv hL hε
  refine ⟨T', fun n s' hT hs' hsh hreg => ?_⟩
  have hsn : s' ≤ (n : ℝ) := hsh.trans (F.observation.horizon_eq n).le
  let τ : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon := ⟨s', hs'.le, hsh⟩
  have hact : actS_S70 (F.tower.history n).toHistory s' = (F.tower.history n).toHistory.activeStage τ :=
    actS_eq_activeStage_S93 (F.tower.history n).toHistory τ
  have hnot : s' ∉ F.observation.eventTimes := by
    rw [mem_eventTimes_history_iff_S132 (T := F.observation) n hs' hsn]
    refine (regular_iff_not_mem_eventTimes_S74 (H := (F.tower.history n).toHistory) (t := τ) hs').mp ?_
    rw [← hact]
    exact hreg
  obtain ⟨s, rfl⟩ := regularSlice_exists_of_not_eventTime_S37 F.observation s' hs' hnot
  have hA : s.stage = (F.tower.history n).toHistory.stage
      (actS_S70 (F.tower.history n).toHistory s.time) :=
    (postStage_regularSlice F.observation s).symm.trans
      ((postStage_eq_stage_active_CPD2 F.observation n τ).trans (congrArg _ hact.symm))
  have hg : HEq s.metric ((F.tower.history n).toHistory.stageMetric
      (actS_S70 (F.tower.history n).toHistory s.time) s.time) :=
    (postMetric_regularSlice F.observation s).symm.trans
      ((postMetric_heq_stageMetric_S65 F.observation n τ).trans (by rw [hact]; exact HEq.rfl))
  intro p' h1 h2 q hq V
  exact seed_transport_S132 hA s.metric _ hg s.positive a v L ε
    (fun p hp1 hp2 q hq V => hT' s hT p ⟨hp1, hp2⟩ q hq V) p' h1 h2 q hq V

end Regular

section JB

theorem jb_facts_S132 (H : FiniteVolumeHyperbolicModel.{u}) {A B : OrientedThreeStage.{u}} (hP : A = B)
    (f : H.Carrier → A.Carrier) (U : TopologicalSpace.Opens H.Carrier) {R : ℝ} (hR : 0 < R)
    (hU : riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => cast (congrArg OrientedThreeStage.Carrier hP) (f p))
        (riemannianBallOf H.metric H.basepoint (2 * R)) ∧
      Set.InjOn (fun p => cast (congrArg OrientedThreeStage.Carrier hP) (f p))
        (riemannianBallOf H.metric H.basepoint (2 * R)) ∧
      IsOpen ((fun p => cast (congrArg OrientedThreeStage.Carrier hP) (f p)) ''
        riemannianBallOf H.metric H.basepoint (2 * R)) ∧
      IsPreconnected ((fun p => cast (congrArg OrientedThreeStage.Carrier hP) (f p)) ''
        riemannianBallOf H.metric H.basepoint (2 * R)) ∧
      (riemannianBallOf H.metric H.basepoint (2 * R)).Nonempty := by
  subst hP
  have hpos : 0 < 2 * R := mul_pos two_pos hR
  have hconn : IsPreconnected (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    (isPathConnected_riemannianBallOf H.metric H.basepoint hpos).isConnected.isPreconnected
  refine ⟨hf.mono hU, ?_, isOpen_image_slice_O44 U f hemb (isOpen_riemannianBallOf_S61 H _) hU,
    hconn.image f (hf.continuousOn.mono hU), ?_⟩
  · intro x hx y hy hxy
    have := hemb.isEmbedding.injective
      (show (fun x : U => f x) ⟨x, hU hx⟩ = (fun x : U => f x) ⟨y, hU hy⟩ from hxy)
    exact congrArg Subtype.val this
  · refine ⟨H.basepoint, ?_⟩
    change riemannianEDistOf H.metric H.basepoint H.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hpos

theorem exists_v_S132 (H : FiniteVolumeHyperbolicModel.{u}) {a : ℝ} (ha : 0 < a) :
    ∃ v : ℝ, 0 < v ∧ ENNReal.ofReal (v * a ^ 3) ≤
      ENNReal.ofReal (1 / 8) * ballVolume H.metric H.basepoint (a / 2) := by
  have hpos : 0 < ballVolume H.metric H.basepoint (a / 2) := ballVolume_pos_of_pos _ _ (half_pos ha)
  have hfin : ballVolume H.metric H.basepoint (a / 2) ≠ ⊤ :=
    ((MeasureTheory.measure_mono (subset_univ _)).trans_lt H.finite_volume).ne
  set V := (ballVolume H.metric H.basepoint (a / 2)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos hpos.ne' hfin
  have ha3 : 0 < a ^ 3 := by positivity
  refine ⟨V / (8 * a ^ 3), by positivity, ?_⟩
  have h1 : V / (8 * a ^ 3) * a ^ 3 = 1 / 8 * V := by field_simp
  rw [h1, ENNReal.ofReal_mul (by norm_num), hV, ENNReal.ofReal_toReal hfin]

end JB

end GC.LongTime.Ch12
