import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TerminalDefect_S85
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

set_option autoImplicit false

/-!
# CH12-S93 / G1a: Ricci naturality through the survivor chart of an event

`ricci_survivor_chart_S93` : the survivor chart `E : terminalRegularOpen ⇢ stage i.succ` of an event is an
isometry from the terminal metric to the output metric on its source; hence
`Ric_{output}(E z)(dE v, dE v) = Ric_{terminal}(z)(v, v)`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem ricci_survivor_chart_S93 (K : ObservedHistory.{u}) (i : Fin K.eventCount)
    (E : PartialDiffeomorph ThreeModel ThreeModel
      (K.event i).incoming.terminalRegularOpen (K.stage i.succ).Carrier ∞)
    (hiso : ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
      (K.event i).outputMetric.inner (E z)
        (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
        (K.event i).terminal.metric.inner z v w)
    (z : (K.event i).incoming.terminalRegularOpen) (hz : z ∈ E.source)
    (v : TangentSpace ThreeModel z) :
    ricciTensor (K.event i).outputMetric (E z)
        (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z v) =
      ricciTensor (K.event i).terminal.metric z v v := by
  classical
  let U : TopologicalSpace.Opens (K.event i).incoming.terminalRegularOpen := ⟨E.source, E.open_source⟩
  let x : U := ⟨z, hz⟩
  let Phi : U → (K.stage i.succ).Carrier := fun y => E y.1
  have hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi := fun y =>
    (isLocalDiffeomorph_subtype_val (I := ThreeModel) U y).comp ThreeModel (K.stage i.succ).Carrier
      (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ E y.2)
  have hmf : ∀ y : U, mfderiv ThreeModel ThreeModel Phi y =
      (mfderiv ThreeModel ThreeModel E y.1).comp
        (mfderiv ThreeModel ThreeModel (Subtype.val : U → _) y) := by
    intro y
    have h1 : ContMDiffAt ThreeModel ThreeModel ∞ E y.1 :=
      E.contMDiffOn.contMDiffAt (E.open_source.mem_nhds y.2)
    have h2 : ContMDiffAt ThreeModel ThreeModel ∞ (Subtype.val : U → _) y :=
      contMDiff_subtype_val.contMDiffAt
    exact mfderiv_comp y (h1.mdifferentiableAt (by simp)) (h2.mdifferentiableAt (by simp))
  have hval : ∀ (y : U) (a : TangentSpace ThreeModel y),
      mfderiv ThreeModel ThreeModel (Subtype.val : U → _) y a = a := fun y a =>
    mfderiv_subtype_val_apply (I := ThreeModel) U y a
  have hpull : localPullMetric (I := ThreeModel) (J := ThreeModel) (K.event i).outputMetric Phi hPhi =
      (K.event i).terminal.metric.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    rw [localPullMetric_inner, hmf, SmoothRiemannianMetric.restrictOpen_inner]
    simp only [ContinuousLinearMap.comp_apply, hval]
    exact hiso y.1 y.2 a b
  have h := ricciTensor_localPull (I := ThreeModel) (J := ThreeModel) (K.event i).outputMetric Phi hPhi x v v
  have h2 := ricciTensor_restrictOpen (I := ThreeModel) (K.event i).terminal.metric U x v v
  rw [hpull] at h
  have h3 : ricciTensor (K.event i).terminal.metric z v v =
      ricciTensor (K.event i).outputMetric (Phi x)
        (mfderiv ThreeModel ThreeModel Phi x v) (mfderiv ThreeModel ThreeModel Phi x v) := by
    refine Eq.trans ?_ (h2.symm.trans h)
    rw [hval x v]
  have e : ((mfderiv ThreeModel ThreeModel E x.1).comp
      (mfderiv ThreeModel ThreeModel (Subtype.val : U → _) x)) v =
      mfderiv ThreeModel ThreeModel E z v := by
    exact congrArg (mfderiv ThreeModel ThreeModel E z) (hval x v)
  rw [hmf, e] at h3
  exact h3.symm

theorem defectAllAt_of_stage_S93 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η r : ℝ} {j : Fin (K.eventCount + 1)}
    (hact : actS_S70 K r = j)
    (h : ∀ (hj : j0 ≤ j), ∀ x ∈ B, ∀ z : (K.stage j).Carrier, TrackedAt_S70 K hj J x z →
      ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K j z V η r) :
    DefectAllAt_S85 K j0 J B η r := by
  subst hact
  exact h

/-- Restricted metric: Ricci and inner product at a subtype point, as the unrestricted ones. -/
theorem ricci_restrict_S93 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [BoundarylessManifold ThreeModel M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : TopologicalSpace.Opens M) (x : U)
    (v : TangentSpace ThreeModel (x : M)) :
    ricciTensor (g.restrictOpen U) x v v = ricciTensor g (x : M) v v ∧
      (g.restrictOpen U).inner x v v = g.inner (x : M) v v := by
  refine ⟨?_, SmoothRiemannianMetric.restrictOpen_inner g U x v v⟩
  have h := ricciTensor_restrictOpen (I := ThreeModel) g U x v v
  refine h.trans ?_
  exact congrArg₂ (fun a b => ricciTensor g (x : M) a b)
    (mfderiv_subtype_val_apply (I := ThreeModel) U x v)
    (mfderiv_subtype_val_apply (I := ThreeModel) U x v)

/-- **Closed step at an event time** (survival and defect): `Weak η` on `[t, τ)` gives `Weak η` at the
event time `τ = time i.succ` on the new stage (left limit of the vector defect through the survivor chart). -/
theorem weak_closed_event_S93 (K : ObservedHistory.{u}) {i : Fin K.eventCount}
    {pr : CutoffParameters} (R : GeometricCutoffRecord K i pr) {Λ η t : ℝ} (hΛ : 1 ≤ Λ)
    (hKΛ : 2 * (9 * 189) < Λ ^ 2) (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hη : η ≤ 1) (ht0 : 0 < t)
    (hts : t < K.time i.succ)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ Real.sqrt (max t (K.time i.castSucc)))
    {j0 : Fin (K.eventCount + 1)} (hj0 : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (hJo : IsOpen (J '' B))
    (hJp : IsPreconnected (J '' B)) (hBne : B.Nonempty)
    (hW : ∀ r ∈ Ico t (K.time i.succ), WeakAt_S85 K j0 J B η r) :
    WeakAt_S85 K j0 J B η (K.time i.succ) := by
  obtain ⟨E, hE, hiso, hsurv⟩ :=
    weak_surv_event_S85 K R hΛ hKΛ hδ hη ht0 hts hnom hj0 J B hJo hJp hBne hW
  refine ⟨hsurv, ?_⟩
  set a' := max t (K.time i.castSucc) with ha'
  have hlt : K.time i.castSucc < K.time i.succ := K.time_strictMono i.castSucc_lt_succ
  have ha'lt : a' < K.time i.succ := max_lt hts hlt
  have hta : t ≤ a' := le_max_left _ _
  have hact : ∀ r ∈ Ico a' (K.time i.succ), actS_S70 K r = i.castSucc := fun r hr =>
    actS_eq_castSucc_S85 K i ⟨(le_max_right _ _).trans hr.1, hr.2⟩
  have hsurvPre : ∀ x ∈ B, ∃ z : (K.stage i.castSucc).Carrier, TrackedAt_S70 K hj0 J x z :=
    survAt_stage_S85 K j0 J B (hact a' ⟨le_rfl, ha'lt⟩) hj0 (hW a' ⟨hta, ha'lt⟩).1
  refine defectAllAt_of_stage_S93 K j0 J B (actS_time_stage_S85 K i.succ) (fun hj x hx z' hz' V => ?_)
  obtain ⟨z, hz⟩ := hsurvPre x hx
  obtain ⟨h, hmem, hz2⟩ := hE x hx z hz
  have hzz : z' = E ⟨z, h⟩ := tracked_unique_S70 K hj J x hz' hz2
  subst hzz
  have hmet : K.stageMetric i.succ (K.time i.succ) = (K.event i).outputMetric :=
    (K.stageMetric_initial i.succ).trans (K.event_output i).symm
  obtain ⟨w, hw⟩ := ((PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ E hmem
    ).mfderivToContinuousLinearEquiv (by simp)).surjective V
  have hd : mfderiv ThreeModel ThreeModel E ⟨z, h⟩ w = V := hw
  have hdefR : ∀ t' ∈ Ico a' (K.time i.succ),
      |2 * t' * ricciTensor (((K.event i).incoming.flow.base.metric t').restrictOpen
          (K.event i).incoming.terminalRegularOpen) ⟨z, h⟩ w w +
          (((K.event i).incoming.flow.base.metric t').restrictOpen
            (K.event i).incoming.terminalRegularOpen).inner ⟨z, h⟩ w w| ≤
        η * (((K.event i).incoming.flow.base.metric t').restrictOpen
          (K.event i).incoming.terminalRegularOpen).inner ⟨z, h⟩ w w := by
    intro t' ht'
    have hd' := defectAllAt_transport_S85 K j0 J B (hact t' ht')
      (hW t' ⟨hta.trans ht'.1, ht'.2⟩).2 hj0 x hx z hz w
    have hd'' : |2 * t' * ricciTensor ((K.event i).incoming.flow.base.metric t') z w w +
        ((K.event i).incoming.flow.base.metric t').inner z w w| ≤
        η * ((K.event i).incoming.flow.base.metric t').inner z w w := by
      simpa only [DefectAt_S85, ObservedHistory.stageMetric_castSucc_apply] using hd'
    obtain ⟨e1, e2⟩ := ricci_restrict_S93 ((K.event i).incoming.flow.base.metric t')
      (K.event i).incoming.terminalRegularOpen ⟨z, h⟩ w
    rw [e1, e2]
    exact hd''
  have hdefT := terminal_defect_of_flow_defect_S85 (K.event i).incoming (K.event i).terminal.metric
    (K.event i).terminal.converges ⟨z, h⟩ w ha'lt hdefR
  have hRic := ricci_survivor_chart_S93 K i E hiso ⟨z, h⟩ hmem w
  have hInn := hiso ⟨z, h⟩ hmem w w
  unfold DefectAt_S85
  rw [hmet, ← hd]
  rw [hRic, hInn]
  exact hdefT

end GC.LongTime.Ch12
