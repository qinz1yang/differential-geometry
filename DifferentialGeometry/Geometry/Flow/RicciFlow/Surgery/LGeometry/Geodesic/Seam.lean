import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.MinimizerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Naturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve (chartCurve)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
  (chartRepAt chartRepAtBase covDerivAlong)

section Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuousAt_chartPhase {γ : ℝ → M} {w : ℝ}
    (hγ : ContinuousAt (fun r => (TotalSpace.mk' E (γ r) (lVelocity (I := I) γ r) :
      TangentBundle I M)) w) :
    ContinuousAt γ w ∧ ContinuousAt (fun r => (chartCurve (I := I) (γ w) γ r,
      chartRepAtBase (I := I) (γ w) γ (fun u => lVelocity (I := I) γ u) r)) w := by
  rw [FiberBundle.continuousAt_totalSpace] at hγ
  obtain ⟨h1, h2⟩ := hγ
  have hγc : ContinuousAt γ w := h1
  have hsrc : ∀ᶠ r in 𝓝 w, γ r ∈ (chartAt H (γ w)).source :=
    hγc.preimage_mem_nhds ((chartAt H (γ w)).open_source.mem_nhds (mem_chart_source H (γ w)))
  refine ⟨hγc, ((continuousAt_extChartAt (I := I) (γ w)).comp hγc).prodMk (h2.congr ?_)⟩
  filter_upwards [hsrc] with r hr
  have hb : γ r ∈ (trivializationAt E (TangentSpace I) (γ w)).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  exact ((trivializationAt E (TangentSpace I) (γ w)).continuousLinearMapAt_apply_of_mem ℝ hb
    (lVelocity (I := I) γ r)).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isLRegularizedGeodesicOn_singleton_lPhaseCurve
    (S : SolutionOn (I := I) (M := M) D) {T : ℝ} (x0 : M) {z : ℝ → E × E} {s : ℝ}
    (hz : ∀ᶠ r in 𝓝 s, HasDerivAt z (lPhaseField S T x0 r (z r)) r ∧
      (z r).1 ∈ interior (extChartAt I x0).target)
    (hreg : T - s ^ 2 ∈ D.regular) :
    IsLRegularizedGeodesicOn S T (lPhaseCurve (I := I) x0 z) {s} := by
  have hq : ∀ᶠ r in 𝓝 s, HasDerivAt (fun u : ℝ => (z u).1) (z r).2 r :=
    hz.mono fun r hr => by
      simpa [lPhaseField, Function.comp_def] using hasFDerivAt_fst.comp_hasDerivAt r hr.1
  have hfield : (fun r => lVelocity (I := I) (lPhaseCurve (I := I) x0 z) r) =ᶠ[𝓝 s]
      lPhaseVelocity (I := I) x0 z := by
    filter_upwards [hq, hz] with r hr hr'
    exact lPhase_velocity (I := I) x0 z r hr hr'.2
  intro r hr
  rw [mem_singleton_iff.mp hr]
  obtain ⟨hzs, hint⟩ := hz.self_of_nhds
  have hv : HasDerivAt (fun u : ℝ => (z u).2) (lPhaseField S T x0 s (z s)).2 s := by
    simpa [Function.comp_def] using hasFDerivAt_snd.comp_hasDerivAt s hzs
  refine ⟨hreg, lPhaseCurve_mdiff (I := I) x0 z s hq.self_of_nhds.differentiableAt hint, ?_, ?_⟩
  · exact (lPhaseVelocity_diff (I := I) x0 z s hq.self_of_nhds.differentiableAt
      hv.differentiableAt hint).congr_of_eventuallyEq
      (DifferentialGeometry.Geometry.Riemannian.Variation.chartRepAt_eventuallyEq_of_eventuallyEq
        (I := I) (lPhaseCurve (I := I) x0 z) hfield)
  · calc
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (lPhaseCurve (I := I) x0 z)
          (fun r => lVelocity (I := I) (lPhaseCurve (I := I) x0 z) r) s =
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (lPhaseCurve (I := I) x0 z)
          (lPhaseVelocity (I := I) x0 z) s :=
        DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
          (I := I) _ _ hfield
      _ = lRegularizedAccel S T s (lPhaseCurve (I := I) x0 z s)
          (lPhaseVelocity (I := I) x0 z s) := lPhase_accel S T x0 z s hzs hint
      _ = _ := by rw [hfield.eq_of_nhds]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsLRegularizedGeodesicOn.union_Ioo_of_continuousAt
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S) {T c w d : ℝ}
    {γ : ℝ → M} (h₁ : IsLRegularizedGeodesicOn S T γ (Ioo c w))
    (h₂ : IsLRegularizedGeodesicOn S T γ (Ioo w d)) (hcw : c < w) (hwd : w < d)
    (hreg : T - w ^ 2 ∈ D.regular)
    (hγ : ContinuousAt (fun r => (TotalSpace.mk' E (γ r) (lVelocity (I := I) γ r) :
      TangentBundle I M)) w) :
    IsLRegularizedGeodesicOn S T γ (Ioo c d) := by
  intro s hs
  rcases lt_trichotomy s w with h | rfl | h
  · exact h₁ s ⟨hs.1, h⟩
  swap
  · exact h₂ s ⟨h, hs.2⟩
  obtain ⟨hγc, hzc⟩ := continuousAt_chartPhase hγ
  set x0 := γ s with hx0
  let z : ℝ → E × E := fun r => (chartCurve (I := I) x0 γ r,
    chartRepAtBase (I := I) x0 γ (fun u => lVelocity (I := I) γ u) r)
  let G : ℝ → E × E := fun r => lPhaseField S T x0 r (z r)
  have hsrc : ∀ᶠ r in 𝓝 s, γ r ∈ (chartAt H x0).source :=
    hγc.preimage_mem_nhds ((chartAt H x0).open_source.mem_nhds (mem_chart_source H x0))
  have hint : ∀ᶠ r in 𝓝 s, (z r).1 ∈ interior (extChartAt I x0).target := by
    filter_upwards [hsrc] with r hr
    rw [(isOpen_extChartAt_target (I := I) x0).interior_eq]
    exact (extChartAt I x0).map_source (by rwa [extChartAt_source])
  have hside : ∀ᶠ r in 𝓝 s, r ≠ s → HasDerivAt z (G r) r := by
    filter_upwards [hsrc, Ioo_mem_nhds hcw hwd] with r hr hrI hne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨-, hmd, hvel, hacc⟩ := h₁ r ⟨hrI.1, h⟩
      exact lRegularizedCurve_phase S T x0 γ r hmd hr hvel hacc
    · obtain ⟨-, hmd, hvel, hacc⟩ := h₂ r ⟨h, hrI.2⟩
      exact lRegularizedCurve_phase S T x0 γ r hmd hr hvel hacc
  have hG : ContinuousAt G s :=
    (lPhaseField_smoothAt S hS T x0 hreg hint.self_of_nhds).continuousAt.comp
      (f := fun r => (r, z r)) (continuousAt_id.prodMk hzc)
  have hderiv : HasDerivAt z (G s) s := by
    have hR : HasDerivWithinAt z (G s) (Ici s) s := by
      refine hasDerivWithinAt_Ici_of_tendsto_deriv
        (s := {r | r ≠ s → HasDerivAt z (G r) r} ∩ Ioi s)
        (fun r hr => (hr.1 (ne_of_gt hr.2)).differentiableAt.differentiableWithinAt)
        hzc.continuousWithinAt (inter_mem (nhdsWithin_le_nhds hside) self_mem_nhdsWithin) ?_
      refine (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds hside, self_mem_nhdsWithin] with r hr hr'
      exact (hr (ne_of_gt hr')).deriv.symm
    have hL : HasDerivWithinAt z (G s) (Iic s) s := by
      refine hasDerivWithinAt_Iic_of_tendsto_deriv
        (s := {r | r ≠ s → HasDerivAt z (G r) r} ∩ Iio s)
        (fun r hr => (hr.1 (ne_of_lt hr.2)).differentiableAt.differentiableWithinAt)
        hzc.continuousWithinAt (inter_mem (nhdsWithin_le_nhds hside) self_mem_nhdsWithin) ?_
      refine (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds hside, self_mem_nhdsWithin] with r hr hr'
      exact (hr (ne_of_lt hr')).deriv.symm
    have h := hL.union hR
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h
  have hz : ∀ᶠ r in 𝓝 s, HasDerivAt z (lPhaseField S T x0 r (z r)) r ∧
      (z r).1 ∈ interior (extChartAt I x0).target := by
    filter_upwards [hside, hint] with r hr hr'
    refine ⟨?_, hr'⟩
    by_cases hrs : r = s
    · subst hrs
      exact hderiv
    · exact hr hrs
  have heq : γ =ᶠ[𝓝 s] lPhaseCurve (I := I) x0 z := by
    filter_upwards [hsrc] with r hr
    exact ((extChartAt I x0).left_inv (by rwa [extChartAt_source])).symm
  exact IsLRegularizedGeodesicOn.congr_of_eventuallyEq
    (isLRegularizedGeodesicOn_singleton_lPhaseCurve S x0 hz hreg)
    (fun r hr => by rw [mem_singleton_iff.mp hr]; exact heq) s rfl

end Geodesic

section OneSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

theorem mfderivWithin_Ici_eq_of_eqOn_comp {f : M → N} {γ : ℝ → M} {α : ℝ → N} {s c : ℝ}
    (hsc : s < c) (hf : MDifferentiableAt I J f (γ s)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (heq : EqOn (f ∘ γ) α (Icc s c)) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) J α (Ici s) s ∧
      mfderivWithin 𝓘(ℝ, ℝ) J α (Ici s) s 1 = mfderiv I J f (γ s) (lVelocity (I := I) γ s) := by
  have hd := (hf.comp s hγ).hasMFDerivAt.hasMFDerivWithinAt (s := Ici s)
  have hα : α =ᶠ[𝓝[Ici s] s] f ∘ γ :=
    eventuallyEq_of_mem (Icc_mem_nhdsGE hsc) fun r hr => (heq hr).symm
  have h := hd.congr_of_eventuallyEq hα (heq ⟨le_rfl, hsc.le⟩).symm
  refine ⟨h.mdifferentiableWithinAt, ?_⟩
  rw [h.mfderivWithin (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Ici s)),
    mfderiv_comp s hf hγ]
  rfl

theorem mfderivWithin_Iic_eq_of_eqOn_comp {f : M → N} {γ : ℝ → M} {α : ℝ → N} {s c : ℝ}
    (hcs : c < s) (hf : MDifferentiableAt I J f (γ s)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (heq : EqOn (f ∘ γ) α (Icc c s)) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) J α (Iic s) s ∧
      mfderivWithin 𝓘(ℝ, ℝ) J α (Iic s) s 1 = mfderiv I J f (γ s) (lVelocity (I := I) γ s) := by
  have hd := (hf.comp s hγ).hasMFDerivAt.hasMFDerivWithinAt (s := Iic s)
  have hα : α =ᶠ[𝓝[Iic s] s] f ∘ γ :=
    eventuallyEq_of_mem (Icc_mem_nhdsLE hcs) fun r hr => (heq hr).symm
  have h := hd.congr_of_eventuallyEq hα (heq ⟨hcs.le, le_rfl⟩).symm
  refine ⟨h.mdifferentiableWithinAt, ?_⟩
  rw [h.mfderivWithin (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Iic s)),
    mfderiv_comp s hf hγ]
  rfl

end OneSided

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {H : ObservedHistory.{u}}

private theorem time_lt_stageEndTime_of_lt {j k : Fin (H.eventCount + 1)} (hjk : j < k) :
    H.time j < H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => exact absurd hjk (not_lt.2 (Fin.le_last k))
  | cast m =>
    rw [stageEndTime_castSucc]
    exact H.time_strictMono m.castSucc_lt_succ

private theorem lt_time_of_mem_stageDomain_of_lt {j k : Fin (H.eventCount + 1)} (hjk : j < k)
    {t : ℝ} (ht : t ∈ H.stageDomain j) : t < H.time k := by
  cases j using Fin.lastCases with
  | last => exact absurd hjk (not_lt.2 (Fin.le_last k))
  | cast m =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    exact ht.2.trans_le (H.time_strictMono.monotone (Fin.castSucc_lt_iff_succ_le.1 hjk))

private theorem mem_stageDomain_of_le_of_lt {j : Fin (H.eventCount + 1)} {t : ℝ}
    (h₁ : H.time j ≤ t) (h₂ : t < H.stageEndTime j) : t ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    rw [stageEndTime_last] at h₂
    simp only [stageDomain, Fin.lastCases_last, mem_Icc]
    exact ⟨h₁, h₂.le⟩
  | cast m =>
    rw [stageEndTime_castSucc] at h₂
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
    exact ⟨h₁, h₂⟩

theorem exists_incomingSlab_stageMetric (j : Fin (H.eventCount + 1))
    (hj : H.time j < H.stageEndTime j) :
    ∃ G : (H.stage j).IncomingSlab (H.time j) (H.stageEndTime j),
      G.flow.base.metric (H.time j) = H.initialMetric j ∧
      ∀ t ∈ Ioo (H.time j) (H.stageEndTime j), H.stageMetric j t = G.flow.base.metric t := by
  cases j using Fin.lastCases with
  | last =>
    rw [stageEndTime_last] at hj ⊢
    refine ⟨(H.finalSlab hj).restrictIncoming le_rfl hj le_rfl, H.final_initial hj, ?_⟩
    intro t _
    simp only [stageMetric, Fin.lastCases_last, dite_eq_left hj]
    rfl
  | cast k =>
    rw [stageEndTime_castSucc] at hj ⊢
    exact ⟨(H.event k).incoming, H.event_initial k, fun t _ => by
      simp only [stageMetric, Fin.lastCases_castSucc]⟩

namespace LWindow

section Crossing

variable {lo hi : Fin (H.eventCount + 1)} {T : ℝ} (W : H.LWindow lo hi T)

theorem eventuallyEq_comp_of_regularCrossing (i : Fin H.eventCount) (hl : lo ≤ i.castSucc)
    (hh : i.succ ≤ hi) (z : W.X)
    {ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier}
    (hψ : ∀ᶠ p in 𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z),
      (H.event i).RegularCrossing p (ψ p)) :
    ψ ∘ W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ =ᶠ[𝓝 z]
      W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ := by
  filter_upwards [(W.localDiffeomorph _).contMDiff.continuous.continuousAt.preimage_mem_nhds hψ]
    with y hy
  exact (H.event i).regularCrossing_right_unique hy (W.crossing i hl hh y)

theorem mdifferentiableAt_of_regularCrossing (i : Fin H.eventCount) (hl : lo ≤ i.castSucc)
    (hh : i.succ ≤ hi) (z : W.X)
    {ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier}
    (hψ : ∀ᶠ p in 𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z),
      (H.event i).RegularCrossing p (ψ p)) :
    MDifferentiableAt ThreeModel ThreeModel ψ
      (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z) := by
  have hx := W.localDiffeomorph ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z
  have hev : ψ =ᶠ[𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)]
      W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ ∘ hx.localInverse := by
    filter_upwards [hψ, hx.localInverse_open_source.mem_nhds hx.localInverse_mem_source]
      with p hp hpL
    have h := W.crossing i hl hh (hx.localInverse p)
    rw [hx.localInverse_right_inv hpL] at h
    exact (H.event i).regularCrossing_right_unique hp h
  exact (((W.localDiffeomorph ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ _).mdifferentiableAt
    (by simp)).comp _
    (hx.mdifferentiableAt_localInverse (by simp))).congr_of_eventuallyEq hev

theorem mfderiv_apply_mfderiv_eq_of_regularCrossing (i : Fin H.eventCount)
    (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi) (z : W.X)
    {ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier}
    (hψ : ∀ᶠ p in 𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z),
      (H.event i).RegularCrossing p (ψ p)) (V : TangentSpace ThreeModel z) :
    mfderiv ThreeModel ThreeModel ψ (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)
        (mfderiv ThreeModel ThreeModel
          (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩) z V) =
      mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩) z V := by
  have heq := W.eventuallyEq_comp_of_regularCrossing i hl hh z hψ
  have hpoint : ψ (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z) =
      W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ z := heq.self_of_nhds
  have h := mfderiv_comp z (W.mdifferentiableAt_of_regularCrossing i hl hh z hψ)
    ((W.localDiffeomorph _ z).mdifferentiableAt (by simp))
  rw [heq.mfderiv_eq] at h
  have hv := congrArg
    (fun D : TangentSpace ThreeModel z →L[ℝ]
        TangentSpace ThreeModel
          (ψ (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)) =>
      DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv (I := ThreeModel)
        (ψ (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)) (D V)) h
  dsimp only [Function.comp_apply] at hv
  rw [hpoint] at hv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    tangentSpaceCast] using! hv.symm

theorem eventually_regularCrossing_invFun [Nonempty W.X] (i : Fin H.eventCount)
    (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi) (z : W.X) :
    ∀ᶠ p in 𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z),
      (H.event i).RegularCrossing p (W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩
        (Function.invFun (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩) p)) := by
  filter_upwards [(W.localDiffeomorph _).isOpen_range.mem_nhds (mem_range_self z)] with p hp
  have h := W.crossing i hl hh
    (Function.invFun (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩) p)
  rwa [Function.invFun_eq hp] at h

theorem mfderiv_partialDiffeomorph_apply_eq_of_regularCrossing (i : Fin H.eventCount)
    (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi) (z : W.X)
    (F : PartialDiffeomorph ThreeModel ThreeModel (H.event i).incoming.terminalRegularOpen
      (H.stage i.succ).Carrier ∞)
    (hF : ∀ x ∈ F.source, (H.event i).RegularCrossing x.val (F x))
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ F.source)
    (hxz : x.val = W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)
    (V : TangentSpace ThreeModel z) :
    mfderiv ThreeModel ThreeModel F x
        (mfderiv ThreeModel ThreeModel
          (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩) z V) =
      mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩) z V := by
  classical
  let U := (H.event i).incoming.terminalRegularOpen
  let ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier := fun p =>
    if h : p ∈ U then F ⟨p, h⟩ else F x
  have hψF : ψ ∘ Subtype.val = F := funext fun y => dite_eq_left y.property
  have hopen : IsOpen (Subtype.val '' F.source : Set (H.stage i.castSucc).Carrier) :=
    U.isOpen.isOpenMap_subtype_val _ F.open_source
  have hψ : ∀ᶠ p in 𝓝 (W.f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z),
      (H.event i).RegularCrossing p (ψ p) := by
    rw [← hxz]
    filter_upwards [hopen.mem_nhds ⟨x, hx, rfl⟩] with p hp
    obtain ⟨y, hy, rfl⟩ := hp
    have hψy : ψ y.val = F y := dite_eq_left y.property
    rw [hψy]
    exact hF y hy
  have hd := W.mdifferentiableAt_of_regularCrossing i hl hh z hψ
  have key := W.mfderiv_apply_mfderiv_eq_of_regularCrossing i hl hh z hψ V
  rw [← hxz] at hd key
  rw [← hψF, mfderiv_comp x hd (hasMFDerivAt_subtype_val U x).mdifferentiableAt,
    mfderiv_subtype_val U x]
  exact key

end Crossing

section Seam

variable {T : ℝ} {i : Fin H.eventCount} (W : H.LWindow i.castSucc i.succ T)

theorem time_succ_le : H.time i.succ ≤ T - W.a ^ 2 :=
  H.time_le_of_mem_stageDomain W.upper

theorem lt_time_succ : T - W.b ^ 2 < H.time i.succ := by
  have h := W.lower
  simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at h
  exact h.2

theorem a_le_sqrt : W.a ≤ Real.sqrt (T - H.time i.succ) := by
  rw [← Real.sqrt_sq W.nonneg]
  exact Real.sqrt_le_sqrt (by linarith [W.time_succ_le])

theorem sqrt_lt_b : Real.sqrt (T - H.time i.succ) < W.b := by
  rw [← Real.sqrt_sq (W.nonneg.trans W.lt.le)]
  exact Real.sqrt_lt_sqrt (by nlinarith [W.time_succ_le, sq_nonneg W.a])
    (by linarith [W.lt_time_succ])

theorem regularizedStageStart_castSucc_eq :
    H.regularizedStageStart T W.a i.castSucc = Real.sqrt (T - H.time i.succ) := by
  simp only [regularizedStageStart, stageEndTime_castSucc, min_eq_right W.time_succ_le]

theorem regularizedStageEnd_castSucc_eq : H.regularizedStageEnd T W.b i.castSucc = W.b :=
  H.regularizedStageEnd_eq_of_mem_stageDomain (W.nonneg.trans W.lt.le) W.lower

theorem regularizedStageStart_succ_eq : H.regularizedStageStart T W.a i.succ = W.a :=
  H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc

theorem regularizedStageEnd_succ_eq :
    H.regularizedStageEnd T W.b i.succ = Real.sqrt (T - H.time i.succ) := by
  simp only [regularizedStageEnd, max_eq_right W.lt_time_succ.le]

theorem isLRegularizedGeodesicOn_of_comp {Do Dn : RealTimeInterval}
    (So : SolutionOn (I := ThreeModel) (M := (H.stage i.castSucc).Carrier) Do)
    (Sn : SolutionOn (I := ThreeModel) (M := (H.stage i.succ).Carrier) Dn)
    (hSo : ∀ s ∈ Ioo (Real.sqrt (T - H.time i.succ)) W.b,
      So.base.metric (T - s ^ 2) = H.stageMetric i.castSucc (T - s ^ 2))
    (hSn : ∀ s ∈ Ioo W.a (Real.sqrt (T - H.time i.succ)),
      Sn.base.metric (T - s ^ 2) = H.stageMetric i.succ (T - s ^ 2))
    (haw : W.a < Real.sqrt (T - H.time i.succ)) (γ : ℝ → W.X) (hγ : ContinuousOn γ (Ioo W.a W.b))
    (ho : IsLRegularizedGeodesicOn So T (W.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ ∘ γ)
      (Ioo (Real.sqrt (T - H.time i.succ)) W.b))
    (hn : IsLRegularizedGeodesicOn Sn T (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ ∘ γ)
      (Ioo W.a (Real.sqrt (T - H.time i.succ))))
    (hC1 : ContinuousAt (fun r => (TotalSpace.mk' ThreeSpace (γ r)
      (lVelocity (I := ThreeModel) γ r) : TangentBundle ThreeModel W.X))
      (Real.sqrt (T - H.time i.succ))) :
    IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hwb := W.sqrt_lt_b
  have hcont : ∀ K ⊆ Ioo W.a W.b, IsOpen K → ∀ s ∈ K, ∀ᶠ r in 𝓝 s, ContinuousAt γ r :=
    fun K hK hKo s hs => by
      filter_upwards [hKo.mem_nhds hs] with r hr
      exact hγ.continuousAt (isOpen_Ioo.mem_nhds (hK hr))
  have hold : IsLRegularizedGeodesicOn W.S T γ (Ioo (Real.sqrt (T - H.time i.succ)) W.b) := by
    refine ho.of_comp_localPullMetric (W.localDiffeomorph _) (fun s hs => ?_)
      (fun s hs _ => W.regular s ⟨haw.le.trans hs.1.le, hs.2.le⟩)
      (hcont _ (Ioo_subset_Ioo_left haw.le) isOpen_Ioo) (fun s hs => ?_)
    · have hm := W.metric ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ s (by
        change s ∈ Ioo (H.regularizedStageStart T W.a i.castSucc)
          (H.regularizedStageEnd T W.b i.castSucc)
        rw [W.regularizedStageStart_castSucc_eq, W.regularizedStageEnd_castSucc_eq]
        exact hs)
      rw [hm, ← hSo s hs]
    · filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact (ho r hr).2.1
  have hnew : IsLRegularizedGeodesicOn W.S T γ (Ioo W.a (Real.sqrt (T - H.time i.succ))) := by
    refine hn.of_comp_localPullMetric (W.localDiffeomorph _) (fun s hs => ?_)
      (fun s hs _ => W.regular s ⟨hs.1.le, hs.2.le.trans hwb.le⟩)
      (hcont _ (Ioo_subset_Ioo_right hwb.le) isOpen_Ioo) (fun s hs => ?_)
    · have hm := W.metric ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ s (by
        change s ∈ Ioo (H.regularizedStageStart T W.a i.succ) (H.regularizedStageEnd T W.b i.succ)
        rw [W.regularizedStageStart_succ_eq, W.regularizedStageEnd_succ_eq]
        exact hs)
      rw [hm, ← hSn s hs]
    · filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact (hn r hr).2.1
  exact hnew.union_Ioo_of_continuousAt W.solution hold haw hwb
    (W.regular _ ⟨haw.le, hwb.le⟩) hC1

end Seam

section Window

variable {lo hi : Fin (H.eventCount + 1)} {T : ℝ} (W : H.LWindow lo hi T)

theorem isLRegularizedGeodesicOn_comp (j : H.StageInterval lo hi) {D' : RealTimeInterval}
    (S' : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D') {K : Set ℝ}
    (hK : IsOpen K)
    (hKsub : K ⊆ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hS' : ∀ s ∈ K, S'.base.metric (T - s ^ 2) = H.stageMetric j.val (T - s ^ 2))
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D'.regular) {γ : ℝ → W.X}
    (h : IsLRegularizedGeodesicOn W.S T γ K) :
    IsLRegularizedGeodesicOn S' T (W.f j ∘ γ) K := by
  refine h.comp_of_localPullMetric (W.localDiffeomorph j)
    (fun s hs => by rw [W.metric j s (hKsub hs), hS' s hs]) (fun s hs _ => hreg s hs)
    (fun s hs => ?_)
  filter_upwards [hK.mem_nhds hs] with r hr
  exact (h r hr).2.1

theorem isLRegularizedJacobi_comp (j : H.StageInterval lo hi) {D' : RealTimeInterval}
    (S' : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D') {K : Set ℝ}
    (hK : IsOpen K)
    (hKsub : K ⊆ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hS' : ∀ s ∈ K, S'.base.metric (T - s ^ 2) = H.stageMetric j.val (T - s ^ 2))
    {γ : ℝ → W.X} {Y : ∀ r, TangentSpace ThreeModel (γ r)}
    (h : IsLRegularizedJacobi W.S T γ Y K) :
    IsLRegularizedJacobi S' T (W.f j ∘ γ)
      (fun r => mfderiv ThreeModel ThreeModel (W.f j) (γ r) (Y r)) K :=
  h.comp_of_localPullMetric (W.localDiffeomorph j) hK
    (fun s hs => by rw [W.metric j s (hKsub hs), hS' s hs])

end Window

section Minimizer

variable {T : ℝ}

theorem exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hw : u < Real.sqrt (T - H.time i.succ)) :
    ∃ W : H.LWindow i.castSucc i.succ T, u ≤ W.a ∧ W.a < Real.sqrt (T - H.time i.succ) ∧
      Real.sqrt (T - H.time i.succ) < W.b ∧ W.b ≤ v ∧
      ∃ γ : ℝ → W.X, Continuous γ ∧
        Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b ∧
        (∀ j : H.StageInterval i.castSucc i.succ,
          EqOn (W.f j ∘ γ) (α ⟨j.val, hf.trans j.property.1, j.property.2.trans hl⟩)
            (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) ∧
        IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) := by
  classical
  have hsl : H.time i.succ ≤ H.time last := H.time_strictMono.monotone hl
  have hTw : 0 ≤ T - H.time i.succ := by nlinarith [hupper.1, sq_nonneg u]
  have hw2 : Real.sqrt (T - H.time i.succ) ^ 2 = T - H.time i.succ := Real.sq_sqrt hTw
  have hsu : H.time i.succ < T - u ^ 2 := by
    have := pow_lt_pow_left₀ hw hu two_ne_zero
    linarith
  have hvt : T - v ^ 2 < H.time i.succ :=
    lt_time_of_mem_stageDomain_of_lt (hf.trans_lt i.castSucc_lt_succ) hlower
  have hse : H.time i.succ < H.stageEndTime i.succ := by
    rcases hl.lt_or_eq with h | h
    · exact time_lt_stageEndTime_of_lt h
    · calc H.time i.succ < T - u ^ 2 := hsu
        _ ≤ H.stageEndTime last := hupper.2
        _ = H.stageEndTime i.succ := by rw [h]
  have hso : H.regularizedStageStart T u i.castSucc = Real.sqrt (T - H.time i.succ) := by
    simp only [regularizedStageStart, stageEndTime_castSucc, min_eq_right hsu.le]
  have hen : H.regularizedStageEnd T v i.succ = Real.sqrt (T - H.time i.succ) := by
    simp only [regularizedStageEnd, max_eq_right hvt.le]
  have hmax : max (T - v ^ 2) (H.time i.castSucc) < H.time i.succ :=
    max_lt hvt (H.time_strictMono i.castSucc_lt_succ)
  have hmin' : H.time i.succ < min (T - u ^ 2) (H.stageEndTime i.succ) := lt_min hsu hse
  have hvo : Real.sqrt (T - H.time i.succ) < H.regularizedStageEnd T v i.castSucc :=
    Real.sqrt_lt_sqrt hTw (by linarith)
  have hsn0 : 0 ≤ T - min (T - u ^ 2) (H.stageEndTime i.succ) := by
    have := min_le_left (T - u ^ 2) (H.stageEndTime i.succ)
    nlinarith [sq_nonneg u]
  have hsn : H.regularizedStageStart T u i.succ < Real.sqrt (T - H.time i.succ) :=
    Real.sqrt_lt_sqrt hsn0 (by linarith)
  have hbo := (H.regularizedStage_bounds hu huv hupper hlower
    ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩).2.2
  have hbn := (H.regularizedStage_bounds hu huv hupper hlower
    ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩).1
  have hco : ContinuousOn (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) (H.regularizedStageEnd T v i.castSucc)) := by
    have h : ContinuousOn (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (uIcc (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)) :=
      (hα _).1
    rwa [hso, uIcc_of_le hvo.le] at h
  have hcn : ContinuousOn (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc (H.regularizedStageStart T u i.succ) (Real.sqrt (T - H.time i.succ))) := by
    have h : ContinuousOn (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        (uIcc (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)) :=
      (hα _).1
    rwa [hen, uIcc_of_le hsn.le] at h
  obtain ⟨x, -, hx1, -⟩ := hcross i hf hl
  let p₀ : (H.event i).incoming.terminalRegularOpen := (H.event i).oldTerminal x
  have hp₀ : p₀.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      (Real.sqrt (T - H.time i.succ)) := ((H.event i).oldTerminal_eq x).trans hx1
  obtain ⟨F, hsource, hpF, -, hFt, hFcross, -⟩ :=
    MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph (H.event i) (p := p₀)
      (by rw [hp₀]; exact hcross i hf hl)
  let Wo : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨F.source, F.open_source⟩
  have hW : ∀ y ∈ Wo, y.val ∈ interior (Subtype.val '' (H.event i).old) := by
    intro y hy
    change y ∈ F.source at hy
    rw [hsource] at hy
    exact hy
  have hUo : IsOpen (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _ F.open_source
  obtain ⟨b, hwb, hbv', hbmaps⟩ : ∃ b, Real.sqrt (T - H.time i.succ) < b ∧
      b < H.regularizedStageEnd T v i.castSucc ∧
      MapsTo (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (Icc (Real.sqrt (T - H.time i.succ)) b)
        (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) := by
    have hmem : α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ ⁻¹'
        (Subtype.val '' (Wo : Set (H.event i).incoming.terminalRegularOpen)) ∈
        𝓝[≥] Real.sqrt (T - H.time i.succ) := by
      rw [← nhdsWithin_Icc_eq_nhdsGE hvo]
      exact (hco _ ⟨le_rfl, hvo.le⟩).preimage_mem_nhdsWithin (hUo.mem_nhds ⟨p₀, hpF, hp₀⟩)
    obtain ⟨b₀, hb₀, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hmem
    exact ⟨min b₀ ((Real.sqrt (T - H.time i.succ) + H.regularizedStageEnd T v i.castSucc) / 2),
      lt_min hb₀ (by linarith), (min_le_right _ _).trans_lt (by linarith),
      fun s hs => hsub ⟨hs.1, hs.2.trans (min_le_left _ _)⟩⟩
  obtain ⟨a, hsa, haw, hamaps⟩ : ∃ a, H.regularizedStageStart T u i.succ < a ∧
      a < Real.sqrt (T - H.time i.succ) ∧
      MapsTo (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        (Icc a (Real.sqrt (T - H.time i.succ))) F.target := by
    have hmem : α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ ⁻¹' F.target ∈
        𝓝[≤] Real.sqrt (T - H.time i.succ) := by
      rw [← nhdsWithin_Icc_eq_nhdsLE hsn]
      exact (hcn _ ⟨hsn.le, le_rfl⟩).preimage_mem_nhdsWithin (F.open_target.mem_nhds hFt)
    obtain ⟨a₀, ha₀, hsub⟩ := mem_nhdsLE_iff_exists_Icc_subset.1 hmem
    exact ⟨max a₀ ((H.regularizedStageStart T u i.succ + Real.sqrt (T - H.time i.succ)) / 2),
      (by linarith : H.regularizedStageStart T u i.succ < _).trans_le (le_max_right _ _),
      max_lt ha₀ (by linarith), fun s hs => hsub ⟨(le_max_left _ _).trans hs.1, hs.2⟩⟩
  have ha0 : 0 ≤ a := (hu.trans hbn).trans hsa.le
  have hsa2 : H.regularizedStageStart T u i.succ ^ 2 < a ^ 2 :=
    pow_lt_pow_left₀ hsa (Real.sqrt_nonneg _) two_ne_zero
  have hss2 : H.regularizedStageStart T u i.succ ^ 2 =
      T - min (T - u ^ 2) (H.stageEndTime i.succ) :=
    Real.sq_sqrt hsn0
  have haw2 : a ^ 2 < Real.sqrt (T - H.time i.succ) ^ 2 := pow_lt_pow_left₀ haw ha0 two_ne_zero
  have hbw2 : Real.sqrt (T - H.time i.succ) ^ 2 < b ^ 2 :=
    pow_lt_pow_left₀ hwb (Real.sqrt_nonneg _) two_ne_zero
  have hbv2 : b ^ 2 < H.regularizedStageEnd T v i.castSucc ^ 2 :=
    pow_lt_pow_left₀ hbv' (ha0.trans (haw.trans hwb).le) two_ne_zero
  have hve2 : H.regularizedStageEnd T v i.castSucc ^ 2 =
      T - max (T - v ^ 2) (H.time i.castSucc) := Real.sq_sqrt (by linarith)
  have hupe : T - a ^ 2 < H.stageEndTime i.succ := by
    have := min_le_right (T - u ^ 2) (H.stageEndTime i.succ)
    linarith
  have hup : T - a ^ 2 ∈ H.stageDomain i.succ :=
    mem_stageDomain_of_le_of_lt (by linarith) hupe
  have hdown₀ : H.time i.castSucc < T - b ^ 2 := by
    have := le_max_right (T - v ^ 2) (H.time i.castSucc)
    linarith
  obtain ⟨G, hG0, hGstage⟩ := H.exists_incomingSlab_stageMetric i.succ hse
  obtain ⟨Wn, hWa, hWb, hrange⟩ := LWindow.exists_seam i G (hG0.trans (H.event_output i).symm)
    hGstage Wo ⟨p₀, hpF⟩ hW ha0 (haw.trans hwb) hup hupe hdown₀ (by linarith)
  have htarget : F.target ⊆ range (Wn.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) := by
    intro q hq
    have hy : F.toPartialEquiv.symm q ∈ F.source := F.toPartialEquiv.map_target hq
    obtain ⟨z, hz⟩ : (F.toPartialEquiv.symm q).val ∈
        range (Wn.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩) := by
      rw [hrange]
      exact ⟨_, hy, rfl⟩
    refine ⟨z, ?_⟩
    have h1 := Wn.crossing i le_rfl le_rfl z
    rw [hz] at h1
    have h2 := hFcross _ hy
    have h3 : F (F.toPartialEquiv.symm q) = q := F.toPartialEquiv.right_inv hq
    rw [h3] at h2
    exact (H.event i).regularCrossing_right_unique h1 h2
  have hcases : ∀ k : Fin (H.eventCount + 1), i.castSucc ≤ k → k ≤ i.succ →
      k = i.castSucc ∨ k = i.succ := by
    intro k h1 h2
    rcases h1.lt_or_eq with h | h
    · exact Or.inr (le_antisymm h2 (Fin.castSucc_lt_iff_succ_le.1 h))
    · exact Or.inl h.symm
  have hrange' : ∀ j : H.StageInterval i.castSucc i.succ,
      MapsTo (α ⟨j.val, hf.trans j.property.1, j.property.2.trans hl⟩)
        (Icc (H.regularizedStageStart T Wn.a j.val) (H.regularizedStageEnd T Wn.b j.val))
        (range (Wn.f j)) := by
    rintro ⟨k, h1, h2⟩
    rcases hcases k h1 h2 with rfl | rfl
    · dsimp only
      rw [Wn.regularizedStageStart_castSucc_eq, Wn.regularizedStageEnd_castSucc_eq, hWb]
      intro s hs
      change _ ∈ range (Wn.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩)
      rw [hrange]
      exact hbmaps hs
    · dsimp only
      rw [Wn.regularizedStageStart_succ_eq, Wn.regularizedStageEnd_succ_eq, hWa]
      intro s hs
      exact htarget (hamaps hs)
  have hua : u ≤ Wn.a := by rw [hWa]; linarith
  have hbv : Wn.b ≤ v := by rw [hWb]; linarith
  obtain ⟨γ, hγc, hγ, heq, hgeo⟩ := Wn.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    hle hf hl hu hua hbv hupper hlower hfloor α hα
    (fun i' hf' hl' => let ⟨z, _, h1, h2⟩ := hcross i' hf' hl'; ⟨z, h1, h2⟩) hmin hfin hrange'
  exact ⟨Wn, hua, hWa ▸ haw, hWb ▸ hwb, hbv, γ, hγc, hγ, heq, hgeo⟩

private theorem exists_seam_mfderivWithin_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hw : u < Real.sqrt (T - H.time i.succ)) :
    ∃ W : H.LWindow i.castSucc i.succ T, ∃ γ : ℝ → W.X,
      W.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ (γ (Real.sqrt (T - H.time i.succ))) =
        α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
      (MDifferentiableWithinAt 𝓘(ℝ, ℝ) ThreeModel
          (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
          (Ici (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) ∧
        mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (Ici (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1 =
          mfderiv ThreeModel ThreeModel (W.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩)
            (γ (Real.sqrt (T - H.time i.succ)))
            (lVelocity (I := ThreeModel) γ (Real.sqrt (T - H.time i.succ)))) ∧
      (MDifferentiableWithinAt 𝓘(ℝ, ℝ) ThreeModel
          (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (Iic (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) ∧
        mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
            (Iic (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1 =
          mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩)
            (γ (Real.sqrt (T - H.time i.succ)))
            (lVelocity (I := ThreeModel) γ (Real.sqrt (T - H.time i.succ)))) := by
  obtain ⟨W, -, haw, hwb, -, γ, -, -, heq, hgeo⟩ :=
    exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq hle hu huv hupper hlower hfloor α
      hα hcross hmin hfin i hf hl hw
  have hmd := (hgeo _ ⟨haw, hwb⟩).2.1
  have heqo : EqOn (W.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ ∘ γ)
      (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) W.b) := by
    have h := heq ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩
    dsimp only at h
    rwa [W.regularizedStageStart_castSucc_eq, W.regularizedStageEnd_castSucc_eq] at h
  have heqn : EqOn (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ ∘ γ)
      (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc W.a (Real.sqrt (T - H.time i.succ))) := by
    have h := heq ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩
    dsimp only at h
    rwa [W.regularizedStageStart_succ_eq, W.regularizedStageEnd_succ_eq] at h
  exact ⟨W, γ, heqo ⟨le_rfl, hwb.le⟩,
    mfderivWithin_Ici_eq_of_eqOn_comp hwb
      ((W.localDiffeomorph _ _).mdifferentiableAt (by simp)) hmd heqo,
    mfderivWithin_Iic_eq_of_eqOn_comp haw
      ((W.localDiffeomorph _ _).mdifferentiableAt (by simp)) hmd heqn⟩

theorem mfderiv_mfderivWithin_Ici_eq_mfderivWithin_Iic_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hw : u < Real.sqrt (T - H.time i.succ))
    (ψ : (H.stage i.castSucc).Carrier → (H.stage i.succ).Carrier)
    (hψ : ∀ᶠ p in 𝓝 (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      (Real.sqrt (T - H.time i.succ))), (H.event i).RegularCrossing p (ψ p)) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (Ici (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) ∧
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        (Iic (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) ∧
      mfderiv ThreeModel ThreeModel ψ
          (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
          (mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (Ici (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1) =
        mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (Iic (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1 := by
  obtain ⟨W, γ, hpt, ho, hn⟩ := exists_seam_mfderivWithin_of_regularizedCost_eq hle hu huv hupper
    hlower hfloor α hα hcross hmin hfin i hf hl hw
  refine ⟨ho.1, hn.1, ?_⟩
  rw [ho.2, hn.2]
  rw [← hpt] at hψ ⊢
  exact W.mfderiv_apply_mfderiv_eq_of_regularCrossing i le_rfl le_rfl _ hψ _

theorem mfderiv_partialDiffeomorph_mfderivWithin_Ici_eq_of_regularizedCost_eq
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hw : u < Real.sqrt (T - H.time i.succ))
    (F : PartialDiffeomorph ThreeModel ThreeModel (H.event i).incoming.terminalRegularOpen
      (H.stage i.succ).Carrier ∞)
    (hF : ∀ x ∈ F.source, (H.event i).RegularCrossing x.val (F x))
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ F.source)
    (hxα : x.val =
      α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ))) :
    mfderiv ThreeModel ThreeModel F x
        (mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
          (Ici (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1) =
      mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        (Iic (Real.sqrt (T - H.time i.succ))) (Real.sqrt (T - H.time i.succ)) 1 := by
  obtain ⟨W, γ, hpt, ho, hn⟩ := exists_seam_mfderivWithin_of_regularizedCost_eq hle hu huv hupper
    hlower hfloor α hα hcross hmin hfin i hf hl hw
  rw [ho.2, hn.2]
  exact W.mfderiv_partialDiffeomorph_apply_eq_of_regularCrossing i le_rfl le_rfl _ F hF hx
    (hxα.trans hpt.symm) _

end Minimizer

end LWindow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
