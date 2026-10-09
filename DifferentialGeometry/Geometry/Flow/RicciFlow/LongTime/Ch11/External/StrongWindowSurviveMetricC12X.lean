import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSurviveC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowCommonC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction

/-!
# `hwin` Survive: metric identification of the pulled-in tube (C12X, S16I G2)

For a survivor pull-in `Sv : SpliceSurvivor_C12X D k hik` (`StrongWindowSurviveC12X`) and any
survivor package `P` with start `Sv.first` (`StrongWindowCommonC12X`):

* `metric_pre`: on the whole deep window `v ∈ [-θ, 0]` the parabolically rescaled package metric
  pulled back by `Ψ` is the deep backward-neck metric,
  `Ψ^*((r²)⁻¹ · gflow (t_i + r² v)) = D.metric v` on `U` (per slab by `deep_metric_on_slab`, at
  `v = 0` by the normalized terminal neck);
* `metric_surgery`: at the surgery time the same pullback is the output initial metric pulled back
  through the output-stage survivor image `π_{i.succ} ∘ Ψ` (the other side of the surgery);
* `gflow_eq_restrict_C12X`: two packages with nested starts agree after the later start (domain
  inclusion); `metric_post`: hence after the surgery `Ψ` reads any package started at `i.succ`
  (e.g. the window package of the Birth lane) through `inclusion ∘ Ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The slab of a time `τ ∈ [time a, time b)`. -/
private theorem s16i_exists_slab (H : ObservedHistory.{u}) {a b : Fin (H.eventCount + 1)} {τ : ℝ}
    (h1 : H.time a ≤ τ) (h2 : τ < H.time b) :
    ∃ j : Fin H.eventCount, a ≤ j.castSucc ∧ j.succ ≤ b ∧ H.time j.castSucc ≤ τ ∧
      τ < H.time j.succ := by
  classical
  have hab : a < b := H.time_strictMono.lt_iff_lt.mp (h1.trans_lt h2)
  let S : Finset (Fin (H.eventCount + 1)) :=
    Finset.univ.filter fun m => m < b ∧ H.time m ≤ τ
  have ha : a ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hab, h1⟩
  have hmem := (Finset.mem_filter.mp (Finset.max'_mem S ⟨a, ha⟩)).2
  have hne : S.max' ⟨a, ha⟩ ≠ Fin.last H.eventCount :=
    ne_of_lt (lt_of_lt_of_le hmem.1 (Fin.le_last b))
  have hsb : ((S.max' ⟨a, ha⟩).castPred hne).succ ≤ b := by
    apply Fin.le_iff_val_le_val.mpr
    have h := Fin.lt_def.mp hmem.1
    change (S.max' ⟨a, ha⟩).val + 1 ≤ b.val
    omega
  refine ⟨(S.max' ⟨a, ha⟩).castPred hne, S.le_max' a ha, hsb, hmem.2, ?_⟩
  by_contra hle'
  have hle := not_lt.mp hle'
  rcases hsb.lt_or_eq with hlt | heq
  · have hin : ((S.max' ⟨a, ha⟩).castPred hne).succ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, hle⟩
    have h3 := S.le_max' _ hin
    have h4 : S.max' ⟨a, ha⟩ < ((S.max' ⟨a, ha⟩).castPred hne).succ := by
      apply Fin.lt_def.mpr
      change (S.max' ⟨a, ha⟩).val < (S.max' ⟨a, ha⟩).val + 1
      omega
    exact absurd h3 (not_le.mpr h4)
  · rw [heq] at hle
    linarith

/-- An equal-dimensional smooth embedding of the neck buffer is a local diffeomorphism. -/
private theorem s16i_isLocalDiffeomorph {δ : ℝ}
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    {c : neckBuffer δ → Y} (hc : Manifold.IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ c := fun y =>
  Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
    (by simp [ThreeSpace, Module.finrank_prod]) (hc.isImmersion.isImmersionAt y)

private theorem s16i_pull_congr {δ : ℝ} {U : Opens (neckBuffer δ)}
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
    (g : SmoothRiemannianMetric ThreeModel Y) {F F' : U → Y} (e : F = F')
    (hF : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ F)
    (hF' : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ F') :
    localPullMetric g F hF = localPullMetric g F' hF' := by
  subst e
  rfl

/-- Pulling back a pulled-back metric along `Ψ` when the composite is a chart `c` on `U`. -/
private theorem s16i_pull_eq {δ : ℝ} (U : Opens (neckBuffer δ))
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    [T2Space X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
    (g : SmoothRiemannianMetric ThreeModel Y) (f : X → Y)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (Ψ : U → X) (hΨ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ)
    (c : neckBuffer δ → Y) (hc : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ c)
    (h : ∀ u, f (Ψ u) = c u.1) :
    localPullMetric (localPullMetric g f hf) Ψ hΨ = (localPullMetric g c hc).restrictOpen U := by
  rw [localPullMetric_comp g f Ψ hf hΨ (isLocalDiffeomorph_comp hf hΨ),
    ← localPullMetric_subtype_val (localPullMetric g c hc) U,
    localPullMetric_comp g c Subtype.val hc (isLocalDiffeomorph_subtype_val U)
      (isLocalDiffeomorph_comp hc (isLocalDiffeomorph_subtype_val U))]
  exact s16i_pull_congr g (show f ∘ Ψ = c ∘ Subtype.val from funext h) _ _

namespace ObservedHistory

variable {H : ObservedHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s}

/-- Two survivor packages with nested starts `first ≤ first'` agree on `[time first', s)`, the
earlier one being the restriction of the later one to the smaller survivor domain. -/
theorem SurvivorNeckPackage_C12X.gflow_eq_restrict_C12X {first first' : Fin (H.eventCount + 1)}
    {hle : first ≤ k} {hle' : first' ≤ k} (P : H.SurvivorNeckPackage_C12X k G first hle)
    (P' : H.SurvivorNeckPackage_C12X k G first' hle') (hff : first ≤ first') {τ : ℝ}
    (hτ : τ ∈ Ico (H.time first') s) :
    P.gflow τ = localPullMetric (P'.gflow τ)
      (Opens.inclusion (H.backwardSurvivorDomain_mono_first (hfirst := hle) (hnext := hle') hff))
      (H.backwardSurvivorDomain_inclusion_isLocalDiffeomorph (hfirst := hle) (hnext := hle')
        hff) := by
  rcases lt_or_ge τ (H.time k) with hτk | hτk
  · obtain ⟨j, hf, hl, hlo, hhi⟩ := s16i_exists_slab H hτ.1 hτk
    rw [P.slab_eq j (hff.trans hf) hl τ ⟨hlo, hhi.le⟩, P'.slab_eq j hf hl τ ⟨hlo, hhi.le⟩,
      H.localPullMetric_backwardSurvivorSlabMetric_restrictFirst (hfirst := hle) (hnext := hle')
        hff j hf hl τ]
  · rw [P.cur_eq τ ⟨hτk, hτ.2⟩, P'.cur_eq τ ⟨hτk, hτ.2⟩]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, mfderiv_opens_incl]
    rfl

namespace SpliceSurvivor_C12X

variable {i : Fin H.eventCount} {δ : ℝ} {kk : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ kk} {r θ : ℝ}
  {D : IncomingBackwardNeckDeep_C12X H i neck r θ} {hik : i.succ ≤ k}
  (Sv : H.SpliceSurvivor_C12X D k hik)

/-- **Pre-surgery identification.** On the whole deep window `v ∈ [-θ, 0]`, the parabolically
rescaled package metric pulled back by `Ψ` is the deep backward-neck metric on `U`. -/
theorem metric_pre (hscale : neck.scale = (r ^ 2)⁻¹)
    (P : H.SurvivorNeckPackage_C12X k G Sv.first Sv.hle) {v : ℝ} (hv : v ∈ Icc (-θ) 0) :
    localPullMetric (scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr (pow_pos D.radius_pos 2))
        (P.gflow (H.time i.succ + r ^ 2 * v))) Sv.Ψ Sv.Ψ_diffeo =
      (D.metric v).restrictOpen Sv.U := by
  have hr2 : 0 < r ^ 2 := pow_pos D.radius_pos 2
  rw [localPullMetric_scaleMetric]
  rcases hv.2.lt_or_eq with hv0 | hv0
  · have hτlt : H.time i.succ + r ^ 2 * v < H.time i.succ := by nlinarith
    have hτge : H.time Sv.first ≤ H.time i.succ + r ^ 2 * v := by
      have h1 := Sv.time_first
      have h2 : -(θ * r ^ 2) ≤ r ^ 2 * v := by nlinarith [hv.1]
      linarith
    obtain ⟨j, hf, hl, hlo, hhi⟩ := s16i_exists_slab H hτge hτlt
    have hj : j.val ≤ i.val := by
      have h := Fin.le_iff_val_le_val.mp hl
      change j.val + 1 ≤ i.val + 1 at h
      omega
    have ha := Sv.time_start j hf
    rw [P.slab_eq j hf (hl.trans hik) _ ⟨hlo, hhi.le⟩,
      H.backwardSurvivorSlabMetric_before Sv.first k Sv.hle j hf (hl.trans hik) hhi,
      s16i_pull_eq Sv.U _ _ _ Sv.Ψ Sv.Ψ_diffeo _
        (s16i_isLocalDiffeomorph (D.deepChart_smooth j hj ha))
        (fun u => Sv.chart_eq j hj ha hf _ u)]
    apply SmoothRiemannianMetric.ext_inner
    intro u V W
    rw [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    erw [localPullMetric_inner, D.deep_metric_on_slab j hj ha v ⟨hv.1, hv0⟩ hlo hhi u.1 V W]
  · subst hv0
    rw [show H.time i.succ + r ^ 2 * 0 = H.time i.succ by ring,
      P.slab_eq i Sv.first_le hik _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩]
    unfold backwardSurvivorSlabMetric
    rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal,
      s16i_pull_eq Sv.U _ (H.backwardSurvivorTerminalMap Sv.first k Sv.hle i Sv.first_le hik) _
        Sv.Ψ Sv.Ψ_diffeo (fun x => neck.chart x)
        (s16i_isLocalDiffeomorph neck.chart_smooth) (fun u => Subtype.ext (Sv.terminal_eq u))]
    apply SmoothRiemannianMetric.ext_inner
    intro u V W
    rw [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, D.terminal_metric]
    erw [localPullMetric_inner, neck.normalized_inner, hscale]

/-- **Surgery time, output side.** At `time i.succ` the package metric pulled back by `Ψ` is the
output initial metric pulled back through the output-stage survivor image `π_{i.succ} ∘ Ψ`. -/
theorem metric_surgery (P : H.SurvivorNeckPackage_C12X k G Sv.first Sv.hle) :
    localPullMetric (P.gflow (H.time i.succ)) Sv.Ψ Sv.Ψ_diffeo =
      localPullMetric (H.initialMetric i.succ)
        (H.backwardSurvivorMap Sv.first k Sv.hle i.succ (Sv.first_le.trans i.castSucc_lt_succ.le)
          hik ∘ Sv.Ψ)
        (isLocalDiffeomorph_comp (H.backwardSurvivorMap_isLocalDiffeomorph Sv.first k Sv.hle
          i.succ (Sv.first_le.trans i.castSucc_lt_succ.le) hik) Sv.Ψ_diffeo) := by
  rw [P.slab_eq i Sv.first_le hik _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
    H.backwardSurvivorSlabMetric_terminal]
  exact localPullMetric_comp _ _ _ _ _ _

/-- **After the surgery.** For `τ ∈ [time i.succ, s)`, `Ψ` reads any package started at
`i.succ` (e.g. the window package) through the domain inclusion. -/
theorem metric_post (P : H.SurvivorNeckPackage_C12X k G Sv.first Sv.hle)
    (P' : H.SurvivorNeckPackage_C12X k G i.succ hik) {τ : ℝ} (hτ : τ ∈ Ico (H.time i.succ) s) :
    localPullMetric (P.gflow τ) Sv.Ψ Sv.Ψ_diffeo =
      localPullMetric (P'.gflow τ)
        (Opens.inclusion (H.backwardSurvivorDomain_mono_first (hfirst := Sv.hle) (hnext := hik)
          (Sv.first_le.trans i.castSucc_lt_succ.le)) ∘ Sv.Ψ)
        (isLocalDiffeomorph_comp (H.backwardSurvivorDomain_inclusion_isLocalDiffeomorph
          (hfirst := Sv.hle) (hnext := hik) (Sv.first_le.trans i.castSucc_lt_succ.le))
          Sv.Ψ_diffeo) := by
  rw [P.gflow_eq_restrict_C12X P' (Sv.first_le.trans i.castSucc_lt_succ.le) hτ]
  exact localPullMetric_comp _ _ _ _ _ _

end SpliceSurvivor_C12X

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
