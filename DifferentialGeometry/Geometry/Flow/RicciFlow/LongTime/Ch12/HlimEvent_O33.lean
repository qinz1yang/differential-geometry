import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverEvent_O33
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowStage
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

/-! CH12-O33 G2b — the right-limit pull-back `hlim` ([FROZEN] CH12-O33 G2 addendum) and the
event-time cover `cover_event_O33` ([FROZEN] CH12-O33 G2).
* `patch_right_limit_O33`: a `PersistentModelPatch` at `(a, y)` gives right joint continuity of
  `(t, x) ↦ map t x` at `(a, y)` into the FIXED stage `Q = postStage a`: on `[a, a + δ)` the active
  stage of the patch history is constant (`exists_right_const_activeStage_CPD7`, event times
  allowed), the patch survivor map is continuous (`survivorCM`), `agrees` identifies it with `f`,
  and `postStage a` is the active stage (`postStage_eq_stage_active_CPD2`); Hausdorff ⇒ limit.
* `hlim_O33`: closed model balls are compact (Hopf–Rinow, `closedEBall_isCompact` from
  `FiniteVolumeHyperbolicModel.complete`), so a subsequence `y_n → z ∈ closedBall N ⊆ B(N+1)`,
  and `B(N+1) ⊆ B(2α⁻¹) ⊆ slice(Ω) a` puts the patch at `(a, z)`.
* `cover_event_O33 := cover_event_of_lim_O33 … (hlim_O33 …)`; the radius `w'⁻¹` at the event time
  is recovered inside `cover_event_of_lim_O33` by `hpi07_thick_transfer_O27`, which is stated for
  every `t ≥ T` with the post-metric (event times included) — this is the `hRadiusAtEvent` step of
  review R4 Q9. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter Topology
open Manifold GC.LongTime GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Backward survivor maps at equal stage indices are `HEq`. -/
theorem backwardSurvivorMap_heq_O33 (Hn : ObservedHistory.{u})
    (first last : Fin (Hn.eventCount + 1)) (hle : first ≤ last)
    {j j' : Fin (Hn.eventCount + 1)} (hjj : j = j')
    (h1 : first ≤ j) (h2 : j ≤ last) (h1' : first ≤ j') (h2' : j' ≤ last)
    (z : Hn.backwardSurvivorDomain first last hle) :
    HEq (Hn.backwardSurvivorMap first last hle j h1 h2 z)
      (Hn.backwardSurvivorMap first last hle j' h1' h2' z) := by
  subst hjj
  rfl

/-- **Fixed-stage right limit through a persistent patch at `(a, y)`.** If `t_n ↓ a` (`t_n ≥ a`),
`x_n → y`, all `t_n` have post stage `Q = postStage a`, and `f t_n x_n = q` in `Q`, then
`f a y = q`. -/
theorem patch_right_limit_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {H : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ}
    {α : ℝ → ℝ} {domain : ℝ → TopologicalSpace.Opens H.Carrier}
    {f : (t : ℝ) → T₀ ≤ t → H.Carrier → (postStage F.observation t).Carrier} {a : ℝ}
    {y : H.Carrier} (p : PersistentModelPatch F H T₀ α domain f a y) (hTa : T₀ ≤ a)
    {Q : OrientedThreeStage.{u}} (hQa : postStage F.observation a = Q) (q : Q.Carrier)
    (ts : ℕ → ℝ) (xs : ℕ → H.Carrier) (hts : Tendsto ts atTop (𝓝 a))
    (hxs : Tendsto xs atTop (𝓝 y)) (hta : ∀ n, a ≤ ts n) (hT : ∀ n, T₀ ≤ ts n)
    (hQ : ∀ n, postStage F.observation (ts n) = Q)
    (heq : ∀ n, cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) (hQ n))
      (f (ts n) (hT n) (xs n)) = q) :
    cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQa) (f a hTa y) = q := by
  set Hn := (F.tower.history p.n).toHistory with hHn
  have haI : a ∈ Ioo p.a p.b := ⟨p.before, p.after⟩
  set ta := patchTime_CPD2 p haI with hta_def
  set k := Hn.activeStage ta with hk
  obtain ⟨δ, hδ, hconst⟩ := exists_right_const_activeStage_CPD7 Hn ta.2.1 ta.2.2
  have hk1 : p.first ≤ k := (p.stages ta haI).1
  have hk2 : k ≤ p.last := (p.stages ta haI).2
  let Φ : ℝ × H.Carrier → (Hn.stage k).Carrier := fun z =>
    survivorCM Hn p.first p.last p.ordered k hk1 hk2 (p.map z)
  have hΦ : ∀ (t : ℝ) (ht : t ∈ Ioo p.a p.b) (hTt : T₀ ≤ t), a ≤ t → t < a + δ →
      ∀ x ∈ p.neighborhood, HEq (Φ (t, x)) (f t hTt x) := by
    intro t ht hTt hat htδ x hx
    have hact : Hn.activeStage (patchTime_CPD2 p ht) = k :=
      hconst t (patchTime_CPD2 p ht).2.1 (patchTime_CPD2 p ht).2.2 hat htδ
    exact (backwardSurvivorMap_heq_O33 Hn p.first p.last p.ordered hact.symm hk1 hk2 _ _ _).trans
      (p.agrees (patchTime_CPD2 p ht) ht hTt x hx)
  have hU : Ioo p.a p.b ×ˢ (p.neighborhood : Set H.Carrier) ∈ 𝓝 (a, y) :=
    prod_mem_nhds (Ioo_mem_nhds p.before p.after)
      (p.neighborhood.isOpen.mem_nhds p.mem_neighborhood)
  have hmapc : ContinuousAt p.map (a, y) := p.smooth.continuousOn.continuousAt hU
  have hΦc : ContinuousAt Φ (a, y) :=
    (survivorCM Hn p.first p.last p.ordered k hk1 hk2).continuous.continuousAt.comp hmapc
  have hlimΦ : Tendsto (fun n => Φ (ts n, xs n)) atTop (𝓝 (Φ (a, y))) :=
    hΦc.tendsto.comp (hts.prodMk_nhds hxs)
  have hstage : Hn.stage k = Q :=
    (postStage_eq_stage_active_CPD2 F.observation p.n ta).symm.trans hQa
  set q' : (Hn.stage k).Carrier :=
    cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hstage.symm) q with hq'
  have hev : ∀ᶠ n in atTop, q' = Φ (ts n, xs n) := by
    have h1 : ∀ᶠ n in atTop, ts n ∈ Ioo p.a p.b := hts (Ioo_mem_nhds p.before p.after)
    have h2 : ∀ᶠ n in atTop, ts n < a + δ := hts (Iio_mem_nhds (by linarith))
    have h3 : ∀ᶠ n in atTop, xs n ∈ p.neighborhood :=
      hxs (p.neighborhood.isOpen.mem_nhds p.mem_neighborhood)
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    apply eq_of_heq
    refine (cast_heq _ q).trans ?_
    refine (heq_of_eq (heq n)).symm.trans ?_
    exact (cast_heq _ _).trans (hΦ (ts n) hn1 (hT n) (hta n) hn2 (xs n) hn3).symm
  have hfin : Φ (a, y) = q' :=
    tendsto_nhds_unique hlimΦ ((tendsto_const_nhds (x := q')).congr' hev)
  have hΦa := hΦ a haI hTa le_rfl (by linarith) y p.mem_neighborhood
  apply eq_of_heq
  exact (cast_heq _ _).trans (hΦa.symm.trans ((heq_of_eq hfin).trans (cast_heq _ q)))

/-- **G2b `hlim_O33`**: the `hlim` binder of `cover_event_of_lim_O33` ([FROZEN] CH12-O33 G2
addendum, verbatim) from the patch conjunct of `hfam` and `hball`. -/
theorem hlim_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (count : ℕ)
    (model : Fin count → FiniteVolumeHyperbolicModel.{u})
    (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
    (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (hpos : ∀ i t, start i ≤ t → 0 < α i t)
    (hball : ∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
      (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t)
    (hpatch : ∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
      Nonempty (PersistentModelPatch F (model i) (start i) (α i)
        (sourceSlice_CX5 (Ω i)) (map i) t x)) :
    ∀ (i : Fin count) (a : ℝ) (ha : start i ≤ a) (Q : OrientedThreeStage.{u})
      (hQa : postStage F.observation a = Q) (N : ℝ), N + 1 < (α i a)⁻¹ → ∀ q : Q.Carrier,
      (∀ δ : ℝ, 0 < δ → ∃ (t : ℝ) (ht : start i ≤ t) (hQt : postStage F.observation t = Q),
        a < t ∧ t ≤ a + δ ∧ ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint N,
          cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQt) (map i t ht y) = q) →
      ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint (N + 1),
        cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQa) (map i a ha y) = q := by
  intro i a ha Q hQa N hN q hseq
  choose t ht hQt hat htδ y hy hyq using
    fun n : ℕ => hseq (1 / ((n : ℝ) + 1)) (by positivity)
  have hK := RiemannianMetricComplete.closedEBall_isCompact (I := 𝓡 3) (model i).complete
    (model i).basepoint N
  have hyK : ∀ n, y n ∈ {x : (model i).Carrier |
      riemannianEDistOf (I := 𝓡 3) (model i).metric (model i).basepoint x ≤ ENNReal.ofReal N} :=
    fun n => show riemannianEDistOf (I := 𝓡 3) (model i).metric (model i).basepoint (y n) ≤
        ENNReal.ofReal N from le_of_lt (hy n : riemannianEDistOf (I := 𝓡 3) (model i).metric
          (model i).basepoint (y n) < ENNReal.ofReal N)
  obtain ⟨z, hzK, φ, hφ, hlimz⟩ := hK.tendsto_subseq hyK
  have hN0 : 0 < N := by
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal N := lt_of_le_of_lt zero_le
      (hy 0 : riemannianEDistOf (I := 𝓡 3) (model i).metric (model i).basepoint
        (y 0) < ENNReal.ofReal N)
    exact ENNReal.ofReal_pos.mp h0
  have hz1 : z ∈ riemannianBallOf (model i).metric (model i).basepoint (N + 1) :=
    lt_of_le_of_lt (hzK : riemannianEDistOf (I := 𝓡 3) (model i).metric (model i).basepoint z ≤
      ENNReal.ofReal N) ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  have hαpos := hpos i a ha
  have hzS : z ∈ sourceSlice_CX5 (Ω i) a := hball i a ha
    (riemannianBallOf_mono _ _ (by have := inv_pos.mpr hαpos; linarith) hz1)
  have hδ0 : Tendsto (fun n => a + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 a) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
    simpa using (tendsto_const_nhds (x := a)).add h
  have hts : Tendsto (fun n => t (φ n)) atTop (𝓝 a) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ0
      (fun n => (hat (φ n)).le) (fun n => htδ (φ n))
  exact ⟨z, hz1, patch_right_limit_O33 (hpatch i a ha z hzS).some ha hQa q
    (fun n => t (φ n)) (fun n => y (φ n)) hts hlimz (fun n => (hat (φ n)).le)
    (fun n => ht (φ n)) (fun n => hQt (φ n)) (fun n => hyq (φ n))⟩

/-- **R4e `cover_event_O33`** ([FROZEN] CH12-O33 G2, binders = `cover_regular_O27`'s + `hpatch`):
the event-time cover with model radius `w'⁻¹`, COV not weakened. -/
theorem cover_event_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K count : ℕ)
    (model : Fin count → FiniteVolumeHyperbolicModel.{u}) (Tr : ∀ i, HyperbolicTruncation (model i))
    (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
    (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (hstart : ∀ i, 0 < start i) (hpos : ∀ i t, start i ≤ t → 0 < α i t)
    (hdecay : ∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε)
    (hsmooth : ∀ i t (ht : start i ≤ t),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t))
    (hemb : ∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x))
    (hball : ∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
      (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t)
    (hck : ∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
        ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t)
    (hpatch : ∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
      Nonempty (PersistentModelPatch F (model i) (start i) (α i)
        (sourceSlice_CX5 (Ω i)) (map i) t x))
    (hDone : ∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R)) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht0 : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes → ∀ w' : ℝ, w ≤ w' → w' ≤ w0 →
        ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
            ENNReal.ofReal r →
          ENNReal.ofReal (w' * r ^ 3) ≤
            ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
          ∃ (i : Fin count) (hi : start i ≤ t),
            p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹ :=
  cover_event_of_lim_O33 F K count model Tr start α Ω map hstart hpos hdecay hsmooth hemb hball
    hck hDone (hlim_O33 F count model start α Ω map hpos hball hpatch)

end GC.LongTime.Ch12
