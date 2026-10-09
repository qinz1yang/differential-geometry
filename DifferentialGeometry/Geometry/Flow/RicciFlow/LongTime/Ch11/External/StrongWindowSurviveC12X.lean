import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceConcat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph

/-!
# `hwin` Survive: the pre-surgery tube in a survivor domain (C12X, S16I G1)

Design `docs/geometrization/chapter8/out/CH12X-S16-HWIN-design.md` §4 G3 (lane C), route β
(deep backward necks, `StrongWindowDeepC12X`).  For a deep backward neck
`D : IncomingBackwardNeckDeep_C12X H i neck r θ` of event `i` and a stage `k ≥ i.succ`,
`SpliceSurvivor_C12X D k hik` pulls the tube into the backward survivor domain `first … k`,
where `first` is the stage containing the start `time i.succ − θ r²` of the deep window:

* `U ⊆ neckBuffer δ` open and `Ψ : U → backwardSurvivorDomain first k`, an injective local
  diffeomorphism, with `π_{j.castSucc} ∘ Ψ = D.deepChart j` for every stage of the deep window
  (`chart_eq`);
* `U` is maximal: every buffer point whose terminal image crosses event `i` into a point that
  survives to `k` lies in `U` (`maximal`).

Construction: `nonempty_spliceSurvivor_C12X` (the deep charts and crossings form backward traces;
`Ψ` inverts the survivor map onto the terminal stage).  Consequences: `terminal_eq`, `crossing`
(surgery-time identification of the two sides), `val_eq_of_succ_eq` (forward determinism).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- The deep backward neck `D` of event `i`, pulled into the backward survivor domain
`first … k`: `first` is the stage of the deep window start, `Ψ : U → backwardSurvivorDomain`
reproduces every deep stage chart, and `U` contains every buffer point whose terminal image
crosses event `i` into a point surviving to `k`. -/
structure SpliceSurvivor_C12X (H : ObservedHistory.{u}) {i : Fin H.eventCount} {δ : ℝ} {kk : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric δ kk} {r θ : ℝ}
    (D : IncomingBackwardNeckDeep_C12X H i neck r θ) (k : Fin (H.eventCount + 1))
    (hik : i.succ ≤ k) where
  first : Fin (H.eventCount + 1)
  first_le : first ≤ i.castSucc
  time_first : H.time first ≤ H.time i.succ - θ * r ^ 2
  time_start : ∀ j : Fin H.eventCount, first ≤ j.castSucc →
    H.time i.succ - θ * r ^ 2 < H.time j.succ
  U : Opens (neckBuffer δ)
  Ψ : U → H.backwardSurvivorDomain first k (first_le.trans (i.castSucc_lt_succ.le.trans hik))
  Ψ_diffeo : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ
  Ψ_injective : Function.Injective Ψ
  chart_eq : ∀ (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - θ * r ^ 2 < H.time j.succ) (hf : first ≤ j.castSucc)
    (hk : j.castSucc ≤ k) (u : U),
    H.backwardSurvivorMap first k (first_le.trans (i.castSucc_lt_succ.le.trans hik))
      j.castSucc hf hk (Ψ u) = D.deepChart j hj ha u.1
  maximal : ∀ (u : neckBuffer δ) (z : H.backwardSurvivorDomain i.succ k hik),
    (H.event i).RegularCrossing (neck.chart u).1
      (H.backwardSurvivorMap i.succ k hik i.succ le_rfl hik z) →
    ∃ hu : u ∈ U, (Ψ ⟨u, hu⟩).val = z.val

end ObservedHistory

private theorem s16i_ne_last {n : ℕ} {i : Fin n} {m : Fin (n + 1)} (hm : m ≤ i.castSucc) :
    m ≠ Fin.last n := by
  rintro rfl
  exact absurd hm (not_le.mpr (Fin.castSucc_lt_last i))

private theorem s16i_val_le {n : ℕ} {i : Fin n} {m : Fin (n + 1)} (hm : m ≤ i.castSucc) :
    (m.castPred (s16i_ne_last hm)).val ≤ i.val :=
  Fin.le_iff_val_le_val.mp hm

private theorem s16i_lt {n : ℕ} {i j : Fin n} (hl : j.succ ≤ i.castSucc) : j.val < i.val := by
  have h := Fin.le_iff_val_le_val.mp hl
  change j.val + 1 ≤ i.val at h
  omega

/-- The stage containing a time `a ∈ [0, time i.succ)`, at or before `i.castSucc`. -/
private theorem s16i_exists_first (H : ObservedHistory.{u}) (i : Fin H.eventCount) {a : ℝ}
    (ha0 : 0 ≤ a) (hai : a < H.time i.succ) :
    ∃ first : Fin (H.eventCount + 1), first ≤ i.castSucc ∧ H.time first ≤ a ∧
      ∀ j : Fin H.eventCount, first ≤ j.castSucc → a < H.time j.succ := by
  classical
  let S : Finset (Fin (H.eventCount + 1)) :=
    Finset.univ.filter fun m => m ≤ i.castSucc ∧ H.time m ≤ a
  have h0 : (0 : Fin (H.eventCount + 1)) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Fin.zero_le _, H.time_zero.symm ▸ ha0⟩
  have hmem := Finset.max'_mem S ⟨0, h0⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨S.max' ⟨0, h0⟩, hmem.1, hmem.2, fun j hj => ?_⟩
  by_contra hle'
  have hle := not_lt.mp hle'
  by_cases hji : j.succ ≤ i.castSucc
  · have hin : j.succ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hji, hle⟩
    exact absurd (hj.trans_lt j.castSucc_lt_succ) (not_lt.mpr (S.le_max' _ hin))
  · have hij : i.succ ≤ j.succ := by
      apply Fin.le_iff_val_le_val.mpr
      have h := mt Fin.le_iff_val_le_val.mpr hji
      change ¬ j.val + 1 ≤ i.val at h
      change i.val + 1 ≤ j.val + 1
      omega
    have := H.time_strictMono.monotone hij
    linarith

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {kk : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ kk} {r θ : ℝ}

/-- The deep chart of the terminal stage is the neck chart. -/
private theorem s16i_deepChart_self (D : IncomingBackwardNeckDeep_C12X H i neck r θ)
    (ha : H.time i.succ - θ * r ^ 2 < H.time i.succ) (u : neckBuffer δ) :
    D.deepChart i le_rfl ha u = (neck.chart u).1 := by
  have hr : H.time i.succ - r ^ 2 < H.time i.succ := by
    have := pow_pos D.radius_pos 2
    linarith
  rw [D.deepChart_eq i le_rfl hr ha]
  exact D.terminal_chart hr u

/-- The deep stage charts of one buffer point form a backward trace from `first`. -/
private def s16i_stageTrace (D : IncomingBackwardNeckDeep_C12X H i neck r θ)
    {first : Fin (H.eventCount + 1)} (hfi : first ≤ i.castSucc)
    (hstart : ∀ j : Fin H.eventCount, first ≤ j.castSucc →
      H.time i.succ - θ * r ^ 2 < H.time j.succ)
    (u : neckBuffer δ) (e : (H.stage i.castSucc).Carrier)
    (he : D.deepChart i le_rfl (hstart i hfi) u = e) :
    BackwardPointTrace H first i.castSucc hfi e where
  point m hm hmi := D.deepChart (m.castPred (s16i_ne_last hmi)) (s16i_val_le hmi) (hstart _ hm) u
  endpoint_eq := he
  crossing j hf hl :=
    D.deep_crossing j (s16i_lt hl) (hstart _ hf) (hstart _ (hf.trans j.castSucc_lt_succ.le)) u

/-- A buffer point whose terminal image crosses event `i` into a point surviving to `k` survives
back to `first`, with terminal survivor image the neck chart point. -/
private theorem s16i_mem_domain (D : IncomingBackwardNeckDeep_C12X H i neck r θ)
    {first : Fin (H.eventCount + 1)} (hfi : first ≤ i.castSucc)
    (hstart : ∀ j : Fin H.eventCount, first ≤ j.castSucc →
      H.time i.succ - θ * r ^ 2 < H.time j.succ)
    {k : Fin (H.eventCount + 1)} (hik : i.succ ≤ k) (u : neckBuffer δ)
    (z : H.backwardSurvivorDomain i.succ k hik)
    (hcross : (H.event i).RegularCrossing (neck.chart u).1
      (H.backwardSurvivorMap i.succ k hik i.succ le_rfl hik z)) :
    ∃ hz : z.val ∈ H.backwardSurvivorDomain first k
        (hfi.trans (i.castSucc_lt_succ.le.trans hik)),
      H.backwardSurvivorMap first k (hfi.trans (i.castSucc_lt_succ.le.trans hik)) i.castSucc hfi
        (i.castSucc_lt_succ.le.trans hik) ⟨z.val, hz⟩ = (neck.chart u).1 := by
  let A : BackwardPointTrace H i.succ k hik z.val := Classical.choice z.property
  let B := A.prepend (neck.chart u).1 hcross
  have hBp : B.point i.castSucc le_rfl (i.castSucc_lt_succ.le.trans hik) = (neck.chart u).1 :=
    A.prepend_point_first _ hcross
  let T := s16i_stageTrace D hfi hstart u (B.point i.castSucc le_rfl _)
    ((s16i_deepChart_self D _ u).trans hBp.symm)
  have hz : z.val ∈ H.backwardSurvivorDomain first k
      (hfi.trans (i.castSucc_lt_succ.le.trans hik)) := ⟨B.concat T⟩
  refine ⟨hz, ?_⟩
  rw [H.backwardSurvivorMap_eq_point first k _ i.castSucc hfi _ ⟨z.val, hz⟩ (B.concat T),
    B.concat_point_of_le T i.castSucc hfi _ le_rfl]
  exact T.endpoint_eq.trans hBp

namespace ObservedHistory

/-- **Construction.** Every deep backward neck of event `i` and every stage `k ≥ i.succ` carry a
survivor pull-in. -/
theorem nonempty_spliceSurvivor_C12X (D : IncomingBackwardNeckDeep_C12X H i neck r θ)
    (k : Fin (H.eventCount + 1)) (hik : i.succ ≤ k) :
    Nonempty (H.SpliceSurvivor_C12X D k hik) := by
  have hr2 : 0 < θ * r ^ 2 :=
    mul_pos (lt_of_lt_of_le one_pos D.one_le_depth) (pow_pos D.radius_pos 2)
  obtain ⟨first, hfi, htf, hstart⟩ :=
    s16i_exists_first H i D.deep_left_nonneg (show H.time i.succ - θ * r ^ 2 < H.time i.succ
      by linarith)
  have hik' : i.castSucc ≤ k := i.castSucc_lt_succ.le.trans hik
  have hfk : first ≤ k := hfi.trans hik'
  let π := H.backwardSurvivorMap first k hfk i.castSucc hfi hik'
  have hπ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ π :=
    H.backwardSurvivorMap_isLocalDiffeomorph first k hfk i.castSucc hfi hik'
  have hπi : Function.Injective π := H.backwardSurvivorMap_injective first k hfk i.castSucc hfi hik'
  let Φ := Topology.Manifold.diffeomorphOntoImage π hπ hπi
  let g : neckBuffer δ → (H.stage i.castSucc).Carrier := fun u => (neck.chart u).1
  have hg : Continuous g := continuous_subtype_val.comp neck.chart.continuous
  let U : Opens (neckBuffer δ) := ⟨g ⁻¹' (hπ.image : Set _), hπ.image.isOpen.preimage hg⟩
  let g' : U → hπ.image := fun u => ⟨g u.1, u.2⟩
  let Ψ : U → H.backwardSurvivorDomain first k hfk := fun u => Φ.symm (g' u)
  have hπΨ : ∀ u, π (Ψ u) = g u.1 := fun u =>
    Topology.Manifold.diffeomorphOntoImage_symm_apply π hπ hπi (g' u)
  have hc : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ neck.chart := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
      (by simp [ThreeSpace, Module.finrank_prod]) (neck.chart_smooth.isImmersion.isImmersionAt y)
  have hgl : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (fun u : U => g u.1) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
      (isLocalDiffeomorph_comp hc (isLocalDiffeomorph_subtype_val U))
  have hΨc : Continuous Ψ :=
    Φ.symm.continuous.comp ((hg.comp continuous_subtype_val).subtype_mk fun u => u.2)
  have hΨ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ := fun u => by
    have he : π ∘ Ψ = fun u : U => g u.1 := funext hπΨ
    exact isLocalDiffeomorphAt_of_comp_right hΨc.continuousAt (hπ (Ψ u)) (he ▸ hgl u)
  have hΨi : Function.Injective Ψ := by
    intro u v huv
    have h := congrArg π huv
    rw [hπΨ, hπΨ] at h
    exact Subtype.ext (neck.chart_smooth.isEmbedding.injective (Subtype.ext h))
  refine ⟨⟨first, hfi, htf, hstart, U, Ψ, hΨ, hΨi, ?_, ?_⟩⟩
  · intro j hj ha hf hk u
    let A := Classical.choice (Ψ u).property
    have hpt : D.deepChart i le_rfl (hstart i hfi) u.1 = A.point i.castSucc hfi hik' := by
      exact (s16i_deepChart_self D _ u.1).trans (hπΨ u).symm
    let T := s16i_stageTrace D hfi hstart u.1 (A.point i.castSucc hfi hik') hpt
    have hji : j.castSucc ≤ i.castSucc := Fin.le_iff_val_le_val.mpr hj
    exact BackwardPointTrace.point_unique (A.restrictLast hfi hik') T j.castSucc hf hji
  · intro u z hcross
    obtain ⟨hz, hzπ⟩ := s16i_mem_domain D hfi hstart hik u z hcross
    have h1 : g u ∈ hπ.image.1 := by
      rw [hπ.image_coe]
      exact ⟨_, hzπ⟩
    refine ⟨h1, ?_⟩
    have h2 : Ψ ⟨u, h1⟩ = ⟨z.val, hz⟩ := hπi ((hπΨ _).trans hzπ.symm)
    rw [h2]

namespace SpliceSurvivor_C12X

variable {D : IncomingBackwardNeckDeep_C12X H i neck r θ} {k : Fin (H.eventCount + 1)}
  {hik : i.succ ≤ k} (Sv : H.SpliceSurvivor_C12X D k hik)

theorem hle : Sv.first ≤ k := Sv.first_le.trans (i.castSucc_lt_succ.le.trans hik)

/-- Terminal-stage survivor image of `Ψ u`: the neck chart point. -/
theorem terminal_eq (u : Sv.U) :
    H.backwardSurvivorMap Sv.first k Sv.hle i.castSucc Sv.first_le
      (i.castSucc_lt_succ.le.trans hik) (Sv.Ψ u) = (neck.chart u.1).1 := by
  rw [Sv.chart_eq i le_rfl (Sv.time_start i Sv.first_le) Sv.first_le _ u]
  exact s16i_deepChart_self D _ u.1

/-- Surgery-time identification: the neck chart point of `u` crosses event `i` into the
output-stage survivor image of `Ψ u`. -/
theorem crossing (u : Sv.U) :
    (H.event i).RegularCrossing (neck.chart u.1).1
      (H.backwardSurvivorMap Sv.first k Sv.hle i.succ
        (Sv.first_le.trans i.castSucc_lt_succ.le) hik (Sv.Ψ u)) := by
  have h := H.backwardSurvivorMap_crossing Sv.first k Sv.hle i Sv.first_le hik (Sv.Ψ u)
  rwa [Sv.terminal_eq u] at h

/-- Forward determinism: a point surviving from `i.succ` with the same output-stage image as
`Ψ u` is `Ψ u`. -/
theorem val_eq_of_succ_eq (u : Sv.U) (z : H.backwardSurvivorDomain i.succ k hik)
    (hz : H.backwardSurvivorMap i.succ k hik i.succ le_rfl hik z =
      H.backwardSurvivorMap Sv.first k Sv.hle i.succ (Sv.first_le.trans i.castSucc_lt_succ.le)
        hik (Sv.Ψ u)) :
    z.val = (Sv.Ψ u).val := by
  have hfs : Sv.first ≤ i.succ := Sv.first_le.trans i.castSucc_lt_succ.le
  have h1 := congrFun (H.backwardSurvivorMap_comp_inclusion_first (hfirst := Sv.hle)
    (hnext := hik) hfs i.succ le_rfl hik) (Sv.Ψ u)
  have h2 := H.backwardSurvivorMap_injective i.succ k hik i.succ le_rfl hik (hz.trans h1.symm)
  rw [h2]

end SpliceSurvivor_C12X

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
