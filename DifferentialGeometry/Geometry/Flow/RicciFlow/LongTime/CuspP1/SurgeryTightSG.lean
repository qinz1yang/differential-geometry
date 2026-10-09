import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryStaticSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowStage

/-!
# tight window：`Fs = activeStage s`（`s < τ₀`），`Ls = activeStage τ₀`（G4d，S-A14-SURGERY）

`exists_smoothWindow_CPD7` 给出的 stage 区间 `[Fs, Ls]` 可能比 `τ₀` 附近真正用到的更宽，
于是 `D = backwardSurvivorDomain Fs Ls` 偏小（只含回溯到 `Fs` 仍存活的点）。
`SmoothDatum_CPD7.restrictRange` 可以把区间收紧到 `[F', L']`（`D` 变大，
`backwardSurvivorDomain_mono_first`）。本文件把时间集收紧到 `τ₀` 附近的 `J'`，使

* `t ∈ J'`、`t < τ₀` ⇒ `activeStage t = Fs`；
* `t ∈ J'`、`τ₀ ≤ t` ⇒ `activeStage t = Ls`（`= activeStage τ₀`），

并重新给出 G1 主定理的全部结论（`ι_t`、agreement、光滑性）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

/-- `τ > 0` 左侧一小段上 active stage 是常值。 -/
theorem exists_left_const_activeStage_SG (H : ObservedHistory.{u}) {τ : ℝ} (hτ : 0 < τ)
    (h1 : τ ≤ H.horizon) :
    ∃ ρ > 0, ∃ F' : Fin (H.eventCount + 1), ∀ t (h0' : 0 ≤ t) (h1' : t ≤ H.horizon),
      τ - ρ < t → t < τ → H.activeStage ⟨t, h0', h1'⟩ = F' := by
  classical
  have hfin : (range H.time ∩ Iio τ).Finite := (Set.finite_range _).inter_of_left _
  have hne : (range H.time ∩ Iio τ).Nonempty := ⟨H.time 0, ⟨0, rfl⟩, by
    rw [mem_Iio, H.time_zero]; exact hτ⟩
  set m := hfin.toFinset.max' (by simpa using hne) with hm
  have hmmem : m ∈ range H.time ∩ Iio τ :=
    hfin.mem_toFinset.mp (Finset.max'_mem hfin.toFinset (by simpa using hne))
  have hmτ : m < τ := mem_Iio.mp hmmem.2
  have hmge : ∀ y ∈ range H.time ∩ Iio τ, y ≤ m := fun y hy =>
    Finset.le_max' _ _ (by simpa using hy)
  have hm0 : 0 ≤ m := by
    obtain ⟨k, hk⟩ := hmmem.1
    rw [← hk]; exact H.time_nonneg k
  have key : ∀ (t t' : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ H.horizon) (h0' : 0 ≤ t')
      (h1' : t' ≤ H.horizon), m < t → t < τ → m < t' →
      H.activeStage ⟨t, h0, h1⟩ ≤ H.activeStage ⟨t', h0', h1'⟩ := by
    intro t t' h0 h1 h0' h1' hmt htτ hmt'
    apply H.le_activeStage ⟨t', h0', h1'⟩
    have h2 := H.activeStage_time_le ⟨t, h0, h1⟩
    simp only at h2
    have h3 : H.time (H.activeStage ⟨t, h0, h1⟩) ≤ m :=
      hmge _ ⟨⟨_, rfl⟩, lt_of_le_of_lt h2 htτ⟩
    exact h3.trans hmt'.le
  have hmid : 0 ≤ (m + τ) / 2 := by linarith
  have hmid1 : (m + τ) / 2 ≤ H.horizon := by linarith
  refine ⟨τ - m, by linarith, H.activeStage ⟨(m + τ) / 2, hmid, hmid1⟩, ?_⟩
  intro t h0' h1' ht1 ht2
  have hmt : m < t := by linarith
  exact le_antisymm (key t _ h0' h1' hmid hmid1 hmt ht2 (by linarith))
    (key _ t hmid hmid1 h0' h1' (by linarith) (by linarith) hmt)

section Tight

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **tight window**：G1 主定理的全部结论（`ι_t`、agreement、光滑性），并且 `t ∈ J`、
`t < τ₀` ⇒ `activeStage t = Fs`，`τ₀ ≤ t` ⇒ `activeStage t = Ls`（`= activeStage τ₀`）。 -/
theorem exists_tight_window_SG (cores : PersistentHyperbolicCores F K) {τ₀ : ℝ}
    (hτ₀ : cores.start < τ₀) (S : ∀ i, Set (cores.model i).Carrier)
    (hS : ∀ i, IsCompact (S i)) (hdom : ∀ i, S i ⊆ cores.domain i τ₀) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (J : Set ℝ) (U : ∀ i, Set (cores.model i).Carrier)
      (z : ∀ i, ℝ × (cores.model i).Carrier →
        (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
      (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
      (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls),
      τ₀ ∈ J ∧ IsOpen J ∧ J ⊆ Ioi cores.start ∧
      (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, ∀ t ∈ J, cores.start ≤ t → U i ⊆ cores.domain i t) ∧
      (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (z i) (J ×ˢ U i)) ∧
      (∀ i (t : ℝ) (ht : t ∈ J) (hts : cores.start ≤ t) (y : (cores.model i).Carrier),
        y ∈ U i → windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y)) =
          cores.map i t hts y) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → τ₀ ≤ t →
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Ls) := by
  obtain ⟨N, Fs, Ls, hFL, J, U, D, hτJ, hJo, hJstart, -, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_smoothWindow_CPD7 cores hτ₀ S hS hdom
  have hτ0 : 0 < τ₀ := cores.start_pos.trans hτ₀
  have h0 := (hJh τ₀ hτJ).1
  have h1 := (hJh τ₀ hτJ).2
  obtain ⟨ρ, hρ, F', hF'⟩ := exists_left_const_activeStage_SG (F.observation.history N) hτ0 h1
  obtain ⟨δR, hδR, hR⟩ := exists_right_const_activeStage_CPD7 (F.observation.history N) h0 h1
  let J' : Set ℝ := J ∩ Ioo (τ₀ - ρ) (τ₀ + δR)
  have hJ'o : IsOpen J' := hJo.inter isOpen_Ioo
  have hτJ' : τ₀ ∈ J' := ⟨hτJ, by constructor <;> linarith⟩
  have hJ'sub : J' ⊆ J := inter_subset_left
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hJ'o τ₀ hτJ'
  have ht₁ : τ₀ - r / 2 ∈ J' := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |τ₀ - r / 2 - τ₀| = r / 2 := by rw [abs_of_neg (by linarith)]; ring
    rw [this]; linarith)
  have hF'eq : (F.observation.history N).activeStage
      ⟨τ₀ - r / 2, (hJh _ (hJ'sub ht₁)).1, (hJh _ (hJ'sub ht₁)).2⟩ = F' :=
    hF' _ (hJh _ (hJ'sub ht₁)).1 (hJh _ (hJ'sub ht₁)).2 ht₁.2.1 (by linarith)
  have hFs : Fs ≤ F' := by
    have := (hst _ (hJh _ (hJ'sub ht₁)).1 (hJh _ (hJ'sub ht₁)).2 (hJ'sub ht₁)).1
    rwa [hF'eq] at this
  have hLs : (F.observation.history N).activeStage ⟨τ₀, h0, h1⟩ ≤ Ls := (hst τ₀ h0 h1 hτJ).2
  have hF'L : F' ≤ (F.observation.history N).activeStage ⟨τ₀, h0, h1⟩ := by
    rw [← hF'eq]
    exact (F.observation.history N).activeStage_mono
      (show (⟨τ₀ - r / 2, (hJh _ (hJ'sub ht₁)).1, (hJh _ (hJ'sub ht₁)).2⟩ :
        Icc (0 : ℝ) (F.observation.history N).horizon) ≤ ⟨τ₀, h0, h1⟩ from by
          change τ₀ - r / 2 ≤ τ₀
          linarith)
  have hleft : ∀ t (h0' : 0 ≤ t) (h1' : t ≤ (F.observation.history N).horizon), t ∈ J' → t < τ₀ →
      (F.observation.history N).activeStage ⟨t, h0', h1'⟩ = F' :=
    fun t h0' h1' ht hlt => hF' t h0' h1' ht.2.1 hlt
  have hright : ∀ t (h0' : 0 ≤ t) (h1' : t ≤ (F.observation.history N).horizon), t ∈ J' →
      τ₀ ≤ t → (F.observation.history N).activeStage ⟨t, h0', h1'⟩ =
        (F.observation.history N).activeStage ⟨τ₀, h0, h1⟩ :=
    fun t h0' h1' ht hle => hR t h0' h1' hle (by have := ht.2.2; linarith)
  have hst' : ∀ t (h0' : 0 ≤ t) (h1' : t ≤ (F.observation.history N).horizon), t ∈ J' →
      F' ≤ (F.observation.history N).activeStage ⟨t, h0', h1'⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0', h1'⟩ ≤
          (F.observation.history N).activeStage ⟨τ₀, h0, h1⟩ := by
    intro t h0' h1' ht
    rcases lt_or_ge t τ₀ with hlt | hge
    · rw [hleft t h0' h1' ht hlt]; exact ⟨le_rfl, hF'L⟩
    · rw [hright t h0' h1' ht hge]; exact ⟨hF'L, le_rfl⟩
  let D' : ∀ i, SmoothDatum_CPD7 F.observation cores.start (cores.map i) N J' (U i) F'
      ((F.observation.history N).activeStage ⟨τ₀, h0, h1⟩) hF'L := fun i =>
    ((D i).mono hJ'sub hJ'o subset_rfl).restrictRange hF'L hFs hLs
      (fun t ht => hst' t (hJh t (hJ'sub ht)).1 (hJh t (hJ'sub ht)).2 ht)
  have hJh' : ∀ t ∈ J', 0 ≤ t ∧ t ≤ (F.observation.history N).horizon :=
    fun t ht => hJh t (hJ'sub ht)
  refine ⟨N, F', (F.observation.history N).activeStage ⟨τ₀, h0, h1⟩, hF'L, J', U,
    fun i => (D' i).z, hJh', hst', hτJ', hJ'o, fun t ht => hJstart (hJ'sub ht), hUo, hSU,
    fun i t ht hts => hUd i t (hJ'sub ht) hts, fun i => (D' i).smooth, ?_, hleft, hright⟩
  intro i t ht hts y hy
  exact windowEmbed_agrees_SG F.observation N F'
    ((F.observation.history N).activeStage ⟨τ₀, h0, h1⟩) hF'L J' hJh' hst' (cores.map i)
    (D' i).toLocalDatum_CPD6 t ht y hy

end Tight

end GC.LongTime.CuspP1
