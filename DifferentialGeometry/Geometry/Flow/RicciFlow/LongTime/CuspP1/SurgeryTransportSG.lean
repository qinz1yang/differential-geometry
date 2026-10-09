import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryStaticSG

/-!
# 手术时刻的 smooth transport `P_t`（G2，S-A14-SURGERY）

G1（`SurgeryStaticSG.lean`）把窗口写成 "同一个 `D = backwardSurvivorDomain Fs Ls` 经开嵌入
`ι_t` 进入每个 `postStage t`，`cores.map i t = ι_t ∘ z i (t, ·)`"。CP1-D5 的
`exists_ambient_isotopy_of_smooth_families_CPD5` 在固定流形 `D` 上给出紧支撑、joint C^∞ 的
isotopy `Φ`，`Φ s t (z i (s, x)) = z i (t, x)`；但 `exists_regionHomeo_of_window_CPD7`
只用它产出 homeo，smooth 信息被丢掉。本文件把它保留下来，并给出 IMS07 的 `P_t`：

* `exists_window_isotopy_SG`：discharge `himm / hinj / hdisj`（用 `cores.embedding`、
  `cores.disjoint`、`ι_t` 单射、G1 的 agreement），得到 `D` 上的 `Φ`；
* `windowTransport_SG`：`P_{s→t} := ι_t ∘ Φ_{s,t} ∘ ι_s⁻¹`（`Function.extend`），
  `ContMDiffOn`（开集 `range ι_s` 上）、`InjOn`、`P (ι_s w) = ι_t (Φ s t w)`；
  跨 event 时 `P` 把 pre-stage 的开集 `range ι_s` 送到 post-stage 的 `range ι_t`；
* `windowTransport_core_SG`、`windowTransport_transported_SG`：`P (cores.map i s y) = cores.map i t y`
  与 `P ∘ M.transported s = M.transported t`；
* `windowTransport_region_SG`：`region` 在 `P` 下的对应。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology GC.Endpoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Isotopy

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **窗口上的光滑 isotopy。** 输入就是 G1 `exists_static_identification_SG` 的结论
（窗口 `J, U, z` 与 agreement），输出是 `D` 上紧支撑、joint C^∞ 的 isotopy `Φ`，
`Φ s t` 把 core 在时刻 `s` 的 D-位置 `z i (s,x)` 送到 `z i (t,x)`（`x ∈ S i` 紧集，`s t ∈ [a,b]`）。 -/
theorem exists_window_isotopy_SG (cores : PersistentHyperbolicCores F K) (N : ℕ)
    (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
    (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (z : ∀ i, ℝ × (cores.model i).Carrier →
      (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
    (U S : ∀ i, Set (cores.model i).Carrier)
    (hJo : IsOpen J) (hJstart : J ⊆ Ioi cores.start) (hUo : ∀ i, IsOpen (U i))
    (hSc : ∀ i, IsCompact (S i)) (hSU : ∀ i, S i ⊆ U i)
    (hUd : ∀ i, ∀ t ∈ J, cores.start ≤ t → U i ⊆ cores.domain i t)
    (hz : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (z i) (J ×ˢ U i))
    (hag : ∀ i (t : ℝ) (ht : t ∈ J) (hts : cores.start ≤ t) (y : (cores.model i).Carrier),
      y ∈ U i → windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y)) =
        cores.map i t hts y)
    {a b : ℝ} (hab : a ≤ b) (hJab : Icc a b ⊆ J) :
    ∃ (Φ : ℝ → ℝ → (F.observation.history N).backwardSurvivorDomain Fs Ls hFL →
        (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
      (C : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL)),
      IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × (F.observation.history N).backwardSurvivorDomain Fs Ls hFL =>
          Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ S i, Φ s t (z i (s, x)) = z i (t, x) := by
  have himm : ∀ i, ∀ t ∈ J, ∀ x ∈ U i,
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => z i (t, y)) x) := by
    intro i t ht x hx
    have hts : cores.start ≤ t := (hJstart ht).le
    have hzat : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (z i) (t, x) :=
      (hz i).contMDiffAt ((hJo.prod (hUo i)).mem_nhds ⟨ht, hx⟩)
    have hgat : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => z i (t, y)) x :=
      hzat.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    have hdx : x ∈ cores.domain i t := hUd i t ht hts hx
    have hmap : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (cores.map i t hts) x :=
      (cores.smooth i t hts).contMDiffAt ((cores.domain i t).isOpen.mem_nhds hdx)
    have hinjmap : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (cores.map i t hts) x) :=
      mfderiv_injective_of_subtype_CPD7 (cores.domain i t) _ ⟨x, hdx⟩
        (hmap.mdifferentiableAt (by simp))
        ((cores.embedding i t hts).isImmersion.mfderiv_injective (by decide) ⟨x, hdx⟩)
    have hev : (fun y => windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y)))
        =ᶠ[nhds x] cores.map i t hts := by
      filter_upwards [(hUo i).mem_nhds hx] with y hy
      exact hag i t ht hts y hy
    have h3 : mfderiv (𝓡 3) (𝓡 3)
        (fun y => windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y))) x =
        (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht)
          (z i (t, x))).comp (mfderiv (𝓡 3) (𝓡 3) (fun y => z i (t, y)) x) :=
      mfderiv_comp x
        ((windowEmbed_contMDiff_SG F.observation N Fs Ls hFL J hJh hst t ht).contMDiffAt
          |>.mdifferentiableAt (by simp))
        (hgat.mdifferentiableAt (by simp))
    have h4 := hev.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
    rw [h3] at h4
    have h5 : Function.Injective
        ((mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht)
          (z i (t, x))).comp (mfderiv (𝓡 3) (𝓡 3) (fun y => z i (t, y)) x)) := by
      rw [h4]
      exact hinjmap
    exact Function.Injective.of_comp h5
  have hinj : ∀ i, ∀ t ∈ J, InjOn (fun y => z i (t, y)) (S i) := by
    intro i t ht
    have hts : cores.start ≤ t := (hJstart ht).le
    exact (windowPoint_injOn_SG cores i N Fs Ls hFL J hJh hst (z i) (U i) t ht hts
      (hUd i t ht hts) (fun y hy => hag i t ht hts y hy)).mono (hSU i)
  have hdisj : ∀ i j, i ≠ j → ∀ t ∈ J, ∀ x ∈ S i, ∀ x' ∈ S j, z i (t, x) ≠ z j (t, x') := by
    intro i j hij t ht x hx x' hx' h
    have hts : cores.start ≤ t := (hJstart ht).le
    have h12 : cores.map i t hts x = cores.map j t hts x' := by
      rw [← hag i t ht hts x (hSU i hx), ← hag j t ht hts x' (hSU j hx')]
      exact congrArg _ h
    exact Set.disjoint_left.mp (cores.disjoint t hts hij)
      ⟨x, hUd i t ht hts (hSU i hx), rfl⟩ (h12 ▸ ⟨x', hUd j t ht hts (hSU j hx'), rfl⟩)
  exact exists_ambient_isotopy_of_smooth_families_CPD5 (F := z) hJo hUo hSc hSU hab hJab hz himm
    hinj hdisj

end Isotopy

section Transport

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)

/-- `P_{s→t} := ι_t ∘ Φ_{s,t} ∘ ι_s⁻¹`，在 `range ι_s` 之外用 `ι_t w₀` 补全（只是为了得到全函数）。 -/
def windowTransport_SG
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (s t : ℝ) (hs : s ∈ J) (ht : t ∈ J) (w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL) :
    (postStage T s).Carrier → (postStage T t).Carrier :=
  Function.extend (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs)
    (fun w => windowEmbed_SG T N Fs Ls hFL J hJh hst t ht (Φ s t w))
    (fun _ => windowEmbed_SG T N Fs Ls hFL J hJh hst t ht w₀)

variable
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (s t : ℝ) (hs : s ∈ J) (ht : t ∈ J) (w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL)

theorem windowTransport_apply_SG (w : (T.history N).backwardSurvivorDomain Fs Ls hFL) :
    windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀
        (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs w) =
      windowEmbed_SG T N Fs Ls hFL J hJh hst t ht (Φ s t w) :=
  (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst s hs).extend_apply _ _ w

/-- `Φ s t` 光滑（joint 光滑 isotopy 的一个切片）。 -/
theorem isotopy_slice_contMDiff_SG
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2)) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (Φ s t) :=
  hsm.comp (f := fun y => ((s, t), y)) (contMDiff_const.prodMk contMDiff_id)

/-- `P_{s→t}` 在开集 `range ι_s` 上光滑。 -/
theorem windowTransport_contMDiffOn_SG
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
      (range (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs)) := by
  have : Nonempty ((T.history N).backwardSurvivorDomain Fs Ls hFL) := ⟨w₀⟩
  obtain ⟨ψ, hψs, -, hψ⟩ := exists_partialDiffeomorph_of_open_embeddings_SG
    (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) (id : (T.history N).backwardSurvivorDomain
      Fs Ls hFL → (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst s hs)
    (Diffeomorph.refl (𝓡 3) _ ∞).isLocalDiffeomorph
    (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst s hs) Function.injective_id
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun p => windowEmbed_SG T N Fs Ls hFL J hJh hst t ht (Φ s t (ψ p))) ψ.source :=
    (windowEmbed_contMDiff_SG T N Fs Ls hFL J hJh hst t ht).comp_contMDiffOn
      ((isotopy_slice_contMDiff_SG T N Fs Ls hFL Φ s t hsm).comp_contMDiffOn
        ψ.contMDiffOn_toFun)
  rw [hψs] at hcomp
  refine hcomp.congr ?_
  rintro p ⟨w, rfl⟩
  rw [windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ w, hψ w]
  rfl

/-- isotopy 的 `Φ s t` 单射（左逆 `Φ t s`）。 -/
theorem isotopy_slice_injective_SG
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) :
    Function.Injective (Φ s t) := by
  intro y y' h
  have h1 : ∀ y, Φ t s (Φ s t y) = y := fun y => by rw [hcoc, hself]
  rw [← h1 y, ← h1 y', h]

/-- `P_{s→t}` 在 `range ι_s` 上单射。 -/
theorem windowTransport_injOn_SG
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) :
    InjOn (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
      (range (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs)) := by
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ h
  rw [windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ w,
    windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ w'] at h
  rw [isotopy_slice_injective_SG T N Fs Ls hFL Φ s t hself hcoc
    (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst t ht h)]

/-- `P_{s→t}` 把 `range ι_s` 双射地送到 `range ι_t`。 -/
theorem windowTransport_image_SG
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) :
    windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ ''
        (range (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs)) =
      range (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) := by
  ext q
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨Φ s t w, (windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ w).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨windowEmbed_SG T N Fs Ls hFL J hJh hst s hs (Φ t s v), ⟨_, rfl⟩, ?_⟩
    rw [windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀, hcoc, hself]

end Transport

section Region

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {cores : PersistentHyperbolicCores F K}

/-- `region r` 的成员刻画（`E.start ≤ r`）。 -/
theorem mem_region_iff_SG {E : PersistentCuspExterior cores} {r : ℝ} (hr : E.start ≤ r)
    {p : (postStage F.observation r).Carrier} :
    p ∈ E.region r ↔ ∀ (i : Fin cores.count) (c : (E.truncation i).core.Carrier),
      c ∈ ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier) →
        p ≠ cores.map i r (E.after_cores.trans hr) ((E.truncation i).inclusion c) := by
  simp only [PersistentCuspExterior.region, hr, ↓reduceDIte, mem_compl_iff, mem_iUnion,
    mem_image, not_exists, not_and]
  constructor
  · intro h i c hc hp
    exact h i _ ⟨c, hc, rfl⟩ hp.symm
  · rintro h i _ ⟨c, hc, rfl⟩ hp
    exact h i c hc hp.symm

end Region

section CoreTransport

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (cores : PersistentHyperbolicCores F K) (N : ℕ)
    (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (z : ∀ i, ℝ × (cores.model i).Carrier →
      (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
    (U S : ∀ i, Set (cores.model i).Carrier) (hSU : ∀ i, S i ⊆ U i)
    (hag : ∀ i (t : ℝ) (ht : t ∈ J) (hts : cores.start ≤ t) (y : (cores.model i).Carrier),
      y ∈ U i → windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y)) =
        cores.map i t hts y)
    (Φ : ℝ → ℝ → (F.observation.history N).backwardSurvivorDomain Fs Ls hFL →
      (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
    (s t : ℝ) (hs : s ∈ J) (ht : t ∈ J) (hs' : cores.start ≤ s) (ht' : cores.start ≤ t)
    (w₀ : (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)

include hSU hag

/-- core 的实际位置在 `P_{s→t}` 下对应：`P (cores.map i s x) = cores.map i t x`（`x ∈ S i`）。 -/
theorem windowTransport_core_SG (i : Fin cores.count)
    (hΦ : ∀ x ∈ S i, Φ s t (z i (s, x)) = z i (t, x)) (x : (cores.model i).Carrier)
    (hx : x ∈ S i) :
    windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t hs ht w₀
        (cores.map i s hs' x) = cores.map i t ht' x := by
  rw [← hag i s hs hs' x (hSU i hx), windowTransport_apply_SG F.observation N Fs Ls hFL J hJh hst
    Φ s t hs ht w₀, hΦ x hx, hag i t ht ht' x (hSU i hx)]

/-- `P_{s→t}` 与 `region`：`range ι_s` 内的 `region s` 被双射地送到 `range ι_t` 内的 `region t`。
`S i` 取 `range (E.truncation i).inclusion`。 -/
theorem windowTransport_region_SG (E : PersistentCuspExterior cores)
    (hSE : ∀ i, range (E.truncation i).inclusion ⊆ S i)
    (hΦ : ∀ i, ∀ x ∈ S i, Φ s t (z i (s, x)) = z i (t, x))
    (hΦ' : ∀ i, ∀ x ∈ S i, Φ t s (z i (t, x)) = z i (s, x))
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y)
    (hsE : E.start ≤ s) (htE : E.start ≤ t) :
    windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t hs ht w₀ ''
        (E.region s ∩ range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hs)) =
      E.region t ∩ range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht) := by
  have hinjΦ : ∀ a b, Function.Injective (Φ a b) := fun a b =>
    isotopy_slice_injective_SG F.observation N Fs Ls hFL Φ a b hself hcoc
  have key : ∀ (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) (ha' : E.start ≤ a) (hb' : E.start ≤ b),
      (∀ i, ∀ x ∈ S i, Φ a b (z i (a, x)) = z i (b, x)) → ∀ w,
      windowEmbed_SG F.observation N Fs Ls hFL J hJh hst a ha w ∈ E.region a →
        windowEmbed_SG F.observation N Fs Ls hFL J hJh hst b hb (Φ a b w) ∈ E.region b := by
    intro a b ha hb ha' hb' hΦab w hw
    rw [mem_region_iff_SG hb']
    intro i c hc hp
    rw [mem_region_iff_SG ha'] at hw
    apply hw i c hc
    have hmem : (E.truncation i).inclusion c ∈ S i := hSE i ⟨c, rfl⟩
    have h1 := hag i b hb (E.after_cores.trans hb') _ (hSU i hmem)
    have h2 : Φ a b w = z i (b, (E.truncation i).inclusion c) :=
      windowEmbed_injective_SG F.observation N Fs Ls hFL J hJh hst b hb (hp.trans h1.symm)
    have h3 : w = z i (a, (E.truncation i).inclusion c) :=
      hinjΦ a b (h2.trans (hΦab i _ hmem).symm)
    rw [h3]
    exact hag i a ha (E.after_cores.trans ha') _ (hSU i hmem)
  ext q
  constructor
  · rintro ⟨_, ⟨hr, ⟨w, rfl⟩⟩, rfl⟩
    rw [windowTransport_apply_SG F.observation N Fs Ls hFL J hJh hst Φ s t hs ht w₀ w]
    exact ⟨key s t hs ht hsE htE hΦ w hr, ⟨_, rfl⟩⟩
  · rintro ⟨hq, ⟨v, rfl⟩⟩
    refine ⟨windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hs (Φ t s v),
      ⟨key t s ht hs htE hsE hΦ' v hq, ⟨_, rfl⟩⟩, ?_⟩
    rw [windowTransport_apply_SG F.observation N Fs Ls hFL J hJh hst Φ s t hs ht w₀, hcoc, hself]

/-- `P_{s→t}` 把 prescribed 曲线 `M.transported s` 送到 `M.transported t`
（`S` 取 `range (trunc i).inclusion`，cusp 环面 `cuspMap (·, halfZero)` 落在其中）。 -/
theorem windowTransport_transported_SG (M : PrescribedCuspMeridian cores)
    (hSM : range (M.exterior.truncation M.model).inclusion ⊆ S M.model)
    (hΦ : ∀ x ∈ S M.model, Φ s t (z M.model (s, x)) = z M.model (t, x))
    (hsE : M.exterior.start ≤ s) (htE : M.exterior.start ≤ t) (x : loopCircle) :
    windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t hs ht w₀
        (M.transported s hsE x) = M.transported t htE x := by
  have hmem : (M.exterior.truncation M.model).cuspMap M.port (M.loop x, halfZero) ∈
      S M.model := hSM ⟨(M.exterior.truncation M.model).boundary.torusMap M.port (M.loop x),
        ((M.exterior.truncation M.model).cusp_zero M.port (M.loop x)).symm⟩
  rw [M.prescribed s hsE x, M.prescribed t htE x]
  exact windowTransport_core_SG cores N Fs Ls hFL J hJh hst z U S hSU hag Φ s t hs ht
    (M.exterior.after_cores.trans hsE) (M.exterior.after_cores.trans htE) w₀ M.model hΦ _ hmem

end CoreTransport

section Final

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **手术时刻的 smooth transport（G2 主定理）。** 对 `M : PrescribedCuspMeridian cores` 与
`τ₀ > M.exterior.start`（`τ₀` 可以是 event 时刻）：存在 G1 的窗口、`a < τ₀ < b`、`D` 上紧支撑
joint C^∞ 的 isotopy `Φ`（支撑 `C` 紧），使得 ∀ `s t ∈ [a, b]`，`P := P_{s→t}`：
开集 `range ι_s ⊆ postStage s` 上 `P` 光滑、单射，双射地送到 `range ι_t ⊆ postStage t`；
`P (ι_s w) = ι_t w`（`w ∉ C`，即在支撑外就是静态识别）；
`P ∘ M.transported s = M.transported t`；`region` 对应 `P '' (region s ∩ range ι_s) =
region t ∩ range ι_t`。`s < τ₀ ≤ t` 且 `τ₀` 是 event 时刻时 `P` 就是 pre-surgery 开集到
post-surgery 开集的 transport（Route W 的左侧 TPW：`K := range ι_s` 开）。 -/
theorem exists_surgery_transport_SG (cores : PersistentHyperbolicCores F K)
    (M : PrescribedCuspMeridian cores) {τ₀ : ℝ} (hτ₀ : M.exterior.start < τ₀) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
      (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
      (a b : ℝ) (hJab : Icc a b ⊆ J) (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t)
      (Φ : ℝ → ℝ → (F.observation.history N).backwardSurvivorDomain Fs Ls hFL →
        (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
      (C : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL)),
      a < τ₀ ∧ τ₀ < b ∧
      Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) ∧ IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × (F.observation.history N).backwardSurvivorDomain Fs Ls hFL =>
          Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
        (w₀ : (F.observation.history N).backwardSurvivorDomain Fs Ls hFL),
        IsOpen (range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs))) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞
          (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀)
          (range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs))) ∧
        InjOn (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀)
          (range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs))) ∧
        windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀ ''
            (range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs))) =
          range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t (hJab ht)) ∧
        (∀ w, w ∉ C →
          windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀
              (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs) w) =
            windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t (hJab ht) w) ∧
        (∀ x, windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀
            (M.transported s (hE s hs) x) = M.transported t (hE t ht) x) ∧
        windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀ ''
            (M.exterior.region s ∩
              range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs))) =
          M.exterior.region t ∩
            range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t (hJab ht)) := by
  have hEs : M.exterior.start ≤ τ₀ := hτ₀.le
  have hcs : cores.start < τ₀ := lt_of_le_of_lt M.exterior.after_cores hτ₀
  have hSc : ∀ i, IsCompact (range (M.exterior.truncation i).inclusion) := fun i =>
    isCompact_range (M.exterior.truncation i).inclusion.continuous
  have hdom : ∀ i, range (M.exterior.truncation i).inclusion ⊆ cores.domain i τ₀ :=
    fun i y hy => cores.advertised_ball i τ₀ (M.exterior.after_cores.trans hEs)
      (M.exterior.in_ball i τ₀ hEs hy)
  obtain ⟨N, Fs, Ls, hFL, J, U, z, hJh, hst, hτJ, hJo, -, hJstart, hUo, hSU, hUd, hz, -, hag, -⟩ :=
    exists_static_identification_SG cores hcs (fun i => range (M.exterior.truncation i).inclusion)
      hSc hdom
  have hJ' : IsOpen (J ∩ Ioi M.exterior.start) := hJo.inter isOpen_Ioi
  obtain ⟨l, u, ⟨hl, hu⟩, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ'.mem_nhds ⟨hτJ, hτ₀⟩)
  obtain ⟨a, b, hτab, hIcc⟩ : ∃ a b : ℝ, (a < τ₀ ∧ τ₀ < b) ∧
      Icc a b ⊆ J ∩ Ioi M.exterior.start :=
    ⟨(l + τ₀) / 2, (τ₀ + u) / 2, ⟨by linarith, by linarith⟩,
      fun t ht => hIoo ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hJab : Icc a b ⊆ J := fun t ht => (hIcc ht).1
  have hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t := fun t ht => (hIcc ht).2.le
  obtain ⟨Φ, C, hCc, hsm, hself, hcoc, hsupp, hmap⟩ := exists_window_isotopy_SG cores N Fs Ls hFL
    J hJh hst z U (fun i => range (M.exterior.truncation i).inclusion) hJo hJstart hUo hSc hSU hUd
    hz hag (a := a) (b := b) (hτab.1.le.trans hτab.2.le) hJab
  refine ⟨N, Fs, Ls, hFL, J, hJh, hst, a, b, hJab, hE, Φ, C, hτab.1, hτab.2,
    ⟨z M.model (τ₀, (cores.model M.model).basepoint)⟩, hCc, hsm, hself, hcoc, hsupp, ?_⟩
  intro s hs t ht w₀
  have hΦ : ∀ i, ∀ x ∈ range (M.exterior.truncation i).inclusion,
      Φ s t (z i (s, x)) = z i (t, x) := fun i x hx => hmap i s hs t ht x hx
  have hΦ' : ∀ i, ∀ x ∈ range (M.exterior.truncation i).inclusion,
      Φ t s (z i (t, x)) = z i (s, x) := fun i x hx => hmap i t ht s hs x hx
  refine ⟨(windowEmbed_isOpenEmbedding_SG F.observation N Fs Ls hFL J hJh hst s
      (hJab hs)).isOpen_range,
    windowTransport_contMDiffOn_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht)
      w₀ hsm,
    windowTransport_injOn_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀
      hself hcoc,
    windowTransport_image_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀
      hself hcoc, ?_, ?_, ?_⟩
  · intro w hw
    rw [windowTransport_apply_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht)
      w₀ w, hsupp s t w hw]
  · intro x
    exact windowTransport_transported_SG cores N Fs Ls hFL J hJh hst z U
      (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s t (hJab hs) (hJab ht) w₀
      M (fun _ hx => hx) (hΦ M.model) (hE s hs) (hE t ht) x
  · exact windowTransport_region_SG cores N Fs Ls hFL J hJh hst z U
      (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s t (hJab hs) (hJab ht)
      w₀ M.exterior (fun _ _ hx => hx) hΦ hΦ' hself hcoc (hE s hs) (hE t ht)

/-- consumer（Route W 的 TPW packet 的 **非度量** 五个字段，对应 `smoothCompetitor_transport_K8`
的 `hK hφ hW hγ`）：`K₀ := range ι_s` 开、`φ` 在 `K₀` 上光滑、`MapsTo φ (K₀ ∩ region s) (region t)`、
`φ ∘ M.transported s = M.transported t`。`hmetric`（`φ^* g_t ≤ e^ε g_s` on `K₀' ⋐ K₀`）是
metric C⁰ 连续性（sheet SG-5），不在 G2。 -/
theorem exists_tpw_nonmetric_SG (cores : PersistentHyperbolicCores F K)
    (M : PrescribedCuspMeridian cores) {τ₀ : ℝ} (hτ₀ : M.exterior.start < τ₀) :
    ∃ (a b : ℝ) (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t), a < τ₀ ∧ τ₀ < b ∧
      ∀ (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b),
        ∃ (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation t).Carrier),
          IsOpen K₀ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K₀ ∧
          MapsTo φ (K₀ ∩ M.exterior.region s) (M.exterior.region t) ∧
          ∀ θ, φ (M.transported s (hE s hs) θ) = M.transported t (hE t ht) θ := by
  obtain ⟨N, Fs, Ls, hFL, J, hJh, hst, a, b, hJab, hE, Φ, C, hτa, hτb, ⟨w₀⟩, hCc, hsm, hself, hcoc,
    hsupp, hall⟩ := exists_surgery_transport_SG cores M hτ₀
  refine ⟨a, b, hE, hτa, hτb, fun s hs t ht => ?_⟩
  obtain ⟨hopen, hsmooth, -, -, -, htr, hreg⟩ := hall s hs t ht w₀
  refine ⟨_, _, hopen, hsmooth, ?_, htr⟩
  intro p hp
  have hmem := mem_image_of_mem
    (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s t (hJab hs) (hJab ht) w₀)
    (show p ∈ M.exterior.region s ∩ _ from ⟨hp.2, hp.1⟩)
  rw [hreg] at hmem
  exact hmem.1

end Final

end GC.LongTime.CuspP1
