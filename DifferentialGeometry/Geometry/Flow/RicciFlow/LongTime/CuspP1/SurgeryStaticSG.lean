import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowBuild
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelHistory

/-!
# 手术时刻的 static identification（IMS07 / IAU02 的 Lean 落点，G1，S-A14-SURGERY）

`exists_smoothWindow_CPD7`（`ExteriorWindowBuild.lean`）把有限个 `PersistentModelPatch`
（`cores.static_patches`）粘成一个窗口：固定 history `N`、stage 区间 `[Fs, Ls]`、开时间集 `J`
（`τ₀ ∈ J`，`τ₀` 可以是 event 时刻）、`z i : ℝ × model → D`，其中
`D = backwardSurvivorDomain Fs Ls`（`stage Ls` 的开子集，与 `t` 无关）。本文件把它改写成
IMS07 需要的 "同一个 `D` 开嵌入到每个 `postStage t`" 的形状：

* `windowEmbed_SG`：`ι_t : D → (postStage t).Carrier`，`ι_t = (stage/slice 恒等) ∘ Φ_{active t}`；
* `windowEmbed_isOpenEmbedding_SG` / `_contMDiff_SG` / `_isLocalDiffeomorph_SG`；
* `exists_partialDiffeomorph_of_open_embeddings_SG`：两个开嵌入给出 `PartialDiffeomorph ψ`，
  `ψ ∘ f = g`，`source = range f`，`target = range g`；
* `exists_static_identification_SG`：主定理（`ι_t (z i (t, y)) = cores.map i t y`，
  `ψ_{t₁ t₂}`；事件时刻 `t₀` 两侧 `postStage` 的类型不同，`ψ` 正是跨 event 的 identification）。

度量方面只有 `windowEmbed_metric_crossing_SG`（事件处的等距，直接来自
`backwardSurvivorMap_metric_crossing`）；t 方向的连续性不在本文件。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u v w

section Generic

/-- 两个（光滑、单射的）local diffeomorphism `f : X → M`、`g : X → N` 给出
`M ⊃ range f` 到 `N ⊃ range g` 的 `PartialDiffeomorph ψ`，`ψ ∘ f = g`。 -/
theorem exists_partialDiffeomorph_of_open_embeddings_SG
    {X : Type u} {M : Type v} {N : Type w}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [Nonempty X]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : X → M) (g : X → N)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g)
    (hfi : Function.Injective f) (hgi : Function.Injective g) :
    ∃ ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
      ψ.source = range f ∧ ψ.target = range g ∧ ∀ x, ψ (f x) = g x := by
  let e₁ := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hf hfi
  let e₂ := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage g hg hgi
  let x₀ : X := Classical.arbitrary X
  let i₁ := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) hf.image ⟨e₁ x₀⟩
  let i₂ := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) hg.image ⟨e₂ x₀⟩
  let ψ := (i₁.symm.trans (e₁.symm.trans e₂).toPartialDiffeomorph).trans i₂
  have h1 : i₁.target = (hf.image : Set M) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have h2 : i₂.target = (hg.image : Set N) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hs : ψ.source = (hf.image : Set M) := by
    ext x
    change ((x ∈ i₁.target ∧ i₁.symm x ∈ (univ : Set hf.image)) ∧
      (e₁.symm.trans e₂) (i₁.symm x) ∈ (univ : Set hg.image)) ↔ x ∈ hf.image
    simp only [mem_univ, and_true, h1]
    rfl
  have ht : ψ.target = (hg.image : Set N) := by
    ext y
    change (y ∈ i₂.target ∧
      i₂.symm y ∈ (i₁.symm.trans (e₁.symm.trans e₂).toPartialDiffeomorph).target) ↔
        y ∈ hg.image
    constructor
    · rintro ⟨h, -⟩
      rwa [h2] at h
    · intro hy
      refine ⟨by rwa [h2], ?_⟩
      change (i₂.symm y ∈ (e₁.symm.trans e₂).toPartialDiffeomorph.target ∧
        (e₁.symm.trans e₂).toPartialDiffeomorph.symm (i₂.symm y) ∈ i₁.symm.target)
      exact ⟨trivial, trivial⟩
  have hv : ∀ x, ψ (f x) = g x := by
    intro x
    have hfx : f x ∈ hf.image := ⟨x, rfl⟩
    have hi : i₁.symm (f x) = ⟨f x, hfx⟩ :=
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hfx
    change (e₂ (e₁.symm (i₁.symm (f x))) : N) = g x
    rw [hi]
    have : e₁ x = ⟨f x, hfx⟩ := rfl
    rw [← this, Diffeomorph.symm_apply_apply]
    rfl
  exact ⟨ψ, by rw [hs]; rfl, by rw [ht]; rfl, hv⟩

end Generic

section Window

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- 窗口里的开嵌入 `ι_t : D → (postStage t).Carrier`：`D = backwardSurvivorDomain Fs Ls`
（与 `t` 无关），`ι_t = (stage active t = postStage t 的恒等) ∘ Φ_{active t}`。 -/
def windowEmbed_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (t : ℝ) (ht : t ∈ J) :
    (T.history N).backwardSurvivorDomain Fs Ls hFL → (postStage T t).Carrier :=
  fun w => (carrierHomeo_CPD2
    (postStage_eq_stage_active_CPD2 T N ⟨t, (hJh t ht).1, (hJh t ht).2⟩).symm)
      ((T.history N).backwardSurvivorMap Fs Ls hFL
        ((T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩)
        (hst t (hJh t ht).1 (hJh t ht).2 ht).1 (hst t (hJh t ht).1 (hJh t ht).2 ht).2 w)

variable (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)

theorem carrierHomeo_comp_isLocalDiffeomorph_SG {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {A B : OrientedThreeStage.{u}} (h : A = B)
    (f : X → A.Carrier) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x => carrierHomeo_CPD2 h (f x)) := by
  subst h
  exact hf

theorem windowEmbed_isLocalDiffeomorph_SG (t : ℝ) (ht : t ∈ J) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) :=
  carrierHomeo_comp_isLocalDiffeomorph_SG _ _
    ((T.history N).backwardSurvivorMap_isLocalDiffeomorph Fs Ls hFL _ _ _)

theorem windowEmbed_injective_SG (t : ℝ) (ht : t ∈ J) :
    Function.Injective (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) :=
  (Homeomorph.injective _).comp ((T.history N).backwardSurvivorMap_injective Fs Ls hFL _ _ _)

theorem windowEmbed_isOpenEmbedding_SG (t : ℝ) (ht : t ∈ J) :
    Topology.IsOpenEmbedding (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) :=
  (carrierHomeo_CPD2
    (postStage_eq_stage_active_CPD2 T N ⟨t, (hJh t ht).1, (hJh t ht).2⟩).symm).isOpenEmbedding.comp
      (isOpenEmbedding_survivorMap_CPD7 _ _ _ _ _ _ _)

theorem windowEmbed_contMDiff_SG (t : ℝ) (ht : t ∈ J) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) :=
  (windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst t ht).contMDiff

/-- `ι_t` 把窗口里的点族 `z (t, y)` 送到实际的 `m t y`（`m = cores.map i`）。 -/
theorem windowEmbed_agrees_SG {H : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ}
    (m : ∀ t : ℝ, T₀ ≤ t → H.Carrier → (postStage T t).Carrier) {U : Set H.Carrier}
    (D : LocalDatum_CPD6 T T₀ m N J U Fs Ls hFL) (t : ℝ) (ht : t ∈ J) (y : H.Carrier)
    (hy : y ∈ U) :
    windowEmbed_SG T N Fs Ls hFL J hJh hst t ht (D.z (t, y)) = m t (D.hJ t ht).1 y :=
  carrierHomeo_eq_of_heq_CPD2 _ _ _ (D.agrees t ht y hy)

/-- 任意两个窗口时刻 `t₁ t₂ ∈ J`：`ι_{t₁}`、`ι_{t₂}` 给出 `postStage t₁ ⊃ range ι_{t₁}` 到
`postStage t₂ ⊃ range ι_{t₂}` 的 `PartialDiffeomorph ψ`（`D` 非空时），`ψ ∘ ι_{t₁} = ι_{t₂}`。
跨 event（`t₁ < t₀ ≤ t₂`）时两个 `postStage` 是不同的 3-流形，`ψ` 就是 "unscathed 区域" 上的
static identification。 -/
theorem exists_window_partialDiffeomorph_SG
    (hD : Nonempty ((T.history N).backwardSurvivorDomain Fs Ls hFL))
    (t₁ t₂ : ℝ) (h₁ : t₁ ∈ J) (h₂ : t₂ ∈ J) :
    ∃ ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) (postStage T t₁).Carrier (postStage T t₂).Carrier ∞,
      ψ.source = range (windowEmbed_SG T N Fs Ls hFL J hJh hst t₁ h₁) ∧
      ψ.target = range (windowEmbed_SG T N Fs Ls hFL J hJh hst t₂ h₂) ∧
      ∀ w, ψ (windowEmbed_SG T N Fs Ls hFL J hJh hst t₁ h₁ w) =
        windowEmbed_SG T N Fs Ls hFL J hJh hst t₂ h₂ w :=
  exists_partialDiffeomorph_of_open_embeddings_SG _ _
    (windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst t₁ h₁)
    (windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst t₂ h₂)
    (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst t₁ h₁)
    (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst t₂ h₂)

end Window

section Main

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **手术时刻的 static identification（G1 主定理）。** 对任意 `τ₀ > cores.start`（`τ₀` 可以是
event 时刻）与 `domain i τ₀` 里的紧集族 `S i`，存在 history `N`、stage 区间 `[Fs, Ls]`、开的
OrdConnected 时间集 `J ∋ τ₀`、开集 `U i ⊇ S i`、光滑点族 `z i : J × U i → D`
（`D = backwardSurvivorDomain Fs Ls`，与 `t` 无关），使得对每个 `t ∈ J`：
`ι_t : D → postStage t` 是光滑开嵌入，`ι_t (z i (t, y)) = cores.map i t y`（`y ∈ U i`），并且
`D` 非空时任意 `t₁ t₂ ∈ J` 之间有 `PartialDiffeomorph ψ`，`ψ ∘ ι_{t₁} = ι_{t₂}`。 -/
theorem exists_static_identification_SG (cores : PersistentHyperbolicCores F K) {τ₀ : ℝ}
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
      τ₀ ∈ J ∧ IsOpen J ∧ J.OrdConnected ∧ J ⊆ Ioi cores.start ∧
      (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, ∀ t ∈ J, cores.start ≤ t → U i ⊆ cores.domain i t) ∧
      (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (z i) (J ×ˢ U i)) ∧
      (∀ (t : ℝ) (ht : t ∈ J),
        Topology.IsOpenEmbedding
            (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht) ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht)) ∧
      (∀ i (t : ℝ) (ht : t ∈ J) (hts : cores.start ≤ t) (y : (cores.model i).Carrier),
        y ∈ U i → windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z i (t, y)) =
          cores.map i t hts y) ∧
      (Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) →
        ∀ (t₁ t₂ : ℝ) (h₁ : t₁ ∈ J) (h₂ : t₂ ∈ J),
          ∃ ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) (postStage F.observation t₁).Carrier
              (postStage F.observation t₂).Carrier ∞,
            ψ.source = range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₁ h₁) ∧
            ψ.target = range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₂ h₂) ∧
            ∀ w, ψ (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₁ h₁ w) =
              windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₂ h₂ w) := by
  obtain ⟨N, Fs, Ls, hFL, J, U, D, hτJ, hJo, hJstart, hJord, hUo, hSU, hUd, hJh, hst⟩ :=
    exists_smoothWindow_CPD7 cores hτ₀ S hS hdom
  refine ⟨N, Fs, Ls, hFL, J, U, fun i => (D i).z, hJh, hst, hτJ, hJo, hJord, hJstart, hUo, hSU,
    hUd, fun i => (D i).smooth, fun t ht => ⟨windowEmbed_isOpenEmbedding_SG _ N Fs Ls hFL J hJh hst
      t ht, windowEmbed_contMDiff_SG _ N Fs Ls hFL J hJh hst t ht⟩, ?_, ?_⟩
  · intro i t ht hts y hy
    exact windowEmbed_agrees_SG F.observation N Fs Ls hFL J hJh hst (cores.map i)
      (D i).toLocalDatum_CPD6 t ht y hy
  · intro hD t₁ t₂ h₁ h₂
    exact exists_window_partialDiffeomorph_SG F.observation N Fs Ls hFL J hJh hst hD t₁ t₂ h₁ h₂

/-- consumer（G2 的 `hinj` 的原料）：窗口点族在每个固定时刻 `t ∈ J` 于 `U i` 上单射：
`ι_t` 单射 + `ι_t ∘ z = cores.map i t` + `cores.embedding`。 -/
theorem windowPoint_injOn_SG (cores : PersistentHyperbolicCores F K) (i : Fin cores.count)
    (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
    (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (z : ℝ × (cores.model i).Carrier →
      (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
    (U : Set (cores.model i).Carrier) (t : ℝ) (ht : t ∈ J) (hts : cores.start ≤ t)
    (hUd : U ⊆ cores.domain i t)
    (hag : ∀ y ∈ U, windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t ht (z (t, y)) =
      cores.map i t hts y) :
    InjOn (fun y => z (t, y)) U := by
  intro y hy y' hy' h
  have h1 : cores.map i t hts y = cores.map i t hts y' := by
    rw [← hag y hy, ← hag y' hy']
    exact congrArg _ h
  exact congrArg Subtype.val ((cores.embedding i t hts).isEmbedding.injective
    (a₁ := ⟨y, hUd hy⟩) (a₂ := ⟨y', hUd hy'⟩) h1)

/-- consumer（使用 `exists_static_identification_SG` 的结论）：窗口点族在 `U i` 上逐时刻单射。 -/
theorem exists_static_identification_injOn_SG (cores : PersistentHyperbolicCores F K) {τ₀ : ℝ}
    (hτ₀ : cores.start < τ₀) (S : ∀ i, Set (cores.model i).Carrier)
    (hS : ∀ i, IsCompact (S i)) (hdom : ∀ i, S i ⊆ cores.domain i τ₀) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (J : Set ℝ) (U : ∀ i, Set (cores.model i).Carrier)
      (z : ∀ i, ℝ × (cores.model i).Carrier →
        (F.observation.history N).backwardSurvivorDomain Fs Ls hFL),
      τ₀ ∈ J ∧ IsOpen J ∧ (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (z i) (J ×ˢ U i)) ∧
      ∀ i, ∀ t ∈ J, InjOn (fun y => z i (t, y)) (U i) := by
  obtain ⟨N, Fs, Ls, hFL, J, U, z, hJh, hst, hτJ, hJo, -, hJstart, hUo, hSU, hUd, hz, -, hag, -⟩ :=
    exists_static_identification_SG cores hτ₀ S hS hdom
  exact ⟨N, Fs, Ls, hFL, J, U, z, hτJ, hJo, hUo, hSU, hz, fun i t ht =>
    windowPoint_injOn_SG cores i N Fs Ls hFL J hJh hst (z i) (U i) t ht (hJstart ht).le
      (hUd i t ht (hJstart ht).le) (fun y hy => hag i t ht (hJstart ht).le y hy)⟩

end Main

end GC.LongTime.CuspP1
