import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop

/-!
# G2 的 Top 版本（S-A14-SURGERY，(c7)）

`exists_surgery_transport_SG` / `exists_tpw_nonmetric_SG` / `windowTransport_transported_SG` 的证明只用
`exterior / model / port / loop / transported / prescribed` 这些字段，所以对
`PrescribedCuspMeridianTop_CPQ`（`spans` 换成 `fills`）逐字成立。下面三个定理是
`SurgeryTransportSG.lean` 里同名定理逐字拷贝，仅把 `PrescribedCuspMeridian` 换成
`PrescribedCuspMeridianTop_CPQ`、名字加 `_Top`（Top ⇒ PrescribedCuspMeridian 需要 `hP2`，不能 cast）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology GC.Endpoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

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

/-- `P_{s→t}` 把 prescribed 曲线 `M.transported s` 送到 `M.transported t`
（`S` 取 `range (trunc i).inclusion`，cusp 环面 `cuspMap (·, halfZero)` 落在其中）。 -/
theorem windowTransport_transported_Top_SG (M : PrescribedCuspMeridianTop_CPQ cores)
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

/-- **手术时刻的 smooth transport（G2 主定理）。** 对 `M : PrescribedCuspMeridianTop_CPQ cores` 与
`τ₀ > M.exterior.start`（`τ₀` 可以是 event 时刻）：存在 G1 的窗口、`a < τ₀ < b`、`D` 上紧支撑
joint C^∞ 的 isotopy `Φ`（支撑 `C` 紧），使得 ∀ `s t ∈ [a, b]`，`P := P_{s→t}`：
开集 `range ι_s ⊆ postStage s` 上 `P` 光滑、单射，双射地送到 `range ι_t ⊆ postStage t`；
`P (ι_s w) = ι_t w`（`w ∉ C`，即在支撑外就是静态识别）；
`P ∘ M.transported s = M.transported t`；`region` 对应 `P '' (region s ∩ range ι_s) =
region t ∩ range ι_t`。`s < τ₀ ≤ t` 且 `τ₀` 是 event 时刻时 `P` 就是 pre-surgery 开集到
post-surgery 开集的 transport（Route W 的左侧 TPW：`K := range ι_s` 开）。 -/
theorem exists_surgery_transport_Top_SG (cores : PersistentHyperbolicCores F K)
    (M : PrescribedCuspMeridianTop_CPQ cores) {τ₀ : ℝ} (hτ₀ : M.exterior.start < τ₀) :
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
    exact windowTransport_transported_Top_SG cores N Fs Ls hFL J hJh hst z U
      (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s t (hJab hs) (hJab ht) w₀
      M (fun _ hx => hx) (hΦ M.model) (hE s hs) (hE t ht) x
  · exact windowTransport_region_SG cores N Fs Ls hFL J hJh hst z U
      (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s t (hJab hs) (hJab ht)
      w₀ M.exterior (fun _ _ hx => hx) hΦ hΦ' hself hcoc (hE s hs) (hE t ht)

/-- consumer（Route W 的 TPW packet 的 **非度量** 五个字段，对应 `smoothCompetitor_transport_K8`
的 `hK hφ hW hγ`）：`K₀ := range ι_s` 开、`φ` 在 `K₀` 上光滑、`MapsTo φ (K₀ ∩ region s) (region t)`、
`φ ∘ M.transported s = M.transported t`。`hmetric`（`φ^* g_t ≤ e^ε g_s` on `K₀' ⋐ K₀`）是
metric C⁰ 连续性（sheet SG-5），不在 G2。 -/
theorem exists_tpw_nonmetric_Top_SG (cores : PersistentHyperbolicCores F K)
    (M : PrescribedCuspMeridianTop_CPQ cores) {τ₀ : ℝ} (hτ₀ : M.exterior.start < τ₀) :
    ∃ (a b : ℝ) (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t), a < τ₀ ∧ τ₀ < b ∧
      ∀ (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b),
        ∃ (K₀ : Set (postStage F.observation s).Carrier)
          (φ : (postStage F.observation s).Carrier → (postStage F.observation t).Carrier),
          IsOpen K₀ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K₀ ∧
          MapsTo φ (K₀ ∩ M.exterior.region s) (M.exterior.region t) ∧
          ∀ θ, φ (M.transported s (hE s hs) θ) = M.transported t (hE t ht) θ := by
  obtain ⟨N, Fs, Ls, hFL, J, hJh, hst, a, b, hJab, hE, Φ, C, hτa, hτb, ⟨w₀⟩, hCc, hsm, hself, hcoc,
    hsupp, hall⟩ := exists_surgery_transport_Top_SG cores M hτ₀
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
