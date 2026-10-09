import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTightSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryMetricTpwSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportTopSG

/-!
# 完整 TPW packet（G4，S-A14-SURGERY）：手术时刻左侧的 transport + hmetric

`exists_tpw_Top_WA`（O-W-ASSEMBLY 的 Top 拷贝，原件 S-A14-SURGERY G4 `exists_tpw_SG`）：
对 `M : PrescribedCuspMeridianTop_CPQ cores` 与 `M.exterior.start < τ₀`（τ₀ 可以是
event 时刻）：tight window（`Fs = activeStage s`，`s < τ₀`；`Ls = activeStage τ₀`）、
`D = backwardSurvivorDomain Fs Ls` 上的紧支撑 isotopy `Φ`，以及 **对任意紧 `KD ⊆ D`、`ε > 0`**
的 `η`：∀ `s ∈ [a, b]`、`s < τ₀`、`|s - τ₀| < η`，`K₀ := ι_s '' interior KD` 上

1. `K₀` 开；2. `P_{s→τ₀}` 在 `K₀` 上 `ContMDiffOn`；
3. `MapsTo P (K₀ ∩ region s) (region τ₀)`；4. `P ∘ M.transported s = M.transported τ₀`；
5. `∀ p ∈ ι_s '' KD, ∀ w, g_{τ₀}(dP w, dP w) ≤ e^ε g_s(w, w)`。

`K₀` 不藏进 `∃`，由消费者以 `KD` 取（`ι_s '' KD ⊇ K₀`）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology GC.Endpoint
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Tpw

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **完整 TPW packet（左侧，手术时刻）。** -/
theorem exists_tpw_Top_WA (cores : PersistentHyperbolicCores F K)
    (M : PrescribedCuspMeridianTop_CPQ cores) {τ₀ : ℝ} (hτ₀ : M.exterior.start < τ₀) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (J : Set ℝ) (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
      (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
          (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
      (hτJ : τ₀ ∈ J) (a b : ℝ) (hJab : Icc a b ⊆ J) (hτab : τ₀ ∈ Icc a b)
      (hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t)
      (Φ : ℝ → ℝ → (F.observation.history N).backwardSurvivorDomain Fs Ls hFL →
        (F.observation.history N).backwardSurvivorDomain Fs Ls hFL)
      (C : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL)),
      a < τ₀ ∧ τ₀ < b ∧ IsOpen J ∧
      Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) ∧ IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × (F.observation.history N).backwardSurvivorDomain Fs Ls hFL =>
          Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → t < τ₀ →
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Fs) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J → τ₀ ≤ t →
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ = Ls) ∧
      ∀ KD : Set ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL), IsCompact KD →
        ∀ ε : ℝ, 0 < ε → ∃ η > 0, ∀ (s : ℝ) (hs : s ∈ Icc a b), s < τ₀ → |s - τ₀| < η →
          ∀ w₀ : (F.observation.history N).backwardSurvivorDomain Fs Ls hFL,
            IsOpen (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs) ''
              interior KD) ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞
              (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ (hJab hs) hτJ w₀)
              (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs) '' interior KD) ∧
            MapsTo (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ (hJab hs) hτJ w₀)
              (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs) '' interior KD ∩
                M.exterior.region s) (M.exterior.region τ₀) ∧
            (∀ θ, windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ (hJab hs) hτJ w₀
                (M.transported s (hE s hs) θ) = M.transported τ₀ (hE τ₀ hτab) θ) ∧
            ∀ p ∈ windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s (hJab hs) '' KD,
              ∀ w : TangentSpace (𝓡 3) p,
                (postMetric F.observation τ₀).inner
                    (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ (hJab hs) hτJ
                      w₀ p)
                    (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG F.observation N Fs Ls hFL J hJh hst
                      Φ s τ₀ (hJab hs) hτJ w₀) p w)
                    (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG F.observation N Fs Ls hFL J hJh hst
                      Φ s τ₀ (hJab hs) hτJ w₀) p w) ≤
                  Real.exp ε * (postMetric F.observation s).inner p w w := by
  have hEs : M.exterior.start ≤ τ₀ := hτ₀.le
  have hcs : cores.start < τ₀ := lt_of_le_of_lt M.exterior.after_cores hτ₀
  have hSc : ∀ i, IsCompact (range (M.exterior.truncation i).inclusion) := fun i =>
    isCompact_range (M.exterior.truncation i).inclusion.continuous
  have hdom : ∀ i, range (M.exterior.truncation i).inclusion ⊆ cores.domain i τ₀ :=
    fun i y hy => cores.advertised_ball i τ₀ (M.exterior.after_cores.trans hEs)
      (M.exterior.in_ball i τ₀ hEs hy)
  obtain ⟨N, Fs, Ls, hFL, J, U, z, hJh, hst, hτJ, hJo, hJstart, hUo, hSU, hUd, hz, hag, hleft,
      hright⟩ :=
    exists_tight_window_SG cores hcs (fun i => range (M.exterior.truncation i).inclusion)
      hSc hdom
  have hJ' : IsOpen (J ∩ Ioi M.exterior.start) := hJo.inter isOpen_Ioi
  obtain ⟨l, u, ⟨hl, hu⟩, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ'.mem_nhds ⟨hτJ, hτ₀⟩)
  obtain ⟨a, b, hτab, hIcc⟩ : ∃ a b : ℝ, (a < τ₀ ∧ τ₀ < b) ∧
      Icc a b ⊆ J ∩ Ioi M.exterior.start :=
    ⟨(l + τ₀) / 2, (τ₀ + u) / 2, ⟨by linarith, by linarith⟩,
      fun t ht => hIoo ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hJab : Icc a b ⊆ J := fun t ht => (hIcc ht).1
  have hE : ∀ t ∈ Icc a b, M.exterior.start ≤ t := fun t ht => (hIcc ht).2.le
  have hτab' : τ₀ ∈ Icc a b := ⟨hτab.1.le, hτab.2.le⟩
  obtain ⟨Φ, C, hCc, hsm, hself, hcoc, hsupp, hmap⟩ := exists_window_isotopy_SG cores N Fs Ls hFL
    J hJh hst z U (fun i => range (M.exterior.truncation i).inclusion) hJo hJstart hUo hSc hSU hUd
    hz hag (a := a) (b := b) (hτab.1.le.trans hτab.2.le) hJab
  have hnon : Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) :=
    ⟨z M.model (τ₀, (cores.model M.model).basepoint)⟩
  refine ⟨N, Fs, Ls, hFL, J, hJh, hst, hτJ, a, b, hJab, hτab', hE, Φ, C, hτab.1, hτab.2, hJo,
    hnon, hCc, hsm, hself, hcoc, hsupp, hleft, hright, ?_⟩
  intro KD hKD ε hε
  obtain ⟨η, hη, hmet⟩ := window_tpw_metric_left_SG F.observation N Fs Ls hFL J hJh hst
    (cores.start_pos.trans hcs) hτJ hJo Φ hself hsm hKD hε
  refine ⟨η, hη, fun s hs hlt hd w₀ => ?_⟩
  have hsJ : s ∈ J := hJab hs
  have hΦ : ∀ i, ∀ x ∈ range (M.exterior.truncation i).inclusion,
      Φ s τ₀ (z i (s, x)) = z i (τ₀, x) := fun i x hx => hmap i s hs τ₀ hτab' x hx
  have hΦ' : ∀ i, ∀ x ∈ range (M.exterior.truncation i).inclusion,
      Φ τ₀ s (z i (τ₀, x)) = z i (s, x) := fun i x hx => hmap i τ₀ hτab' s hs x hx
  have hreg := windowTransport_region_SG cores N Fs Ls hFL J hJh hst z U
    (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s τ₀ hsJ hτJ w₀ M.exterior
    (fun _ _ hx => hx) hΦ hΦ' hself hcoc (hE s hs) hEs
  have hsmooth := windowTransport_contMDiffOn_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ hsJ
    hτJ w₀ hsm
  have hopen := (windowEmbed_isOpenEmbedding_SG F.observation N Fs Ls hFL J hJh hst s hsJ)
  refine ⟨hopen.isOpenMap _ isOpen_interior, hsmooth.mono (image_subset_range _ _), ?_, ?_,
    hmet s hsJ hlt hd w₀⟩
  · intro p hp
    have hmem := mem_image_of_mem
      (windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φ s τ₀ hsJ hτJ w₀)
      (show p ∈ M.exterior.region s ∩
        range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst s hsJ) from
        ⟨hp.2, image_subset_range _ _ hp.1⟩)
    rw [hreg] at hmem
    exact hmem.1
  · intro θ
    exact windowTransport_transported_Top_SG cores N Fs Ls hFL J hJh hst z U
      (fun i => range (M.exterior.truncation i).inclusion) hSU hag Φ s τ₀ hsJ hτJ w₀
      M (fun _ hx => hx) (hΦ M.model) (hE s hs) hEs θ

end Tpw

end GC.LongTime.CuspP1
