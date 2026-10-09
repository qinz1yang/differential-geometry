import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandPostNK2

/-!
# G3 的 consumer（S-W-NECK-2，后缀 `_NK2`）

R3 全链：SURGERY-2 `exists_window_separation_SG2`（分离 `(KD, U, V)`）+ G3
`scalar_nonneg_on_retained_slab_NK2`（`{0 ≤ z_s ≤ 50}` 上 `R_post ≥ 0`）+ IMS06 G10 的集合版 ⑧
（collar `R_post < 0`）：`γ_s ⊆ range ι_s` 且 `hneg` 时 `γ_s ⊆ U`。`hneg` 是唯一剩下的显式前提
（`cores.metric_error` 的 `C²` 推论，O-W-IMS06 的 ⑧ 余项）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

/-- **R3 全链（modulo `hneg`）**：`∃ KD`（紧，与 `s` 无关）、`∃ d > 0`，`s ∈ J ∩ [τ₀ − d, τ₀)` 时存在开不交
`U V ⊆ M_s`，`M_s ∖ ⋃_b e_s '' Σ_b ⊆ U ∪ V`，`U ⊆ ι_s '' interior KD`，且 `γ_s ⊆ U`。 -/
theorem exists_window_separation_gamma_NK2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (N : ℕ) (i : Fin (F.observation.history N).eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord (F.observation.history N) i p)
    (hcol : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      100 < ((R.static b).delta)⁻¹)
    (hδ : ∀ b : ((F.observation.history N).event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000)
    (hFL : i.castSucc ≤ i.succ) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      i.castSucc ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ i.succ)
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ KD : Set ((F.observation.history N).backwardSurvivorDomain i.castSucc i.succ hFL),
      IsCompact KD ∧ ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs : s ∈ J)
        (hact : (F.observation.history N).activeStage ⟨s, (hJh s hs).1, (hJh s hs).2⟩ =
          i.castSucc),
        (F.observation.history N).time i.succ - d ≤ s →
        s < (F.observation.history N).time i.succ → ∀ hsM : M.exterior.start ≤ s,
        (∀ q ∈ cores.map M.model s (M.exterior.after_cores.trans hsM) ''
          riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
            (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) q < 0) →
        (∀ θ : loopCircle, M.transported s hsM θ ∈
          range (windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst s hs)) →
        ∃ U V : Set (postStage F.observation s).Carrier, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
          U ⊆ windowEmbed_SG F.observation N i.castSucc i.succ hFL J hJh hst s hs ''
            interior KD ∧
          (∀ x, (∀ b, x ∉ sliceHomeo_SG2 F.observation N i s (hJh s hs).1 (hJh s hs).2 hact ''
              neckSlab_SG2 R b {50}) → x ∈ U ∪ V) ∧
          ∀ θ : loopCircle, M.transported s hsM θ ∈ U := by
  obtain ⟨KD, hKD, hsep⟩ := exists_window_separation_SG2 F.observation N i hFL J hJh hst R hcol
  obtain ⟨d, hd, hnn⟩ := scalar_nonneg_on_retained_slab_NK2 F.observation N i R hδ
  refine ⟨KD, hKD, d, hd, fun s hs hact hs1 hs2 hsM hneg hag => ?_⟩
  obtain ⟨U, V, hU, hV, hUV, hUK, hsepUV, hcrit⟩ := hsep s hs hact
  refine ⟨U, V, hU, hV, hUV, hUK, hsepUV, fun θ => hcrit _ (hag θ) ?_⟩
  exact transported_not_mem_of_scalar_nonneg_IM6 M hsM hneg
    (fun b => sliceHomeo_SG2 F.observation N i s (hJh s hs).1 (hJh s hs).2 hact ''
      neckSlab_SG2 R b (Icc 0 50))
    (fun b => hnn s (hJh s hs).1 (hJh s hs).2 hact hs1 hs2 b) θ

end GC.LongTime.CuspP1
