import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredReplacementR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredJordanDiskR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

/-!
# O-MY-R13 G6c：Morrey 极小盘的双向 exchange ⇒ 等面积、exchange disk 也是极小盘

R13 的面积比较是 source-domain parametrized-area 替换（外审 D-24，允许 `Ω₁ = Ω₂`）：把 `u` 在 `Ω₂` 上换成
`U ∘ B`（G6a 引擎，`A(f̂) = A(u) − A(U|Ω₂) + A(U|Ω₁)`），并反向把 `Ω₁` 上换成 `U ∘ B⁻¹`
（`A(f̌) = A(u) − A(U|Ω₁) + A(U|Ω₂)`）。`u` 是 Morrey 极小盘（`minimizesLipschitz`）⇒ 两式都 `≥ A(u)`
⇒ `A(U|Ω₁) = A(U|Ω₂)`，于是 `A(f̂) = A(u)`，`f̂` 对同 trace 的 Lipschitz 盘也面积极小——这正是 R4C
`fold_seam_conormal_sum_eq_zero_of_minimal_R4C` 的 `hmin` 前提（R13 的 fold 一半）。

* `BilipschitzOn_R13.invFunOn_R13`：bi-Lipschitz 双射的逆仍是 bi-Lipschitz 双射，边界对边界，
  且 `U ∘ B⁻¹ = U` on `∂K₁`。
* **`exists_minimal_exchange_R13`**（G6c 主定理，一般紧集版）。
* **`exists_minimal_exchange_cornered_R13`**：cornered 版（`IsCorneredJordanDisk_R13` 给 null frontier；
  `B` 是 R13-S 的 bi-Lipschitz Schoenflies 映射 `B = b` on `∂Ω₂`，`b` 边界双射，`U ∘ b = U`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- bi-Lipschitz 双射 `B : K₂ → K₁`（边界对边界）的逆 `B' = invFunOn B K₂`：bi-Lipschitz、
`BijOn B' K₁ K₂`、`BijOn B' (∂K₁) (∂K₂)`。 -/
theorem BilipschitzOn_R13.invFunOn_R13 {B : ℂ → ℂ} {K₁ K₂ : Set ℂ} (hB : BilipschitzOn_R13 B K₂)
    (hBK : BijOn B K₂ K₁) (hBfr : BijOn B (frontier K₂) (frontier K₁))
    (hfr₂ : frontier K₂ ⊆ K₂) :
    BilipschitzOn_R13 (Function.invFunOn B K₂) K₁ ∧ BijOn (Function.invFunOn B K₂) K₁ K₂ ∧
      BijOn (Function.invFunOn B K₂) (frontier K₁) (frontier K₂) := by
  obtain ⟨K, hK⟩ := hB
  have hmaps : MapsTo (Function.invFunOn B K₂) K₁ K₂ := hBK.surjOn.mapsTo_invFunOn
  have hright : ∀ y ∈ K₁, B (Function.invFunOn B K₂ y) = y :=
    fun y hy => hBK.surjOn.rightInvOn_invFunOn hy
  have hleft : ∀ x ∈ K₂, Function.invFunOn B K₂ (B x) = x :=
    fun x hx => hBK.injOn.leftInvOn_invFunOn hx
  have hbij : BijOn (Function.invFunOn B K₂) K₁ K₂ := hBK.symm hBK.invOn_invFunOn.symm
  have hfr₁ : frontier K₁ ⊆ K₁ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hBfr.surjOn hy
    exact hBK.mapsTo (hfr₂ hx)
  refine ⟨⟨K, fun x hx y hy => ?_⟩, hbij, ⟨?_, hbij.injOn.mono hfr₁, ?_⟩⟩
  · have h := hK _ (hmaps hx) _ (hmaps hy)
    rw [hright x hx, hright y hy] at h
    exact ⟨h.2, h.1⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hBfr.surjOn hy
    rw [hleft x (hfr₂ hx)]
    exact hx
  · intro x hx
    exact ⟨B x, hBfr.mapsTo hx, hleft x (hfr₂ hx)⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- **G6c 主定理（一般紧集版）**：`u` Morrey 极小；`B : K₂ → K₁` bi-Lipschitz 双射、边界对边界、
边界上 `U ∘ B = U`；`K₁ K₂ ⊆ D°`、边界 null。则 `A(U|K₁) = A(U|K₂)`，且 exchange disk `v`
（`K₂` 上 `= U ∘ B`、`interior K₂` 外 `= u`，同 trace、metric-Lipschitz、`range ⊆ W`）满足
`A(v) = A(u)`，并对同 `diskTrace` 的 metric-Lipschitz 盘面积极小。 -/
theorem exists_minimal_exchange_R13
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    {K₁ K₂ : Set ℂ} (hK₂ : IsCompact K₂)
    (hinside₁ : K₁ ⊆ Metric.ball (0 : ℂ) 1) (hinside₂ : K₂ ⊆ Metric.ball (0 : ℂ) 1)
    (hnull₁ : volume (frontier K₁) = 0) (hnull₂ : volume (frontier K₂) = 0)
    {B : ℂ → ℂ} (hB : BilipschitzOn_R13 B K₂) (hBK : BijOn B K₂ K₁)
    (hBfr : BijOn B (frontier K₂) (frontier K₁))
    (hboundary : ∀ z ∈ frontier K₂, diskExtension u (B z) = diskExtension u z)
    {W : Set M} (huW : Set.range u ⊆ W) :
    riemannianArea g (diskExtension u) K₁ = riemannianArea g (diskExtension u) K₂ ∧
    ∃ (v : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, (z : ℂ) ∈ K₂ → v z = diskExtension u (B z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior K₂ → v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      ∀ w : C(closedDisk, M), diskTrace w = diskTrace v →
        (∃ K : ℝ≥0, ∀ z z' : closedDisk,
          riemannianEDistOf g (w z) (w z') ≤ (K : ℝ≥0∞) * edist z z') →
        riemannianDiskArea g v ≤ riemannianDiskArea g w := by
  have hfr₂ : frontier K₂ ⊆ K₂ := hK₂.isClosed.frontier_subset
  obtain ⟨v, L, hvLip, hvtr, hvW, hvin, hvout, hvA⟩ :=
    exists_bilipschitz_paired_replacement_R13 g u hUext hK₂ hinside₁ hinside₂ hnull₁ hnull₂
      hB hBK hBfr hboundary huW
  obtain ⟨hB', hBK', hBfr'⟩ := hB.invFunOn_R13 hBK hBfr hfr₂
  have hK₁ : IsCompact K₁ := by
    obtain ⟨A, hA, -⟩ := hB.lipschitzOnWith
    rw [← hBK.image_eq]
    exact hK₂.image_of_continuousOn hA.continuousOn
  have hboundary' : ∀ y ∈ frontier K₁,
      diskExtension u (Function.invFunOn B K₂ y) = diskExtension u y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hBfr.surjOn hy
    rw [hBK.injOn.leftInvOn_invFunOn (hfr₂ hx)]
    exact (hboundary x hx).symm
  obtain ⟨v', L', hv'Lip, hv'tr, -, -, -, hv'A⟩ :=
    exists_bilipschitz_paired_replacement_R13 g u hUext hK₁ hinside₂ hinside₁ hnull₂ hnull₁
      hB' hBK' hBfr' hboundary' huW
  obtain ⟨σ, hσ, hσeq⟩ := hu.trace
  have hmin : ∀ w : C(closedDisk, M), diskTrace w = diskTrace u →
      (∃ K : ℝ≥0, ∀ z z' : closedDisk,
        riemannianEDistOf g (w z) (w z') ≤ (K : ℝ≥0∞) * edist z z') →
      riemannianDiskArea g u ≤ riemannianDiskArea g w :=
    fun w hw hwLip => hu.minimizesLipschitz w ⟨σ, hσ, hw.trans hσeq⟩ hwLip
  have h1 := hmin v hvtr ⟨L, hvLip⟩
  have h2 := hmin v' hv'tr ⟨L', hv'Lip⟩
  have heqA : riemannianArea g (diskExtension u) K₁ = riemannianArea g (diskExtension u) K₂ := by
    linarith
  refine ⟨heqA, v, L, hvLip, hvtr, hvW, hvin, hvout, by linarith, ?_⟩
  intro w hw hwLip
  have := hmin w (hw.trans hvtr) hwLip
  linarith

/-- **G6c，cornered 版**：`Ω₁ Ω₂` 是 cornered Jordan 子盘（⇒ null frontier）、`⊆ D°`；`b` 是
`∂Ω₂ → ∂Ω₁` 的双射、`U ∘ b = U`；`B` 是 R13-S 的 bi-Lipschitz Schoenflies 映射（`BijOn B Ω₂ Ω₁`、
`B = b` on `∂Ω₂`）。结论同 `exists_minimal_exchange_R13`（`K₂ = Ω₂`、`K₁ = Ω₁`）。 -/
theorem exists_minimal_exchange_cornered_R13
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ} {C₁ C₂ : Finset ℝ}
    (h₁ : IsCorneredJordanDisk_R13 Ω₁ c₁ C₁) (h₂ : IsCorneredJordanDisk_R13 Ω₂ c₂ C₂)
    (hsub₁ : Ω₁ ⊆ Metric.ball (0 : ℂ) 1) (hsub₂ : Ω₂ ⊆ Metric.ball (0 : ℂ) 1)
    {b : ℂ → ℂ} (hbij : BijOn b (frontier Ω₂) (frontier Ω₁))
    (hfb : ∀ w ∈ frontier Ω₂, diskExtension u (b w) = diskExtension u w)
    {B : ℂ → ℂ} (hB : BilipschitzOn_R13 B Ω₂) (hBK : BijOn B Ω₂ Ω₁) (hBb : EqOn B b (frontier Ω₂))
    {W : Set M} (huW : Set.range u ⊆ W) :
    riemannianArea g (diskExtension u) Ω₁ = riemannianArea g (diskExtension u) Ω₂ ∧
    ∃ (v : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, (z : ℂ) ∈ Ω₂ → v z = diskExtension u (B z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior Ω₂ → v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      ∀ w : C(closedDisk, M), diskTrace w = diskTrace v →
        (∃ K : ℝ≥0, ∀ z z' : closedDisk,
          riemannianEDistOf g (w z) (w z') ≤ (K : ℝ≥0∞) * edist z z') →
        riemannianDiskArea g v ≤ riemannianDiskArea g w :=
  exists_minimal_exchange_R13 hu hUext h₂.1 hsub₁ hsub₂ h₁.volume_frontier h₂.volume_frontier hB
    hBK (hbij.congr hBb.symm) (fun z hz => (congrArg (diskExtension u) (hBb hz)).trans (hfb z hz))
    huW

/-- consumer（`Ω₁ = Ω₂` 允许）：`B = b = id` 时 G6c 给出 exchange disk 与原盘同面积，并且对同 trace 的
metric-Lipschitz 盘面积极小（`Ω` 是任意 `⊆ D°` 的 cornered Jordan 子盘，例如单位圆盘的缩小）。 -/
example {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ} (h : IsCorneredJordanDisk_R13 Ω c Cr)
    (hsub : Ω ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ v : C(closedDisk, M), diskTrace v = diskTrace u ∧
      riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨-, v, -, -, hvtr, -, -, -, hvA, -⟩ :=
    exists_minimal_exchange_cornered_R13 hu hUext h h hsub hsub (bijOn_id _)
      (fun _ _ => rfl) (bilipschitzOn_id_R13 Ω) (bijOn_id Ω) (fun _ _ => rfl)
      (W := Set.univ) (subset_univ _)
  exact ⟨v, hvtr, hvA⟩

end DifferentialGeometry.Geometry
