import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CompletionMetricR7E
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CompletionTransportR7E
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskSmoothLipschitz

/-!
# O-MY-R7E G5：confined solution 的生产（R7-E 存在性，单个度量）

链条（R-MY3 定稿）：
1. G2 `exists_completion_metric_R7E`：`Ĝ` 在 `K°` 上 complete + homogeneously regular；
2. 树里 [V] `exists_morrey_disk`：`Ĝ`-Morrey 盘 `u`（`hspan` 给 `spanningDiskCompetitors` 非空）；
3. G2 的 barrier：`ρ ∘ u ≤ −b − δ`，`Ĝ = G|K°` 在每个 `u z` 的邻域上；
4. G1 jets 版 `isMorreyDisk_of_completion_R7E`：每个 `G|K°`-Lipschitz competitor `v` 取 generic level
   `c ∈ (−b−δ, −b−δ/2)`（G3 的可数例外集之外），`w = r c ∘ v`：像在 `{ρ < −b − δ/2}`（`Ĝ = G`）、
   trace 不变（`r c` 固定 `Γ`）、`Ĝ`-Lipschitz（`lipschitz_change_metric_R7E`）、`A(w) ≤ A(v)`；
   ⇒ `u` 是**原** `G|K°` 的 Morrey 盘。

`exists_confined_morrey_disk_R7E`：`∃ u, IsMorreyDisk (G.restrictOpen K°) Γ u ∧ ρ ∘ u ≤ −b − δ`。
（MYD3 `exists_confined_morrey_disks_MYD3` 的单度量版；三点归一不在本车道。）
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- 固定 trace 的映射保持弱 Jordan trace 类。 -/
theorem diskWeakJordanTrace_comp_of_fix_R7E {Q : Type*} [TopologicalSpace Q] {Γ : freeLoop Q}
    {v : C(closedDisk, Q)} (hv : DiskWeakJordanTrace Γ v) (r : C(Q, Q))
    (hr : ∀ θ, r (Γ θ) = Γ θ) : DiskWeakJordanTrace Γ (r.comp v) := by
  obtain ⟨σ, hσ, htr⟩ := hv
  refine ⟨σ, hσ, ?_⟩
  ext θ
  have h := congrArg (fun γ : freeLoop Q => γ θ) htr
  change r (v (diskBoundary θ)) = Γ (σ θ)
  change v (diskBoundary θ) = Γ (σ θ) at h
  rw [h, hr]

/-- 区间里避开可数集的点。 -/
theorem exists_mem_Ioo_notMem_of_countable_R7E {S : Set ℝ} (hS : S.Countable) {c₁ c₂ : ℝ}
    (h : c₁ < c₂) : ∃ c ∈ Ioo c₁ c₂, c ∉ S := by
  by_contra hcon
  have hsub : Ioo c₁ c₂ ⊆ S := fun c hc => by
    by_contra hcS
    exact hcon ⟨c, hc, hcS⟩
  have h0 := measure_mono_null hsub (hS.measure_zero volume)
  rw [Real.volume_Ioo] at h0
  exact absurd h0 (by simp [h])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- **G5**（R7-E 存在性，单个度量）：见文件头。 -/
theorem exists_confined_morrey_disk_R7E [T3Space N] [SecondCountableTopology N]
    (hdim : Module.finrank ℝ E = 3) (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hcpt : IsCompact {x | ρ x ≤ -b + η})
    (hcoll : ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun G ρ x v v)
    {K : Set N} (hKcl : IsClosed K) (hKρ : K ⊆ {x | ρ x ≤ -b})
    (hfr : frontier K ⊆ {x | ρ x = -b}) (Ko : TopologicalSpace.Opens N)
    (hKo : (Ko : Set N) = interior K) {Γ : freeLoop Ko} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    (hΓρ : ∀ θ, ρ (Γ θ : N) < -b - δ)
    (hspan : ∃ v : C(closedDisk, Ko), DiskSmoothUpToBoundary (E := E) v ∧ diskTrace v = Γ) :
    ∃ u : C(closedDisk, Ko), IsMorreyDisk (G.restrictOpen Ko) Γ u ∧ ∀ z, ρ (u z : N) ≤ -b - δ := by
  obtain ⟨Ghat, hcomplete, hregular, hgermC, hbarrier⟩ :=
    exists_completion_metric_R7E hdim G hρ hδ hη hcpt hcoll hKcl hKρ hfr Ko hKo
  obtain ⟨r, hrfix, hrρ, hrLip, hrA⟩ :=
    exists_collar_retraction_R7E G hρ hδ hη hcpt hcoll hKcl hKρ hfr Ko hKo
  have hfinite : (spanningDiskCompetitors Ghat Γ).Nonempty := by
    obtain ⟨v, hvs, hvt⟩ := hspan
    exact ⟨v, hvt, hvs.exists_lipschitz Ghat⟩
  obtain ⟨u, hu⟩ := exists_morrey_disk Ghat hcomplete hregular Γ hΓ hfinite
  obtain ⟨hconf, hgerm⟩ := hbarrier Γ u hu hΓ fun θ => (hΓρ θ).le
  refine ⟨u, ?_, hconf⟩
  let C₀ : Set Ko := {x | ρ (x : N) < -b - δ / 2}
  have hagree : ∀ x ∈ C₀, Ghat.inner x = (G.restrictOpen Ko).inner x :=
    fun x hx => (hgermC x hx).self_of_nhds
  have huC : Set.range u ⊆ C₀ := by
    rintro _ ⟨z, rfl⟩
    change ρ (u z : N) < -b - δ / 2
    linarith [hconf z]
  refine isMorreyDisk_of_completion_R7E (G.restrictOpen Ko) Ghat hagree hu huC hgerm ?_
  intro v hv hvL
  obtain ⟨c, hc, hcS⟩ := exists_mem_Ioo_notMem_of_countable_R7E (hrA v hvL)
    (show -b - δ < -b - δ / 2 by linarith)
  have hcI : c ∈ Icc (-b - δ) (-b) := ⟨hc.1.le, by linarith [hc.2]⟩
  obtain ⟨L, hL⟩ := hrLip c hcI v hvL
  obtain ⟨L', hL'⟩ := lipschitz_change_metric_R7E (G.restrictOpen Ko) Ghat hL
  refine ⟨(r c).comp v, ?_, ?_, ⟨L', hL'⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    change ρ (r c (v z) : N) < -b - δ / 2
    linarith [hrρ c hcI (v z), hc.2]
  · exact diskWeakJordanTrace_comp_of_fix_R7E hv (r c) fun θ =>
      hrfix c hcI (Γ θ) (by linarith [hΓρ θ, hc.1])
  · by_contra hbad
    exact hcS ⟨hcI, hbad⟩

end DifferentialGeometry.Geometry
