import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarRetractionR7E
import DifferentialGeometry.Geometry.Metric.Conformal.BarrierProfile

/-!
# O-MY-R7E G2-a：collar 处 `K` 的局部拓扑（为 completion 的 defining function `δ_K` 光滑性）

用 level flow（`CollarFlowR7E`）证明：
* `rho_lt_of_mem_interior_R7E`：`interior K ⊆ {ρ < hi}`（`ρ = hi` 的内点是 `ρ` 的局部极大，而沿 flow
  `d/ds ρ (D_s x) = −1`，Fermat 矛盾）；
* `exists_nhds_dichotomy_R7E`：`ρ x = hi` 处有邻域 `V`，`V ∩ {ρ < hi}` 要么全在 `interior K`、要么全在
  `Kᶜ`（flow 把 `V ∩ {ρ < hi}` 推进 `D_{s₀} x` 所在的 `{ρ < hi}` 连通分支）——即另一个 sublevel 分支不会在
  `{ρ = hi}` 处碰到 `K`；
* `contMDiff_collarDefining_R7E`：`δ_K = 1_K · cutoff(A, ρ − c₀)`（`A = hi − c₀`）光滑，
  `{δ_K > 0} = interior K`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

section Topology

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

include hXc hρ hdρ hβeq in
/-- `interior K ⊆ {ρ < hi}`（`hi ∈ [a, b]` 在 `β = 1` 带内）。 -/
theorem rho_lt_of_mem_interior_R7E {K : Set N} {hi : ℝ} (hahi : a ≤ hi) (hhib : hi ≤ b)
    (hKρ : K ⊆ {x | ρ x ≤ hi}) {x : N} (hx : x ∈ interior K) : ρ x < hi := by
  have hle : ρ x ≤ hi := hKρ (interior_subset hx)
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hd := hasDerivAt_rho_collarFlow_R7E X hXc hρ hdρ x 0
    rw [collarFlow_zero_R7E, h, hβeq hi hahi hhib] at hd
    have hcont : ContinuousAt (fun s => collarFlow_R7E X hXc s x) 0 :=
      ((continuous_collarFlow_joint_R7E X hXc).comp
        (continuous_id.prodMk continuous_const)).continuousAt
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), collarFlow_R7E X hXc s x ∈ interior K := by
      apply hcont.preimage_mem_nhds
      rw [collarFlow_zero_R7E]
      exact isOpen_interior.mem_nhds hx
    have hmax : IsLocalMax (fun s => ρ (collarFlow_R7E X hXc s x)) 0 := by
      filter_upwards [hmem] with s hs
      rw [collarFlow_zero_R7E, h]
      exact hKρ (interior_subset hs)
    have h0 := hmax.hasDerivAt_eq_zero hd
    norm_num at h0

include hXc hρ hdρ hβ0 hβ1 hβeq in
/-- `ρ x = hi` 处的二分：邻域 `V` 里 `{ρ < hi}` 的点要么全在 `interior K`，要么全不在 `K`。 -/
theorem exists_nhds_dichotomy_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hahi : a < hi)
    (hhib : hi < b) (hfr : frontier K ⊆ {x | ρ x = hi}) {x : N} (hx : ρ x = hi) :
    ∃ V ∈ 𝓝 x, (∀ y ∈ V, ρ y < hi → y ∈ interior K) ∨ (∀ y ∈ V, ρ y < hi → y ∉ K) := by
  have : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace E N
  set s₀ : ℝ := (hi - a) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; linarith
  set p := collarFlow_R7E X hXc s₀ x with hp
  have hρp : ρ p = hi - s₀ :=
    hx ▸ rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq (by linarith) hs₀pos.le
      (by rw [hx, hs₀]; linarith)
  set Ω : Set N := {y | ρ y < hi} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt hρ.continuous continuous_const
  have hpΩ : p ∈ Ω := by
    change ρ p < hi
    linarith
  set B := connectedComponentIn Ω p with hB
  have hBo : IsOpen B := hΩo.connectedComponentIn
  have hBΩ : B ⊆ Ω := connectedComponentIn_subset Ω p
  have hpB : p ∈ B := mem_connectedComponentIn hpΩ
  have hΩsub : Ω ⊆ interior K ∪ Kᶜ := by
    intro y hy
    by_contra hnot
    rw [mem_union, not_or, mem_compl_iff, not_not] at hnot
    have hfront : y ∈ frontier K := by
      rw [frontier, hKcl.closure_eq]
      exact ⟨hnot.2, hnot.1⟩
    have h1 : ρ y = hi := hfr hfront
    have h2 : ρ y < hi := hy
    linarith
  have hDc : Continuous (collarFlow_R7E X hXc s₀) := (collarFlow_R7E X hXc s₀).continuous
  set V : Set N := {y | (a + hi) / 2 < ρ y} ∩ collarFlow_R7E X hXc s₀ ⁻¹' B with hV
  have hVn : V ∈ 𝓝 x := by
    apply inter_mem
    · exact (isOpen_lt continuous_const hρ.continuous).mem_nhds
        (by change (a + hi) / 2 < ρ x; rw [hx]; linarith)
    · exact hDc.continuousAt.preimage_mem_nhds (hBo.mem_nhds hpB)
  -- 每个 `y ∈ V ∩ Ω` 与 `p` 由 `Ω` 里的预连通集相连
  have hpath : ∀ y ∈ V, ρ y < hi → ∃ Q : Set N, IsPreconnected Q ∧ Q ⊆ Ω ∧ y ∈ Q ∧ p ∈ Q := by
    intro y hyV hyΩ
    have hy1 : (a + hi) / 2 < ρ y := hyV.1
    let P : Set N := (fun s => collarFlow_R7E X hXc s y) '' Icc 0 s₀
    have hPc : IsPreconnected P :=
      isPreconnected_Icc.image _ ((continuous_collarFlow_joint_R7E X hXc).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    have hPΩ : P ⊆ Ω := by
      rintro _ ⟨s, hs, rfl⟩
      have hρs : ρ (collarFlow_R7E X hXc s y) = ρ y - s :=
        rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq (by linarith) hs.1
          (by linarith [hs.2, show (a + hi) / 2 = a + s₀ by rw [hs₀]; ring])
      change ρ (collarFlow_R7E X hXc s y) < hi
      linarith [hs.1]
    have hyP : y ∈ P := ⟨0, ⟨le_rfl, hs₀pos.le⟩, collarFlow_zero_R7E X hXc y⟩
    have hDyP : collarFlow_R7E X hXc s₀ y ∈ P := ⟨s₀, ⟨hs₀pos.le, le_rfl⟩, rfl⟩
    refine ⟨P ∪ B, hPc.union' ⟨_, hDyP, hyV.2⟩ (isPreconnected_connectedComponentIn),
      union_subset hPΩ hBΩ, Or.inl hyP, Or.inr hpB⟩
  rcases hΩsub hpΩ with hpK | hpK
  · refine ⟨V, hVn, Or.inl fun y hyV hyΩ => ?_⟩
    obtain ⟨Q, hQc, hQΩ, hyQ, hpQ⟩ := hpath y hyV hyΩ
    exact hQc.subset_left_of_subset_union isOpen_interior hKcl.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hQΩ.trans hΩsub) ⟨p, hpQ, hpK⟩ hyQ
  · refine ⟨V, hVn, Or.inr fun y hyV hyΩ => ?_⟩
    obtain ⟨Q, hQc, hQΩ, hyQ, hpQ⟩ := hpath y hyV hyΩ
    exact hQc.subset_right_of_subset_union isOpen_interior hKcl.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hQΩ.trans hΩsub) ⟨p, hpQ, hpK⟩ hyQ

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N] in
theorem cutoff_eq_zero_of_le_R7E {A r : ℝ} (hA : 0 < A) (hr : A ≤ r) : cutoff A r = 0 := by
  have hnn : 0 ≤ cutoff A r := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  rcases hnn.lt_or_eq with h | h
  · exact absurd ((cutoff_pos_iff hA r).mp h) (not_lt.mpr hr)
  · exact h.symm

include hXc hρ hdρ hβ0 hβ1 hβeq in
/-- completion defining function `δ_K = 1_K · cutoff(hi − c₀, ρ − c₀)` 光滑。 -/
theorem contMDiff_collarDefining_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hahi : a < hi)
    (hhib : hi < b) (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi}) {c₀ : ℝ}
    (hc₀ : c₀ < hi) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (K.indicator fun x => cutoff (hi - c₀) (ρ x - c₀)) := by
  set F : N → ℝ := fun x => cutoff (hi - c₀) (ρ x - c₀) with hF
  have hFs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F :=
    (cutoff_smooth (hi - c₀)).contMDiff.comp (hρ.sub contMDiff_const)
  have hF0 : ∀ y, hi ≤ ρ y → F y = 0 := fun y hy =>
    cutoff_eq_zero_of_le_R7E (by linarith) (by linarith)
  have hint : ∀ y ∈ K, ρ y < hi → y ∈ interior K := by
    intro y hyK hy
    by_contra hnot
    have hfront : y ∈ frontier K := by
      rw [frontier, hKcl.closure_eq]
      exact ⟨hyK, hnot⟩
    have h1 : ρ y = hi := hfr hfront
    linarith
  intro x
  by_cases hxK : x ∈ K
  · have hxle : ρ x ≤ hi := hKρ hxK
    rcases hxle.lt_or_eq with hlt | heq
    · refine (hFs x).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_interior.mem_nhds (hint x hxK hlt)] with y hy
      exact indicator_of_mem (interior_subset hy) _
    · obtain ⟨V, hV, hdich⟩ := exists_nhds_dichotomy_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hahi
        hhib hfr heq
      rcases hdich with hin | hout
      · refine (hFs x).congr_of_eventuallyEq ?_
        filter_upwards [hV] with y hy
        by_cases hyK : y ∈ K
        · exact indicator_of_mem hyK _
        · rw [indicator_of_notMem hyK]
          by_contra hne
          have hge : ¬ ρ y < hi := fun h => hyK (interior_subset (hin y hy h))
          exact hne (hF0 y (not_lt.mp hge)).symm
      · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hV] with y hy
        by_cases hyK : y ∈ K
        · rw [indicator_of_mem hyK]
          have hge : ¬ ρ y < hi := fun h => hout y hy h hyK
          exact hF0 y (not_lt.mp hge)
        · exact indicator_of_notMem hyK _
  · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hKcl.isOpen_compl.mem_nhds hxK] with y hy
    exact indicator_of_notMem hy _

include hXc hρ hdρ hβeq in
/-- `{δ_K > 0} = interior K`。 -/
theorem collarDefining_pos_iff_R7E {K : Set N} (hKcl : IsClosed K) {hi : ℝ} (hahi : a < hi)
    (hhib : hi < b) (hKρ : K ⊆ {x | ρ x ≤ hi}) (hfr : frontier K ⊆ {x | ρ x = hi}) {c₀ : ℝ}
    (hc₀ : c₀ < hi) {x : N} :
    x ∈ interior K ↔ 0 < K.indicator (fun x => cutoff (hi - c₀) (ρ x - c₀)) x := by
  constructor
  · intro hx
    rw [indicator_of_mem (interior_subset hx), cutoff_pos_iff (by linarith)]
    have := rho_lt_of_mem_interior_R7E X hXc hρ hdρ hβeq hahi.le hhib.le hKρ hx
    linarith
  · intro hpos
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, cutoff_pos_iff (by linarith)] at hpos
      by_contra hnot
      have hfront : x ∈ frontier K := by
        rw [frontier, hKcl.closure_eq]
        exact ⟨hxK, hnot⟩
      have h1 : ρ x = hi := hfr hfront
      linarith
    · rw [indicator_of_notMem hxK] at hpos
      exact absurd hpos (lt_irrefl 0)

end Topology

end DifferentialGeometry.Geometry
