import DifferentialGeometry.Geometry.MinimalSurface.WeakDiskTransportK8

/-!
# Route W：`A′(t)` 的 e^ε 两向 comparison 与 continuity（IMS08′ kernel，G3′，S-A14-KERNEL）

`A : ℝ → ℝ` 是光滑 Morrey 类上的最小面积（`IsLeast`，面积集合的最小元）；类为
`{v | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace (γ t) v ∧ range v ⊆ W t}`
（S-A08-ATTAIN 的 `morreyLeastAreaS` 的类）。不假设 `A` 的具体定义：`morreyLeastAreaS`
在有 minimizer（Morrey 盘）时满足这里的 `IsLeast` 假设。

* `continuousOn_of_local_exp_comparison_K8`：abstract 连续性 kernel
  （`A t ≤ e^ε A t₀ ∧ A t₀ ≤ e^ε A t`；S-A08-ATTAIN 的 left-lsc 变体也用它）。
* `weakDiskArea_comparison_of_transport_K8`：对固定 `t₀`、`ε`、`δ`：每个 minimizer `q`
  （两个方向）有 `φ`（open `V ⊇ range q` 上 smooth、边界环对应、`range q` 上 `MapsTo`、
  `range q` 上逐点 `φ^*g ≤ exp ε * g`）⇒ 两向 `exp ε` comparison。
* `continuousOn_weakDiskArea_of_transport_K8`：对所有 `t₀`、`ε` 汇总 ⇒ `ContinuousOn A (Ici T)`。
  forward 方向（`t₀` 的 minimizer 送到 `t`）与 backward 方向（`t` 的 minimizer 送回 `t₀`，
  "minimizer 的 range ⊆ dom(Q_t)" 是显式的 `range q ⊆ V`，即 IMS06 的输出）对称。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set Filter
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

/-- abstract 连续性 kernel：`T` 之后任意 `t₀`、`ε > 0`，附近 `t ≥ T` 有两向 `e^ε` comparison ⇒
`ContinuousOn A (Ici T)`（`A` 不需要非负）。 -/
theorem continuousOn_of_local_exp_comparison_K8 (A : ℝ → ℝ) (T : ℝ)
    (hcomp : ∀ t₀, T ≤ t₀ → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ t, T ≤ t → |t - t₀| < δ →
      A t ≤ Real.exp ε * A t₀ ∧ A t₀ ≤ Real.exp ε * A t) :
    ContinuousOn A (Ici T) := by
  have key : ∀ (t₀ : ℝ), T ≤ t₀ → ∀ (ε : ℝ), 0 < ε →
      ∀ᶠ t in 𝓝[Ici T] t₀, A t ≤ Real.exp ε * A t₀ ∧ A t₀ ≤ Real.exp ε * A t := by
    intro t₀ ht₀ ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hcomp t₀ ht₀ ε hε
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun t hdist ht => ?_⟩
    rw [Real.dist_eq] at hdist
    exact hδ' t ht hdist
  intro t₀ ht₀
  have ht₀' : T ≤ t₀ := ht₀
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro a ha
    have hlim : Tendsto (fun ε : ℝ => Real.exp (-ε) * A t₀) (𝓝 0) (𝓝 (A t₀)) := by
      have h1 : Tendsto (fun ε : ℝ => Real.exp (-ε)) (𝓝 0) (𝓝 1) := by
        have := (Real.continuous_exp.comp continuous_neg).tendsto 0
        simpa [Function.comp_def] using this
      simpa using h1.mul_const (A t₀)
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), a < Real.exp (-ε) * A t₀ :=
      hlim.eventually (lt_mem_nhds ha)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : 0 < δ / 2 := by positivity
    have hεa : a < Real.exp (-(δ / 2)) * A t₀ := by
      apply hδ'
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      linarith
    filter_upwards [key t₀ ht₀' (δ / 2) hε] with t ht
    have h2 : Real.exp (-(δ / 2)) * A t₀ ≤ A t := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact ht.2
    exact lt_of_lt_of_le hεa h2
  · intro b hb
    have hlim : Tendsto (fun ε : ℝ => Real.exp ε * A t₀) (𝓝 0) (𝓝 (A t₀)) := by
      have h1 : Tendsto (fun ε : ℝ => Real.exp ε) (𝓝 0) (𝓝 1) := by
        have := Real.continuous_exp.tendsto 0
        simpa using this
      simpa using h1.mul_const (A t₀)
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), Real.exp ε * A t₀ < b :=
      hlim.eventually (gt_mem_nhds hb)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : 0 < δ / 2 := by positivity
    have hεb : Real.exp (δ / 2) * A t₀ < b := by
      apply hδ'
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      linarith
    filter_upwards [key t₀ ht₀' (δ / 2) hε] with t ht
    exact lt_of_le_of_lt ht.1 hεb

section Family

variable (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
  [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)] [∀ t, IsManifold (𝓡 3) ∞ (M t)]

/-- G3′：固定 `t₀`、`ε`、`δ`。`A` 是光滑 Morrey 类上的最小面积（`IsLeast`）；`|t - t₀| < δ` 时，
`t₀` 的每个 minimizer `q`（也包括反向：`t` 的每个 minimizer）带 transport 数据
`φ`（open `V ⊇ range q` 上 smooth；边界环对应；`range q` 上 `MapsTo` 与逐点 metric 比较，
常数 `exp ε`）⇒ `A t ≤ exp ε * A t₀` 且 `A t₀ ≤ exp ε * A t`。 -/
theorem weakDiskArea_comparison_of_transport_K8
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t)) (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (A : ℝ → ℝ)
    (hmin : ∀ (t : ℝ) (ht : T ≤ t),
      IsLeast ((fun v : C(closedDisk, M t) => riemannianDiskArea (g t) v) ''
        {v | DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ t ht) v ∧ range v ⊆ W t}) (A t))
    (t₀ : ℝ) (ht₀ : T ≤ t₀) (ε δ : ℝ)
    (hforward : ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ → ∀ q : C(closedDisk, M t₀),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) q →
      DiskWeakJordanTrace (γ t₀ ht₀) q → range q ⊆ W t₀ →
      riemannianDiskArea (g t₀) q = A t₀ →
      ∃ (φ : M t₀ → M t) (V : Set (M t₀)), IsOpen V ∧ range q ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ (∀ θ, φ (γ t₀ ht₀ θ) = γ t ht θ) ∧
        MapsTo φ (range q) (W t) ∧
        ∀ p ∈ range q, ∀ w : TangentSpace (𝓡 3) p,
          (g t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * (g t₀).inner p w w)
    (hbackward : ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ → ∀ q : C(closedDisk, M t),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) q →
      DiskWeakJordanTrace (γ t ht) q → range q ⊆ W t →
      riemannianDiskArea (g t) q = A t →
      ∃ (ψ : M t → M t₀) (V : Set (M t)), IsOpen V ∧ range q ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ V ∧ (∀ θ, ψ (γ t ht θ) = γ t₀ ht₀ θ) ∧
        MapsTo ψ (range q) (W t₀) ∧
        ∀ p ∈ range q, ∀ w : TangentSpace (𝓡 3) p,
          (g t₀).inner (ψ p) (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
            Real.exp ε * (g t).inner p w w) :
    ∀ (t : ℝ) (_ : T ≤ t), |t - t₀| < δ →
      A t ≤ Real.exp ε * A t₀ ∧ A t₀ ≤ Real.exp ε * A t := by
  intro t ht hd
  obtain ⟨⟨q₀, ⟨hq₀s, hq₀t, hq₀W⟩, hq₀A⟩, hlb₀⟩ := hmin t₀ ht₀
  obtain ⟨⟨q, ⟨hqs, hqt, hqW⟩, hqA⟩, hlb⟩ := hmin t ht
  have hq₀A' : riemannianDiskArea (g t₀) q₀ = A t₀ := hq₀A
  have hqA' : riemannianDiskArea (g t) q = A t := hqA
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, V, hV, hrange, hφ, hγ, hmap, hmet⟩ := hforward t ht hd q₀ hq₀s hq₀t hq₀W hq₀A'
    obtain ⟨w, _, hcls, harea⟩ := exists_smoothCompetitor_map_K8 (g t₀) (g t) hγ hq₀s hq₀t hV
      hrange hφ (S := range q₀) subset_rfl hmap (Real.exp_pos ε) hmet
    calc A t ≤ riemannianDiskArea (g t) w := hlb ⟨w, hcls, rfl⟩
      _ ≤ Real.exp ε * riemannianDiskArea (g t₀) q₀ := harea
      _ = Real.exp ε * A t₀ := by rw [hq₀A']
  · obtain ⟨ψ, V, hV, hrange, hψ, hγ, hmap, hmet⟩ := hbackward t ht hd q hqs hqt hqW hqA'
    obtain ⟨w, _, hcls, harea⟩ := exists_smoothCompetitor_map_K8 (g t) (g t₀) hγ hqs hqt hV
      hrange hψ (S := range q) subset_rfl hmap (Real.exp_pos ε) hmet
    calc A t₀ ≤ riemannianDiskArea (g t₀) w := hlb₀ ⟨w, hcls, rfl⟩
      _ ≤ Real.exp ε * riemannianDiskArea (g t) q := harea
      _ = Real.exp ε * A t := by rw [hqA']

/-- G4′ 前一步：对所有 `t₀ ≥ T`、`ε > 0` 汇总 `weakDiskArea_comparison_of_transport_K8`
⇒ `A` 在 `Ici T` 上连续（transport 数据为显式 hypotheses，`A` 是 `IsLeast` 的最小面积）。 -/
theorem continuousOn_weakDiskArea_of_transport_K8
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t)) (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (A : ℝ → ℝ)
    (hmin : ∀ (t : ℝ) (ht : T ≤ t),
      IsLeast ((fun v : C(closedDisk, M t) => riemannianDiskArea (g t) v) ''
        {v | DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ t ht) v ∧ range v ⊆ W t}) (A t))
    (htransport : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      (∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ → ∀ q : C(closedDisk, M t₀),
        DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) q →
        DiskWeakJordanTrace (γ t₀ ht₀) q → range q ⊆ W t₀ →
        riemannianDiskArea (g t₀) q = A t₀ →
        ∃ (φ : M t₀ → M t) (V : Set (M t₀)), IsOpen V ∧ range q ⊆ V ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ (∀ θ, φ (γ t₀ ht₀ θ) = γ t ht θ) ∧
          MapsTo φ (range q) (W t) ∧
          ∀ p ∈ range q, ∀ w : TangentSpace (𝓡 3) p,
            (g t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (g t₀).inner p w w) ∧
      (∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ → ∀ q : C(closedDisk, M t),
        DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) q →
        DiskWeakJordanTrace (γ t ht) q → range q ⊆ W t →
        riemannianDiskArea (g t) q = A t →
        ∃ (ψ : M t → M t₀) (V : Set (M t)), IsOpen V ∧ range q ⊆ V ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ V ∧ (∀ θ, ψ (γ t ht θ) = γ t₀ ht₀ θ) ∧
          MapsTo ψ (range q) (W t₀) ∧
          ∀ p ∈ range q, ∀ w : TangentSpace (𝓡 3) p,
            (g t₀).inner (ψ p) (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
              Real.exp ε * (g t).inner p w w)) :
    ContinuousOn A (Ici T) := by
  apply continuousOn_of_local_exp_comparison_K8
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, hfwd, hbwd⟩ := htransport t₀ ht₀ ε hε
  exact ⟨δ, hδ, fun t ht hd =>
    weakDiskArea_comparison_of_transport_K8 M g W T γ A hmin t₀ ht₀ ε δ hfwd hbwd t ht hd⟩

/-- Consumer / non-vacuity：常值 family（`M t = N`、`g t = g₀`、`W t = W`、`γ t = γ₀`、`A t = A₀`），
transport 取 `id`，所有 hypotheses 都被满足；真正调用 `continuousOn_weakDiskArea_of_transport_K8`。 -/
example {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (g₀ : SmoothRiemannianMetric (𝓡 3) N) (W : Set N) (T : ℝ)
    (γ₀ : freeLoop N) (A₀ : ℝ)
    (hmin : IsLeast ((fun v : C(closedDisk, N) => riemannianDiskArea g₀ v) ''
      {v | DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
        DiskWeakJordanTrace γ₀ v ∧ range v ⊆ W}) A₀) :
    ContinuousOn (fun _ : ℝ => A₀) (Ici T) := by
  have hid : ∀ (ε : ℝ), 0 ≤ ε → ∀ (q : C(closedDisk, N)), range q ⊆ W →
      ∃ (φ : N → N) (V : Set N), IsOpen V ∧ range q ⊆ V ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧
        (∀ θ, φ (γ₀ θ) = γ₀ θ) ∧ MapsTo φ (range q) W ∧
        ∀ p ∈ range q, ∀ w : TangentSpace (𝓡 3) p,
          g₀.inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * g₀.inner p w w := by
    intro ε hε q hqW
    refine ⟨id, univ, isOpen_univ, subset_univ _, contMDiffOn_id, fun θ => rfl,
      fun p hp => hqW hp, fun p _ w => ?_⟩
    rw [mfderiv_id]
    exact le_mul_of_one_le_left (metric_inner_self_nonneg g₀ p w) (Real.one_le_exp hε)
  exact continuousOn_weakDiskArea_of_transport_K8 (fun _ : ℝ => N) (fun _ => g₀) (fun _ => W) T
    (fun _ _ => γ₀) (fun _ => A₀) (fun _ _ => hmin) (fun t₀ _ ε hε =>
      ⟨1, one_pos, fun t _ _ q _ _ hqW _ => hid ε hε.le q hqW,
        fun t _ _ q _ _ hqW _ => hid ε hε.le q hqW⟩)

end Family

end DifferentialGeometry.Geometry

end
