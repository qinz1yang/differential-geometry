import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.TrimmedSeedR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.NoSheetCoincidenceR3B

/-!
# O-MY-R5 G4：R5 本体 `trimmed_morrey_disk_unique_up_to_mobius_R5` + R7 `huniq` 消费面

MY-T §2 Lemma 8（proper subdisk uniqueness）。输入 = scratch `MYD3/R03R05.lean:90` 合同里**实际用到的**前提：
`q` Morrey、`SmoothDiskExtension q Q`、闭盘 rank、collar `hcol`、`0 < ρ₀ < r₂ < 1`、`u` 是
`Γ₂ := diskTrace (affineSubdisk q 0 r₂)` 的 Morrey 盘（MYD3 合同里的 `hγ`、`hseparate` 在证明中不需要——
`hseparate` 由 `hcol` 推出；文件末 `example` 按 MYD3 原形状逐字型对齐）。结论：
`u = q₂ ∘ mob ∨ u = q₂ ∘ mob ∘ conj`（D-R-MY3-1），且三点归一 ⇒ `u = q₂`（R7 的 `huniq`）。

链：S0 collar 推论 + R3b（`coincidentGermPairs_eq_empty_confHarm_R3B`）→ S1–S3 seed
（`exists_trimmed_seed_R5`）→ G3 `proper_sheet_continuation_R5` → G2 `degree_one_factor_rigidity_R5` →
边界连续延拓（`eq_on_closedDisk_of_eq_on_ball_R5`）→ G1 `normalized_uniqueness_of_unique_up_to_mobius_R5`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry MeasureTheory ComplexConjugate
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- 闭盘上两连续映射在开盘上相等 ⇒ 处处相等。 -/
theorem eq_on_closedDisk_of_eq_on_ball_R5 {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : closedDisk → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z = g z) : ∀ z : closedDisk, f z = g z := by
  intro z
  have hmem : ∀ n : ℕ, ((1 - 1 / ((n : ℝ) + 2)) : ℝ) • (z : ℂ) ∈ closedDisk := by
    intro n
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [abs_of_pos (by linarith)]
    calc (1 - 1 / ((n : ℝ) + 2)) * ‖(z : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul (by linarith) (mem_closedBall_zero_iff.mp z.property) (norm_nonneg _)
            zero_le_one
      _ = 1 := by norm_num
  let x : ℕ → closedDisk := fun n => ⟨_, hmem n⟩
  have hx : Tendsto x atTop (𝓝 z) := by
    rw [tendsto_subtype_rng]
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h1 : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have h2 : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2) : ℝ) • (z : ℂ)) atTop
        (𝓝 ((1 : ℝ) • (z : ℂ))) := h1.smul_const _
    rw [one_smul] at h2
    exact h2
  have hxn : ∀ n, ‖((x n : closedDisk) : ℂ)‖ < 1 := by
    intro n
    change ‖((1 - 1 / ((n : ℝ) + 2)) : ℝ) • (z : ℂ)‖ < 1
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [abs_of_pos (by linarith)]
    calc (1 - 1 / ((n : ℝ) + 2)) * ‖(z : ℂ)‖ ≤ (1 - 1 / ((n : ℝ) + 2)) * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp z.property) (by linarith)
      _ < 1 := by linarith
  exact tendsto_nhds_unique (((hf.tendsto z).comp hx).congr fun n => h (x n) (hxn n))
    ((hg.tendsto z).comp hx)

/-- Möbius 在闭盘上连续。 -/
theorem continuousOn_diskMobius_R5 {a : ℂ} (ha : ‖a‖ < 1) (c : ℂ) :
    ContinuousOn (diskMobius_R5 a c) (closedBall 0 1) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold diskMobius_R5
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact one_sub_conj_mul_ne_zero_R5 ha (mem_closedBall_zero_iff.mp hz)

/-- Möbius 把闭盘映进闭盘。 -/
theorem diskMobius_mem_closedBall_R5 {a c z : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1)
    (hz : z ∈ closedBall (0 : ℂ) 1) : diskMobius_R5 a c z ∈ closedBall (0 : ℂ) 1 := by
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with h | h
  · exact ball_subset_closedBall (mem_ball_zero_iff.mpr (norm_diskMobius_lt_one_R5 ha hc h))
  · exact mem_closedBall_zero_iff.mpr (norm_diskMobius_R5 ha hc h).le

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G4（R5 本体）**：trimmed Morrey 盘唯一性。 -/
theorem trimmed_morrey_disk_unique_up_to_mobius_R5 [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3) {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {ρ₀ r₂ : ℝ} (hρ₀ : 0 < ρ₀) (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : ρ₀ < r₂) (hr1 : r₂ < 1)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g (diskTrace (affineSubdisk q 0 r₂)) u) :
    (∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧
      ((∀ z : closedDisk, u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c z)) ∨
        (∀ z : closedDisk,
          u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c (conj (z : ℂ)))))) ∧
      ∀ θ : Fin 3 → loopCircle, Function.Injective θ →
        (∀ j, diskTrace u (θ j) = diskTrace (affineSubdisk q 0 r₂) (θ j)) →
        u = affineSubdisk q 0 r₂ := by
  have hr0 : 0 < r₂ := hρ₀.trans hr
  obtain ⟨hbdry, hsep, hfiber, htrinj⟩ := collar_consequences_R5 hcol hr hr1 hr0
  have hcoin : coincidentGermPairs (q : closedDisk → M) = ∅ :=
    coincidentGermPairs_eq_empty_confHarm_R3B hdim hQ hrank hq.conformal hq.harmonic hbdry hsep
  have hVrank := diskExtension_rank_of_closed_rank_R5 hQ hrank
  have hfin : ∀ p : M, ((q : closedDisk → M) ⁻¹' {p}).Finite := fun p =>
    finite_fiber_of_isLocallyInjective q.continuous (hQ.isLocallyInjective_MR1 hrank) p
  obtain ⟨Lq, hqLip⟩ := hQ.lipschitz g
  have hVLip := diskExtension_lipschitz_R5 g hqLip
  have hΓ₂ := trimmed_trace_embedded_R5 hq hQ hrank hcol hr hr0 hr1
  obtain ⟨A, -, La, hLa⟩ := morrey_disk_closed_extension_lipschitz_ADP g hΓ₂ hu
  have hULip := diskExtension_lipschitz_R5 g hLa
  obtain ⟨hareaEq, a, b, ha, hb, hval, hgerm⟩ := exists_trimmed_seed_R5 hdim hq hQ hr0 hr1 hΓ₂ hu
  have hArea : riemannianArea g (diskExtension u) (ball 0 1) ≤
      riemannianArea g (diskExtension q) (ball 0 r₂) := by
    rw [riemannianArea_ball_eq_closedBall_R5, riemannianArea_ball_eq_closedBall_R5]
    exact hareaEq.le
  -- seed 换到 `q` 坐标
  have hr0' : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set W₀ : ℂ := (r₂ : ℂ) * a with hW₀def
  have hW₀ : ‖W₀‖ < r₂ := by
    rw [hW₀def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r₂ * ‖a‖ < r₂ * 1 := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp ha) hr0
      _ = r₂ := mul_one _
  have haK : a ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall ha
  have hval₀ : diskExtension u b = diskExtension q W₀ := by
    rw [← hval, diskExtension_affineSubdisk_R5 q r₂ haK]
  have hgerm₀ : Filter.map (diskExtension u) (𝓝 b) = Filter.map (diskExtension q) (𝓝 W₀) := by
    rw [← hgerm]
    have heq : diskExtension (affineSubdisk q 0 r₂) =ᶠ[𝓝 a]
        diskExtension q ∘ (Homeomorph.mulLeft₀ (r₂ : ℂ) hr0') := by
      filter_upwards [isOpen_ball.mem_nhds ha] with z hz
      exact diskExtension_affineSubdisk_R5 q r₂ (ball_subset_closedBall hz)
    rw [Filter.map_congr heq, ← Filter.map_map, Homeomorph.map_nhds_eq]
    rfl
  obtain ⟨φ, han, hmaps, hfac⟩ := proper_sheet_continuation_R5 hdim hq hVrank hcoin hfin hVLip hr1
    hfiber hu hΓ₂ hULip hArea hb hW₀ hval₀ hgerm₀.le
  obtain ⟨a', c', ha', hc', hφeq⟩ := degree_one_factor_rigidity_R5 hq hVrank hVLip hr0 hr1 hfiber
    hu hΓ₂ hULip hArea han hmaps hfac
  have hq₂c : Continuous (diskExtension (affineSubdisk q 0 r₂)) :=
    (affineSubdisk q 0 r₂).continuous.comp diskRetraction_lipschitz.continuous
  have hmob : ∀ z : closedDisk, diskMobius_R5 a' c' (z : ℂ) ∈ closedBall (0 : ℂ) 1 := fun z =>
    diskMobius_mem_closedBall_R5 ha' hc' z.property
  have hmobc : ∀ z : closedDisk, diskMobius_R5 a' c' (conj (z : ℂ)) ∈ closedBall (0 : ℂ) 1 :=
    fun z => diskMobius_mem_closedBall_R5 ha' hc'
      (by rw [mem_closedBall_zero_iff, Complex.norm_conj]; exact mem_closedBall_zero_iff.mp z.2)
  have hmain : (∀ z : closedDisk,
        u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a' c' z)) ∨
      (∀ z : closedDisk,
        u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a' c' (conj (z : ℂ)))) := by
    rcases hφeq with h | h
    · left
      refine eq_on_closedDisk_of_eq_on_ball_R5 u.continuous
        (hq₂c.comp ((continuousOn_diskMobius_R5 ha' c').comp_continuous continuous_subtype_val
          fun z => z.property)) ?_
      intro z hz
      have hzB : (z : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
      change u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a' c' z)
      rw [diskExtension_affineSubdisk_R5 q r₂ (hmob z), ← h z hzB, ← hfac z hzB,
        diskExtension_coe]
    · right
      have hcc : Continuous fun z : closedDisk => diskMobius_R5 a' c' (conj (z : ℂ)) :=
        (continuousOn_diskMobius_R5 ha' c').comp_continuous
          (Complex.continuous_conj.comp continuous_subtype_val)
          (fun z => by
            rw [mem_closedBall_zero_iff, Complex.norm_conj]
            exact mem_closedBall_zero_iff.mp z.property)
      refine eq_on_closedDisk_of_eq_on_ball_R5 u.continuous (hq₂c.comp hcc) ?_
      intro z hz
      have hzB : (z : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
      change u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a' c' (conj (z : ℂ)))
      rw [diskExtension_affineSubdisk_R5 q r₂ (hmobc z), ← h z hzB, ← hfac z hzB,
        diskExtension_coe]
  exact ⟨⟨a', c', ha', hc', hmain⟩, fun θ hθ hmark =>
    normalized_uniqueness_of_unique_up_to_mobius_R5 htrinj ⟨a', c', ha', hc', hmain⟩ θ hθ hmark⟩

/-- **R7 `huniq` 消费面**（MYD3:110 的结论形状）：三点归一 ⇒ `u = q₂`。 -/
theorem trimmed_morrey_disk_normalized_unique_R5 [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3) {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {ρ₀ r₂ : ℝ} (hρ₀ : 0 < ρ₀) (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : ρ₀ < r₂) (hr1 : r₂ < 1) (θ : Fin 3 → loopCircle) (hθ : Function.Injective θ) :
    ∀ u : C(closedDisk, M), IsMorreyDisk g (diskTrace (affineSubdisk q 0 r₂)) u →
      (∀ j, diskTrace u (θ j) = diskTrace (affineSubdisk q 0 r₂) (θ j)) →
      u = affineSubdisk q 0 r₂ :=
  fun _ hu hθu => (trimmed_morrey_disk_unique_up_to_mobius_R5 hdim hq hQ hrank hρ₀ hcol hr hr1
    hu).2 θ hθ hθu

/-- 型对齐（consumer）：scratch `MYD3/R03R05.lean:90` 合同 `trimmed_morrey_disk_unique_MYD3` 的逐字形状
（`diskMobius_MYD3` ↦ `diskMobius_R5`，同式），多出的 `hγ`、`hseparate` 不需要。 -/
example [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} (hdim : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q) (_hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (_hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ)
    {ρ₀ r₂ : ℝ} (hρ₀ : 0 < ρ₀) (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : ρ₀ < r₂) (hr1 : r₂ < 1)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g (diskTrace (affineSubdisk q 0 r₂)) u) :
    (∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧
      ((∀ z : closedDisk, u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c z)) ∨
        (∀ z : closedDisk,
          u z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c (conj (z : ℂ)))))) ∧
      ∀ θ : Fin 3 → loopCircle, Function.Injective θ →
        (∀ j, diskTrace u (θ j) = diskTrace (affineSubdisk q 0 r₂) (θ j)) →
        u = affineSubdisk q 0 r₂ :=
  trimmed_morrey_disk_unique_up_to_mobius_R5 hdim hq hQ hrank hρ₀ hcol hr hr1 hu

/-- 型对齐（consumer）：R7 `huniq`（`MYD3/R06R07.lean:193`）在 `Γ := diskTrace q₂`、`q := q₂` 时的
逐字形状。 -/
example [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} (hdim : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {ρ₀ r₂ : ℝ} (hρ₀ : 0 < ρ₀) (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : ρ₀ < r₂) (hr1 : r₂ < 1) (θ : Fin 3 → loopCircle) (hθ : Function.Injective θ) :
    ∀ u : C(closedDisk, M), IsMorreyDisk g (diskTrace (affineSubdisk q 0 r₂)) u →
      (∀ j, diskTrace u (θ j) = (diskTrace (affineSubdisk q 0 r₂)) (θ j)) →
      u = affineSubdisk q 0 r₂ :=
  trimmed_morrey_disk_normalized_unique_R5 hdim hq hQ hrank hρ₀ hcol hr hr1 θ hθ

end DifferentialGeometry.Geometry
