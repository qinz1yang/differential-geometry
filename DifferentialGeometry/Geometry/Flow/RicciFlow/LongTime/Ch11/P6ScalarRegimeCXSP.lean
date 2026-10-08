import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarBadSequenceCXSP

/-!
# CX-SPINE：P6(c) 的实际 ratio regime 与原数据的同一子列

对原 r/nr 分成频繁有界子列，或趋于无穷且全项 nr≤r 的尾列。
两种情况都重索引同一个 P6(c) 反例序列，保持原 history、同 A 的 seed volume、
A*r ball 和 delta accuracy。不是从 P6(b) 反证序列借 ratio；guard 频繁也未冒充发散。
这只生产真实 regime，尚不生产该 regime 的 scalar 矛盾。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 正尺度比的真实二分；无界分支取尾列，使 nr≤r 在每项成立。 -/
theorem seed_ratio_regime_subsequence_CXSP (r nr : ℕ → ℝ) (hnr : ∀ i, 0 < nr i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ i, r (φ i) ≤ Λ * nr (φ i)) ∨
        ((∀ i, nr (φ i) ≤ r (φ i)) ∧
          Tendsto (fun i => r (φ i) / nr (φ i)) atTop atTop)) := by
  by_cases hbounded : ∃ Λ : ℝ, ∃ᶠ i in atTop, r i / nr i ≤ Λ
  · obtain ⟨Λ, hΛ⟩ := hbounded
    obtain ⟨φ, hφ, hbound⟩ := extraction_of_frequently_atTop hΛ
    refine ⟨φ, hφ, Or.inl ⟨max Λ 1, le_max_right _ _, ?_⟩⟩
    intro i
    exact (div_le_iff₀ (hnr (φ i))).mp ((hbound i).trans (le_max_left _ _))
  · have hlim : Tendsto (fun i => r i / nr i) atTop atTop := by
      apply tendsto_atTop.mpr
      intro B
      have hB : ¬ ∃ᶠ i in atTop, r i / nr i ≤ B := fun h => hbounded ⟨B, h⟩
      have hgt : ∀ᶠ i in atTop, B < r i / nr i := by
        simpa only [not_frequently, not_le] using hB
      exact hgt.mono fun _ h => h.le
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop 1)
    let φ : ℕ → ℕ := fun i => i + N
    have hφ : StrictMono φ := fun i j h => Nat.add_lt_add_right h N
    refine ⟨φ, hφ, Or.inr ⟨?_, hlim.comp hφ.tendsto_atTop⟩⟩
    intro i
    have h := (le_div_iff₀ (hnr (φ i))).mp (hN (φ i) (Nat.le_add_left N i))
    simpa only [one_mul] using h

/-- 对 P6(c) 自身的坏序列作完整 ratio 分解，保持原 history、同 A 和全部 accuracy。 -/
theorem exists_prepared_scalar_bad_regimes_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters) {delta : ℝ → ℝ} {alpha : ℝ → ℝ → ℝ}
    {A : ℝ} (hA : 0 < A) (hnot : ¬ LargerBallScalarAt_C11S F delta alpha A) :
    ∃ (idx : ℕ → ℕ)
      (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
      (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
      (r : ℕ → ℝ),
      let R := fun i => metricScalarAt
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
      (∀ i, 0 < r i) ∧ (∀ i, 0 < (t i : ℝ)) ∧
      (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
      (∀ i, ∀ s ∈ Icc ((t i : ℝ) / 2) (t i), delta s < alpha A s) ∧
      (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
        (t i) (p i) (r i)) ∧
      (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤ ballVolume
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) ∧
      (∀ i, r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1)) ∧
      (∀ i, x i ∈ riemannianBallOf
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i)) ∧
      (∀ i : ℕ, (i : ℝ) + 1 < R i * r i ^ 2) ∧
      Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun i => R i * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
      ((∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ i, r i ≤ Λ * q.neckRadius (t i)) ∨
        ((∀ i, q.neckRadius (t i) ≤ r i) ∧
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop atTop)) := by
  obtain ⟨idx, t, p, x, r, hr, ht, htime, hacc, hsmall, hvol, hscale,
    hx, hbad, hratio, hescape, hlate⟩ :=
    exists_prepared_scalar_bad_sequence_CXSP S F hTower hA hnot
  obtain ⟨φ, hφ, hregime⟩ := seed_ratio_regime_subsequence_CXSP
    r (fun i => q.neckRadius (t i)) (fun i => q.neckRadius_pos _ (t i).2.1)
  refine ⟨idx ∘ φ, (fun i => t (φ i)), (fun i => p (φ i)),
    (fun i => x (φ i)), r ∘ φ, (fun i => hr (φ i)), (fun i => ht (φ i)),
    (fun i => htime (φ i)), (fun i => hacc (φ i)), (fun i => hsmall (φ i)),
    (fun i => hvol (φ i)), ?_, (fun i => hx (φ i)), ?_,
    hratio.comp hφ.tendsto_atTop, hescape.comp hφ.tendsto_atTop,
    hlate.comp hφ.tendsto_atTop, hregime⟩
  · intro i
    exact (hscale (φ i)).trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (by positivity) (by exact_mod_cast Nat.add_le_add_right (hφ.id_le i) 1))
  · intro i
    have hle : (i : ℝ) + 1 ≤ (φ i : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (hφ.id_le i) 1
    exact hle.trans_lt (hbad (φ i))

end GC.LongTime.Ch11

end
