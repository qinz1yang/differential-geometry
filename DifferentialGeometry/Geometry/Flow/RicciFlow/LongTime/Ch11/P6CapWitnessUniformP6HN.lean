import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SupplyRescaleP6HN

/-!
# 窗口 spatial canonical witness，常数对窗口半径一致（O-CH11-HNOT-LOCALDT G6a，后缀 `_P6HN`）

(CWW) witness `hcww` 的 standard 侧：树内 `exists_window_cap_spatialCanonicalWitness_of_standard_close`
（StandardWindowCapWitness:26）的 `Cw = 1000·Cs` 取在窗口半径 `r` **之后**（源是 cap 型
`exists_cap_spatialCanonicalWitness_with_margins … r`，`Cs` 依赖 `r`）——这正是 P6R2 头注说的
"`Cs` 依赖 `Dw`"。树内另有对 `x ∈ ℝ³` 一致的带 margins 版本
`StandardSolution.exists_spatialCanonicalWitness_with_margins`（StandardSpatialCanonicalMargins:483；
cap 或 neck，`C = C(ε, Θ)`）。本文件 = 前者证明逐字（生成器切片），只换这一个源、去掉 frontier 合取
（两个源经 G5 的 import 链传递可见）：
**`exists_window_spatialCanonicalWitness_uniform_P6HN`**：`Cw` 选在 `r, ρ` 之前（对 `Dw → ∞` 一致）。
生成器 `build-logs/scratch/O-CH11-HNOT-LOCALDT/gen/gen6.py`。
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance standardWindowSigmaCompactP6HN (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

/-- **窗口 spatial witness，常数对窗口半径一致（`_P6HN`，PROVED）**：`StandardWindowCapWitness:26` 的孪生，
源换成对 `x` 一致的 `StandardSolution.exists_spatialCanonicalWitness_with_margins`，`Cw` 在 `r` 之前。 -/
theorem exists_window_spatialCanonicalWitness_uniform_P6HN {ε Θ : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 11) (hΘ : Θ < 1) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ r ρ : ℝ, ∃ (D : ℝ) (N : ℕ) (e : ℝ), r + ρ < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ →
    ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
      (∀ i ≤ N, ∀ v : standardCapWindow D,
        metricDerivNorm i g ((Q.val.metric T).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ z : standardCapWindow D, ‖z.val‖ < r →
    ∀ C2 : ℝ, Cw ≤ C2 →
      (∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) z v)| ≤
          C2 * metricScalarAt g z * Real.sqrt (metricScalarAt g z) *
            Real.sqrt (g.inner z v v)) →
      ∃ W : SpatialCanonicalWitness g ε Cw C2 z, W.capTubeHasNeckChart ε := by
  have ha : 0 < ε / 2 := by positivity
  have hsmall : 2 * (ε / 2) < 1 / 11 := by linarith
  have heps₀ : 0 < neckModelTolerance (ε / 2) := neckModelTolerance_pos ha
  have heps₀s : neckModelTolerance (ε / 2) < 1 / 11 :=
    (neckModelTolerance_le _).trans_lt (by linarith)
  set Θp := max Θ 0 with hΘp
  have hΘp0 : 0 ≤ Θp := le_max_right _ _
  have hΘp1 : Θp < 1 := max_lt hΘ one_pos
  obtain ⟨Cs, hCs, hstd⟩ :=
    StandardSolution.exists_spatialCanonicalWitness_with_margins heps₀ heps₀s hΘp1
  obtain ⟨δ₄, hδ₄, htr⟩ :=
    SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance
      (P := EuclideanSpace ℝ (Fin 3)) ha hsmall (m := 1 / 20) (by norm_num) (by norm_num) hCs hCs
      one_pos
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_ball_placement hΘp1
  obtain ⟨e₂, he₂, hM2⟩ := StandardSolution.exists_window_metricComparisonOn_of_lt hΘp0 hΘp1
    (max 2 ⌈(2 * (ε / 2))⁻¹⌉₊) (η := min δ₄ (1 / 2)) (lt_min hδ₄ (by norm_num))
    ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  refine ⟨1000 * Cs, by linarith, fun r ρ => ?_⟩
  refine ⟨r + Λ * (L + 1) + 2 + max ρ 0, max 2 ⌈(2 * (ε / 2))⁻¹⌉₊, e₂,
    by linarith [le_max_left ρ 0, le_max_right ρ 0], he₂, ?_⟩
  set D := r + Λ * (L + 1) + 2 + max ρ 0 with hDdef
  have hρ0 : 0 ≤ max ρ 0 := le_max_right _ _
  intro Q T hT g hclose z hz C2 hC2 hgrad
  have hTp : T ∈ Icc 0 Θp := ⟨hT.1, hT.2.trans (le_max_left _ _)⟩
  obtain ⟨W0, hW0, hM0⟩ := hstd Q z.val T hTp
  have hR1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
    Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘp1 hTp) z.val
  have hsR : 1 ≤ Real.sqrt (metricScalarAt (Q.val.metric T) z.val) := Real.one_le_sqrt.mpr hR1
  have hne : Nonempty (standardCapWindow D) := ⟨z⟩
  set F := (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
    (standardCapWindow D) hne).symm with hFdef
  have hFsrc : F.source = (standardCapWindow D : Set (EuclideanSpace ℝ (Fin 3))) :=
    (standardCapWindow D).openPartialHomeomorphSubtypeCoe_target hne
  have hUF : ((standardCapWindow (D - 1) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) :
      Set (EuclideanSpace ℝ (Fin 3))) ⊆ F.source := by
    rw [hFsrc]
    intro y hy
    change ‖y‖ < D + 1
    have : ‖y‖ < D - 1 + 1 := hy
    linarith
  have hFz : F z.val = z := Subtype.ext
    ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) (standardCapWindow D) hne).right_inv' (by
      change z.val ∈ F.source
      rw [hFsrc]
      exact z.2))
  have hRbL : (8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs) /
      Real.sqrt (metricScalarAt (Q.val.metric T) z.val) ≤ L := by
    rw [← hLdef]
    exact div_le_self hL0 hsR
  have hsubL := riemannianClosedBallOf_mono (Q.val.metric T) z.val hRbL
  obtain ⟨hcptL, hplL⟩ := hplace Q T hTp L z.val hL0
  have hcpt := hcptL.of_isClosed_subset
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hsubL
  have hsub : riemannianClosedBallOf (I := I3) (Q.val.metric T) z.val
      ((8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs) /
        Real.sqrt (metricScalarAt (Q.val.metric T) z.val)) ⊆
      (standardCapWindow (D - 1) : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro y hy
    have h := hplL y (hsubL hy)
    change ‖y‖ < D - 1 + 1
    linarith
  obtain ⟨Cmp⟩ := hM2 D hne Q T hTp g (fun i hi v => hclose i hi v) (D - 1) (by linarith)
  have hC2' : 1000 * Cs ≤ C2 := hC2
  have hgrad' : ∀ v : TangentSpace I3 (F z.val),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (F z.val) v)| ≤
        C2 * metricScalarAt g (F z.val) *
          Real.sqrt (metricScalarAt g (F z.val)) *
          Real.sqrt (g.inner (F z.val) v v) := by
    rw [hFz]
    exact hgrad
  obtain ⟨W', hW', -⟩ := htr (Q.val.metric T) z.val W0 hW0 hM0 hR1
    (standardCapWindow (D - 1)) hcpt hsub (standardCapWindow D) g F hUF
    (Cmp.mono subset_rfl le_rfl (min_le_left _ _)) C2 hC2' hgrad'
  have hCw : 2 * Cs ≤ 1000 * Cs := by linarith
  rw [← hFz, show ε = 2 * (ε / 2) by ring]
  exact ⟨W'.enlargeConstants hCw le_rfl, hW'.enlarge_constants hCw le_rfl⟩

/-- consumer（`_P6HN`）：同一 `Cw` 服务所有窗口半径 `r = n + 2`。 -/
example {ε Θ : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (hΘ : Θ < 1) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ n : ℕ, ∃ D : ℝ, ((n : ℝ) + 2) < D := by
  obtain ⟨Cw, hCw, hall⟩ := exists_window_spatialCanonicalWitness_uniform_P6HN (Θ := Θ) hε hε' hΘ
  refine ⟨Cw, hCw, fun n => ?_⟩
  obtain ⟨D, -, -, hD, -⟩ := hall ((n : ℝ) + 2) 0
  exact ⟨D, by linarith⟩

end DifferentialGeometry.PDE.RicciFlow
