import DifferentialGeometry.Geometry.Curvature.StabilityGaussWS
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.Measure.Area.InducedVolume
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

/-!
# S-W-STAB-2 G1：共形坐标 ℂ 形式的 stability inequality

`stability_inequality_gauss_WS` 在 `N` 的流形结构上陈述（`gN`-梯度、`μ_{gN}`）。`U` 在 `N` 上共形
（Morrey disk）时 `gN = λ |dz|²`（`λ = diskMapConformalCoefficient g U = |∂_x U|²_g`），于是
`dμ_{gN} = λ dx dy`、`|∇φ|²_{gN} dμ_{gN} = ‖dψ‖² dx dy`，把它换成 `ℂ` 上的平面形式（`W := λ·VJ`）：

* `stability_inequality_conformal_WS2`：`∃ VJ : ℂ → ℝ`（`C^∞(N)`，`= K_Σ − q̃`，`≤ K_Σ − R/2`），
  `∀ ψ ∈ C_c^∞(ℂ), tsupport ψ ⊆ N → 0 ≤ ∫ ‖dψ‖² + λ·VJ·ψ²`（`‖dψ‖² = ψ_x² + ψ_y²`）；
* `stability_inequality_scalar_lower_conformal_WS2`：`R ≥ σ` ⇒ `(σ/2)∫ λψ² ≤ ∫ ‖dψ‖² + λ·K_Σ·ψ²`；
* `IsMorreyDisk` 版（`hmin hmean hconf` 自动）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

/-- `ℂ →L[ℝ] ℝ` 的算子范数平方 = `L(1)² + L(i)²`（Euclidean 梯度的模平方）。 -/
theorem norm_sq_complex_clm_WS2 (L : ℂ →L[ℝ] ℝ) : ‖L‖ ^ 2 = L 1 ^ 2 + L Complex.I ^ 2 := by
  have hL : ∀ z : ℂ, L z = z.re * L 1 + z.im * L Complex.I := by
    intro z
    have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  set a := L 1 with ha
  set b := L Complex.I with hb
  set A := a ^ 2 + b ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have h1 : ‖L‖ ^ 2 ≤ A := by
    have hup : ‖L‖ ≤ Real.sqrt A := by
      refine L.opNorm_le_bound (Real.sqrt_nonneg _) (fun z => ?_)
      rw [Real.norm_eq_abs, hL z]
      have hle : (z.re * a + z.im * b) ^ 2 ≤ (Real.sqrt A * ‖z‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA0, hsq z]
        nlinarith [sq_nonneg (z.re * b - z.im * a)]
      exact abs_le_of_sq_le_sq hle (by positivity)
    calc ‖L‖ ^ 2 ≤ Real.sqrt A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hup 2
      _ = A := Real.sq_sqrt hA0
  have h2 : A ^ 2 ≤ ‖L‖ ^ 2 * A := by
    set c : ℂ := ⟨a, b⟩ with hc
    have hLc : L c = A := by
      rw [hL c]
      simp only [hc, hA]
      ring
    have hcn : ‖c‖ ^ 2 = A := by
      rw [hsq c]
    have hle : (L c) ^ 2 ≤ (‖L‖ * ‖c‖) ^ 2 := by
      have habs := L.le_opNorm c
      rw [Real.norm_eq_abs] at habs
      exact sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
    rw [hLc, mul_pow, hcn] at hle
    exact hle
  rcases eq_or_lt_of_le hA0 with h0 | hpos
  · exact le_antisymm h1 (h0 ▸ sq_nonneg _)
  · refine le_antisymm h1 ?_
    exact le_of_mul_le_mul_right (by nlinarith [h2]) hpos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 共形因子在 `N` 上为正（`U` 在 `N` 上 immersion + 共形）。 -/
theorem diskMapConformalCoefficient_pos_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (q : N) :
    0 < diskMapConformalCoefficient g U q := by
  rcases (diskMapConformalCoefficient_nonneg g U q).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q = 0 :=
      ((hconf q q.2).coefficient_eq_zero_iff).mp h.symm
    have hinj := hiN q
    have h0' : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q = 0 := by
      rw [DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N q]
      exact h0
    have h10 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q (1 : ℂ) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q (0 : ℂ) := by
      rw [h0']
      rfl
    have h01 : (1 : ℂ) = 0 := @hinj (1 : ℂ) (0 : ℂ) h10
    exact one_ne_zero h01

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- `U` 在 `N` 上光滑（子类型版 ⇒ 开集上的 `ContMDiffOn`）。 -/
theorem contMDiffOn_of_subtype_WS2 {U : ℂ → M} (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q)) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
  intro z hz
  exact (contMDiffAt_subtype_iff.mp
    (hUN.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 共形因子在 `N` 上光滑、为正。 -/
theorem conformalFactor_data_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) :
    ContDiffOn ℝ ∞ (diskMapConformalCoefficient g U) (N : Set ℂ) ∧
      ∀ z ∈ N, 0 < diskMapConformalCoefficient g U z :=
  ⟨contDiffOn_diskMapConformalCoefficient g N.isOpen (contMDiffOn_of_subtype_WS2 N hUN),
    fun z hz => diskMapConformalCoefficient_pos_WS2 g N hiN hconf ⟨z, hz⟩⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 共形时诱导度量 `gN = λ · 欧氏内积`。 -/
theorem pullback_inner_conformal_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (q : N) (v w : ℂ) :
    (g.pullback (fun p : N => U p) hUN hiN).inner q v w =
      diskMapConformalCoefficient g U q * inner ℝ v w := by
  have hdf := DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N q
  change g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q w) = _
  rw [hdf]
  exact (hconf q q.2).inner_partials v w

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 共形时面积密度 = 共形因子。 -/
theorem riemannianAreaDensity_conformal_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    {z : ℂ} (h : DiskMapConformalAt g U z) :
    riemannianAreaDensity g U z = diskMapConformalCoefficient g U z := by
  have hnn := diskMapConformalCoefficient_nonneg g U z
  unfold riemannianAreaDensity tangentTwoJacobian
  change Real.sqrt (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) *
    g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) -
    g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) ^ 2) = _
  rw [h.1, ← h.2]
  unfold diskMapConformalCoefficient at hnn ⊢
  rw [show ∀ a : ℝ, a * a - 0 ^ 2 = a ^ 2 from fun a => by ring, Real.sqrt_sq hnn]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- `λ · |∇φ|²_{gN} = ‖dψ‖²`（`φ = ψ|_N`）。 -/
theorem lam_mul_gradSq_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (ψ : ℂ → ℝ) (q : N) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    diskMapConformalCoefficient g U q *
        gN.inner q (gradFun gN (fun p : N => ψ p) q) (gradFun gN (fun p : N => ψ p) q) =
      ‖fderiv ℝ ψ q‖ ^ 2 := by
  intro gN
  set G : ℂ := gradFun gN (fun p : N => ψ p) q with hG
  have hd : ∀ v : ℂ, gN.inner q G v = fderiv ℝ ψ q v := by
    intro v
    rw [hG, inner_gradFun gN (fun p : N => ψ p) q v,
      DifferentialGeometry.mfderiv_restrict_open ψ N q, mfderiv_eq_fderiv]
    rfl
  have hc : ∀ v w : ℂ, gN.inner q v w = diskMapConformalCoefficient g U q * inner ℝ v w :=
    pullback_inner_conformal_WS2 g N hUN hiN hconf q
  have hi : ∀ v w : ℂ, inner ℝ v w = v.re * w.re + v.im * w.im := by
    intro v w
    simp [Complex.inner, Complex.mul_re, mul_comm]
  have ha : diskMapConformalCoefficient g U q * G.re = fderiv ℝ ψ q 1 := by
    have h := (hc G 1).symm.trans (hd 1)
    rw [hi] at h
    simpa using h
  have hb : diskMapConformalCoefficient g U q * G.im = fderiv ℝ ψ q Complex.I := by
    have h := (hc G Complex.I).symm.trans (hd Complex.I)
    rw [hi] at h
    simpa using h
  have hGG : gN.inner q G G =
      diskMapConformalCoefficient g U q * (G.re ^ 2 + G.im ^ 2) := by
    have h := hc G G
    rw [hi] at h
    rw [h]
    ring
  rw [norm_sq_complex_clm_WS2, hGG, ← ha, ← hb]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 共形时：`∫_N F dμ_{gN} = ∫_{N} H dx dy`（`λ F = H` 在 `N` 上）。 -/
theorem integral_pullback_conformal_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (F : N → ℝ) (H : ℂ → ℝ)
    (hFH : ∀ q : N, diskMapConformalCoefficient g U q * F q = H q) :
    ∫ q : N, F q ∂(riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N)
        (g.pullback (fun p : N => U p) hUN hiN)) = ∫ z in (N : Set ℂ), H z := by
  have hlamc : Continuous fun q : N => diskMapConformalCoefficient g U q :=
    ((contDiffOn_diskMapConformalCoefficient g N.isOpen
      (contMDiffOn_of_subtype_WS2 N hUN)).continuousOn).domRestrict
  have hvol := riemannianVolumeMeasure_induced_complex_open N g U hUN hiN
  have hfun : (fun q : N => ENNReal.ofReal (riemannianAreaDensity g U q)) =
      fun q : N => ENNReal.ofReal (diskMapConformalCoefficient g U q) := by
    funext q
    rw [riemannianAreaDensity_conformal_WS2 g (hconf q q.2)]
  rw [hvol, hfun]
  let μD := MeasureTheory.Measure.comap (Subtype.val : N → ℂ) (volume : MeasureTheory.Measure ℂ)
  have hJm : Measurable fun q : N => ENNReal.ofReal (diskMapConformalCoefficient g U q) :=
    ENNReal.measurable_ofReal.comp hlamc.measurable
  have hJfin : ∀ᵐ (q : N) ∂μD,
      ENNReal.ofReal (diskMapConformalCoefficient g U (q : ℂ)) < (⊤ : ENNReal) :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hJm hJfin]
  have hval : MeasurableEmbedding (Subtype.val : N → ℂ) :=
    N.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel N)
  have hmap := hval.integral_map (μ := μD) H
  rw [hval.map_comap, Subtype.range_coe] at hmap
  refine Eq.trans ?_ hmap.symm
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (diskMapConformalCoefficient_nonneg g U q), smul_eq_mul]
  exact hFH q

/-- `ψ` 在 `ℂ` 上的紧支集（含于 `N`）限制到 `N` 仍是紧支集。 -/
theorem hasCompactSupport_comp_val_WS2 (N : TopologicalSpace.Opens ℂ) {ψ : ℂ → ℝ}
    (hc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ (N : Set ℂ)) :
    HasCompactSupport (fun q : N => ψ q) := by
  have hK : IsCompact ((Subtype.val : N → ℂ) ⁻¹' tsupport ψ) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_inter_range,
      Subtype.range_coe, Set.inter_eq_left.mpr hsub]
    exact hc
  refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
  refine closure_minimal (fun q hq => subset_tsupport ψ hq) ?_
  exact (isClosed_tsupport ψ).preimage continuous_subtype_val

open scoped Classical in
/-- 延拓函数在 `N` 内与原函数一致。 -/
theorem dite_mem_WS2 (N : TopologicalSpace.Opens ℂ) (f : N → ℝ) (q : N) :
    (if hz : (q : ℂ) ∈ N then f ⟨q, hz⟩ else 0) = f q := by
  simp [q.2]

open scoped Classical in
/-- `N` 上的 `C^∞` 函数延拓为 `ℂ` 上的函数（`N` 外取 `0`），在 `N` 上 `ContDiffOn`。 -/
theorem contDiffOn_extend_WS2 (N : TopologicalSpace.Opens ℂ) (f : N → ℝ)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (fun z : ℂ => if hz : z ∈ N then f ⟨z, hz⟩ else 0) (N : Set ℂ) := by
  have hfun : (fun q : N => (fun z : ℂ => if hz : z ∈ N then f ⟨z, hz⟩ else 0) q) = f := by
    funext q
    exact dite_mem_WS2 N f q
  rw [← contMDiffOn_iff_contDiffOn]
  intro z hz
  have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun q : N => (fun z : ℂ => if hz : z ∈ N then f ⟨z, hz⟩ else 0) q) ⟨z, hz⟩ := by
    rw [hfun]
    exact hf.contMDiffAt
  exact ((contMDiffAt_subtype_iff (U := N)
    (f := fun z : ℂ => if hz : z ∈ N then f ⟨z, hz⟩ else 0) (x := ⟨z, hz⟩)).mp
      h1).contMDiffWithinAt

/-- 紧集上连续、紧集外为零 ⇒ 可积。 -/
theorem integrable_of_continuousOn_WS2 {f : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hz : ∀ x, x ∉ K → f x = 0) : Integrable f := by
  refine (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    (hf.integrableOn_compact hK)
  intro x hx
  by_contra h
  exact hx (hz x h)

/-- `tsupport ψ` 外 `ψ` 与 `dψ` 为零。 -/
theorem fderiv_eq_zero_of_notMem_tsupport_WS2 {ψ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport ψ) :
    ψ x = 0 ∧ fderiv ℝ ψ x = 0 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hx (subset_tsupport ψ h)
  · by_contra h
    exact hx (support_fderiv_subset ℝ h)

/-- `h`（在 `N` 上连续）下 `h·ψ²` 可积。 -/
theorem integrable_weight_sq_WS2 {N : TopologicalSpace.Opens ℂ} {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ (N : Set ℂ))
    {h : ℂ → ℝ} (hh : ContinuousOn h (N : Set ℂ)) : Integrable (fun x => h x * ψ x ^ 2) := by
  refine integrable_of_continuousOn_WS2 hc
    ((hh.mono hsub).mul (hψ.continuous.pow 2).continuousOn) ?_
  intro x hx
  simp [(fderiv_eq_zero_of_notMem_tsupport_WS2 hx).1]

/-- `‖dψ‖²` 可积。 -/
theorem integrable_gradSq_WS2 {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := by
  refine integrable_of_continuousOn_WS2 hc
    ((hψ.continuous_fderiv (by simp)).norm.pow 2).continuousOn ?_
  intro x hx
  simp [(fderiv_eq_zero_of_notMem_tsupport_WS2 hx).2]

/-- 权 `h`（在 `N` 上连续）下 `‖dψ‖² + h·ψ²` 可积。 -/
theorem integrable_energy_WS2 {N : TopologicalSpace.Opens ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ (N : Set ℂ)) {h : ℂ → ℝ}
    (hh : ContinuousOn h (N : Set ℂ)) :
    Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 + h x * ψ x ^ 2) :=
  (integrable_gradSq_WS2 hψ hc).add (integrable_weight_sq_WS2 hψ hc hsub hh)

/-- **G1a `stability_inequality_conformal_WS2`.**  Morrey 型共形盘（`hconf`：`U` 在 `N` 上共形）的
regular part `N` 上的 stability inequality 的平面形式：存在 `VJ ∈ C^∞(N)`（`= K_Σ − q̃`，
`≤ K_Σ − R/2`），对一切 `ψ ∈ C_c^∞(ℂ)`、`tsupport ψ ⊆ N`：
`0 ≤ ∫_ℂ ‖dψ‖² + λ·VJ·ψ² dx dy`，`λ = diskMapConformalCoefficient g U`（EIG 的 `W = λ·VJ`）。 -/
theorem stability_inequality_conformal_WS2 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hUN hiN).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun p : N => U p) hUN hiN)
        g (fun p : N => U p) q (b i) (b i) = 0)
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (N : Set ℂ) ∧
      (∀ q : N, VJ q = scalarCurv gN q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q)) ∧
      (∀ q : N, VJ q ≤ scalarCurv gN q / 2 - scalarCurv g (U q) / 2) ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (N : Set ℂ) →
        Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
          diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) ∧
        0 ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) := by
  classical
  intro gN
  obtain ⟨VJ, hform, -, hbound, hstab⟩ :=
    stability_inequality_gauss_WS hdim g W γ hExt hW htr hmin N hNball hUN hiN hint
      ν hν hunit hnormal hmean
  have hlamC : ContDiffOn ℝ ∞ (diskMapConformalCoefficient g U) (N : Set ℂ) :=
    contDiffOn_diskMapConformalCoefficient g N.isOpen (contMDiffOn_of_subtype_WS2 N hUN)
  have hVJC := contDiffOn_extend_WS2 N VJ VJ.contMDiff
  refine ⟨fun z => if hz : z ∈ N then VJ ⟨z, hz⟩ else 0, hVJC, ?_, ?_, ?_⟩
  · intro q
    beta_reduce
    rw [dite_mem_WS2 N VJ q]
    exact hform q
  · intro q
    beta_reduce
    rw [dite_mem_WS2 N VJ q]
    exact hbound q
  · intro ψ hψ hψc hψN
    have hint' := integrable_energy_WS2 hψ hψc hψN
      ((hlamC.continuousOn).mul (hVJC.continuousOn))
    refine ⟨?_, ?_⟩
    · refine hint'.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
    have hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun q : N => ψ q) :=
      hψ.contMDiff.comp contMDiff_subtype_val
    obtain ⟨-, hnn⟩ := hstab (fun q : N => ψ q) hφ (hasCompactSupport_comp_val_WS2 N hψc hψN)
    rw [integral_pullback_conformal_WS2 g N hUN hiN hconf _
      (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
        diskMapConformalCoefficient g U x * (if hz : x ∈ N then VJ ⟨x, hz⟩ else 0) * ψ x ^ 2)
      (fun q => by
        rw [mul_add, lam_mul_gradSq_WS2 g N hUN hiN hconf ψ q, dite_mem_WS2 N VJ q]
        ring)] at hnn
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hnn
    · exact hnn
    · intro x hx
      have hx' : x ∉ tsupport ψ := fun h => hx (hψN h)
      obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
      simp [h1, h2]

/-- **G1b `stability_inequality_scalar_lower_conformal_WS2`.**  `R∘U ≥ σ`（在 `ψ ≠ 0` 处）⇒
`(σ/2) ∫ λψ² ≤ ∫ ‖dψ‖² + λ·K_Σ·ψ²`，`K_Σ = scalarCurv gN / 2`。 -/
theorem stability_inequality_scalar_lower_conformal_WS2 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hUN hiN).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun p : N => U p) hUN hiN)
        g (fun p : N => U p) q (b i) (b i) = 0)
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (σ : ℝ) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    ∃ K : ℂ → ℝ, ContDiffOn ℝ ∞ K (N : Set ℂ) ∧ (∀ q : N, K q = scalarCurv gN q / 2) ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (N : Set ℂ) →
        (∀ x ∈ N, ψ x ≠ 0 → σ ≤ metricScalarAt g (U x)) →
        Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
          diskMapConformalCoefficient g U x * K x * ψ x ^ 2) ∧
        Integrable (fun x => diskMapConformalCoefficient g U x * ψ x ^ 2) ∧
        (σ / 2) * ∫ x, diskMapConformalCoefficient g U x * ψ x ^ 2 ≤
          ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * K x * ψ x ^ 2) := by
  classical
  intro gN
  obtain ⟨VJ, -, -, hbound, hstab⟩ :=
    stability_inequality_conformal_WS2 hdim g W γ hExt hW htr hmin N hNball hUN hiN hint
      ν hν hunit hnormal hmean hconf
  have hlamC : ContDiffOn ℝ ∞ (diskMapConformalCoefficient g U) (N : Set ℂ) :=
    contDiffOn_diskMapConformalCoefficient g N.isOpen (contMDiffOn_of_subtype_WS2 N hUN)
  have hKC := contDiffOn_extend_WS2 N (fun q : N => scalarCurv gN q / 2)
    ((scalarCurv_contMDiff gN).div_const 2)
  obtain ⟨K, hKC, hK⟩ : ∃ K : ℂ → ℝ, ContDiffOn ℝ ∞ K (N : Set ℂ) ∧
      ∀ q : N, K q = scalarCurv gN q / 2 :=
    ⟨_, hKC, fun q => dite_mem_WS2 N (fun q : N => scalarCurv gN q / 2) q⟩
  refine ⟨K, hKC, hK, ?_⟩
  intro ψ hψ hψc hψN hσ
  obtain ⟨hI, hnn⟩ := hstab ψ hψ hψc hψN
  have hI1 : Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
      diskMapConformalCoefficient g U x * K x * ψ x ^ 2) :=
    integrable_energy_WS2 hψ hψc hψN (hlamC.continuousOn.mul hKC.continuousOn)
  have hI2 : Integrable (fun x => diskMapConformalCoefficient g U x * ψ x ^ 2) :=
    integrable_weight_sq_WS2 hψ hψc hψN hlamC.continuousOn
  have hle : ∀ x : ℂ, ‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2 ≤
      (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * K x * ψ x ^ 2) -
        (σ / 2) * (diskMapConformalCoefficient g U x * ψ x ^ 2) := by
    intro x
    by_cases hψx : ψ x = 0
    · simp [hψx]
    · have hxN : x ∈ N := hψN (subset_tsupport ψ hψx)
      have h1 : VJ x ≤ scalarCurv gN ⟨x, hxN⟩ / 2 - scalarCurv g (U x) / 2 :=
        hbound ⟨x, hxN⟩
      have h2 := hσ x hxN hψx
      rw [metricScalar_eq_scal] at h2
      have hKx : K x = scalarCurv gN ⟨x, hxN⟩ / 2 := hK ⟨x, hxN⟩
      have hcoef : VJ x ≤ K x - σ / 2 := by linarith
      have hlam0 := diskMapConformalCoefficient_nonneg g U x
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hlam0)
        (sq_nonneg (ψ x))
      nlinarith [this]
  have hint2 : Integrable (fun x => (‖fderiv ℝ ψ x‖ ^ 2 +
      diskMapConformalCoefficient g U x * K x * ψ x ^ 2) -
        (σ / 2) * (diskMapConformalCoefficient g U x * ψ x ^ 2)) :=
    hI1.sub (hI2.const_mul (σ / 2))
  have hmono := integral_mono hI hint2 hle
  rw [integral_sub hI1 (hI2.const_mul (σ / 2)), integral_const_mul] at hmono
  refine ⟨hI1, hI2, ?_⟩
  linarith

/-- **G1 `IsMorreyDisk` 版（共形 stability）.**  `hmin`、`hmean`、`hconf` 自动
（`IsMorreyDisk.area_eq_morreyLeastAreaS`、harmonic + conformal）。 -/
theorem IsMorreyDisk.stability_inequality_conformal_WS2 [T3Space M]
    (hdim : Module.finrank ℝ E = 3)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (N : Set ℂ) ∧
      (∀ q : N, VJ q = scalarCurv gN q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q)) ∧
      (∀ q : N, VJ q ≤ scalarCurv gN q / 2 - scalarCurv g (U q) / 2) ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (N : Set ℂ) →
        Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
          diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) ∧
        0 ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) := by
  intro gN
  have hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W →
        riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    intro v hv hw hWv
    rw [hu.area_eq_morreyLeastAreaS hdim hγ hW]
    exact morreyLeastAreaS_le g hv hw hWv
  have hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) =
        gN.inner z v w := by
    intro z v w
    have hdf := DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z
    exact (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U z) (L v) (L w)) hdf).symm
  have hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (fun p : N => U p) q (b i) (b i) = 0 :=
    fun q b' hb' => sum_secondFundamentalForm_orthonormal_eq_zero_WS N gN g U hUN hmetric q
      (hu.conformal_of_extension hExt q (hNball q.property))
      (hu.tension_eq_zero_of_extension hExt q (hNball q.property)) b' hb'
  exact DifferentialGeometry.Geometry.stability_inequality_conformal_WS2 hdim g W γ hExt hW
    hu.trace hmin N hNball hUN hiN hint ν hν hunit hnormal hmean
    (fun z hz => hu.conformal_of_extension hExt z (hNball hz))

/-- **G1 consumer：EIG 的 Rayleigh 商输入形状.**  `IsMorreyDisk` 的 regular part `N` 上：
权 `ρ = λ`（`C^∞(N)`，`> 0`）与势 `Wt = λ·VJ`（`C^∞(N)`）使得对一切开子集 `Ω ⊆ N` 与
`ψ ∈ C_c^∞(Ω)`：`0 ≤ ∫_Ω ‖dψ‖² + Wt ψ²`。 -/
theorem IsMorreyDisk.planar_stability_WS2 [T3Space M] (hdim : Module.finrank ℝ E = 3)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0) :
    ∃ ρ Wt : ℂ → ℝ, ContDiffOn ℝ ∞ ρ (N : Set ℂ) ∧ ContDiffOn ℝ ∞ Wt (N : Set ℂ) ∧
      (∀ z ∈ N, 0 < ρ z) ∧
      ∀ Ω : Set ℂ, Ω ⊆ (N : Set ℂ) → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ω → 0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + Wt x * ψ x ^ 2) := by
  have hconf : ∀ z ∈ N, DiskMapConformalAt g U z :=
    fun z hz => hu.conformal_of_extension hExt z (hNball hz)
  obtain ⟨hlamC, hlamP⟩ := conformalFactor_data_WS2 g N hUN hiN hconf
  obtain ⟨VJ, hVJC, -, -, hstab⟩ :=
    IsMorreyDisk.stability_inequality_conformal_WS2 hdim hγ hu hExt W hW N hNball hUN hiN hint
      ν hν hunit hnormal
  refine ⟨diskMapConformalCoefficient g U, fun x => diskMapConformalCoefficient g U x * VJ x,
    hlamC, hlamC.mul hVJC, hlamP, ?_⟩
  intro Ω hΩ ψ hψ hψc hψΩ
  have h := (hstab ψ hψ hψc (hψΩ.trans hΩ)).2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)] at h
  · refine le_of_le_of_eq h (integral_congr_ae (Eventually.of_forall fun x => ?_))
    simp only [mul_assoc]
  · intro x hx
    have hx' : x ∉ tsupport ψ := fun hh => hx (hψΩ hh)
    obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
    simp [h1, h2]

end DifferentialGeometry.Geometry
