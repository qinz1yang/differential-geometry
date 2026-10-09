import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionEdgeSidesR10
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFlatFIX
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairCutConfig

/-!
# O-MY-R10PL G1/G2 consumers：平坦标准盘的 R10 witness（`_R10`）

* G1：`flatDisk_relRegularNbhd_R10`——一般 producer `relative_regular_nbhd_spine_R10`
  （derived neighborhood）
  对 `flatDisk_prepared_FIX` 实例化。
* G2：R9 字段 `local_product` 与 `ambient_collar` 的 flat witness，取 `Nb = h(|A|) = W`
  （`W = {‖π q‖ + |q₂| ≤ 1}`，double cone）：
  - collapse：`R q = flat(π q)`（竖直投影到 sheet），`H(t, q) = q − t q₂ e₃`；
  - 2-strata：开像面 `O ⊆ flat(D°)` 的两侧 = `∂W` 上 `±q₂ > 0` 的部分，section `y ↦ flat(π y) ± (1 − ‖π y‖) e₃`；
  - 1-strata：`T` 的内部边 `{0, v}` 恰有两个 germs `{0, v, a}`、`{0, v, b}`（`m = 1`），两个 sector = 上下两侧；
    `F` 单射，没有 transverse collision edge；
  - ambient collar：`O = univ`，`G(t, q) = (1 − t + t / max 1 ‖q‖_W) • q`（沿 lens gauge 的径向压缩）。
  再经联合 producer 得 `flatDisk_sectorControlled_R10`（同一 witness 的 R10.1 + R10.2 + `HO`，非空）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Bundle Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal Manifold unitInterval

namespace DifferentialGeometry.Geometry

/-! ## G1 consumer -/

/-- **G1 consumer**：一般 R10.1 producer（derived neighborhood）对平坦标准盘的 prepared witness 实例化。 -/
theorem flatDisk_relRegularNbhd_R10 :
    ∃ (Nb : Set E3_FIX) (R : E3_FIX → E3_FIX), IsRelRegularNbhd_R10 flatDisk_FIX Nb R ∧
      Nb ⊆ bipyramidRealization_FIX '' bipyramid_FIX.space :=
  relative_regular_nbhd_spine_R10 flatDisk_prepared_FIX

/-! ## lens 坐标 -/

/-- 竖直单位向量 `e₃`。 -/
abbrev e3_R10 : E3_FIX := mk3_FIX 0 0 1

theorem proj12_e3_R10 : proj12_FIX e3_R10 = 0 := by
  rw [proj12_mk3_FIX]
  exact Complex.ext rfl rfl

theorem pz_e3_R10 : pzCLM_FIX e3_R10 = 1 := pz_mk3_FIX 0 0 1

theorem decomp_R10 (q : E3_FIX) : flatCLM_FIX (proj12_FIX q) + pzCLM_FIX q • e3_R10 = q := by
  rw [flat_eq_mk3_FIX, mk3_add_smul_FIX, pzCLM_apply_FIX]
  exact (mk3_coord_FIX q).symm

theorem proj12_add_e3_R10 (q : E3_FIX) (c : ℝ) : proj12_FIX (q + c • e3_R10) = proj12_FIX q := by
  rw [proj12_add_FIX, proj12_smul_FIX, proj12_e3_R10, smul_zero, add_zero]

theorem pz_add_e3_R10 (q : E3_FIX) (c : ℝ) : pzCLM_FIX (q + c • e3_R10) = pzCLM_FIX q + c := by
  rw [map_add, map_smul, pz_e3_R10, smul_eq_mul, mul_one]

/-- lens gauge `‖π q‖ + |q₂|`（`W = {gauge ≤ 1}`）。 -/
def lensGauge_R10 (q : E3_FIX) : ℝ := ‖proj12_FIX q‖ + |pzCLM_FIX q|

theorem continuous_lensGauge_R10 : Continuous lensGauge_R10 := continuous_realizationGauge_FIX

theorem lensGauge_smul_R10 {t : ℝ} (ht : 0 ≤ t) (q : E3_FIX) :
    lensGauge_R10 (t • q) = t * lensGauge_R10 q := by
  simp only [lensGauge_R10, proj12_smul_FIX, map_smul, smul_eq_mul, norm_smul, abs_mul,
    Real.norm_eq_abs, abs_of_nonneg ht]
  ring

theorem mem_W_iff_R10 {q : E3_FIX} : q ∈ realizationImage_FIX ↔ lensGauge_R10 q ≤ 1 := Iff.rfl

theorem frontier_W_R10 : frontier realizationImage_FIX = {q | lensGauge_R10 q = 1} :=
  Subset.antisymm (frontier_le_subset_eq continuous_lensGauge_R10 continuous_const) fun _ hq =>
    mem_frontier_sublevel_FIX continuous_lensGauge_R10 (fun _ q ht => lensGauge_smul_R10 ht q) hq

/-- 竖直投影 `R q = flat(π q)`。 -/
def lensProj_R10 (q : E3_FIX) : E3_FIX := flatCLM_FIX (proj12_FIX q)

theorem continuous_lensProj_R10 : Continuous lensProj_R10 :=
  flatCLM_FIX.continuous.comp continuous_proj12_FIX

/-- 直线压扁 `H(t, q) = q − t q₂ e₃`。 -/
def lensHom_R10 (p : unitInterval × E3_FIX) : E3_FIX :=
  p.2 + (-((p.1 : ℝ) * pzCLM_FIX p.2)) • e3_R10

theorem continuous_lensHom_R10 : Continuous lensHom_R10 := by
  unfold lensHom_R10
  fun_prop

theorem norm_proj12_lt_R10 {q : E3_FIX} (hq : lensProj_R10 q ∈ flatCLM_FIX '' ball (0 : ℂ) 1) :
    ‖proj12_FIX q‖ < 1 := by
  obtain ⟨w, hw, hwq⟩ := hq
  rw [← flatCLM_injective_FIX hwq]
  rwa [mem_ball, dist_zero_right] at hw

/-- `±1`。 -/
def bsgn_R10 (b : Bool) : ℝ := if b then 1 else -1

theorem bsgn_mul_self_R10 (b : Bool) : bsgn_R10 b * bsgn_R10 b = 1 := by
  cases b <;> norm_num [bsgn_R10]

theorem abs_bsgn_mul_R10 (b : Bool) (x : ℝ) : |bsgn_R10 b * x| = |x| := by
  cases b <;> simp [bsgn_R10]

/-- 侧 section `y ↦ flat(π y) ± (1 − ‖π y‖) e₃`。 -/
def lensSec_R10 (b : Bool) (y : E3_FIX) : E3_FIX :=
  flatCLM_FIX (proj12_FIX y) + (bsgn_R10 b * (1 - ‖proj12_FIX y‖)) • e3_R10

theorem continuous_lensSec_R10 (b : Bool) : Continuous (lensSec_R10 b) := by
  unfold lensSec_R10
  have := continuous_proj12_FIX
  fun_prop

/-- 开像集 `O` 上的 `b` 侧：`∂W` 中投影落在 `O`、`±q₂ > 0` 的点。 -/
def lensSide_R10 (O : Set E3_FIX) (b : Bool) : Set E3_FIX :=
  {q | q ∈ frontier realizationImage_FIX ∧ lensProj_R10 q ∈ O ∧ 0 < bsgn_R10 b * pzCLM_FIX q}

theorem lensSec_mem_R10 {O : Set E3_FIX} (hOD : O ⊆ flatCLM_FIX '' ball (0 : ℂ) 1) (b : Bool)
    {y : E3_FIX} (hy : y ∈ O) :
    lensSec_R10 b y ∈ lensSide_R10 O b ∧ lensProj_R10 (lensSec_R10 b y) = y := by
  obtain ⟨w, hw, rfl⟩ := hOD hy
  have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have hp : proj12_FIX (lensSec_R10 b (flatCLM_FIX w)) = w := by
    rw [lensSec_R10, proj12_add_e3_R10, proj12_flat_FIX, proj12_flat_FIX]
  have hz : pzCLM_FIX (lensSec_R10 b (flatCLM_FIX w)) = bsgn_R10 b * (1 - ‖w‖) := by
    rw [lensSec_R10, pz_add_e3_R10, pz_flat_FIX, proj12_flat_FIX, zero_add]
  have hR : lensProj_R10 (lensSec_R10 b (flatCLM_FIX w)) = flatCLM_FIX w := by
    rw [lensProj_R10, hp]
  refine ⟨⟨?_, by rw [hR]; exact hy, ?_⟩, hR⟩
  · rw [frontier_W_R10, mem_ofPred_eq, lensGauge_R10, hp, hz, abs_bsgn_mul_R10,
      abs_of_pos (by linarith)]
    ring
  · rw [hz, ← mul_assoc, bsgn_mul_self_R10, one_mul]
    linarith

theorem eq_lensSec_R10 {O : Set E3_FIX} (hOD : O ⊆ flatCLM_FIX '' ball (0 : ℂ) 1) {b : Bool}
    {q : E3_FIX} (hq : q ∈ lensSide_R10 O b) : q = lensSec_R10 b (lensProj_R10 q) := by
  obtain ⟨hfr, hO, hpos⟩ := hq
  have hlt := norm_proj12_lt_R10 (hOD hO)
  rw [frontier_W_R10, mem_ofPred_eq, lensGauge_R10] at hfr
  have habs : |pzCLM_FIX q| = bsgn_R10 b * pzCLM_FIX q := by
    rw [← abs_bsgn_mul_R10 b, abs_of_pos hpos]
  have hz : pzCLM_FIX q = bsgn_R10 b * (1 - ‖proj12_FIX q‖) := by
    have h1 : bsgn_R10 b * pzCLM_FIX q = 1 - ‖proj12_FIX q‖ := by linarith
    rw [← h1, ← mul_assoc, bsgn_mul_self_R10, one_mul]
  rw [lensSec_R10, lensProj_R10, proj12_flat_FIX, ← hz, decomp_R10]

/-- 2-strata local model：`O ⊆ flat(D°)` preconnected ⇒ `O` 在 `∂W` 上恰两侧。 -/
theorem lens_isTwoSided_R10 {O : Set E3_FIX} (hO : IsPreconnected O)
    (hOD : O ⊆ flatCLM_FIX '' ball (0 : ℂ) 1) :
    IsTwoSidedFace_R10 realizationImage_FIX lensProj_R10 O (lensSide_R10 O) := by
  have himg : ∀ b, lensSide_R10 O b = lensSec_R10 b '' O := by
    intro b
    ext q
    constructor
    · intro hq
      exact ⟨_, hq.2.1, (eq_lensSec_R10 hOD hq).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact (lensSec_mem_R10 hOD b hy).1
  refine ⟨?_, ?_, fun b => ⟨?_, ?_, ?_, lensSec_R10 b, (continuous_lensSec_R10 b).continuousOn,
    fun y hy => lensSec_mem_R10 hOD b hy⟩⟩
  · rw [Set.disjoint_left]
    rintro q ⟨-, -, h1⟩ ⟨-, -, h2⟩
    simp only [bsgn_R10, ite_true, one_mul, Bool.false_eq_true, ite_false] at h1 h2
    linarith
  · ext q
    constructor
    · rintro (⟨hfr, hO', -⟩ | ⟨hfr, hO', -⟩) <;> exact ⟨hfr, hO'⟩
    · rintro ⟨hfr, hO'⟩
      have hlt := norm_proj12_lt_R10 (hOD hO')
      have hfr' := hfr
      rw [frontier_W_R10, mem_ofPred_eq, lensGauge_R10] at hfr'
      rcases lt_trichotomy (pzCLM_FIX q) 0 with hneg | hzero | hpos
      · right
        refine ⟨hfr, hO', ?_⟩
        simp only [bsgn_R10, Bool.false_eq_true, ite_false]
        linarith
      · rw [hzero, abs_zero] at hfr'
        linarith
      · left
        refine ⟨hfr, hO', ?_⟩
        simp only [bsgn_R10, ite_true, one_mul]
        exact hpos
  · rw [himg b]
    exact hO.image _ (continuous_lensSec_R10 b).continuousOn
  · intro q hq q' hq' hqq
    rw [eq_lensSec_R10 hOD hq, eq_lensSec_R10 hOD hq', hqq]
  · ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq.2.1
    · intro hy
      exact ⟨_, (lensSec_mem_R10 hOD b hy).1, (lensSec_mem_R10 hOD b hy).2⟩

/-- 侧的闭包在别处开像集上的部分仍在同号侧里。 -/
theorem closure_lensSide_inter_R10 {O O' : Set E3_FIX}
    (hO'D : O' ⊆ flatCLM_FIX '' ball (0 : ℂ) 1) (b : Bool) :
    closure (lensSide_R10 O b) ∩ lensProj_R10 ⁻¹' O' ⊆ lensSide_R10 O' b := by
  have hC : lensSide_R10 O b ⊆ {q | bsgn_R10 b * pzCLM_FIX q = 1 - ‖proj12_FIX q‖} := by
    rintro q ⟨hfr, -, hpos⟩
    rw [frontier_W_R10, mem_ofPred_eq, lensGauge_R10] at hfr
    rw [mem_ofPred_eq, ← abs_of_pos hpos, abs_bsgn_mul_R10]
    linarith
  have hCc : IsClosed {q : E3_FIX | bsgn_R10 b * pzCLM_FIX q = 1 - ‖proj12_FIX q‖} :=
    isClosed_eq (continuous_const.mul pzCLM_FIX.continuous)
      (continuous_const.sub continuous_proj12_FIX.norm)
  rintro q ⟨hq, hqO'⟩
  have hq' : bsgn_R10 b * pzCLM_FIX q = 1 - ‖proj12_FIX q‖ := closure_minimal hC hCc hq
  have hlt := norm_proj12_lt_R10 (hO'D hqO')
  refine ⟨?_, hqO', by linarith⟩
  rw [frontier_W_R10, mem_ofPred_eq, lensGauge_R10, ← abs_bsgn_mul_R10 b, hq',
    abs_of_pos (by linarith)]
  ring

/-- 若 `y ∈ O'` 在 `O` 的闭包里，则 `O` 的 `b` 侧闭包与 `O'` 的 `b` 侧相交。 -/
theorem closure_lensSide_inter_nonempty_R10 {O O' : Set E3_FIX}
    (hOD : O ⊆ flatCLM_FIX '' ball (0 : ℂ) 1) (hO'D : O' ⊆ flatCLM_FIX '' ball (0 : ℂ) 1)
    (b : Bool) {y : E3_FIX} (hyO' : y ∈ O') (hyO : y ∈ closure O) :
    (closure (lensSide_R10 O b) ∩ lensSide_R10 O' b).Nonempty := by
  refine ⟨lensSec_R10 b y, ?_, (lensSec_mem_R10 hO'D b hyO').1⟩
  refine closure_mono ?_ (mem_closure_image (continuous_lensSec_R10 b).continuousAt hyO)
  rintro _ ⟨y', hy', rfl⟩
  exact (lensSec_mem_R10 hOD b hy').1

/-! ## collapse 与 ambient collar -/

theorem lensHom_proj12_R10 (p : unitInterval × E3_FIX) :
    proj12_FIX (lensHom_R10 p) = proj12_FIX p.2 := proj12_add_e3_R10 _ _

theorem lensHom_pz_R10 (p : unitInterval × E3_FIX) :
    pzCLM_FIX (lensHom_R10 p) = (1 - (p.1 : ℝ)) * pzCLM_FIX p.2 := by
  rw [lensHom_R10, pz_add_e3_R10]
  ring

theorem range_flatDisk_R10 : Set.range flatDisk_FIX = flatCLM_FIX '' closedBall (0 : ℂ) 1 := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

/-- 径向压缩系数 `1 − t + t / max 1 gauge`。 -/
def collarCoeff_R10 (p : unitInterval × E3_FIX) : ℝ :=
  1 - (p.1 : ℝ) + (p.1 : ℝ) * (max 1 (lensGauge_R10 p.2))⁻¹

theorem continuous_collarCoeff_R10 : Continuous collarCoeff_R10 := by
  have ht : Continuous fun p : unitInterval × E3_FIX => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hm : Continuous fun p : unitInterval × E3_FIX => max 1 (lensGauge_R10 p.2) :=
    continuous_const.max (continuous_lensGauge_R10.comp continuous_snd)
  exact (continuous_const.sub ht).add
    (ht.mul (hm.inv₀ fun p => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'))

/-- **R9 字段 `ambient_collar` 的 flat witness**：`O = univ`，`G(t, q) = collarCoeff • q`。 -/
theorem flatDisk_ambientCollar_R10 :
    HasAmbientCollar_R10 (bipyramidRealization_FIX '' bipyramid_FIX.space) := by
  rw [realization_image_FIX]
  refine ⟨univ, fun p => collarCoeff_R10 p • p.2, isOpen_univ, subset_univ _,
    (continuous_collarCoeff_R10.smul continuous_snd).continuousOn, ?_, ?_, ?_, fun _ _ _ => trivial⟩
  · intro x _
    simp [collarCoeff_R10]
  · intro x _
    have hm : 0 < max 1 (lensGauge_R10 x) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hc : collarCoeff_R10 (1, x) = (max 1 (lensGauge_R10 x))⁻¹ := by
      simp [collarCoeff_R10]
    change lensGauge_R10 (collarCoeff_R10 (1, x) • x) ≤ 1
    rw [hc, lensGauge_smul_R10 (inv_nonneg.mpr hm.le), inv_mul_le_iff₀ hm, mul_one]
    exact le_max_right _ _
  · intro t x hx
    have hx' : lensGauge_R10 x ≤ 1 := hx
    change collarCoeff_R10 (t, x) • x = x
    rw [collarCoeff_R10, max_eq_left hx', inv_one, mul_one, sub_add_cancel, one_smul]

/-! ## `T` 的组合：内部边 `{0, v}` 与它的两个 germs -/

theorem convex_openSimplex_R10 (s : Finset ℂ) : Convex ℝ (openSimplex s) := by
  rintro x ⟨w, hw, hw1, rfl⟩ y ⟨w', hw', hw'1, rfl⟩ a b ha hb hab
  refine ⟨fun v => a * w v + b * w' v, fun v hv => ?_, ?_, ?_⟩
  · rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hw v hv)) (mul_nonneg hb (hw' v hv).le)
    · have hb1 : b = 1 := by linarith
      change 0 < a * w v + b * w' v
      rw [← ha', hb1, zero_mul, zero_add, one_mul]
      exact hw' v hv
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hw'1, mul_one, mul_one,
      hab]
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]

theorem zero_notMem_triVerts_R10 : (0 : ℂ) ∉ triVerts_FIX := by
  intro h
  simp only [triVerts_FIX, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;>
    simp [Complex.ext_iff, triV1_FIX, triV2_FIX, triV3_FIX] at h

theorem openSimplex_nonempty_R10 {s : Finset ℂ} (hs : s.Nonempty) : (openSimplex s).Nonempty :=
  ⟨_, centroid_mem_openSimplex hs⟩

/-- flat 的开像面：`O_s = flat(α(s°))`。 -/
abbrev flatFace_R10 (s : Finset ℂ) : Set E3_FIX :=
  openImageFace_R10 (⇑flatCLM_FIX) radialGrid_FIX s

theorem flatFace_preconnected_R10 (s : Finset ℂ) : IsPreconnected (flatFace_R10 s) :=
  ((convex_openSimplex_R10 s).isPreconnected.image _
    radialGrid_continuous_FIX.continuousOn).image _ flatCLM_FIX.continuous.continuousOn

theorem flatFace_subset_R10 {s : Finset ℂ} (hs : radialGrid_FIX '' openSimplex s ⊆ ball 0 1) :
    flatFace_R10 s ⊆ flatCLM_FIX '' ball (0 : ℂ) 1 :=
  image_mono hs

theorem flatFace_two_subset_R10 {s2 : Finset ℂ} (hs2 : s2 ∈ triComplex_FIX.faces)
    (hc : s2.card = 3) : flatFace_R10 s2 ⊆ flatCLM_FIX '' ball (0 : ℂ) 1 :=
  flatFace_subset_R10 (flatDisk_prepared_FIX.image_openSimplex_subset_ball_R10 hs2 hc)

/-- 边界边（`⊆ triVerts`）的开像在单位圆上，不满足内部条件。 -/
theorem not_interior_boundary_edge_R10 {e : Finset ℂ} (he : e ∈ triBoundary_FIX.faces) :
    ¬ radialGrid_FIX '' openSimplex e ⊆ ball 0 1 := by
  intro hball
  have hne : e.Nonempty := he.2.1
  have hz := centroid_mem_openSimplex hne
  have hmem : e.centroid ℝ id ∈ frontier {z : ℂ | triGauge_FIX z ≤ 1} := by
    rw [← convexHull_triVerts_FIX, frontier_triSet_FIX]
    exact triBoundary_FIX.convexHull_subset_space he (openSimplex_subset_convexHull e hz)
  rw [frontier_triSet_eq_FIX, mem_ofPred_eq] at hmem
  have h1 := hball (mem_image_of_mem _ hz)
  rw [mem_ball, dist_zero_right, norm_radialGrid_FIX, hmem] at h1
  exact lt_irrefl _ h1

/-- 内部边的形状：`e = {0, v}`，`v ∈ triVerts`。 -/
theorem interior_edge_eq_R10 {e : Finset ℂ} (he : e ∈ triComplex_FIX.faces) (hc : e.card = 2)
    (hball : radialGrid_FIX '' openSimplex e ⊆ ball 0 1) :
    ∃ v ∈ triVerts_FIX, e = {0, v} := by
  rcases (mem_coneComplex_faces_iff isConeBase_tri_FIX).mp he with h | h | ⟨τ, hτ, rfl⟩
  · exact absurd hball (not_interior_boundary_edge_R10 h)
  · rw [h] at hc
    simp at hc
  · have h0 : (0 : ℂ) ∉ τ := fun h0 => zero_notMem_triVerts_R10 (hτ.1 h0)
    rw [Finset.card_insert_of_notMem h0] at hc
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : τ.card = 1)
    exact ⟨v, hτ.1 (Finset.mem_singleton_self v), rfl⟩

/-- `F ∘ α` 单射 ⇒ 同开像的面相同（`T` 的面）。 -/
theorem face_eq_of_flatFace_eq_R10 {e e' : Finset ℂ} (he : e ∈ triComplex_FIX.faces)
    (he' : e' ∈ triComplex_FIX.faces) (hEq : flatFace_R10 e' = flatFace_R10 e) : e' = e := by
  have hinj : Function.Injective (⇑flatCLM_FIX ∘ radialGrid_FIX) :=
    flatCLM_injective_FIX.comp radialGrid_injective_FIX
  have hEq' : openSimplex e' = openSimplex e := by
    have h2 : (⇑flatCLM_FIX ∘ radialGrid_FIX) '' openSimplex e' =
        (⇑flatCLM_FIX ∘ radialGrid_FIX) '' openSimplex e := by
      rw [image_comp, image_comp]
      exact hEq
    exact hinj.image_injective h2
  have hz := centroid_mem_openSimplex (triComplex_FIX.nonempty_of_mem_faces he)
  exact face_eq_of_mem_openSimplex triComplex_FIX he' he (hEq' ▸ hz) hz

/-- 内部边 `{0, v}` 处的 germ `{0, v, x}`（`x ∈ triVerts`，`x ≠ v`）是 `T` 的 2-面。 -/
theorem germ_face_R10 {v x : ℂ} (hv : v ∈ triVerts_FIX) (hx : x ∈ triVerts_FIX) (hxv : x ≠ v) :
    ({0, v, x} : Finset ℂ) ∈ triComplex_FIX.faces ∧ ({0, v, x} : Finset ℂ).card = 3 := by
  have hv0 : v ≠ 0 := fun h => zero_notMem_triVerts_R10 (h ▸ hv)
  have hx0 : x ≠ 0 := fun h => zero_notMem_triVerts_R10 (h ▸ hx)
  have hτ : ({v, x} : Finset ℂ) ∈ triBoundary_FIX.faces := by
    refine ⟨Finset.insert_subset hv (Finset.singleton_subset_iff.mpr hx), by simp, fun h => ?_⟩
    have h2 : ({v, x} : Finset ℂ).card = 2 := Finset.card_pair (Ne.symm hxv)
    rw [h, triVerts_card_FIX] at h2
    omega
  refine ⟨(mem_coneComplex_faces_iff isConeBase_tri_FIX).mpr (Or.inr (Or.inr ⟨_, hτ, rfl⟩)), ?_⟩
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hv0, Ne.symm hx0]),
    Finset.card_pair (Ne.symm hxv)]

/-- `y₀ = F(α(v/2))` 在开像边 `O_{0v}` 里，且在每个 germ `{0, v, x}` 的开像面的闭包里。 -/
theorem half_point_R10 {v x : ℂ} (hv0 : v ≠ 0) (hx0 : x ≠ 0) (hxv : x ≠ v) :
    flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v)) ∈ flatFace_R10 {0, v} ∧
      flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v)) ∈ closure (flatFace_R10 {0, v, x}) := by
  refine ⟨mem_image_of_mem _ (mem_image_of_mem _ ?_), ?_⟩
  · refine ⟨fun _ => 1 / 2, fun _ _ => by norm_num, ?_, ?_⟩
    · rw [Finset.sum_pair (Ne.symm hv0)]
      norm_num
    · rw [Finset.sum_pair (Ne.symm hv0), smul_zero, zero_add]
  · have hcont : Continuous fun ε : ℝ =>
        flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v + ε • x)) :=
      flatCLM_FIX.continuous.comp (radialGrid_continuous_FIX.comp
        (continuous_const.add (continuous_id.smul continuous_const)))
    have ht : Tendsto (fun ε : ℝ => flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v + ε • x)))
        (𝓝[>] 0) (𝓝 (flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v)))) := by
      have h0 : Tendsto (fun ε : ℝ => flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v + ε • x)))
          (𝓝[>] 0) (𝓝 (flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v + (0 : ℝ) • x)))) :=
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [zero_smul, add_zero] using h0
    refine mem_closure_of_tendsto ht (Filter.eventually_of_mem
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) fun ε hε => ?_)
    refine mem_image_of_mem _ (mem_image_of_mem _ ?_)
    exact mem_openSimplex_triple (w₁ := 1 / 2 - ε) (w₂ := 1 / 2) (w₃ := ε) (Ne.symm hv0)
      (Ne.symm hx0) (Ne.symm hxv) (by linarith [hε.2]) (by norm_num) hε.1 (by ring)
      (by rw [smul_zero, zero_add])

/-- **1-strata local model（flat）**：内部边 `{0, v}` 的 realized rotation system，`m = 1`，
germs `{0, v, a}`、`{0, v, b}`（`triVerts \ {v} = {a, b}`），sector = 上 / 下两侧。 -/
theorem flat_rotation_R10 {e : Finset ℂ} (he : e ∈ triComplex_FIX.faces) (hc : e.card = 2)
    (hball : radialGrid_FIX '' openSimplex e ⊆ ball 0 1) :
    HasRealizedRotationSystem_R10 (E := E3_FIX) (⇑flatCLM_FIX) triComplex_FIX radialGrid_FIX
      realizationImage_FIX lensProj_R10 (fun s b => lensSide_R10 (flatFace_R10 s) b) e := by
  obtain ⟨v, hv, rfl⟩ := interior_edge_eq_R10 he hc hball
  have hv0 : v ≠ 0 := fun h => zero_notMem_triVerts_R10 (h ▸ hv)
  have hcard : (triVerts_FIX.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, triVerts_card_FIX]
  obtain ⟨a, b, hab, hEr⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ triVerts_FIX.erase v := by rw [hEr]; simp
  have hb : b ∈ triVerts_FIX.erase v := by rw [hEr]; simp
  obtain ⟨hav, haT⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbv, hbT⟩ := Finset.mem_erase.mp hb
  have ha0 : a ≠ 0 := fun h => zero_notMem_triVerts_R10 (h ▸ haT)
  have hb0 : b ≠ 0 := fun h => zero_notMem_triVerts_R10 (h ▸ hbT)
  set Oe := flatFace_R10 {0, v} with hOe
  have hOeD : Oe ⊆ flatCLM_FIX '' ball (0 : ℂ) 1 := flatFace_subset_R10 hball
  have hTS := lens_isTwoSided_R10 (flatFace_preconnected_R10 {0, v}) hOeD
  let germ : Fin (2 * 1) → Finset ℂ := fun j => if j.val = 0 then {0, v, a} else {0, v, b}
  let out : Fin (2 * 1) → Bool := fun j => decide (j.val = 0)
  have hgerm : ∀ k, ∃ x, x ∈ triVerts_FIX ∧ x ≠ v ∧ x ≠ 0 ∧ germ k = {0, v, x} := by
    intro k
    by_cases hk : k.val = 0
    · exact ⟨a, haT, hav, ha0, by simp only [germ, hk, ↓reduceIte]⟩
    · exact ⟨b, hbT, hbv, hb0, by simp only [germ, hk, ↓reduceIte]⟩
  have hgD : ∀ k, flatFace_R10 (germ k) ⊆ flatCLM_FIX '' ball (0 : ℂ) 1 := by
    intro k
    obtain ⟨x, hxT, hxv, -, hk⟩ := hgerm k
    rw [hk]
    exact flatFace_two_subset_R10 (germ_face_R10 hv hxT hxv).1 (germ_face_R10 hv hxT hxv).2
  have hy0 : ∀ k, flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v)) ∈ Oe ∧
      flatCLM_FIX (radialGrid_FIX ((1 / 2 : ℝ) • v)) ∈ closure (flatFace_R10 (germ k)) := by
    intro k
    obtain ⟨x, -, hxv, hx0, hk⟩ := hgerm k
    rw [hk]
    exact half_point_R10 hv0 hx0 hxv
  have hrot : ∀ j : Fin (2 * 1), (!out (finRotate (2 * 1) j)) = out j := by decide
  have hopp : ∀ j : Fin (2 * 1), finRotate (2 * 1) (finRotate (2 * 1) j) = j ∧
      finRotate (2 * 1) j ≠ j := by decide
  have hdist : ∀ j k : Fin (2 * 1), j ≠ k → out j = !out k := by decide
  have hab' : ({0, v, a} : Finset ℂ) ≠ {0, v, b} := by
    intro h
    have : a ∈ ({0, v, b} : Finset ℂ) := h ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    exacts [ha0 h1, hav h1, hab h1]
  refine ⟨1, germ, fun _ => {0, v}, finRotate (2 * 1), out,
    fun j => lensSide_R10 Oe (out j), one_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- germ 单射
    intro i j hij
    by_contra hne
    have hd := hdist i j hne
    by_cases hi : i.val = 0
    · have hj : j.val ≠ 0 := fun hj => hne (Fin.ext (hi.trans hj.symm))
      simp only [germ, hi, hj, ↓reduceIte] at hij
      exact hab' hij
    · have hj : j.val = 0 := by omega
      simp only [germ, hi, hj, ↓reduceIte] at hij
      exact hab' hij.symm
  · -- germ 与 half-sheet germs 双射
    intro s2
    constructor
    · rintro ⟨hs2, hs2c, e', he', -, he's2, hEq⟩
      have he'e : e' = {0, v} := face_eq_of_flatFace_eq_R10 he he' hEq
      obtain ⟨τ, hτ, rfl⟩ := triComplex_face_card_three_FIX hs2 hs2c
      have h0τ : (0 : ℂ) ∉ τ := fun h0 => zero_notMem_triVerts_R10 (hτ.1 h0)
      have hvτ : v ∈ τ := by
        have : v ∈ insert (0 : ℂ) τ := he's2 (he'e ▸ by simp)
        rcases Finset.mem_insert.mp this with h | h
        exacts [absurd h hv0, h]
      have hτc : τ.card = 2 := by
        rw [Finset.card_insert_of_notMem h0τ] at hs2c
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
        (by rw [Finset.card_erase_of_mem hvτ, hτc] : (τ.erase v).card = 1)
      have hxτ : x ∈ τ.erase v := by rw [hx]; simp
      obtain ⟨hxv, hxτ'⟩ := Finset.mem_erase.mp hxτ
      have hτeq : τ = {v, x} := by
        rw [← Finset.insert_erase hvτ, hx]
      have hxE : x ∈ triVerts_FIX.erase v := Finset.mem_erase.mpr ⟨hxv, hτ.1 hxτ'⟩
      rw [hEr] at hxE
      rcases Finset.mem_insert.mp hxE with rfl | hxb
      · exact ⟨⟨0, by norm_num⟩, by simp [germ, hτeq]⟩
      · rw [Finset.mem_singleton.mp hxb] at hτeq
        exact ⟨⟨1, by norm_num⟩, by simp [germ, hτeq]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨x, hxT, hxv, -, hj⟩ := hgerm j
      refine ⟨by rw [hj]; exact (germ_face_R10 hv hxT hxv).1,
        by rw [hj]; exact (germ_face_R10 hv hxT hxv).2, {0, v}, he, hc, ?_, rfl⟩
      rw [hj]
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with hu | hu
      exacts [Or.inl hu, Or.inr (Or.inl hu)]
  · -- sheetEdge
    intro j
    obtain ⟨x, -, -, -, hj⟩ := hgerm j
    refine ⟨he, hc, ?_, rfl⟩
    rw [hj]
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    rcases hu with hu | hu
    exacts [Or.inl hu, Or.inr (Or.inl hu)]
  · -- opp
    intro j
    exact ⟨(hopp j).1, (hopp j).2, rfl⟩
  · -- 无 transverse collision edge（`F` 单射）
    intro ht
    exfalso
    obtain ⟨-, ⟨w, -, hwz, hFw⟩, -⟩ :=
      ht.2 _ (mem_image_of_mem _ (show (1 / 2 : ℝ) • v ∈ openSimplex ({0, v} : Finset ℂ) from
        ⟨fun _ => 1 / 2, fun _ _ => by norm_num, by rw [Finset.sum_pair (Ne.symm hv0)]; norm_num,
          by rw [Finset.sum_pair (Ne.symm hv0), smul_zero, zero_add]⟩))
    exact hwz (flatCLM_injective_FIX hFw)
  · -- sectors 的并
    rw [← hTS.2.1]
    ext q
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      cases hoj : out j
      · rw [hoj] at hj
        exact Or.inr hj
      · rw [hoj] at hj
        exact Or.inl hj
    · rintro (hq | hq)
      · exact ⟨⟨0, by norm_num⟩, hq⟩
      · exact ⟨⟨1, by norm_num⟩, hq⟩
  · -- 两两不交
    intro j k hjk
    change Disjoint (lensSide_R10 Oe (out j)) (lensSide_R10 Oe (out k))
    rw [hdist j k hjk]
    cases out k
    · exact hTS.1
    · exact hTS.1.symm
  · intro j
    refine ⟨(hTS.2.2 (out j)).1, (hTS.2.2 (out j)).2.2.1,
      closure_lensSide_inter_R10 hOeD (out j), ?_,
      closure_lensSide_inter_nonempty_R10 (hgD j) hOeD (out j) (hy0 j).1 (hy0 j).2, ?_⟩
    · change closure (lensSide_R10 (flatFace_R10 (germ (finRotate (2 * 1) j)))
        (!out (finRotate (2 * 1) j))) ∩ _ ⊆ _
      rw [hrot j]
      exact closure_lensSide_inter_R10 hOeD (out j)
    · change (closure (lensSide_R10 (flatFace_R10 (germ (finRotate (2 * 1) j)))
        (!out (finRotate (2 * 1) j))) ∩ _).Nonempty
      rw [hrot j]
      exact closure_lensSide_inter_nonempty_R10 (hgD (finRotate (2 * 1) j)) hOeD (out j)
        (hy0 (finRotate (2 * 1) j)).1 (hy0 (finRotate (2 * 1) j)).2

/-- **R9 字段 `local_product` 的 flat witness**：`Nb = h(|A|) = W`，竖直投影 collapse + 两侧 + rotation。 -/
theorem flatDisk_localProduct_R10 :
    HasLocalProductCollapse_R10 (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX (bipyramidRealization_FIX '' bipyramid_FIX.space) := by
  rw [realization_image_FIX]
  refine ⟨lensProj_R10, lensHom_R10, continuous_lensProj_R10.continuousOn, ?_, ?_,
    continuous_lensHom_R10.continuousOn, ?_, ?_, ?_, ?_,
    fun s b => lensSide_R10 (flatFace_R10 s) b,
    fun s2 hs2 hc => lens_isTwoSided_R10 (flatFace_preconnected_R10 s2)
      (flatFace_two_subset_R10 hs2 hc),
    fun e he hc hball => flat_rotation_R10 he hc hball⟩
  · intro q hq
    have hq' : lensGauge_R10 q ≤ 1 := hq
    rw [range_flatDisk_R10]
    refine ⟨proj12_FIX q, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have := abs_nonneg (pzCLM_FIX q)
    rw [lensGauge_R10] at hq'
    linarith
  · rintro _ ⟨z, rfl⟩
    change flatCLM_FIX (proj12_FIX (flatCLM_FIX z)) = flatCLM_FIX z
    rw [proj12_flat_FIX]
  · intro x _
    simp [lensHom_R10]
  · intro x _
    have hx := decomp_R10 x
    change x + (-((1 : ℝ) * pzCLM_FIX x)) • e3_R10 = flatCLM_FIX (proj12_FIX x)
    rw [one_mul, neg_smul, ← sub_eq_add_neg, sub_eq_iff_eq_add]
    exact hx.symm
  · rintro t _ ⟨z, rfl⟩
    change flatCLM_FIX z + (-((t : ℝ) * pzCLM_FIX (flatCLM_FIX z))) • e3_R10 = flatCLM_FIX z
    rw [pz_flat_FIX, mul_zero, neg_zero, zero_smul, add_zero]
  · intro t q hq
    have hq' : lensGauge_R10 q ≤ 1 := hq
    change lensGauge_R10 (lensHom_R10 (t, q)) ≤ 1
    rw [lensGauge_R10, lensHom_proj12_R10, lensHom_pz_R10, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr t.2.2)]
    rw [lensGauge_R10] at hq'
    have h1 : (1 - (t : ℝ)) * |pzCLM_FIX q| ≤ |pzCLM_FIX q| := by
      have := abs_nonneg (pzCLM_FIX q)
      nlinarith [t.2.1]
    change ‖proj12_FIX q‖ + (1 - (t : ℝ)) * |pzCLM_FIX q| ≤ 1
    linarith

/-- **G2 consumer（非空）**：平坦标准盘的**同一 witness** `Nb = h(|A|)` 同时满足 R10.1、R10.2，并带 R11 的
ambient collar（经联合 producer `relative_regular_nbhd_sector_collar_R10`）。 -/
theorem flatDisk_sectorControlled_R10 :
    ∃ (Nb : Set E3_FIX) (R : E3_FIX → E3_FIX), IsRelRegularNbhd_R10 flatDisk_FIX Nb R ∧
      IsSectorControlledCollapse_R10 (E := E3_FIX) (⇑flatCLM_FIX) triComplex_FIX radialGrid_FIX
        Nb R ∧ HasAmbientCollar_R10 Nb ∧
      Nb = bipyramidRealization_FIX '' bipyramid_FIX.space :=
  relative_regular_nbhd_sector_collar_R10 flatDisk_prepared_FIX flatDisk_localProduct_R10
    flatDisk_ambientCollar_R10

end DifferentialGeometry.Geometry
