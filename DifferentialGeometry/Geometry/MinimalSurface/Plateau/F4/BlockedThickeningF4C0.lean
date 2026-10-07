import DifferentialGeometry.Geometry.MinimalSurface.Plateau.F4.OutputF4D

/-!
# O-MY-F4C0 G1：F4-c blocked thickening 骨架（`_F4C0`）

设计文档：`docs/geometrization/chapter8/design-F4c-thickening-20261006.md`。本文件只含 `def` / `structure`
与已证引理（无 sorry，无新 admission）：

* **两侧引擎**：`isTwoSidedFace_of_sections_F4C0`（preconnected 面 + 两个连续 section ⇒ `IsTwoSidedFace_R10`）、
  `isTwoSidedFace_congr_F4C0`（两侧性只依赖 `R` 在 `frontier Nb ∩ R⁻¹ O` 上的值）。
* **graph-slab 模型**（块图 `ℂ × ℝ` 里，sheet = 竖直图 `y = g u`）：`slab_F4C0`、厚度规则 `thicknessRule_F4C0`
  （design §2.1 (T1)：面区 `τ_j + τ_k < |g_j − g_k|`）、cross core 规则 `crossRule_F4C0`（(T2)：`2τ ≤ aκ`）、
  tangency 定量形 `thicknessRule_of_powerBound_F4C0`（§2.2：`2τ < c r^m ≤ |g_j − g_k|`）；
  局部模型 notion `IsSlabBlockModel_F4C0` + inhabitants：flat lens（单 sheet，`τ = 1 − ‖u‖`）与
  单条横截 double segment 的 cross block（两 sheet `y = 0`、`y = a · re u`）。
* **全局骨架** `IsBlockedThickening_F4C0`：细化 O-MY-F4D 的 `IsThickeningOutput_F4D`——显式 `(R, H, side)`
  witness、有限块族（类型 `BlockKind_F4C0`、块图 `SlabBlockData_F4C0`）、源厚度 `τ`、拼接相容条款
  （覆盖、块内部不交、`R`/`H` 保持每块、面区 slab 方程与规则、块厚度 = 源厚度）；flat inhabitant
  `flatDisk_blockedThickening_F4C0`；consumer `IsBlockedThickening_F4C0.localProduct_F4C0`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

/-! ## §1 两侧引擎 -/

section Engine

variable {M : Type u} [TopologicalSpace M]

/-- 两侧在 `frontier Nb ∩ R⁻¹ O` 里。 -/
theorem IsTwoSidedFace_R10.subset_frontier_F4C0 {Nb : Set M} {R : M → M} {O : Set M}
    {sd : Bool → Set M} (h : IsTwoSidedFace_R10 Nb R O sd) (b : Bool) :
    sd b ⊆ frontier Nb ∩ R ⁻¹' O := by
  obtain ⟨-, hunion, -⟩ := h
  rw [← hunion]
  cases b
  · exact subset_union_right
  · exact subset_union_left

/-- **两侧引擎**：`O` preconnected，两个连续 section `sec b` 落在 `frontier Nb` 上、`R ∘ sec b = id`、
两像不交且覆盖 `frontier Nb ∩ R⁻¹ O` ⇒ `O` 两侧，侧 = `sec b '' O`。 -/
theorem isTwoSidedFace_of_sections_F4C0 {Nb : Set M} {R : M → M} {O : Set M}
    (sec : Bool → M → M) (hO : IsPreconnected O) (hcont : ∀ b, ContinuousOn (sec b) O)
    (hfr : ∀ b, ∀ y ∈ O, sec b y ∈ frontier Nb) (hR : ∀ b, ∀ y ∈ O, R (sec b y) = y)
    (hdisj : ∀ y ∈ O, ∀ y' ∈ O, sec true y ≠ sec false y')
    (hcover : frontier Nb ∩ R ⁻¹' O ⊆ sec true '' O ∪ sec false '' O) :
    IsTwoSidedFace_R10 Nb R O (fun b => sec b '' O) := by
  refine ⟨?_, ?_, fun b => ⟨hO.image _ (hcont b), ?_, ?_, sec b, hcont b,
    fun y hy => ⟨⟨y, hy, rfl⟩, hR b y hy⟩⟩⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy⟩
    exact hdisj y hy y' hy' hyy.symm
  · refine Subset.antisymm ?_ hcover
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · refine ⟨hfr true y hy, ?_⟩
      change R (sec true y) ∈ O
      rw [hR true y hy]
      exact hy
    · refine ⟨hfr false y hy, ?_⟩
      change R (sec false y) ∈ O
      rw [hR false y hy]
      exact hy
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hyy
    rw [hR b y hy, hR b y' hy'] at hyy
    rw [hyy]
  · ext y
    constructor
    · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      rw [hR b y' hy']
      exact hy'
    · intro hy
      exact ⟨sec b y, ⟨y, hy, rfl⟩, hR b y hy⟩

/-- 两侧性只依赖 `R` 在 `frontier Nb ∩ R⁻¹ O` 上的值：若 `R`、`R'` 在 frontier 上拉回 `O` 的集合相同且
在其上一致，则两侧结构照搬（F4-L7：core 收缩与面区竖直投影只在面区 frontier 上一致）。 -/
theorem isTwoSidedFace_congr_F4C0 {Nb : Set M} {R R' : M → M} {O : Set M} {sd : Bool → Set M}
    (hpre : frontier Nb ∩ R ⁻¹' O = frontier Nb ∩ R' ⁻¹' O)
    (hRR : EqOn R R' (frontier Nb ∩ R ⁻¹' O)) (h : IsTwoSidedFace_R10 Nb R O sd) :
    IsTwoSidedFace_R10 Nb R' O sd := by
  have hsub : ∀ b, sd b ⊆ frontier Nb ∩ R ⁻¹' O := h.subset_frontier_F4C0
  obtain ⟨hdisj, hunion, hb⟩ := h
  refine ⟨hdisj, hunion.trans hpre, fun b => ?_⟩
  obtain ⟨hpc, hinj, himg, sec, hsc, hsec⟩ := hb b
  refine ⟨hpc, hinj.congr (hRR.mono (hsub b)), ?_, sec, hsc, fun y hy => ?_⟩
  · rw [← (hRR.mono (hsub b)).image_eq]
    exact himg
  · obtain ⟨h1, h2⟩ := hsec y hy
    refine ⟨h1, ?_⟩
    rw [← hRR (hsub b h1)]
    exact h2

/-- 特例：`R = R'` 在整个 `frontier Nb` 上。 -/
theorem isTwoSidedFace_congr_frontier_F4C0 {Nb : Set M} {R R' : M → M} {O : Set M}
    {sd : Bool → Set M} (hRR : EqOn R R' (frontier Nb)) (h : IsTwoSidedFace_R10 Nb R O sd) :
    IsTwoSidedFace_R10 Nb R' O sd := by
  refine isTwoSidedFace_congr_F4C0 ?_ (hRR.mono inter_subset_left) h
  ext x
  constructor
  · rintro ⟨hx, hxO⟩
    refine ⟨hx, ?_⟩
    rw [mem_preimage, ← hRR hx]
    exact hxO
  · rintro ⟨hx, hxO⟩
    refine ⟨hx, ?_⟩
    rw [mem_preimage, hRR hx]
    exact hxO

end Engine

/-! ## §2 graph-slab 模型与厚度规则 -/

section Slab

/-- 竖直 slab `{(u, y) : |y − g u| ≤ τ u}`：块图 `ℂ × ℝ` 里 sheet `y = g u` 的厚化（design §0）。 -/
def slab_F4C0 (g τ : ℂ → ℝ) : Set (ℂ × ℝ) := {q | |q.2 - g q.1| ≤ τ q.1}

/-- sheet `y = g u` 在底区 `V` 上的图（开像面在块图里的模型）。 -/
def sheetGraph_F4C0 (g : ℂ → ℝ) (V : Set ℂ) : Set (ℂ × ℝ) := (fun u => (u, g u)) '' V

theorem isClosed_slab_F4C0 {g τ : ℂ → ℝ} (hg : Continuous g) (hτ : Continuous τ) :
    IsClosed (slab_F4C0 g τ) :=
  isClosed_le (continuous_snd.sub (hg.comp continuous_fst)).abs (hτ.comp continuous_fst)

/-- **厚度规则**（design §2.1 (T1)，面区分离形）：底区 `W` 上每个厚度为正，且任两张 sheet 的
slab 厚度之和小于高度差。 -/
def thicknessRule_F4C0 {ι : Type*} (g τ : ι → ℂ → ℝ) (W : Set ℂ) : Prop :=
  ∀ u ∈ W, (∀ j, 0 < τ j u) ∧ ∀ j k, j ≠ k → τ j u + τ k u < |g j u - g k u|

/-- **tangency 定量形**（design §2.2）：底区 `W` 上 sheet 高度差 `≥ c r^m`（nodal 阶 m 的分离下界），
每个厚度 `0 < τ_j` 且 `2 τ_j < c r^m`（即 `τ ≲ r^m`）⇒ 面区厚度规则。 -/
theorem thicknessRule_of_powerBound_F4C0 {ι : Type*} {g τ : ι → ℂ → ℝ} {W : Set ℂ}
    {r : ℂ → ℝ} {m : ℕ} {c : ℝ}
    (hsep : ∀ u ∈ W, ∀ j k, j ≠ k → c * r u ^ m ≤ |g j u - g k u|)
    (hτ : ∀ u ∈ W, ∀ j, 0 < τ j u ∧ 2 * τ j u < c * r u ^ m) :
    thicknessRule_F4C0 g τ W := by
  intro u hu
  refine ⟨fun j => (hτ u hu j).1, fun j k hjk => ?_⟩
  have h1 := (hτ u hu j).2
  have h2 := (hτ u hu k).2
  have h3 := hsep u hu j k hjk
  linarith

/-- **cross core 规则**（design §2.1 (T2)，两 sheet 常参数版）：横截斜率 `a > 0`、厚度 `τ₀ > 0`、
core 半宽 `κ` 满足 `2 τ₀ ≤ a κ`（两 slab 的重叠 `|re u| ≤ 2τ₀/a` 落在 core 内）。 -/
def crossRule_F4C0 (a κ τ₀ : ℝ) : Prop := 0 < a ∧ 0 < τ₀ ∧ 2 * τ₀ ≤ a * κ

/-- double segment / regular-edge cross block 的两张 sheet（块图里）：`false ↦ y = 0`、
`true ↦ y = a · re u`；碰撞边 = `{re u = 0, y = 0}`，`im u` 沿边。 -/
def crossSheet_F4C0 (a : ℝ) (b : Bool) (u : ℂ) : ℝ := if b then a * u.re else 0

theorem crossSheet_false_F4C0 (a : ℝ) (u : ℂ) : crossSheet_F4C0 a false u = 0 := rfl

theorem crossSheet_true_F4C0 (a : ℝ) (u : ℂ) : crossSheet_F4C0 a true u = a * u.re := rfl

theorem continuous_crossSheet_F4C0 (a : ℝ) (b : Bool) : Continuous (crossSheet_F4C0 a b) := by
  cases b
  · rw [show crossSheet_F4C0 a false = fun _ => 0 from funext (crossSheet_false_F4C0 a)]
    exact continuous_const
  · rw [show crossSheet_F4C0 a true = fun u => a * u.re from funext (crossSheet_true_F4C0 a)]
    exact continuous_const.mul Complex.continuous_re

/-- cross block 的面区：core `|re u| ≤ κ` 之外。 -/
def crossFace_F4C0 (κ : ℝ) : Set ℂ := {u | κ < |u.re|}

theorem isOpen_crossFace_F4C0 (κ : ℝ) : IsOpen (crossFace_F4C0 κ) :=
  isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re)

/-- cross core 规则 ⇒ 面区厚度规则（常数厚度 `τ₀`）。 -/
theorem thicknessRule_of_crossRule_F4C0 {a κ τ₀ : ℝ} (h : crossRule_F4C0 a κ τ₀) :
    thicknessRule_F4C0 (crossSheet_F4C0 a) (fun _ _ => τ₀) (crossFace_F4C0 κ) := by
  obtain ⟨ha, hτ, hrule⟩ := h
  intro u hu
  refine ⟨fun _ => hτ, fun j k hjk => ?_⟩
  have hu' : κ < |u.re| := hu
  have hlt : 2 * τ₀ < a * |u.re| := lt_of_le_of_lt hrule (mul_lt_mul_of_pos_left hu' ha)
  have habs : |a * u.re| = a * |u.re| := by rw [abs_mul, abs_of_pos ha]
  cases j <;> cases k
  · exact absurd rfl hjk
  · rw [crossSheet_false_F4C0, crossSheet_true_F4C0, zero_sub, abs_neg, habs]
    linarith
  · rw [crossSheet_false_F4C0, crossSheet_true_F4C0, sub_zero, habs]
    linarith
  · exact absurd rfl hjk

/-- **块图里的 graph-slab 局部模型**（design §0/§1）：有限 sheet 族 `g`、连续厚度 `τ`、开面区 `W`
（厚度规则成立）；`Nb` 闭且在 `W × ℝ` 上恰为 slab 之并；`R` 在面区 slab 上是竖直投影；
`R` 不把面区外的 frontier 点送进面区（core / 顶点球的收缩保持其区域）。 -/
structure IsSlabBlockModel_F4C0 {ι : Type*} (g τ : ι → ℂ → ℝ) (W : Set ℂ)
    (Nb : Set (ℂ × ℝ)) (R : ℂ × ℝ → ℂ × ℝ) : Prop where
  finite : Finite ι
  W_open : IsOpen W
  g_cont : ∀ j, Continuous (g j)
  tau_cont : ∀ j, Continuous (τ j)
  rule : thicknessRule_F4C0 g τ W
  Nb_closed : IsClosed Nb
  Nb_face : Nb ∩ (W ×ˢ univ) = (⋃ j, slab_F4C0 (g j) (τ j)) ∩ (W ×ˢ univ)
  R_face : ∀ j, ∀ q ∈ slab_F4C0 (g j) (τ j), q.1 ∈ W → R q = (q.1, g j q.1)
  R_base : ∀ q ∈ frontier Nb, (R q).1 ∈ W → q.1 ∈ W

/-! ### inhabitant 1：单条横截 double segment 的 cross block -/

/-- cross block 的 thickening（块图里）：两张 sheet 的常厚度 slab 之并（core 里是 X 形）。 -/
def crossNb_F4C0 (a τ₀ : ℝ) : Set (ℂ × ℝ) :=
  ⋃ b, slab_F4C0 (crossSheet_F4C0 a b) (fun _ => τ₀)

/-- 面区用的竖直投影：投到较近的 sheet（保持底坐标；core 里的真正收缩由 F4-L7 给出，
在面区 frontier 上与此一致即可经 `isTwoSidedFace_congr_F4C0` 复用 G2）。 -/
def crossProj_F4C0 (a : ℝ) (q : ℂ × ℝ) : ℂ × ℝ :=
  (q.1, if |q.2| ≤ |q.2 - a * q.1.re| then 0 else a * q.1.re)

/-- **inhabitant（单条横截 double segment）**：cross core 规则 ⇒ cross block 是 graph-slab 局部模型。 -/
theorem crossBlock_slabModel_F4C0 {a κ τ₀ : ℝ} (h : crossRule_F4C0 a κ τ₀) :
    IsSlabBlockModel_F4C0 (crossSheet_F4C0 a) (fun _ _ => τ₀) (crossFace_F4C0 κ)
      (crossNb_F4C0 a τ₀) (crossProj_F4C0 a) where
  finite := inferInstance
  W_open := isOpen_crossFace_F4C0 κ
  g_cont := continuous_crossSheet_F4C0 a
  tau_cont := fun _ => continuous_const
  rule := thicknessRule_of_crossRule_F4C0 h
  Nb_closed := isClosed_iUnion_of_finite fun b =>
    isClosed_slab_F4C0 (continuous_crossSheet_F4C0 a b) continuous_const
  Nb_face := rfl
  R_face := by
    obtain ⟨ha, -, hrule⟩ := h
    intro b q hq hW
    have hW' : κ < |q.1.re| := hW
    have hlt : 2 * τ₀ < a * |q.1.re| := lt_of_le_of_lt hrule (mul_lt_mul_of_pos_left hW' ha)
    have habs : |a * q.1.re| = a * |q.1.re| := by rw [abs_mul, abs_of_pos ha]
    have htri := abs_sub_abs_le_abs_sub (a * q.1.re) q.2
    rw [abs_sub_comm (a * q.1.re) q.2, habs] at htri
    have hq' : |q.2 - crossSheet_F4C0 a b q.1| ≤ τ₀ := hq
    cases b
    · rw [crossSheet_false_F4C0, sub_zero] at hq'
      have hle : |q.2| ≤ |q.2 - a * q.1.re| := by linarith
      change (q.1, if |q.2| ≤ |q.2 - a * q.1.re| then 0 else a * q.1.re) = (q.1, 0)
      simp [hle]
    · rw [crossSheet_true_F4C0] at hq'
      have hnle : ¬ |q.2| ≤ |q.2 - a * q.1.re| := by
        intro hle
        linarith
      change (q.1, if |q.2| ≤ |q.2 - a * q.1.re| then 0 else a * q.1.re) = (q.1, a * q.1.re)
      simp [hnle]
  R_base := fun _ _ hq => hq

/-! ### inhabitant 2：flat lens（单 sheet，`τ = 1 − ‖u‖`） -/

/-- flat lens 的块图模型：`{(w, s) : ‖w‖ + |s| ≤ 1}`。 -/
def lensModel_F4C0 : Set (ℂ × ℝ) := {p | ‖p.1‖ + |p.2| ≤ 1}

theorem slab_flat_F4C0 :
    (⋃ _ : Fin 1, slab_F4C0 (fun _ => 0) (fun u => 1 - ‖u‖)) = lensModel_F4C0 := by
  rw [iUnion_const]
  ext p
  change |p.2 - 0| ≤ 1 - ‖p.1‖ ↔ ‖p.1‖ + |p.2| ≤ 1
  rw [sub_zero]
  constructor <;> intro hp <;> linarith

/-- **inhabitant（flat lens）**：单 sheet `y = 0`、厚度 `1 − ‖u‖`、面区 = 开单位盘。 -/
theorem flatLens_slabModel_F4C0 :
    IsSlabBlockModel_F4C0 (fun (_ : Fin 1) (_ : ℂ) => (0 : ℝ)) (fun _ u => 1 - ‖u‖)
      (Metric.ball (0 : ℂ) 1) lensModel_F4C0 (fun q => (q.1, 0)) where
  finite := inferInstance
  W_open := Metric.isOpen_ball
  g_cont := fun _ => continuous_const
  tau_cont := fun _ => continuous_const.sub continuous_norm
  rule := fun u hu => ⟨fun _ => by
      change 0 < 1 - ‖u‖
      rw [Metric.mem_ball, dist_zero_right] at hu
      linarith,
    fun j k hjk => absurd (Subsingleton.elim j k) hjk⟩
  Nb_closed := isClosed_le ((continuous_norm.comp continuous_fst).add
    (continuous_abs.comp continuous_snd)) continuous_const
  Nb_face := by rw [slab_flat_F4C0]
  R_face := fun _ _ _ _ => rfl
  R_base := fun _ _ hq => hq

end Slab

/-! ## §3 全局骨架：块族、块图、显式 witness -/

/-- F4-c 块类型（design §1）。 -/
inductive BlockKind_F4C0 where
  /-- c3a：2-面的 slab 棱柱。 -/
  | facePrism
  /-- c3b：横截碰撞边的 2m 臂 cross 块。 -/
  | cross
  /-- c3c：顶点锥块（crossing / tangency / cusp）。 -/
  | vertex
  /-- c3d：trace collar（lens 棱）。 -/
  | traceCollar

/-- 一个块的数据（design §0）：类型、目标块 `carrier ⊆ M`、块图 `chart : M ⇀ ℂ × ℝ`、块内 sheet 数、
sheet 高度 `g j`、块厚度 `τ j`（块图坐标）、面区 `face ⊆ ℂ`（slab 两两不交处；vertex 块取 `∅`）。 -/
structure SlabBlockData_F4C0 (M : Type u) [TopologicalSpace M] where
  kind : BlockKind_F4C0
  carrier : Set M
  chart : OpenPartialHomeomorph M (ℂ × ℝ)
  nsh : ℕ
  g : Fin nsh → ℂ → ℝ
  τ : Fin nsh → ℂ → ℝ
  face : Set ℂ

section Blocked

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **F4-c blocked thickening**（细化 `IsThickeningOutput_F4D`，design §1.4 / §3）：
S5 + S9 + S10（`thick`）之外，固定 S9 的显式 witness `(R, H, side)`，给出有限块族 `B`（块图 + 面区
slab 模型）、源厚度 `τ`（`D°` 上正、trace 处为 0）与拼接相容条款（覆盖、块内部不交、`R`/`H`
保持每块、面区厚度规则、块厚度 = 源厚度）。R10 三层 adapter（D-11）从这些显式数据读出。 -/
structure IsBlockedThickening_F4C0 (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) (N : ℕ)
    (A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (φ : ℂ → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N) → M)
    {ι : Type*} (B : ι → SlabBlockData_F4C0 M) (τ : ℂ → ℝ) (R : M → M)
    (H : unitInterval × M → M) (side : Finset ℂ → Bool → Set M) : Prop where
  /-- S5 + S9 + S10（O-MY-F4D 分组）。 -/
  thick : IsThickeningOutput_F4D (E := E) f F T α N A φ h
  /-- 有限块族覆盖 `Nb = h(|A|)`，块紧、块内部两两不交、块在其块图定义域内。 -/
  blocks_finite : Finite ι
  cover : h '' A.space = ⋃ i, (B i).carrier
  carrier_compact : ∀ i, IsCompact (B i).carrier
  interior_disjoint : Pairwise fun i j => Disjoint (interior (B i).carrier) (interior (B j).carrier)
  carrier_source : ∀ i, (B i).carrier ⊆ (B i).chart.source
  /-- 面区 slab 模型：面区开、厚度规则、块像在面区上恰为 slab 之并、`R` 在面区 slab 上是竖直投影。 -/
  face_open : ∀ i, IsOpen (B i).face
  rule : ∀ i, thicknessRule_F4C0 (B i).g (B i).τ (B i).face
  face_slab : ∀ i, (B i).chart '' (B i).carrier ∩ ((B i).face ×ˢ univ) =
    (⋃ j, slab_F4C0 ((B i).g j) ((B i).τ j)) ∩ ((B i).face ×ˢ univ)
  face_R : ∀ i j, ∀ x ∈ (B i).carrier, (B i).chart x ∈ slab_F4C0 ((B i).g j) ((B i).τ j) →
    ((B i).chart x).1 ∈ (B i).face →
      (B i).chart (R x) = (((B i).chart x).1, (B i).g j ((B i).chart x).1)
  /-- 源厚度：`D̄` 上连续、`D°` 上正、trace 处为 0（trace collar = lens 棱）；面区里块厚度 = 源厚度。 -/
  tau_cont : ContinuousOn τ (Metric.closedBall 0 1)
  tau_pos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < τ z
  tau_bdry : ∀ z : ℂ, ‖z‖ = 1 → τ z = 0
  tau_compat : ∀ i j, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, F z ∈ (B i).carrier →
    ((B i).chart (F z)).1 ∈ (B i).face → ((B i).chart (F z)).2 = (B i).g j ((B i).chart (F z)).1 →
      (B i).τ j ((B i).chart (F z)).1 = τ z
  /-- S9 的显式 collapse witness `(R, H)`（与 `HasLocalProductCollapse_R10` 同形）。 -/
  R_cont : ContinuousOn R (h '' A.space)
  R_maps : MapsTo R (h '' A.space) (Set.range f)
  R_fix : ∀ x ∈ Set.range f, R x = x
  H_cont : ContinuousOn H (univ ×ˢ (h '' A.space))
  H_zero : ∀ x ∈ h '' A.space, H (0, x) = x
  H_one : ∀ x ∈ h '' A.space, H (1, x) = R x
  H_fix : ∀ t, ∀ x ∈ Set.range f, H (t, x) = x
  H_maps : ∀ t, MapsTo (fun x => H (t, x)) (h '' A.space) (h '' A.space)
  /-- 块局部性（拼接相容）：`R`、`H` 保持每个块，sides / sectors 可逐块计算。 -/
  R_block : ∀ i, MapsTo R (B i).carrier (B i).carrier
  H_block : ∀ i t, MapsTo (fun x => H (t, x)) (B i).carrier (B i).carrier
  /-- 2-strata 与 1-strata 用**同一个** `side`。 -/
  twoSided : ∀ σ ∈ T.faces, σ.card = 3 →
    IsTwoSidedFace_R10 (h '' A.space) R (openImageFace_R10 F α σ) (side σ)
  rotation : ∀ e ∈ T.faces, e.card = 2 → α '' openSimplex e ⊆ Metric.ball (0 : ℂ) 1 →
    HasRealizedRotationSystem_R10 (E := E) F T α (h '' A.space) R side e

variable {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
  {α : ℂ → ℂ} {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
  {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M} {ι : Type*}
  {B : ι → SlabBlockData_F4C0 M} {τ : ℂ → ℝ} {R : M → M} {H : unitInterval × M → M}
  {side : Finset ℂ → Bool → Set M}

/-- **consumer（S9 用显式 witness 实现）**：blocked thickening 的 `(R, H, side)` 直接给出
`HasLocalProductCollapse_R10`（R10.1 / R10.2 联合 producer 的输入），不经 `thick.local_product` 的 `∃`。 -/
theorem IsBlockedThickening_F4C0.localProduct_F4C0
    (hB : IsBlockedThickening_F4C0 (E := E) f F T α N A φ h B τ R H side) :
    HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space) :=
  ⟨R, H, hB.R_cont, hB.R_maps, hB.R_fix, hB.H_cont, hB.H_zero, hB.H_one, hB.H_fix, hB.H_maps,
    side, hB.twoSided, hB.rotation⟩

/-- **consumer（车道装配）**：S4 输入 + F4-a（S8）+ F4-b + F4-c blocked thickening ⇒ 24 字段 prepared。 -/
theorem IsBlockedThickening_F4C0.prepared_F4C0
    (hB : IsBlockedThickening_F4C0 (E := E) f F T α N A φ h B τ R H side)
    (hext : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w)
    (hnodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
      IsCollisionNodal_FIX2 (E := E) F z w)
    (htri : IsAdaptedTriangulation_F4D T α (collisionSet_F4D F) (tangencySet_F4D (E := E) F)) :
    IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h :=
  prepared_of_lane_outputs_F4D hext hrank hcollar hnodal htri hB.thick

end Blocked

/-! ## §4 flat inhabitant -/

/-- flat 块图 `q ↦ (π q, q₂)`（逆 `(w, s) ↦ flat w + s e₃`）。 -/
def flatChartHomeo_F4C0 : E3_FIX ≃ₜ ℂ × ℝ where
  toFun q := (proj12_FIX q, pzCLM_FIX q)
  invFun p := flatCLM_FIX p.1 + p.2 • e3_R10
  left_inv q := decomp_R10 q
  right_inv p := by
    refine Prod.ext ?_ ?_
    · change proj12_FIX (flatCLM_FIX p.1 + p.2 • e3_R10) = p.1
      rw [proj12_add_e3_R10, proj12_flat_FIX]
    · change pzCLM_FIX (flatCLM_FIX p.1 + p.2 • e3_R10) = p.2
      rw [pz_add_e3_R10, pz_flat_FIX, zero_add]
  continuous_toFun := continuous_proj12_FIX.prodMk pzCLM_FIX.continuous
  continuous_invFun :=
    (flatCLM_FIX.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)

/-- flat 的唯一块：lens `W`，块图 = `flatChartHomeo_F4C0`，单 sheet `y = 0`，厚度 `1 − ‖u‖`。 -/
def flatBlock_F4C0 : SlabBlockData_F4C0 E3_FIX where
  kind := .facePrism
  carrier := realizationImage_FIX
  chart := flatChartHomeo_F4C0.toOpenPartialHomeomorph
  nsh := 1
  g := fun _ _ => 0
  τ := fun _ u => 1 - ‖u‖
  face := Metric.ball 0 1

theorem flatBlock_chart_F4C0 (q : E3_FIX) :
    flatBlock_F4C0.chart q = (proj12_FIX q, pzCLM_FIX q) := rfl

theorem flatBlock_image_F4C0 :
    flatBlock_F4C0.chart '' flatBlock_F4C0.carrier = lensModel_F4C0 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    refine ⟨flatCLM_FIX p.1 + p.2 • e3_R10, ?_, ?_⟩
    · change ‖proj12_FIX (flatCLM_FIX p.1 + p.2 • e3_R10)‖ +
        |pzCLM_FIX (flatCLM_FIX p.1 + p.2 • e3_R10)| ≤ 1
      rw [proj12_add_e3_R10, proj12_flat_FIX, pz_add_e3_R10, pz_flat_FIX, zero_add]
      exact hp
    · exact flatChartHomeo_F4C0.right_inv p

theorem lensProj_mapsTo_F4C0 :
    MapsTo lensProj_R10 realizationImage_FIX realizationImage_FIX := by
  intro q hq
  have hq' : ‖proj12_FIX q‖ + |pzCLM_FIX q| ≤ 1 := hq
  change ‖proj12_FIX (flatCLM_FIX (proj12_FIX q))‖ + |pzCLM_FIX (flatCLM_FIX (proj12_FIX q))| ≤ 1
  rw [proj12_flat_FIX, pz_flat_FIX, abs_zero, add_zero]
  linarith [abs_nonneg (pzCLM_FIX q)]

theorem lensHom_mapsTo_F4C0 (t : unitInterval) :
    MapsTo (fun x => lensHom_R10 (t, x)) realizationImage_FIX realizationImage_FIX := by
  intro q hq
  have hq' : ‖proj12_FIX q‖ + |pzCLM_FIX q| ≤ 1 := hq
  change ‖proj12_FIX (lensHom_R10 (t, q))‖ + |pzCLM_FIX (lensHom_R10 (t, q))| ≤ 1
  rw [lensHom_proj12_R10, lensHom_pz_R10, abs_mul, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
  have h1 : (1 - (t : ℝ)) * |pzCLM_FIX q| ≤ |pzCLM_FIX q| := by
    have := abs_nonneg (pzCLM_FIX q)
    nlinarith [t.2.1]
  change ‖proj12_FIX q‖ + (1 - (t : ℝ)) * |pzCLM_FIX q| ≤ 1
  linarith

/-- **flat inhabitant**：平坦标准盘的 blocked thickening——单块 lens、块图 `(π, q₂)`、
源厚度 `τ z = 1 − ‖z‖`、显式 witness = flat lens 的 `(lensProj, lensHom, lensSide)`。 -/
theorem flatDisk_blockedThickening_F4C0 :
    IsBlockedThickening_F4C0 (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX 3 bipyramid_FIX (⇑flatAffine_FIX) bipyramidRealization_FIX
      (fun _ : Unit => flatBlock_F4C0) (fun z => 1 - ‖z‖) lensProj_R10 lensHom_R10
      (fun s b => lensSide_R10 (flatFace_R10 s) b) where
  thick := flatDisk_thickeningOutput_F4D
  blocks_finite := inferInstance
  cover := by
    rw [realization_image_FIX]
    exact (iUnion_const realizationImage_FIX).symm
  carrier_compact := fun _ => by
    change IsCompact realizationImage_FIX
    rw [← realization_image_FIX]
    exact (isCompact_space_of_finite_R10 bipyramid_FIX
      flatDisk_thickeningOutput_F4D.A_finite).image_of_continuousOn
      flatDisk_thickeningOutput_F4D.h_cont
  interior_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
  carrier_source := fun _ => by
    change realizationImage_FIX ⊆ flatChartHomeo_F4C0.toOpenPartialHomeomorph.source
    rw [Homeomorph.toOpenPartialHomeomorph_source]
    exact subset_univ _
  face_open := fun _ => Metric.isOpen_ball
  rule := fun _ => flatLens_slabModel_F4C0.rule
  face_slab := fun _ => by
    rw [flatBlock_image_F4C0, ← slab_flat_F4C0]
    rfl
  face_R := by
    intro _ _ x _ _ _
    change (proj12_FIX (flatCLM_FIX (proj12_FIX x)), pzCLM_FIX (flatCLM_FIX (proj12_FIX x))) =
      (proj12_FIX x, 0)
    rw [proj12_flat_FIX, pz_flat_FIX]
  tau_cont := (continuous_const.sub continuous_norm).continuousOn
  tau_pos := fun z hz => by
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith
  tau_bdry := fun z hz => by rw [hz, sub_self]
  tau_compat := by
    intro _ _ z _ _ _ _
    change 1 - ‖proj12_FIX (flatCLM_FIX z)‖ = 1 - ‖z‖
    rw [proj12_flat_FIX]
  R_cont := continuous_lensProj_R10.continuousOn
  R_maps := by
    rw [realization_image_FIX, range_flatDisk_R10]
    intro q hq
    have hq' : ‖proj12_FIX q‖ + |pzCLM_FIX q| ≤ 1 := hq
    refine ⟨proj12_FIX q, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [abs_nonneg (pzCLM_FIX q)]
  R_fix := by
    rintro _ ⟨z, rfl⟩
    change flatCLM_FIX (proj12_FIX (flatCLM_FIX z)) = flatCLM_FIX z
    rw [proj12_flat_FIX]
  H_cont := continuous_lensHom_R10.continuousOn
  H_zero := fun x _ => by simp [lensHom_R10]
  H_one := fun x _ => by
    have hx := decomp_R10 x
    change x + (-((1 : ℝ) * pzCLM_FIX x)) • e3_R10 = flatCLM_FIX (proj12_FIX x)
    rw [one_mul, neg_smul, ← sub_eq_add_neg, sub_eq_iff_eq_add]
    exact hx.symm
  H_fix := by
    rintro t _ ⟨z, rfl⟩
    change flatCLM_FIX z + (-((t : ℝ) * pzCLM_FIX (flatCLM_FIX z))) • e3_R10 = flatCLM_FIX z
    rw [pz_flat_FIX, mul_zero, neg_zero, zero_smul, add_zero]
  H_maps := fun t => by
    rw [realization_image_FIX]
    exact lensHom_mapsTo_F4C0 t
  R_block := fun _ => lensProj_mapsTo_F4C0
  H_block := fun _ t => lensHom_mapsTo_F4C0 t
  twoSided := fun σ hσ hc => by
    rw [realization_image_FIX]
    exact lens_isTwoSided_R10 (flatFace_preconnected_R10 σ) (flatFace_two_subset_R10 hσ hc)
  rotation := fun e he hc hball => by
    rw [realization_image_FIX]
    exact flat_rotation_R10 he hc hball

/-- consumer（flat）：显式 witness 给出 flat 盘的 S9。 -/
example :
    HasLocalProductCollapse_R10 (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX (bipyramidRealization_FIX '' bipyramid_FIX.space) :=
  flatDisk_blockedThickening_F4C0.localProduct_F4C0

end DifferentialGeometry.Geometry
