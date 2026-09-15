# H 车道交接：同调与曲面（§21–§22、23.14–23.19、28.11），R3 已定为本库奇异同调

交接日期 2026-09-15。本文件是接手者的唯一入口。用户已决定计划 §8 R3：**同调层用本库奇异同调**
（`DifferentialGeometry/Topology/Homology/*`，Mathlib `SingularHomology`），不引入单纯链复形；Euler 数走
`faceEulerChar`（组合）与奇异 `eulerChar` 的既有桥；可定向性用 Moise 23.14 的**顶维组合定向**（不需要链复形）。
本文件把计划行 H.1–H.6 按这个决定改写成可执行的砖块。

## 0. 决定 D3′（写入计划 §1 D3 的修订）

- χ：多面体 `|K|` 的 Euler 数 = `faceEulerChar K.toPreAbstractSimplicialComplex`（顶点 − 边 + 面 …），
  与奇异 `eulerChar k (TopCat.of K.space)`（`k` 任意域）相等（本库 `eulerChar_geometricSpace_eq_faceEulerChar`），
  因而是同伦不变量（`eulerChar_eq_of_homotopyEquiv`）；§21 的"开胞腔复形"与运算 α–δ **不需要**。
- `p¹`：一维 Betti 数取 ℚ 系数：`bettiOne X := Module.finrank ℚ (H₁(X; ℚ))`（`singularHomologyFunctor (ModuleCat ℚ) 1`）。
  Moise 用 ℤ 系数的自由秩，二者相等（泛系数），但本车道只用 ℚ 版本；需要 ℤ 或 ℤ₂ 信息的地方（C.5 的
  `H₁ → ℤ₂` 满射）在砖 H.5 里用 ℤ₂ 系数的 Betti 数 `bettiOneTwo` 直接陈述，避免泛系数定理。
- 可定向性：组合定义（23.14）：`n` 维带边组合流形 `K` 的**相干定向** = 每个 `n`-面一个顶点顺序的奇偶类，使得
  相邻 `n`-面在公共 `(n−1)`-面上诱导相反定向；`IsOrientable K := ∃ 相干定向`。不经同调；与 `H_n` 的关系（砖 H.4a）
  只在需要的方向证明。
- 柄数：可定向闭连通曲面 `B` 的 `h B := bettiOne B / 2`（22.6/22.7 之后这是定义与定理的合一，砖 H.4a 证明
  `bettiOne B` 为偶数且 `χ B = 2 − bettiOne B`）；23.18/23.19 用 `bettiOne` 陈述，`h` 只作缩写。
- 分类（22.8–22.10）与识别（22.11 "单连通 ⟹ 2-球面"、"χ = 2 ⟹ 2-球面"）：**不在本车道前半**；见砖 H.4b 的决定项。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-h`，分支 `codex/moise-h`（从 F 车道 HEAD c5e5d4450 分出）。只在此工作树工作、
  只提交到此分支并推送同名远程分支；不合并进其它分支；绝不碰 main；不 force-push。
- 另外三个 Codex 分别在 `D:\differential-geometry-moise-plan`（F）、`D:\differential-geometry-moise-s`（S）、
  `D:\differential-geometry-moise-e3`（C）工作：不要进入它们的目录；不改共享检出 `E:\differential-geometry-dev` 的源码或分支；
  不运行 `lake build`；不登记根聚合 `DifferentialGeometry.lean`。
- 主机 Lean 进程配额 4 个，四条车道各 1 个：你**同时只跑 1 个**，并且检查前用 `tasklist` 看一眼 `lean.exe` 数量，
  ≥ 4 时等待。
- 验证只用 `D:\differential-geometry-moise-h\.lake\scratch\tools\` 的 `check-f.ps1`/`audit-f.ps1`（`$root` 指向本工作树，
  olean 写进共享库 `E:\differential-geometry-dev\.lake\build\lib\lean`）。**注意**：F 车道最近把它自己的脚本改成写入
  私有目录 `D:\differential-geometry-moise-plan\.lake\scratch\f-lib`，所以 F 车道最新的模块在共享库里可能没有 olean；
  本车道只依赖 F4.1/F4.2/Join*/BoundaryOfBall/ManifoldSubdivision 等较早的模块（共享库都有）。若 import 报"unknown module"，
  报告，不要把 `f-lib` 加进搜索路径（两个库混用会导致 olean 哈希不一致）。
- `AGENTS.md`（= `CLAUDE.md`）：零注释零 docstring；无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`；Mathlib 标准
  linter 集零警告；提交信息用英文描述数学结果。含 `IsCombinatorialManifold*`/`geometricLink` 的定理写成
  `open Classical in theorem …`，不带 `[DecidableEq E]`，证明里 `classical`。
- 计划 D4/R7：复用本库 `Topology/Homology/*`、`Topology/SimplicialComplex/*` 的每条声明，首次使用时单独 `#print axioms`
  并记入 `MOISE_PLAN.md` §6；`Homology/HurewiczLowDegrees.lean` 含 `sorry`，经它的链不能用。我已审计并确认只含标准
  三公理的：`integralSphereTopHomologyEquiv`、`integralLiftedSphereGenerator_isGenerator`、`integralSphereHomology_subsingleton`、
  `euclideanClosedBallFundamentalClass_ne_zero`、`puncturedNeighborhoodHomologyIso`、`integralSingularHomologyMap_homotopic`。
- 不弱化目标：陈述按 §4；证不出就报告确切缺口（目标/错误）。
- 状态登记：`E:\differential-geometry-dev\WORKING_STATUS.md` 末尾加 "Moise smoothing H(Codex) 2026-09-15"（只编辑不提交）。

## 2. 验证配方

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-h\.lake\scratch\tools\check-f.ps1 `
  -Module DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra *> D:\differential-geometry-moise-h\.lake\scratch\ep.log
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-h\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-h\.lake\scratch\ep.log
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-h\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditH1.lean'
```
exit=0、零错误零警告；审计每条 `depends on axioms: [propext, Classical.choice, Quot.sound]`；模板 `.lake/scratch/AuditTemplate.lean`。
Moise 原书 `.lake/scratch/moise_gtm47.pdf`（书页 p = PDF 页 p+10）：§21 在书页 147–154，§22 在 155–164，23.13–23.19 在 170–173，
28.11 在 205。

## 3. 可用材料（名字已核对）

本库奇异同调（`Topology/Homology/`，命名空间多为 `DifferentialGeometry.Topology` 或 `DifferentialGeometry.Homology`，
以文件首行 `namespace` 为准）：
- `Integral.lean`：`integralSingularHomology n X`、`integralSingularHomologyMap n (f : C(X, Y))`、`_id`、`_comp`、`_homotopic`。
- `EulerCharacteristic.lean`：`finiteHomologyType (X : TopCat)`、`eulerChar (k) (X : TopCat) : ℤ`（`GradedObject.eulerChar` 于
  `singularHomologyFunctor (ModuleCat k) n`）、`singularHomologyIso (e : X ≃ₕ Y)`、`eulerChar_eq_of_homotopyEquiv`、`eulerChar_eq_of_homeomorph`。
- `Homotopy.lean`：`integralSingularHomologyHomotopyEquiv`、`integralSingularHomology_subsingleton_of_contractible (n) (hn : n ≠ 0)`。
- `Reduced.lean`（`DifferentialGeometry.Homology`）：`isZero_reducedSingularHomology_of_contractible`、`reducedSingularHomologySuccIso`。
- `Relative.lean`、`Relative/Excision.lean`（`relativeExcisionIso (hs : IsOpen s) (ht : IsOpen t)`）、`Relative/DisjointExcision.lean`、
  `Reduced/MayerVietoris.lean`（开覆盖的小链 MV）、`SmallHomology.lean`（`integralSingularSmallInclusion_quasiIso`）。
- `Algebra/ExactSequenceEuler.lean`：`homologyEulerChar_additive`（短正合列的 Euler 数可加）、`sum_homology_finrank_exactSequence`；
  `Algebra/FiniteType.lean`。
- 球面与局部同调：`SphereTopHomology.lean`（`integralSphereTopHomologyEquiv (n) (E) (hd : finrank ℝ E = n + 2) : H_{n+1}(S^{n+1}) ≃ₗ[ℤ] ℤ`）、
  `SphereHomologyVanishing.lean`、`SphereEuler.lean`（`eulerChar_euclideanSphere`、`finiteHomologyType_euclideanSphere`）、
  `Local/Neighborhood.lean`（`puncturedNeighborhoodHomologyIso [T1Space X] (hU : IsOpen U) (n)`）、`Local/ClosedBall.lean`
  （`euclideanClosedBallFundamentalClass`、`_ne_zero`、`closedBallLocalHomologyMap`）、`Local/Generator.lean`、`Local/Graded.lean`
  （`localEuclideanSphereHomologyIso`、`not_isZero_localEuclidean_top`、`isZero_localEuclidean_of_gt`）、`LocalDegree/*`（球面映射的度）。
- 几何复形桥（`Topology/SimplicialComplex/`，命名空间 `DifferentialGeometry.Topology.SimplicialComplex`）：
  `EulerCharacteristic.lean`（`faceEulerChar`、`faceEulerChar_eq_of_card_le_three/four`、`faceEulerChar_sup_add_faceEulerChar_inf`、
  `faceEulerChar_map_of_injective`）、`GeometricEulerCharacteristic.lean`（`eulerChar_geometricSpace_eq_faceEulerChar`、
  `eulerChar_geometricSpace_eq_of_coefficients`、`finiteHomologyType_geometricSpace`）、`GeometricLink.lean`
  （`geometricLink_toPreAbstractSimplicialComplex`：几何 link 的抽象复形 = 抽象 `link`）、`LinkEulerSum.lean`
  （`sum_one_sub_faceEulerChar_link : ∑ s, (1 − χ(link K s)) = χ K`）、`BoundaryCounting.lean`
  （`faceEulerChar_eq_two_mul_of_link_counts (hLK : L ≤ K) (hK : 面 ≤ 4 顶点) (hL : 面 ≤ 3) (htri : 每个三角形的四面体余面数 = if s ∈ L then 1 else 2)
  (hedge : χ(link K s) = if s ∈ L then 1 else 0) (hvertex : χ(link K s) = if s ∈ L then 1 else 2) : faceEulerChar L = 2 * faceEulerChar K`
  ——23.18 的引擎，假设全是组合的）、`VertexLinkLocalEuler.lean`/`FaceLinkLocalEuler.lean`（顶点/面星的去心邻域同伦等价于 link，
  `relativeEulerChar_vertex_eq_one_sub_link`）、`GeometricManifoldLinks.lean`（以拓扑流形图卡为假设的 link Euler 数，本车道改用 F4.1）。
- F 车道（`Topology/PiecewiseLinear/`）：`IsCombinatorialManifoldWithBoundary n K`、`boundaryComplex`、`IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_faces_iff`、
  `isPLSphere_or_isPLBall_geometricLink`（面 link 二分法）、`IsCombinatorialManifold.isPLSphere_geometricLink`、`isCombinatorialManifold_boundaryComplex`、
  `IsPLBall.not_isPLSphere`（`PLBallSphere.lean`，经 Euler 数）、`derivedNeighborhood`、`JoinInternal.lean`（`internalJoin`）、
  `geometricLink_derivedNeighborhood_eq`（`DerivedNeighborhoodLink.lean`）、`Gluing.lean`（`glued₁`/`glued₂`/`IsGlueIso`：沿子复形粘接两个复形，
  可用于 23.13 的倍化）、`simplexComplex`、`simplexBoundary`、`stdVertices`、`IsGlueIso.isPLHomeomorphOn`；
  E.0：`Topology/InvarianceOfDomainManifold.lean`。

## 4. 砖块（每砖一个新文件，放在 `DifferentialGeometry/Topology/PiecewiseLinear/`）

### 砖 H.1 `EulerPolyhedra.lean` —— χ 工具箱（计划 H.1 的 χ 部分与 H.3）

```lean
noncomputable def eulerChar (K : Geometry.SimplicialComplex ℝ E) : ℤ := faceEulerChar K.toPreAbstractSimplicialComplex
theorem eulerChar_eq_singular [Finite K.faces] (k : Type) [Field k] : eulerChar K = Homology.eulerChar k (TopCat.of K.space)
theorem eulerChar_eq_of_isPLHomeomorphOn [FD E] [FD F] (K) [Finite K.faces] (L) [Finite L.faces] {f} (hf : IsPLHomeomorphOn f K.space L.space) :
    eulerChar K = eulerChar L                                  -- 21.4/21.5：组合不变量（经同胚不变性）
theorem eulerChar_eq_of_isSubdivision (hK' : IsSubdivision K' K) : eulerChar K' = eulerChar K
theorem eulerChar_of_isPLSphere_one (hK : IsPLSphere 1 K.space) : eulerChar K = 0          -- 21.6
theorem eulerChar_of_isPLBall (hK : IsPLBall n K.space) : eulerChar K = 1                   -- 21.7（可缩）
theorem eulerChar_of_isPLSphere (hK : IsPLSphere n K.space) : eulerChar K = 1 + (-1) ^ n     -- 经 `eulerChar_euclideanSphere`
theorem eulerChar_union_add_inter (K₁ K₂ ≤ K) : eulerChar (K₁ ⊔ K₂) + eulerChar (K₁ ⊓ K₂) = eulerChar K₁ + eulerChar K₂   -- 21.8
theorem eulerChar_geometricLink … ; theorem bettiOne_… 见 H.4a
```
`21.10/21.11`（分裂与张成）先不做独立陈述：它们在 23.19 的归纳里以"沿 2-侧 1-球面切开并补盘后 χ 增 2"的形式出现，
在砖 H.5 内按需要证明（切开操作用 F 车道的 `Gluing`/`restrict` 构造，见 H.5）。

### 砖 H.2 `Orientation.lean` —— 组合定向（计划 H.2）

```lean
structure CoherentOrientation (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) where
  sign : Finset E → (E → ℕ) → ℤ        -- 或：每个 n+1 顶点的面上一个顶点线性序的奇偶类；选一种可判定表示并说明
  ...                                   -- 相邻 n-面在公共 (n−1)-面上诱导相反定向
def IsOrientable (n) (K) : Prop := Nonempty (CoherentOrientation n K)
-- 23.14：定向的边界是 ∂K 的定向
def CoherentOrientation.boundary (h : IsCombinatorialManifoldWithBoundary n K) (o : CoherentOrientation n K) : CoherentOrientation (n-1) (boundaryComplex n K)
theorem IsOrientable.boundary … : IsOrientable (n-1) (boundaryComplex n K)
-- 23.17：可定向流形的子流形复形可定向（限制）
theorem IsOrientable.of_le (hL : L ≤ K) (hLm : IsCombinatorialManifoldWithBoundary n L) (h : IsOrientable n K) : IsOrientable n L
-- 23.13 + 23.15：倍化（沿 ∂K 粘两份，用 Gluing.lean 的 glued₁/glued₂ 与 IsGlueIso），倍化是无边组合流形，K 可定向 ⟹ 倍化可定向
noncomputable def double (h : IsCombinatorialManifoldWithBoundary n K) : Geometry.SimplicialComplex ℝ (E × E × ℝ)
theorem isCombinatorialManifold_double … ; theorem IsOrientable.double …
-- 24.7 用的定向上循环：不可定向连通 ⟹ 二重覆盖的组合数据（交给 C 车道 C.4 消费：给出 ℤ₂ 1-上循环，非上边界）
theorem exists_orientationCocycle_of_not_isOrientable … : ∃ ε : SimplicialBoolCocycle (barycentricSubdivision K), ¬ ε.IsCoboundary
-- 可定向 ⟺ 每个分支可定向；PL 同胚/细分下不变（用 IsGlueIso 与 barycentricSubdivision 的定向诱导）
```
关键组合事实（先证）：带边组合 `n`-流形的每个 `(n−1)`-面恰在 1 个（边界面）或 2 个（内部面）`n`-面中——由 link 二分法
`isPLSphere_or_isPLBall_geometricLink`（`(n−1)`-面的 link 是 0-球面 = 两点 或 0-球 = 一点）与 `LinkDimension.lean`。
上循环：`ε` 取在 `bK` 的边 `{σ̂, τ̂}`（`σ ⊂ τ` 相邻顶维面的重心）上比较 `τ` 与相邻面对 `σ` 的诱导定向，非顶维边取 0；
沿 `bK` 中的边环路（路径提升）的奇偶性；`C` 车道的 `SimplicialBoolCocycle` 定义见 `HANDOFF_CODEX_C.md` 砖 C.2（在 `codex/moise-e3` 分支；
若尚未推送，先在本车道定义同构的结构并在合并时统一）。

### 砖 H.6 `MayerVietorisSubcomplex.lean` —— 子复形的 MV 与 28.11（计划 H.6，也是 H.4a/H.5 的工具）

```lean
-- 子复形在二次导出细分中有开邻域形变收缩到它（沿 internalJoin 的联结线径向收缩）
theorem exists_isOpen_deformationRetract_of_le [Finite K.faces] (hL : L ≤ K) :
    ∃ U, IsOpen U ∧ L.space ⊆ U ∧ U ⊆ K.space ∧ ∃ r : C(U, L.space), (∀ x ∈ L.space, r x = x) ∧ (inclusion ∘ r).Homotopic id  -- 精确形式按 Mathlib 的 `ContinuousMap.Homotopy`
-- MV 正合性（所需片段）：K = K₁ ⊔ K₂，A := K₁ ⊓ K₂
theorem exists_mem_inter_of_map_eq_zero {n} (hK : K = K₁ ⊔ K₂) {z : H_n(K₁.space; ℤ)} (hz : (inclusion).map z = 0 in H_n(K.space)) :
    ∃ y : H_n((K₁ ⊓ K₂).space; ℤ), (incl₁).map y = z ∧ (incl₂).map y = 0     -- 28.11
theorem bettiOne_union_le … ; theorem eulerChar 加法（已由 H.1 组合给出，无需 MV）
```
路线：把 `K₁`、`K₂` 的开邻域 `U₁`、`U₂`（第一条）作开覆盖，用 `Reduced/MayerVietoris.lean` 的小链 MV（或 `Relative/Excision`）
得到 `U₁ ∪ U₂ = |K|`、`U₁ ∩ U₂ ≃ |K₁ ⊓ K₂|`（形变收缩到交，需要 `U_i` 取导出邻域使 `U₁ ∩ U₂` 收缩到 `|A|`：选 `U_i := ` 二次导出
细分中 `K_i'` 的开星邻域，`U₁ ∩ U₂` = `A'` 的开星邻域），同伦不变性搬运。

### 砖 H.4a `SurfaceHomology.lean` —— 闭曲面的顶维同调与 22.6/22.7（计划 H.4 的同调部分）

```lean
-- K 闭连通组合 2-流形（IsCombinatorialManifold 2 K，K.space 连通）
theorem bettiTwo_eq_one_of_isOrientable (ho : IsOrientable 2 K) : Module.finrank ℚ (H₂(K.space; ℚ)) = 1
theorem bettiTwo_eq_zero_of_not_isOrientable (ho : ¬ IsOrientable 2 K) : Module.finrank ℚ (H₂(K.space; ℚ)) = 0
theorem eulerChar_eq_two_sub_bettiOne_of_isOrientable … : eulerChar K = 2 - bettiOne K.space      -- 22.7 (i)
theorem eulerChar_eq_one_sub_bettiOne_of_not_isOrientable … : eulerChar K = 1 - bettiOne K.space   -- 22.7 (ii)
theorem even_bettiOne_of_isOrientable … : Even (bettiOne K.space)                                   -- 22.6 的推论，与 h 的定义
theorem bettiOne_polygon (hJ : IsPLSphere 1 J.space) : bettiOne J.space = 1；polygon 的类生成 H₁（`integralSphereTopHomologyEquiv 0`）
```
路线：`H_q(|K|;ℚ) = 0` 对 `q ≥ 3` 与 `H₂` 的计算用"面归纳 + MV"（H.6）或局部同调：相干定向给出仿射奇异 2-链
`Z = ∑ ±σ`（每个 2-面一个仿射奇异单形，边界项按相干性两两相消），`Z` 在每个 2-面内点的局部同调像是生成元
（`puncturedNeighborhoodHomologyIso` + `euclideanClosedBallFundamentalClass_ne_zero`），故 `[Z] ≠ 0`；任意 2-循环 `c` 在各面内点的
局部像是 `d_σ·gen`，相邻面的 `d_σ` 相等（在公共边内点的局部同调里比较，用 `Local/Graded` 与 F4.1 的 link 为两点），连通性给常数 `d`，
`c − d·Z` 局部处处为零 ⟹ 零（面归纳：去掉一个 2-面的开单形后剩余是 1 维复形并 `H₂ = 0`，用 MV/相对同调），得 `H₂ ≅ ℚ`；
不可定向：若 `H₂ ≠ 0`，取非零类，同样的局部系数 `d_σ` 给出相干定向，矛盾。χ 公式由 `eulerChar_eq_singular` 与 `H₀ ≅ ℚ`（连通）。
若"局部像"论证在形式化里过重，可改用 H.6 的 MV 沿 2-面逐个粘接归纳计算 `H₂`（每粘一个 2-面，`H₂` 至多增 1，恰在闭合时增 1）。

### 砖 H.5 `HandleCount.lean` —— 23.18、23.19 与 C.5 的输入（计划 H.5）

```lean
-- 23.18′：K 可定向组合 3-流形，L ≤ K 维数 ≤ 1，N := derivedNeighborhood K L
theorem eulerChar_boundaryComplex_eq_two_mul (h : IsCombinatorialManifoldWithBoundary 3 N) : eulerChar (boundaryComplex 3 N) = 2 * eulerChar N
    -- 用 BoundaryCounting.faceEulerChar_eq_two_mul_of_link_counts，link 的 χ 由 F4.1（球面 χ = 2，球 χ = 1）与 H.1 给出；对任意带边组合 3-流形成立
theorem bettiOne_derivedNeighborhood_eq (hL : L ≤ K) (hdim : ∀ s ∈ L.faces, s.card ≤ 2) : bettiOne N.space = bettiOne L.space  -- 形变收缩（H.6 第一条）
theorem bettiOne_graph (hdim : ∀ s ∈ L.faces, s.card ≤ 2) (hconn : connected) : bettiOne L.space = 1 - eulerChar L                 -- 图：H₂ = 0
theorem bettiOne_boundary_eq_two_mul_of_graph … : bettiOne (boundaryComplex 3 N).space = 2 * bettiOne N.space                       -- = 23.18（h(B) = p¹(N)）
-- 23.19′（C.5 需要的形式）：K 紧致连通可定向带边组合 3-流形，某边界分支 B 满足 χ B ≠ 2（等价：非 2-球面）⟹ bettiOne K.space > 0
theorem bettiOne_pos_of_boundary_not_sphere … : 0 < bettiOne K.space
-- 供 C.5：进一步给 ℤ₂ 版本 bettiOneTwo K.space > 0（或直接给非上边界的 ℤ₂ 1-上循环，见 C 车道砖 C.2 的 SimplicialBoolCocycle）
```
路线（Moise 23.19 的归纳，去掉柄数语言）：(1) 23.16：`K` 组合等价于某可定向组合 3-流形 `K'` 的子复形 `L`（`dim L ≤ 2`）的正则邻域
`N(L)`——用 F4.2 的 `derivedNeighborhood` 与 M.4（23.12–23.13：`|L|` 与 `N(L)` 组合等价、带边流形是子复形的正则邻域，倍化 `double`）；
M.4 在 C 车道未做，本砖需要的部分（倍化 + `K` 是自身在倍化中的正则邻域）自证并记入计划行 M.4。(2) 对 `L` 的 2-面数归纳：
`dim L ≤ 1` 时由 23.18′ 得 `bettiOne (∂N) = 2 bettiOne N`；加一个 2-面 `σ`：`N(L ∪ σ) = N(L) ∪ N'(σ)`，`N'(σ)` 是 3-球，`N(L) ∩ N'(σ)` 是环带 `A`
（`∂σ` 的正则邻域），MV（H.6）给 `H₁(N(L')) ≅ H₁(N(L))/⟨Z_A⟩`，`Bd N(L')` 由 `Bd N(L)` 沿 `A` 的两条边界圆切开并补两个盘得到，χ 增 2，
`bettiOne` 减 2 或减 0；两种情形分别验证不等式 `bettiOne N ≥ bettiOne (∂N) / 2` 保持。(3) `χ B ≠ 2` 且 `B` 可定向闭连通（23.14）
⟹ `bettiOne B > 0`（H.4a）⟹ `bettiOne (∂K) > 0` ⟹ `bettiOne K > 0`。
替代路线（若 (2) 的切开构造过重）：ℚ 系数的 Poincaré–Lefschetz 对偶 "half lives, half dies"——本树没有，代价更高，不选。

### 砖 H.4b（决定项，先不做）—— 识别定理

22.11（单连通 ⟹ 2-球面）用于 §30.6、§32；22.9（可定向 + χ ⟹ 同胚型）用于 §33 L11–L12，计划 R4 认为后者可能可用
`bettiOne` 计数代替。两条路线：(i) 原生：Moise §22 的"盘加条带"归约（需要 S 车道 vendored 的平面 PL 移动
`ElementaryMove`/`ThinKiteMove`/`PolygonalCrosscut`），估 10k–15k 行；(ii) vendored：外部仓库 `classification_of_surfaces`
（拓扑版，依赖 124 模块 140k 行，且没有 χ/定向计算，还需把组合 2-流形带边接成 `EuclideanHalfSpace 2` 图卡），**不推荐**。
到 I 车道消费前由用户决定；本车道先把 §30.6/§32/§33 实际需要的陈述抄进计划行 H.4 的"拟定 Lean"列。

## 5. 顺序与记录

H.1 → H.2 → H.6 → H.4a → H.5 →（H.4b 待决定）。每砖闭环 = 检查通过 → 审计（复用声明的 D4 审计一并做）→ 提交并推送。
完成后更新计划行 H.1–H.6、M.4（自证部分）、§1 D3 的修订、§8 R3 改为"已定：奇异同调"、`MOISE_PLAN.md` §6；这些文件其它车道也在改：
最后一次提交前 `git fetch origin` 并在 `origin/codex/moise-smoothing` 上 rebase。审计文件 `AuditH<k>.lean` 递增。
报告：模块、端点、审计、检查退出码、未闭合项与确切缺口。

## 6. Lean 坑

- 本库同调的宇宙：`integralSingularHomology (n) (X : Type u)`、`eulerChar (k) (X : TopCat.{u})`；`EuclideanSpace ℝ (Fin k)` 与子类型在 `Type 0`，
  取 `u := 0`；`TopCat.of K.space` 是子类型上的空间，`Homeomorph`/`HomotopyEquiv` 用 `ContinuousMap.HomotopyEquiv`。
- `Module.finrank ℚ` 需要 `Module.Finite`：先证 `finiteHomologyType`（`finiteHomologyType_geometricSpace`）。
- `rw` 关闭目标后再 `rfl` 报 "No goals"；`rcases … with rfl` 会消去固定变量；`▸` 高阶合一易选错实例；`open Classical` 下 `not_imp` 用 `Classical.not_imp`。
- `theorem IsCombinatorialManifoldWithBoundary.foo` 内裸名解析到同命名空间定理，写 `PiecewiseLinear.secondDerived K`。
- Git Bash 无 `grep -P`，用 `sed`。
