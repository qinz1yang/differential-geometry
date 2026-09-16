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

## 7. 2026-09-15 追加：H.2 上循环设计更正；先做线性细分不变性（H.2a），再做上循环（H.2b）

### 7.0 复核

`Orientation.lean` 由本方独立重编 exit=0（32 秒）；`AuditH2BarycentricInverse` 146 项只含标准三公理。
`isOrientable_iff_of_isGlueIso`、`isOrientable_barycentricSubdivision_iff`、`isOrientable_iff_forall_simplicialComponent` 可作为下面的输入。

### 7.1 更正（砖 H.2 原文"非顶维边取 0"作废，你的判断成立）

正确构造：`bK` 的每个顶点 `σ̂`（`σ ∈ K`，任意维）配一个**局部定向** = 闭星 `st(σ, K)`（含 `σ` 的全部顶维单形）的一个相容定向；
边 `{ρ̂, σ̂}`（`ρ ⊂ σ`）的值 = 两个局部定向在任一含 `σ` 的顶维单形上的比较（`st(σ) ⊆ st(ρ)`，`st(σ)` 对偶连通 ⇒ 与选择无关）；
三角形恒等式由同一顶维单形上的传递性；上边界 ⇔ 局部定向可全局翻转成相容 ⇔ `IsOrientable`。
前置正是你指出的缺口：每个闭星可定向且对偶连通。`σ` 顶维、余维 1、余维 2 时初等（两个单形；绕边的扇）；
`σ` 为顶点时 `st(v) = v * lk(v)`，`lk(v)` 是 PL 球面/球（组合流形定义），其组合可定向性需要 **PL 不变性**：
已有同构不变性与重心细分不变性，缺任意线性细分。别走奇异同调局部定向那条路（需要单纯–奇异比较定理，本库没有）。

### 7.2 里程碑 H.2a：线性细分不变性 ⇒ PL 不变性 ⇒ 球、球面、闭星可定向

接口（签名冻结后写进计划行 H.2）：
```lean
theorem isOrientable_iff_of_isSubdivision (h : IsSubdivision K' K) : IsOrientable n K' ↔ IsOrientable n K
theorem isOrientable_iff_of_isPLHomeomorphOn (hf : IsPLHomeomorphOn f K.space L.space) : IsOrientable n K ↔ IsOrientable n L
theorem isOrientable_of_isPLBall (h : IsPLBall n K.space) : IsOrientable n K
theorem isOrientable_of_isPLSphere (h : IsPLSphere n K.space) : IsOrientable (n + 1) K   -- 维数按 IsPLSphere 的约定对齐
theorem coherentOrientation_eq_or_eq_neg (hconn : 顶维单形沿余维一面对偶连通) (o o' : CoherentOrientation n K) : o = o' ∨ o = o'.neg  -- 或以 sign 相等表述
theorem isOrientable_closedStar (hK : IsCombinatorialManifoldWithBoundary n K) (hσ : σ ∈ K.faces) : IsOrientable n (closedStar K σ)
```
架构：`IsSubdivision K' K`（F 的 `Subdivision.lean`：`K'` 的每个单形落在 `K` 的某个单形内、载体相等）。细分单形 `s ⊆ τ` 的定向用
**仿射定向符号**（`s` 的顶点向量组相对于 `τ` 的顶点向量组在 `τ` 方向空间上的行列式符号；在你的 `LinearOrder`/`sign` 词汇里就是
用行列式符号定义 `sign s`）。正向：`K` 的相容定向诱导 `K'` 的相容定向——同一 `τ` 内相邻两单形按同一仿射定向自动相容（线性代数：
公共面两侧的两个单形诱导相反的面定向）；落在 `K` 的公共面 `τ ∩ τ'` 里的 `K'`-面用 `τ, τ'` 的相容性。反向：`K'` 的相容定向在每个 `τ`
内部对偶连通（`τ` 的细分是球，去掉余维 2 骨架仍连通）⇒ 常号 ⇒ 诱导 `K` 的定向。PL 不变性：`exists_isGlueIso_of_isPLHomeomorphOn`
（`IsomorphicSubdivision.lean`）给两侧细分与粘接同构，接 `isOrientable_iff_of_isGlueIso`。球/球面：标准单形及其边界显式可定向。
闭星：`lk(σ)` 是 PL 球/球面 ⇒ 可定向；`σ * lk(σ)` 的相容定向 ⇔ `lk(σ)` 的相容定向（join）；对偶连通由 link 连通（维数 ≥ 1）。

### 7.3 里程碑 H.2b：定向上循环（C.4 消费）

接口：
```lean
def orientationCocycle (hK : IsCombinatorialManifoldWithBoundary n K) (o : ∀ σ ∈ K.faces, CoherentOrientation n (closedStar K σ)) :
    SimplicialBoolCocycle (barycentricSubdivision K)
theorem orientationCocycle_isCoboundary_iff : (orientationCocycle hK o).IsCoboundary ↔ IsOrientable n K
theorem exists_orientationCocycle_of_not_isOrientable : ¬ IsOrientable n K →
    ∃ ε : SimplicialBoolCocycle (barycentricSubdivision K), ¬ ε.IsCoboundary
```
`SimplicialBoolCocycle`、`IsCoboundary` 是 C.2 的（`DoubleCoverComplex.lean`，整合分支）。局部定向族 `o` 由 7.2 存在；
上循环值与 `o` 的选择只差上边界，所以第三条对任意 `o` 成立。

### 7.4 之后

H.6、H.4a、H.5 顺序不变。整合分支现已含 Bennett 的 `Topology/Homology/{Coefficients, ChangeOfRings, CoveringTransfer*,
Reduced/MayerVietorisCoefficients, Reduced/PointClasses}`（`REUSE_AUDIT.md` §2），H.5 的 ℤ₂/ℚ 系数与二重覆盖 transfer 可直接用；
下一个检查点先合并 `origin/codex/moise-integration`。检查点：H.2a 的细分不变性做完汇报，再做 H.2b。

## 8. 夜间里程碑（2026-09-15 → 09-16）

### H-M1 — done，I4 已交付

- 数学提交：`85cd6e095`（局部定向上循环构造）、`fe39d3cca`（上边界等价与非平凡性）；H.2a 已由 `87b44df51` 交付。
- 整合基线：已合并包含 `8fb887bb9` 的整合分支，H 合并提交 `050f9246e`。
- 文件：`OrientationCocycle.lean`，辅助 `DerivedCarrier.lean`；`Orientation.lean` 的限制接口现包含零维。
- I4 三端点：`orientationCocycle`、`orientationCocycle_isCoboundary_iff`、`exists_orientationCocycle_of_not_isOrientable`。
  局部族是每个非空面的 `faceStarComplex` 的相干定向；任意维数、有限复形、有限维实赋范环境，无公开 `DecidableEq`。
- 夜间复核：`check-f.ps1` 检查 `OrientationCocycle` exit=0、零 warning（56.6 秒）；
  `.lake/scratch/AuditNightHM1.lean` 保留 24 项命名空间完整的 `#print axioms`，审计 exit=0，12 项核心与 12 项复用声明仅三公理。
- 确切缺口：I4 无；C.4 覆盖流形的可定向性不是本里程碑端点，余力在 H-M5 做。下一项 H-M2。

### H-M2 — partial，开邻域几何层已闭合

- 新模块 `SubcomplexNeighborhood.lean`：正重心质量定义相对开邻域；
  `subcomplexOpenNeighborhoodStrongDeformationRetract` 给强形变收缩，
  `subcomplexOpenNeighborhoodHomotopyEquiv` 的逆映射是原来的子复形包含；
  `subcomplexOpenNeighborhood_inter` 与 `subcomplexOpenNeighborhood_union` 给交集兼容与开覆盖。
- 聚焦检查 exit=0、零 warning（10.4 秒）。保留 `.lake/scratch/AuditNightHM2Neighborhood.lean`
  的 27 项审计（19 项新声明、8 项复用）及 `AuditNightHM2Reuse.lean` 的 19 项复用预审计；全部仅三公理。
- 此为 H-M2 中间检查点，数学提交哈希见下一段登记。未闭合：小链短正合列的元素级 28.11、
  从开邻域包含同伦等价向子复形搬运的自然性、Betti 数不等式；尚未声明 H-M2 done。

### H-M2 — done，28.11 与子复形 Betti 上界已交付

- 数学提交：`11826f868`（兼容开邻域与强形变收缩）、`c9fff0308`（小链 MV 正合性、子复形搬运与 Betti 上界）。
- `MayerVietorisSubcomplex.lean` 的 `exists_mem_inter_of_map_eq_zero`：有限复形 `K` 的两个子复形覆盖，
  任意次数、任意环及系数模；因此直接包括整系数 28.11。三个包含诱导同调同构，相关包含方块严格交换。
- `bettiNumber_union_le`：`b_(n+1)(K) ≤ b_(n+1)(L) + b_(n+1)(M) + b_n(L∩M)`，任意域系数。
  `bettiOne_union_le` 是有理一阶特例，明确保留交集的 `b_0` 项；未声称任意非连通交集时可删去此项。
  `Homology.bettiOne X` 定义为 `finrank ℚ H₁(X;ℚ)`。
- 可复用代数/同调层在 `Homology/Algebra/PushoutHomology.lean`、`Homology/HomotopyEquivalence.lean`、
  `Homology/BettiNumber.lean`、`Homology/SmallChains/{Exactness,BettiBound}.lean`，无新单纯链复形。
- 七个模块检查均 exit=0、零 warning，最后 `MayerVietorisSubcomplex` 10.5 秒；`git diff --check` 通过。
  `.lake/scratch/AuditNightHM2*.lean` 保留 83 项去重后的命名空间完整审计（39 项新声明、44 项复用/预审计），
  全部只有 `propext`、`Classical.choice`、`Quot.sound` 或更少；复用记录已写 `MOISE_PLAN.md` §6。
- 确切缺口：28.11、相对开邻域 SDR、上述各阶 Betti 上界无；未导出整条命名的子复形长正合列或更尖锐的连通交集估计。
  H-M3 的全局顶维基本类/定向判据、H-M4 的 I5 不是本里程碑结论。下一项 H-M3。

### H-M3 — partial，低阶同调层已交付，顶维定向比较未闭合

- 数学提交：`163a27733`。新模块 `SimplicialComplex/GeometricHomology.lean`、
  `SimplicialComplex/GeometricConnectivity.lean`、`PiecewiseLinear/BettiPolyhedra.lean`；
  `Homology/BettiNumber.lean` 增加路径连通空间的零阶 Betti 数。
- `isZero_singularHomology_geometricSpace_of_card_le` 对任意环与系数模证明维数以上的奇异同调消失。
  复用已有有限 simplicial-set realization 到奇异同调的同构（也是 χ 桥的基础），未新建单纯链复形。
  有限几何复形局部路径连通；连通即路径连通，因此 `bettiNumber_zero_of_isConnected` 给 `b_0=1`。
- `eulerChar_eq_sum_bettiNumber`、`eulerChar_eq_one_sub_bettiOne_add_bettiTwo`、
  `bettiOne_graph`、`bettiOne_polygon` 已闭合。多边形结论是有理 `b_1=1`，不是已交付整系数指定生成元。
  `SubcomplexNeighborhood.subcomplexInclusion` 改为复用原生 `geometricInclusion`，签名不变。
- 五个修改/新增模块检查 exit=0、零 warning；更新后 `MayerVietorisSubcomplex` 再检查 exit=0（12.1 秒）。
  `BettiPolyhedra` 最后检查 11.2 秒。`.lake/scratch/AuditNightHM3*.lean` 保留 26 项去重审计：
  11 项新声明、2 项既有端点复核、13 项复用/预审计，全部仅标准三公理；复用已登记 `MOISE_PLAN.md` §6。
- 确切缺口：相干定向的仿射奇异基本类具有指定局部生成元像；跨公共边的局部生成元符号比较；
  全局顶维类到局部同调的检测/单射定理。已有 `Local/FiniteSet` 只分解相对群
  `H_2(K,K\Z)`，并不证明 `H_2(K)` 到该群单射。缺这些生产者，不能导出定向/非定向的 `b_2=1/0`。
  有理一阶 Betti 数偶性还需交叉配对或曲面归约，尚未闭合。
- §4 路线修正：一般不能说“去掉一个二维开面后剩余是一维复形”；应另证删去所有顶面内点后的
  骨架形变收缩，或沿对偶树作逐面消去。已核对 Moise 原书 22.6–22.7：原证明使用盘加条带归约，
  不能把它当作本库现成的局部到全局基本类比较。
- 按夜间 §0.4 记录这一真实数学缺口后转 H-M4 的独立边界 χ 计算；未弱化 H.4a 的冻结端点，
  未引入结论型假设、`sorry` 或未审计的 Hurewicz 链。

### H-M4 — partial，23.18′ 的 Euler 与导出邻域层已交付，I5 阻塞

- 数学提交：`09bc51619`。新模块 `BoundaryEuler.lean`、`DerivedNeighborhoodHomology.lean`、
  `HandleCount.lean`。
- `eulerChar_boundaryComplex_eq_two_mul` 对任意有限组合带边 3-流形证明
  `χ(boundaryComplex 3 K) = 2χ(K)`；结论实际不需可定向或连通假设。
  `eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary` 同时导出所有面 link 的球/球 Euler 值。
- `derivedNeighborhoodHomotopyEquiv`、`bettiNumber_derivedNeighborhood_eq`、
  `bettiOne_derivedNeighborhood_eq`、`eulerChar_derivedNeighborhood_eq` 证明导出邻域保持全部域系数 Betti 数和 χ。
  `IsOrientable.derivedNeighborhood` 由二次重心细分的可定向性及子流形限制给出；
  `eulerChar_boundary_derivedNeighborhood_eq_two_mul` 和 `bettiOne_derivedNeighborhood_graph` 是 23.18 的直接消费层。
- 三个模块聚焦检查均 exit=0、零 warning：`BoundaryEuler` 12.6 秒、
  `DerivedNeighborhoodHomology` 10.1 秒、`HandleCount` 11.0 秒。
  `.lake/scratch/AuditNightHM4{Reuse,Final}.lean` 保留 32 项去重审计（10 项新、22 项复用/预审计），
  全部仅 `propext`、`Classical.choice`、`Quot.sound`。
- I5 的确切未闭合义务有三项：首先 H-M3 尚缺闭曲面顶维基本类，因而还没有
  `χ(B)=2-b₁(B)`；其次一般带边 3-流形仍缺 23.19 的核心不等式
  `b₁(boundaryComplex 3 K) ≤ 2*b₁(K)`（或等价的 half-lives/half-dies 生产者）；最后从
  `¬ IsPLSphere 2 B.space` 推出 `0 < b₁(B.space)` 需要 H.4b 的闭可定向曲面识别
  `b₁=0 → IsPLSphere 2`。这些都不是 NIGHT_PLAN §1 已给的跨车道接口，不能包装成结论型假设。
- 因而未声明 `bettiOne_pos_of_boundary_component_not_sphere`，也未用 `χ(B)≠2` 替换冻结的非球面假设。
  按 §0.4 转 H-M5 的二重覆盖定向引理。
