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

### H-M5 — done，定向上循环的二重覆盖复形整体可定向

- 数学提交：`c6830cc26`（覆盖复形的流形与局部定向层）、`4e81f6e2d`（sheet 奇偶公式与全局相干定向）。
  模块为 `CoveringOrientation.lean`，并在 `Orientation.lean`、`OrientationCocycle.lean` 导出证明所需的仿射余面相消与
  局部细分定向符号接口。
- `SimplicialBoolCocycle.coveringNeighbor_side` 证明一条提升边两端的 sheet 坐标之 XOR 正是基边上的 `parity`；
  `orientationCocycle_parity_eq_localSubdivisionOrientationSign` 与
  `localSubdivisionOrientationSign_pair_cancel` 把该奇偶公式变成公共余维一面上的边界符号相消。
- `orientationCocycleCoveringOrientation` 显式构造
  `coveringComplex (barycentricSubdivision K) (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj`
  的相干定向；`isOrientable_coveringComplex_orientationCocycle` 给最终可定向性端点。结论对任意维数的有限组合带边流形成立，
  无公开 `DecidableEq`，零维由 `isOrientable_zero` 单独闭合。
- 最终聚焦检查均 exit=0、零 warning：`Orientation` 32.2 秒、`OrientationCocycle` 29.3 秒、
  `CoveringOrientation` 14.9 秒。`.lake/scratch/AuditNightHM5OrientationCover.lean` 审计 37 项
  （13 项新增/提升端点、24 项关键复用），全部只有 `propext`、`Classical.choice`、`Quot.sound`；
  `git diff --check` 与新增禁用项扫描通过。
- H-M5 无未闭合端点。H-M3 的全局顶维基本类/定向比较，以及 H-M4/I5 的 23.19 Betti 不等式与
  `b₁=0 → IsPLSphere 2` 识别仍是原有真实缺口，本里程碑没有弱化或包装这些义务。

### H.4b — done，`faceEulerChar = 2` 的闭组合曲面是 PL 2-球面

- 数学提交：`465433505`；支撑层提交：`c322bee57`、`7cbe0839f`。新模块
  `SurfaceSphereRecognition.lean`，最终端点为
  `IsCombinatorialManifold.isPLSphere_two_of_faceEulerChar_eq_two`。
- 对连通有限闭组合 2-流形取 1-骨架生成树 `T`；Euler 计数使未选边的对偶图
  `dualCotreeGraph K T` 也是树。原面按“顶点/树边”与“三角形/非树边”分区，各自的导出邻域胞腔并
  分别由 `isPLBall_primalTreeCellComplex` 和 `isPLBall_dualCotreeCellComplex` 识别为 PL 2-球。
- 两侧共同面通过两个不同导出胞腔的 PL 1-球交扩张到共同边，因此没有共同顶维面。
  `subcomplexGeneratedBy_compl_eq_of_faces_cover_of_pure_inter` 将两侧互相识别为闭曲面中的闭补复形，
  现有的子流形边界定理给出交集恰是两个球的公共边界；经 `boundaryRelSubdivision`
  使边界满后，`isPLSphere_gluedComplex_of_isPLBall` 完成粘合球面识别。
- `SurfaceSphereRecognition` 聚焦检查 exit=0，11.0 秒，零 warning；
  `.lake/scratch/AuditHSurfaceSphereRecognition.lean` 对 22 个新定理及 11 个关键复用声明逐项审计，
  exit=0，全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- H.4b 无未闭合项。下一里程碑按 `NIGHT_PLAN.md` §6.1 用 `faceEulerChar` 路线交付 I5；
  H-M3 的顶维基本类继续后推。

### I5 / H-M4 — done，非球面边界分支迫使一阶 Betti 数为正

- 数学提交：`1d7ffe266`。新模块 `BoundaryHomology.lean`；`HandleCount.lean` 的跨车道端点为
  `bettiOne_pos_of_boundary_component_not_sphere`，签名保持 `IsCombinatorialManifoldWithBoundary 3 K`、
  `IsOrientable 3 K`、`IsConnected K.space`、指定边界连通分支及该分支非 `IsPLSphere 2`。
- 证明使用现有有序单纯集合的 normalized chain complex 作内部坐标，不新增同调表示层；最终结论仍是本库奇异
  `Homology.bettiOne`。每个非基准边界分支的相干定向 2-循环与所有 3-单形边界组成一个到 2-循环空间的单射，
  给出 `card(other boundary components) ≤ b₂(K)`。同一余维一面传播论证证明带非空边界的连通可定向
  3-流形顶微分单射，因而奇异 `b₃(K)=0`。
- `faceEulerChar` 按连通分支分解；H.4b 与每个闭连通组合曲面的 `χ≤2` 将指定非球面分支改进为严格上界
  `χ(∂K)<2·card(π₀∂K)`。结合 `χ(∂K)=2χ(K)`、`χ(K)=1-b₁+b₂` 和上述秩界，若 `b₁=0`
  即得矛盾，闭合 I5；没有等待 H-M3 的闭曲面全局顶维基本类。
- 聚焦检查均 exit=0、零 warning：`OrderedChainCoordinates` 13.1 秒、`BoundaryHomology` 25.3 秒、
  `HandleCount` 11.9 秒；`fresh.py` 报 7 个相对整合分支改动模块全部 olean 新鲜、零禁用项。
  `.lake/scratch/AuditHI5.lean` 逐项审计 47 个新增声明与 23 个关键复用声明，exit=0，全部仅含
  `propext`、`Classical.choice`、`Quot.sound`。
- I5 无未闭合项。H-M3 的闭曲面基本类、可定向/不可定向闭曲面完整 `b₂` 公式仍按计划后推；本里程碑只证明
  I5 所需的带非空边界三维顶同调消失，不冒充 H-M3 完成。

### H-M6 — done，22.11 单连通闭组合曲面是 PL 2-球面

- 数学提交：`0a4d434c7`。新模块 `Topology/Homology/FieldPathCones.lean` 与
  `PiecewiseLinear/SurfaceSimplyConnected.lean`；最终端点为
  `IsCombinatorialManifold.isPLSphere_two_of_simplyConnectedSpace`。
- `fieldSingularConeZero` / `fieldSingularConeOne` 将既有道路锥论证推广到任意域系数，证明单连通空间的一维奇异同调
  为零；`Homology.bettiOne_eq_zero_of_simplyConnectedSpace` 给出有理 Betti 数版本。
- 对闭组合 2-流形，以所有三角形系数均为 1 构造 ℤ₂ 顶维链；每条边恰有两个余面且 ℤ₂ 中符号消失，故边界为零。
  复形无三维 normalized chains，因而该非零循环给出
  `IsCombinatorialManifold.bettiNumber_two_pos_mod_two`。单连通性再给 `b₀=1`、`b₁=0`，Euler–Betti 公式与
  `faceEulerChar_le_two` 夹出 `faceEulerChar=2`，最后消费 H.4b 的球面识别端点。
- 两个模块聚焦检查 exit=0、零 warning，分别为 9.4 秒与 11.3 秒；`fresh.py` 报两个改动模块 olean 全部新鲜、
  零禁用项。`.lake/scratch/AuditHM6.lean` 逐项审计 26 个新增声明与 18 个关键复用声明，exit=0，全部仅含
  `propext`、`Classical.choice`、`Quot.sound`。
- H-M6 无未闭合项；没有 import `Homology/HurewiczLowDegrees.lean`，没有使用曲面分类。下一项为 H-M7 的
  §21 Euler 运算与 28.20 分裂公式。

### H-M7 — done，§21 Euler 运算与 28.20 分裂公式

- 数学提交：`9bcc38d82`。新模块 `EulerCellOperations.lean` 与 `SurfaceSplitEuler.lean`。
- `OpenCellProfile.Operation` 的 `alpha`、`beta`、`gamma`、`delta` 精确记录四种开胞腔操作对顶点、边、面的计数变化；
  `OpenCellProfile.eulerChar_apply` 与 `eulerChar_eq_of_isRefinement` 证明单步及有限次操作保持 χ。
  `simplicialOpenCellProfile_eulerChar` 将三维数计数重新接回有限二维复形的 `faceEulerChar`；实际线性细分仍由既有
  `eulerChar_eq_of_isSubdivision` 给出 PL 不变量。
- `eulerChar_eq_add_sub_of_faces_union` 是任意公共环境中两个子复形的包含排除式；交为 PL 1-球面时，
  `eulerChar_eq_add_of_faces_union_of_isPLSphere_one` 给出 21.8 的无修正加法。既有
  `eulerChar_of_isPLSphere_one` 与 `eulerChar_of_isPLBall` 分别给 21.6、21.7。
- `SurfaceSplitAlongPolygon` 用公共核心、PL 同胚于 `J × [0,1]` 的环带、两条互不相交的 PL 多边形边界以及切后曲面
  与核心的 PL 同胚定义 21.10 的分裂；`SurfaceSplitAlongPolygon.eulerChar_eq` 证明 χ 不变。
  `SurfaceSplitAndCap` 再记录两个互不相交的 PL 2-胞腔及其边界粘接，
  `SurfaceSplitAndCap.eulerChar_eq_add_two` 同时交付 21.11 与 28.20。结构中没有把任何 Euler 等式作为字段。
- 两个模块聚焦检查 exit=0、零 warning，分别为 9.5 秒与 9.7 秒；`fresh.py` 报本车道相对整合分支的四个改动模块
  olean 全部新鲜、零禁用项。`.lake/scratch/AuditHM7.lean` 逐项审计 21 个新增声明与 18 个关键复用声明，
  exit=0，全部公理闭包均包含于 `propext`、`Classical.choice`、`Quot.sound`。
- H-M7 无未闭合项；下一项为 H-M8 的 22.5–22.7。

### H-M8 — done，22.5–22.7 的闭曲面同调与数值公式

- 数学提交：`3fdf6d58e`。新模块 `SurfaceHomology.lean` 与 `SurfaceInvariants.lean`。
- `SurfaceHomology.lean` 直接在现有有序 normalized chain complex 中计算闭连通组合 2-流形的顶维同调：
  可定向时相干定向链生成 `ker d₂`，不可定向时任一非零有理顶循环会沿对偶图重建相干定向并导致矛盾。
  经既有 realization/奇异同调桥，得到
  `bettiNumber_two_eq_one_of_isOrientable`、`bettiNumber_two_eq_zero_of_not_isOrientable`，以及无条件的 22.7：
  可定向时 `χ = 2 - b₁`，不可定向时 `χ = 1 - b₁`。
- `SurfaceInvariants.lean` 定义标准的 `surfaceHandleCrosscapProfile h m`，证明其
  `χ = 2 - (2h + m)`；凡实际给出该标准剖分的细分见证，22.5 即由开胞腔 refinement 桥传给
  `faceEulerChar`。结合 22.7，分别得到可定向、一个交叉帽、两个交叉帽情形的 22.6 数值公式；
  `surfaceHandleNumber K := Homology.bettiOne K.space / 2`，并证明在可定向柄剖分见证下等于 `h` 且 `b₁` 为偶数。
- 两个模块聚焦检查均 exit=0、零 warning，分别约 14.1 秒与 10.0 秒；`fresh.py` 报相对整合分支的六个改动模块
  olean 全部新鲜、零禁用项。`.lake/scratch/AuditHM8.lean` 逐项审计 36 个新增端点与关键复用声明，exit=0，
  全部公理闭包均包含于 `propext`、`Classical.choice`、`Quot.sound`。
- H-M8 的精确范围是 22.5–22.7：22.7 不依赖曲面分类；22.5–22.6 的柄/交叉帽表述以实际标准剖分及 refinement
  见证为前提，并未冒充已证明 22.4 的正规形存在性。22.8–22.10 的分类仍未闭合；H-M3 原先缺少的闭曲面顶维同调现已闭合。

### H-M9 / B.8 — done，26.8 的欧氏三空间曲面可定向性

- 数学提交：`6a02d3559`。新模块 `EuclideanSurfaceOrientation.lean`；主端点
  `IsCombinatorialManifold.isOrientable_of_finrank_eq_three` 适用于任意三维有限维实赋范空间，
  `isOrientable_euclidean_three` 是 `EuclideanSpace ℝ (Fin 3)` 的直接版本。
- 证明不使用 `H₃ ≅ ℤ`。先把有限曲面放进一个大仿射 3-单形的内部；S 车道 26.6 的
  `IsCombinatorialManifold.isTwoSided` 经子类型嵌入拉回，再由
  `exists_neighborhood_manifold_pair_of_twoSided` 把两侧闭包实现为有限带边组合 3-流形。选定一侧位于该 3-单形内，
  环境仿射定向给出其 `CoherentOrientation`，边界定向随后给整个组合边界的定向。
- 用 `exists_isSubdivision_restrict_isSubdivision` 取同时适配原曲面的边界共同细分；限制边界定向到该曲面子复形，
  再由任意线性细分的定向不变性搬回原三角剖分。这正是 §9.2 的“两侧选择 + 环境定向”路线，且结论为实际
  `IsOrientable 2 L`，没有引入新的表示谓词或结论型假设。
- 聚焦检查 exit=0、10.2 秒、零 warning；`fresh.py` 报相对整合基线七个改动模块 olean 全部新鲜、零禁用项。
  `.lake/scratch/AuditHM9.lean` 审计两个新端点和十四个关键复用声明，exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。H-M9/B.8 无未闭合项。

## 8. 2026-09-17 新批次

### H-M1 — done，H.4a 顶维基本类与 H.6 子复形 Mayer–Vietoris

- `SurfaceHomology.lean` 的闭连通组合曲面顶维计算已在 `3fdf6d58e` 交付：可定向时 `b₂=1`，不可定向时 `b₂=0`，并有
  `χ=2-b₁` / `χ=1-b₁`。本里程碑新增直接消费者
  `IsCombinatorialManifold.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two`。
- `MayerVietorisSubcomplex.lean` 的 `exists_mem_inter_of_map_eq_zero` 已在 `c9fff0308` 交付：有限复形的两个子复形覆盖、
  任意次数、任意环与系数模，严格给出 28.11；相容开邻域强形变收缩来自 `11826f868`。
- `PHASE3_APPROXIMATION_PLAN.md` 的 H.4、H.6 与 R3 陈旧状态已同步；22.8–22.10 是否仍为主链前置留给 H-M2 的证据判断。
- 当前整合树聚焦重编 `SurfaceHomology` exit=0（14.4 秒）、`MayerVietorisSubcomplex` exit=0（10.1 秒），均零 warning；
  `.lake/scratch/AuditHM1Current.lean` 审计九个 H.4a/H.6 端点，exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。

### H-M2 — done，§33 L11–L12 不需要 22.8–22.10

- 原书书页 236（PDF 246）中，Lemma 10 已给 `π₁(Bd X) ≅ π₁(Bd N)`，从而所需的一阶秩相等不依赖 22.9。
  Lemma 11 用 22.9 得到的只是一个不保持分块的同胚；Lemma 13 随后会从各 `A_v`、`A'_v` 重新构造满足
  `f(A_v)=A'_v` 的更强 PLH，因此主链可删 Lemma 11。
- Lemma 12 不走一般曲面正规形。设 `r_v` 为 `A'_v` 的多边形边界分支数，逐分支封 PL 盘得到闭可定向曲面 `Â'_v`。
  由封盘 Euler 加法与 H.4a，`χ(A'_v)=2-r_v-b₁(Â'_v)`；沿公共边界圆拼合后得到
  `b₁(Bd X)=b₁(Bd N)+∑v b₁(Â'_v)`。L10 给左边两 Betti 数相等，故每个非负项都为零；H.4b 的
  `isPLSphere_two_of_faceEulerChar_eq_two` 将每个 `Â'_v` 识别为 PL 2-球面，删去封盘内部即得 `A'_v` 是盘或带孔盘。
- 结论：22.8–22.10 对 §33 主链改为 skip，不移植完整曲面分类。仍需两个窄生产者：不经过
  `Homology/HurewiczLowDegrees.lean` 的一维 Hurewicz/基本群阿贝尔化桥，以及有限个边界分支的封盘复形与删盘识别；
  预计合计 3k–5k 行，归 G.5，而不是 H.4 分类。

### H-M3 — 原 wild 评估保留；§34 的 tame 路线已取代此前置

2026-09-18 更新：`TameNestedCells.lean` 的 `moise305_tame_of_moise304` 已证明，并保留 `Moise304` 为显式输入；`BicollarEmbedding.lean` 生产开集嵌入下 PL 3-胞腔边界的双领口。七模块 709 行，局部检查通过。以下 10k–18k 的一般 wild 估计不再阻塞 §34；它不是一般 `Moise305` 已证的声明。

- `JordanBrouwer.lean` 实际已有不要求光滑性的末端：
  `hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate` 只要嵌入像紧致与
  `HasAlexanderDualityH0Certificate`。光滑性只出现在现有证书生产者和若干包装层，不是分支计数消费者的本质限制。
- `DualityAssembly.lean` 仍显式要求 `SpecializedAlexanderDuality e` 与球面 cellular comparison；前者本身就是
  `reduced H₀(complement) ≅ H²(compactum)`。`SpecializedDuality.lean` 唯一无该假设的生产者
  `specializedAlexanderDuality_of_componentCount` 反而以“两补分支”为输入，且
  `specializedAlexanderDuality_iff_twoComponents` 明示它与目标等价，因此这条链不能用来证明目标。
- 任意拓扑 3-胞腔的边界可为 wild sphere，不能消费现有 smooth/open-bicollar 证书。当前树和 Mathlib 没有 Čech
  上同调、紧支撑上同调或一般 Alexander 对偶；`SphereCellularComparison.lean` 也只做到球面开覆盖的链级短正合列，
  尚未生产 `DualityAssembly` 要的 comparison。
- 最窄路线的成本分解：拓扑胞腔边界参数化与不变域桥 0.5k–1k；球面 cellular comparison 1k–2k；专门的
  `\widetilde H₀(ℝ³-e(S²)) ≅ H²(S²)` Alexander 对偶 8k–14k；从两侧分解推出 `Cᶜ` 连通 0.5k–1k。
  合计约 10k–18k 行且高风险；若建可复用 Čech/紧支撑理论则约 20k–35k。结论是在用户另行批准前不启动 H-M3。

### G.5 封盘 Euler 加法 — done

- `ConeEuler.lean` 的 `eulerChar_coneComplex`：任意有限复形上的锥（`coneComplex`，锥顶在 `IsConeBase` 意义下）
  的组合 Euler 数恒为 1。证明把 `coneFaces` 的面集拆成三块不交部分（原复形的面、`{p}`、`insert p` 的像），
  用 `Finset.sum_union`、`Finset.sum_image` 与 `card_insert_of_notMem` 得到
  `χ(L) + 1 + (-χ(L))`；不用同调，也不假设锥是流形。
- `eulerChar_eq_add_one_of_faces_union_coneComplex`：若 `M` 的面集是 `A` 与该锥的面集之并、且二者的交是 PL 1-球面，
  则 `χ(M) = χ(A) + 1`。它把 §33 Lemma 12 里"逐分支封 PL 盘"的 Euler 记账化为现成引理，
  复用既有的 `eulerChar_eq_add_of_faces_union_of_isPLSphere_one` 与 `eulerChar_of_isPLSphere_one`。
- 聚焦检查 `ConeEuler` exit=0（9.3 秒）、零 warning；`.lake/scratch/AuditHConeEuler.lean` 两项仅
  `propext`、`Classical.choice`、`Quot.sound`。
- 仍未闭合：封盘复形本身的几何构造（把锥顶放在何处使 `M.faces = A.faces ∪ coneFaces` 真的是几何复形，
  且交恰为该边界圆）、删盘识别，以及不经 `Homology/HurewiczLowDegrees.lean` 的一维 Hurewicz 桥。
  本条只交付 Euler 记账层。

### G.5 封盘复形：锥顶条件（`ConeBaseFlat.lean`）

封盘复形的几何困难是锥顶不能放在原环境里（锥可能穿过 `A`）。标准做法是把曲面平放进 `E × ℝ`
的超平面 `{q.2 = 0}`，锥顶取 `(x₀, 1)`。这一层现在有了：

- `convex_snd_eq_zero`、`snd_eq_zero_of_mem_space`：若复形每个面的顶点末坐标为零，则整个载体末坐标为零。
- `isConeBase_of_snd_eq_zero (L) (hL : ∀ q ∈ L.space, q.2 = 0) (x₀) : IsConeBase (x₀, 1) L`：
  三条要求都实际验证。`notMem_space` 与 `indep` 用末坐标：仿射组合的末坐标是零，不可能等于 1
  （`affineIndependent_insert_iff` 正是"锥顶不是底面的仿射组合"）。`radial` 也用末坐标：
  `y = p + t (x - p)` 取末坐标给 `0 = 1 - t`，故 `t = 1`、`y = x`。

于是 `coneComplex (isConeBase_of_snd_eq_zero L hL x₀)` 是实际可用的封盘，配合 §G.5 的
`eulerChar_coneComplex` 与 `eulerChar_eq_add_one_of_faces_union_coneComplex` 即得 Euler 记账。

仍未闭合：把平放后的 `A'` 与该锥的面集之并**构造成**一个几何单纯复形（跨对的
`inter_subset_convexHull` 要用末坐标论证：`A'` 的面落在 `{q.2 = 0}` 内，过锥顶的面与该超平面的交恰是底面），
以及删盘识别；还有不经 `Homology/HurewiczLowDegrees.lean` 的一维 Hurewicz 桥。

### G.5 封盘复形：构造与 Euler 记账（`CapComplex.lean`）— done

- `capComplex A L h hA hLA`：把平放的曲面复形 `A`（所有点末坐标为零）与它的边界圆子复形 `L` 上、
  锥顶 `(x₀, 1)` 的锥拼成一个**真正的几何单纯复形**，面集恰是 `A.faces ∪ (coneComplex h).faces`
  （`capComplex_faces` 是 `rfl`）。三条结构条件都实际验证：下闭性用 `IsRelLowerSet.union`；
  仿射无关性分别来自 `A` 与 `coneFaces_indep`；交条件的跨对情形是本条的几何内容
  （`capFaces_inter_cross`）：`A` 的面落在末坐标零的超平面里，而过锥顶的面与该超平面的交恰是底面，
  所以交点的 `join` 参数必为 1，从而落在 `hull σ` 内，再用 `A` 自己的交条件。
- `capComplex_faces_finite`：有限性。
- `intersectionComplex_capComplex_faces`：`A` 与该锥的交复形的面集**恰是** `L.faces`
  （`{p}` 与 `insert p σ` 都含锥顶，而锥顶不在 `A.space` 内）。
- `eulerChar_capComplex`：若 `L.space` 是 PL 1-球面，则 `χ(capComplex) = χ(A) + 1`。
  它把上一条与 `ConeEuler.lean` 的两条接起来，是 §33 Lemma 12 里"逐分支封 PL 盘"的现成记账。

于是 G.5 的"封盘复形"这一半 done（构造 + Euler）。仍未闭合：删盘识别（`Â` 是 PL 2-球面时
去掉封盘内部得到盘或带孔盘）与不经 `Homology/HurewiczLowDegrees.lean` 的一维 Hurewicz 桥。
`CapComplex` 检查 exit=0（9.4 秒）、零 warning；`.lake/scratch/AuditHCapComplex.lean` 六项无 `sorryAx`。

### G.5 删盘识别（`CapDeletion.lean`）— done（带一条密度前提）

- 载体层把 `capComplex` 的面集等式翻成集合等式：`capComplex_space`（载体 = `A.space ∪ 锥的载体`）、
  `space_inter_coneComplex_space`（`A.space ∩ 锥的载体 = L.space`，跨对论证与 `capFaces_inter_cross`
  同样用末坐标：过锥顶的面上的点若末坐标为零，则 join 参数必为 1，故落在底面）、
  `capComplex_space_sdiff_coneComplex_space`（`Ŝ \ 封盘 = A.space \ L.space`）。
- `isPLBall_coneComplex_space_of_isPLSphere_one`：`L.space` 是 PL 1-球面时封盘本身是 PL 2-球
  （直接是 `IsConeBase.isPLBall_of_isPLSphere`，此处只是把维数与锥顶固定下来）。
- 删盘识别 `isPLBall_space_of_isPLSphere_capComplex`：若封盘后的载体是 PL 2-球面，
  则 `A.space` 是 PL 2-球（盘）。证明消费 `SphericalDiskComplement.lean` 现成的
  `IsPLSphere.isPLBall_closure_sdiff`（2-球面挖掉一个 PL 2-球后的闭包仍是 PL 2-球），
  再用上面的差集等式把 `closure (Ŝ \ 封盘)` 换成 `closure (A.space \ L.space)`。
- 唯一的额外前提是 `A.space ⊆ closure (A.space \ L.space)`，即"曲面是它去掉边界圆后的闭包"。
  它不能从现有接口免费得到：`IsPLBall.closure_sdiff_eq_of_isPLBall` 要求外层已经是 PL 球，正是待证结论。
  对 `A` 是以 `L` 为边界的组合 2-流形的情形它显然成立，但该生产者尚未写；这里按车道规矩写成显式前提，
  没有 `sorry`，也没有削弱结论。

`CapDeletion` 检查 exit=0（10.3 秒）、零 warning；`.lake/scratch/AuditHCapDeletion.lean` 五项仅
`propext`、`Classical.choice`、`Quot.sound`。G.5 剩下的是不经 `Homology/HurewiczLowDegrees.lean`
的一维 Hurewicz 桥，以及上面那条密度前提的组合流形版生产者。

### G.5 删盘识别的密度前提：组合 2-流形生产者（`ManifoldInteriorDensity.lean`）— done

上一条 `CapDeletion.lean` 留下的唯一额外前提 `A.space ⊆ closure (A.space \ L.space)` 现在有了生产者，
而且不需要新的几何内容：树里已经有组合带边流形的纯性，缺的只是把它接到闭包上。

- 纯性不必重证。`ManifoldConnectivity.lean` 的
  `IsCombinatorialManifoldWithBoundary.exists_face_superset_card_eq` 已经给出：有限面、有限维下，
  `n` 维组合带边流形的每个面都含在一个基数 `n+1` 的面里。它对顶点链接是 PL 球或 PL 球面两种情形一起归纳，
  正是"每个面都是某个顶维单形的面"。
- `card_le_of_mem_boundaryComplex_faces`：`boundaryFaces n K` 的定义里就写着 `∃ t ∈ K.faces, s ⊆ t ∧ t.card ≤ n`，
  所以边界复形的面基数都 `≤ n`。纯组合，不用流形假设，也不用 `mem_boundaryComplex_iff_unique_coface`。
- `IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space`（一般 `n`，本条的数学内容）：
  设 `L.faces ⊆ K.faces` 且 `L` 的面基数都 `≤ n`，则 `K.space ⊆ closure (K.space \ L.space)`。
  取 `x ∈ K.space`，`exists_face_mem_openSimplex` 给出 `x ∈ openSimplex s`；纯性给 `t ⊇ s`、`t.card = n+1`。
  基数条件使 `t ∉ L.faces`（`n+1 ≤ n` 不成立），于是 `notMem_space_of_notMem_faces`（`RelativeDerived.lean`）
  给 `openSimplex t ∩ L.space = ∅`，即 `openSimplex t ⊆ K.space \ L.space`；再用
  `convexHull_subset_closure_openSimplex`（`LinkDimension.lean`）把 `x ∈ hull s ⊆ hull t` 送进
  `closure (openSimplex t) ⊆ closure (K.space \ L.space)`。
- `IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space`：
  `L = boundaryComplex n K` 时两条假设自动满足，`K.space ⊆ closure (K.space \ (boundaryComplex n K).space)`。
- 端点重述 `isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary`：
  假设 = `CapDeletion` 原端点的假设减去 `hdense`，加上 `IsCombinatorialManifoldWithBoundary 2 A`，**没有别的新前提**。
  关键的一点是 `L` 的基数条件不必另写：端点本来就带 `hL : IsPLSphere 1 L.space`，
  `card_le_of_isPLSphere`（`LinkDimension.lean`）直接给 `s.card ≤ 2`，正好是 `n = 2` 需要的。
  另有 `isPLBall_space_of_isPLSphere_capComplex_boundaryComplex`，把 `L` 固定成 `boundaryComplex 2 A`。
- 查过但用不上的路线：`ManifoldSubcomplexBoundary.lean` 的
  `boundaryComplex_space_subset_closure_sdiff_of_isCombinatorialManifold` 是
  `(boundaryComplex (n+1) A).space ⊆ closure (K.space \ A.space)`，说的是边界落在**外侧**补集的闭包里，
  方向与这里要的"内部在 `A` 里稠密"相反，不能改写成本条；也不需要它那条导出邻域机器。
- `ManifoldInteriorDensity` 检查 exit=0（9.9 秒）、零 warning；
  `.lake/scratch/AuditHManifoldInteriorDensity.lean` 五项仅 `propext`、`Classical.choice`、`Quot.sound`。

G.5 至此只剩不经 `Homology/HurewiczLowDegrees.lean` 的一维 Hurewicz／基本群阿贝尔化桥。

### G.5 一维 Hurewicz／阿贝尔化桥 — assessed，按 H-M3 先例给成本分解，未启动

G.5 的最后一块。先说三条把结论定死的核对结果，再给分解。

**(1) 禁止导入的那个文件与本题无关。** `Topology/Homology/HurewiczLowDegrees.lean` 全文 46 行，只有
`hurewicz_two_isomorphism` 与 `hurewicz_three_isomorphism` 两条（二维、三维），两条都是 `sorry`。
一维 Hurewicz 根本不在里面。所以"不经过该文件"这条限制的实际成本为零，不构成障碍。

**(2) 需要的是难的那一半，不能只用容易的一半。** L10 给的是 `i_* : π₁(Bd X) → π₁(N'−K')` 同构，
而 `Bd N × (0,1) ≅ Int N'−K'` 给 `j : Bd N ≃ N'−K'` 的同伦等价。`bettiNumber_eq_of_homotopyEquiv`
（`BettiNumber.lean:20`）免费给 `b₁(Bd N) = b₁(N'−K')`。剩下的一步方向必须核对清楚：
- Hurewicz 的**容易一半**（`π₁ → H₁` 满）配 `π₁(i)` 满，只能得到 `H₁(i)` 满，即 `b₁(Bd N) ≤ b₁(Bd X)`。
  代入 L12 的 `b₁(Bd X) = b₁(Bd N) + ∑v b₁(Â'_v)` 后是恒真式，**没有用**。
- 要迫使 `∑v b₁(Â'_v) = 0` 必须有 `b₁(Bd X) ≤ b₁(Bd N)`，也就是 `H₁(i)` **单**，
  它来自 `π₁(i)` 单只能经 `ker(π₁ → H₁) = 换位子群`，即 Hurewicz 的**难一半**。
  结论：不能用弱化版本绕开，必须做完整的一维 Hurewicz。

**(3) 【本条已于 2026-09-18 撤回，见本节末"更正"条；搜索范围漏掉了 `origin/codex/pc-sorry-free`，
该分支已有万有系数与一维 Hurewicz 层。下面的 HB1–HB6 分解随之作废，勿据以施工。】**
没有万有系数定理可用，必须直接在域系数上做。两棵树都查过：本库 `DifferentialGeometry/` 与 Mathlib
都没有 UCT、没有链复形的平坦基变换、没有 `H_n(X;ℤ) ⊗ ℚ ≅ H_n(X;ℚ)`。`ChangeOfRings.lean` 只做
`restrictScalars`（方向相反，且只对约化同调），`Coefficients.lean` 只在固定基环内换系数模。
所以不能"先证 ℤ 版再张量到 ℚ"。好消息是本库已有先例：`FieldPathCones.lean`（214 行）就是把整个
`PathChains` + `PathCones` 的 ℤ 论证在任意域 `k` 上重做一遍，并给出 `fieldSingularChainBasis`
（`Basis (integralSingularSimplex n X) k`）。一维 Hurewicz 照此在 `k` 上直接做即可，目标写成
`H₁(X;k) ≅ Abelianization (π₁ X x) ⊗_ℤ k`。

#### 现成材料（都已核对签名）

- 路径与 1-单形的**双向字典**，无任何附加假设：`PathChains.lean` 的 `integralPathSimplex`、
  `integralPathChain`、`integralPathChain_boundary`、`integralSimplexPath`、
  `integralPathSimplex_simplexPath`。域系数版 `fieldPathChain`、`fieldPathChain_simplexPath` 在
  `FieldPathCones.lean:85,89`。
- **自由基**：`fieldSingularChainBasis`（`FieldPathCones.lean:27`）、`fieldSimplexChain_boundary_one/_two`。
  `Basis.constr` 正是定义逆映射 `Λ` 的工具。
- **模板**：`fieldSingularConeOne`（`constr` 定义链级算子）、`fieldSingularConeTriangle_boundary`、
  `fieldSingularConeOne_equation`、`fieldSingularHomology_one_vanishing_iff` 这一串，形状与要写的
  `Λ`、`Λ∘∂=0`、下降到 `H₁` 完全一致，只是把"总能填三角形"换成"填得动当且仅当回路零伦"。
- **方块 ⟹ 道路同伦**：`Homotopy/SquareBoundary.lean:16` 的 `square_boundary_homotopic`，无 `SimplyConnectedSpace`
  假设，正是难一半要用的方向。
- **圆盘填充**：`LoopSpace/ContinuousFilling.lean:81` 的 `exists_continuous_disk_of_nullhomotopic`
  以"自由回路零伦"为输入，**本身不带单连通假设**。`SimplyConnectedSpace` 只在
  `LoopSpace/SimplyConnectedTarget.lean:21` 的 `circleLoop_nullhomotopic`（18 行）里出现一次，
  再经 `ConvexPlaneExtension.lean:19` 传到 `TriangleFilling.lean:22`。
- **∂Δ² 的三边拼装**：`TrianglePathBoundary.lean` 的 `triangleBoundaryPaths`、`triangleBoundaryMap`、
  `triangleBoundaryMap_edge`，`TriangleFaces.lean:14` 的 `simplexTriangleHomeomorph_face`，都无附加假设。
- **群论层**：Mathlib `GroupTheory/Abelianization/Defs.lean` 完整（`of`、`lift`、`lift_unique`、`hom_ext`、
  `map`、`MulEquiv.abelianizationCongr`）。本库 `Abelianization` 出现次数为 **0**，是全新依赖。
  π₁ 用 Mathlib `FundamentalGroup`，道路同伦商的群律（`trans_assoc`、`refl_trans`、`trans_symm` 等）
  在 `FundamentalGroupoid/Basic.lean` 全部现成。**坑**：`FundamentalGroup.mul_def : p * q = q.trans p` 是反序的。

#### 成本分解（六砖，域系数 `k`，取 `k = ℚ`）

| 砖 | 内容 | 行数 | 风险 |
|---|---|---|---|
| HB1 | 以同伦为前提的三角形填充：`(p.trans q).Homotopic r ⟹ ∃ σ : Δ²` 三个面为 `q, r, p`。把 `circleLoop_nullhomotopic`、`exists_convex_plane_boundary_extension`、`exists_integralPathTriangle` 的 `[SimplyConnectedSpace]` 换成显式零伦前提 | 0.4k–0.8k | 中 |
| HB2 | 逆向：`σ : Δ² ⟹ (face₂ ⬝ face₀).Homotopic face₁`。经 `I×I → Δ²` 的塌缩仿射映射接 `square_boundary_homotopic` | 0.4k–0.8k | 中 |
| HB3 | 串联的**典范**填充（无前提）：`Δ² → I`（顶点 ↦ `0, 1/2, 1`）复合 `p.trans q`，三个面按 `Path.trans` 的分段定义当场对上。可先试从 HB1 取 `Homotopic.refl` 免费得到 | 0.2k–0.4k | 低 |
| HB4 | Hurewicz 同态 `h : Abelianization (π₁ X x) →+ H₁(X;k)`：HB1 给良定义，HB3 给可加性（注意 `mul_def` 反序），退化 2-单形给 `h 1 = 0`，`Abelianization.lift` 收尾 | 0.3k–0.5k | 低 |
| HB5 | 逆映射 `Λ : C₁(X;k) → Abelianization(π₁) ⊗_ℤ k`，用 `fieldSingularChainBasis.constr`、`λ(σ) = [α_{σ0} ⬝ σ ⬝ α_{σ1}⁻¹]`（`α` 取 `PathConnectedSpace.somePath`）；`Λ∘∂₂ = 0`（HB2）、下降到 `H₁`、两侧互逆（cycle 的修正项因 `∂c = 0` 相消） | 0.6k–1.1k | 中 |
| HB6 | 秩层与消费者：`H₁(X;k) ≅ Abelianization(π₁ X x) ⊗_ℤ k`；`bettiOne X = finrank ℚ (Abelianization (FundamentalGroup X x) ⊗_ℤ ℚ)`；端点 `bettiOne_eq_of_mulEquiv_fundamentalGroup`，用 `MulEquiv.abelianizationCongr`。乘法群 `Abelianization` 与 `Additive` 之间的搬运是小摩擦 | 0.3k–0.6k | 低 |

合计 **2.2k–4.2k 行**。真正新的几何只有 HB1 与 HB2 两个填充方向（0.8k–1.6k），其余都是对着
`FieldPathCones.lean` 现成模板的记账。与 PHASE3 行 G.5 原估 3k–5k 相容：那个数字含封盘复形，
而封盘那半已由 `ConeEuler`/`ConeBaseFlat`/`CapComplex`/`CapDeletion`/`ManifoldInteriorDensity` 闭合。

#### 查过但不可用的捷径

- `SphereHurewicz.lean:60` 的 `sphereHurewicz n x c` 在 `n = 0` 处**确实**给出映射
  `HomotopyGroup (Fin 1) X x → integralSingularHomology 1 X`，且有 `_one`、`_transport`、`_natural`。
  但没有任何 `map_mul`，也没有任何一维的双射陈述；而且它落在 ℤ 系数
  （`ModuleCat.of ℤ (ULift ℤ)`），与 `bettiNumber` 的 `ModuleCat.of k k` 不是同一个系数对象。
  它不能省掉上面任何一砖。
- `homotopyGroupToFreeSphere_injective` 要 `[SimplyConnectedSpace X]`，在一维是平凡的，无用。
- 若哪条车道能把 L10 升级成 `Bd X` 与 `N'−K'` **同伦等价**（而不只是 π₁ 同构），
  `bettiNumber_eq_of_homotopyEquiv` 零成本闭合 L12 的 Betti 等式，上面 2.2k–4.2k 全部省掉。
  但书页 236 的 L10 只给 π₁ 同构；把 `Bd N × (0,1)` 里一张诱导 π₁ 同构的闭曲面升级成水平面
  是不可压缩曲面的同痕定理，比 Hurewicz 更贵。记录备查，不建议走。

结论：按 H-M3 先例，在用户另行批准前不启动。启动时建议顺序 HB3 → HB1 → HB4 → HB2 → HB5 → HB6，
先把无前提的那块（HB3）打通以验证面计算的写法，再动两个填充方向。

### G.5 一维 Hurewicz 桥 — 更正（2026-09-18）：`origin/codex/pc-sorry-free` 已有该层，改为分支收敛问题

上一条的核对有一处范围错误，现更正。**撤回**"本库与 Mathlib 都没有万有系数材料、一维 Hurewicz 须从零实现"
这一判断：我只搜了本工作树与 Mathlib，没有搜同一仓库的兄弟分支 `origin/codex/pc-sorry-free`。
该分支上有以下七个文件，我已在本工作树用 `git show`／`git grep`（只读，未合并）逐一核对：

| 文件（均在 `DifferentialGeometry/Topology/Homology/`） | 行数 |
|---|---|
| `UniversalCoefficientsOne.lean` | 293 |
| `UniversalCoefficientsOneLinearEquiv.lean` | 365 |
| `HurewiczOneAbelianization.lean` | 746 |
| `HurewiczOneKernel.lean` | 453 |
| `HurewiczOnePathLoopBridge.lean` | 336 |
| `HurewiczOneVertexPairing.lean` | 241 |
| `RationalHurewiczOne.lean` | 195 |
| 合计 | 2629 |

七个文件在本车道各分支上全部不存在；`git grep -c sorry` 在该分支的 `Topology/Homology` 下无输出，该层无 `sorry`。

#### 已核对的实际内容

- `HurewiczOneAbelianization.lean:695,700` 把缺口收成两个 `Prop`：`HurewiczOneMultiplicative`（`sphereHurewicz 0` 可加）
  与 `HurewiczOneKernel`（核含于换位子群）。`:712` 的 `abelianization_equiv_of_surjective_ker_eq_commutator`
  与 `:727` 的 `abelianizationHomotopyGroupOne_equiv_of_hurewiczOne` 由"可加 + 满 + 核 ⊆ 换位子"给出
  `Abelianization (π₁) ≃* Multiplicative (H₁(X;ℤ))`。
- `RationalHurewiczOne.lean:128` 的 `tensorRational_abelianizationFundamentalGroup_equiv_of_hurewiczOne`
  给出正是 G.5 消费端要的形状 `ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup X x)) ≃ₗ[ℚ] ℚ ⊗[ℤ] H₁(X;ℤ)`，
  条件恰是上述三条。
- **容易一半在那边已证**：`RationalHurewiczOne.lean:114` 的
  `hurewiczOneLoopGeneration_of_hurewiczOneVertexPairing`，配 `integralPathLoopClassMap_mem_span`。
- **难一半在那边同样未闭合**，但已收得更窄：`HurewiczOneVertexPairing.lean:190`
  `hurewiczOneKernel_of_spherePairing` 把 `HurewiczOneKernel` 归到 `HurewiczOneSpherePairing`；
  后者的生产者只有 `_of_subsingleton`（π₁ 平凡，对我们平凡无用）与 `:214`
  `hurewiczOneSpherePairing_of_loopBridge_of_loopClassPairing`，它把难一半再拆成两条具名子事实
  （球面到回路的桥、回路类配对恒等式）。所以上一条"难一半不可避免"的结论**成立**，
  但"须从零实现"的结论**不成立**。
- `HurewiczOnePathLoopBridge.lean:196` 的
  `hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator`
  把可加性整条归约到一个**与空间无关**的全局事实：圆周基本类是球面同调生成元。

#### 两条上一条没提、但施工前必须知道的限定

1. **ℤ → ℚ 的换系数在那边也还是条件，不是定理。** `RationalHurewiczOne.lean:22`
   `rationalSingularHomologyOneCoefficientChange` 的生产者只有全不连通空间（`:37`）与 `PUnit`（`:51`）；
   `:151,163,174,188` 四个下游端点全部把它当显式假设 `hC` 携带。所以 HB6 **没有**被完全消掉。
2. **右端是 `ℚ ⊗ H₁(X;ℤ)`，不是本库 `bettiNumber ℚ _ 1` 的那个对象。** 接到 `bettiOne` 还要上面第 1 条
   加一步 `finrank` 胶水。两边都在 universe 0（`TopCat.{0}` 对我们的 `bettiOne : (X : Type) → _`），无宇宙冲突。

#### HB1–HB6 的修订

| 砖 | 修订后状态 |
|---|---|
| HB1、HB2、HB3（两个方向的三角形填充、典范串联单形） | **作废，不是该走的路**。那边根本不走三角形填充，而是用 `sphereHurewicz 0` 加路径-回路链映射。不要按原分解施工 |
| HB4（Hurewicz 同态与 `Abelianization.lift`） | **已交付**：`hurewiczSphereMonoidHom` + `abelianization_equiv_of_surjective_ker_eq_commutator`。可加性另归约到一条全局圆周事实 |
| HB5（逆映射、容易一半） | **大部分已交付**：回路生成已证；`sphereHurewicz 0` 的满性仍是显式假设 |
| HB6（秩层与消费者） | **部分交付**：张量与 `LinearEquiv.baseChange` 胶水在，但 `rationalSingularHomologyOneCoefficientChange` 的一般生产者仍缺，接到 `bettiOne` 的最后一步仍要写 |

#### 修订后的剩余义务

对 G.5 实际需要的空间（`Bd X`、`Bd N`、各 `Â'_v`，都是道路连通的闭三角剖分曲面）生产：
`HurewiczOneMultiplicative`、`HurewiczOneKernel`、`Function.Surjective (sphereHurewicz 0 x c)`，
外加 `rationalSingularHomologyOneCoefficientChange` 与接到 `bettiOne` 的 `finrank` 收尾。
其中 `HurewiczOneKernel` 是难一半，可经 `hurewiczOneSpherePairing_of_loopBridge_of_loopClassPairing`
的两条子事实进攻；`HurewiczOneMultiplicative` 只差那条全局圆周生成元事实。

#### 交付路线：分支收敛，不是在本车道重写

那七个文件的**传递导入闭包**有 163 个文件、约 45600 行不在本车道各分支上。所以这不是 cherry-pick 能解决的，
是 `codex/pc-sorry-free` 与 Moise 各分支的**收敛**问题，需由协调者安排。在本车道按原 HB1–HB6 重新实现
一维 Hurewicz 属于**重复劳动**，明确不做。本次只做只读核对，未合并该分支，未改动任何 Lean 文件。

附带核对：该分支的 `DifferentialGeometry/Topology/PiecewiseLinear` 文件数为 **0**，其 Alexander 对偶／
紧支撑材料与本车道同源（我们 16 个文件、它 17 个，多出的是射影空间不可嵌入），故上文 H-M3 的评估不受影响。

## 9. 2026-09-18 H 接手 F §19.115 的生产者缺口

### H-A1 — done，锥延拓的球对／相对版本（`ConePairExtension.lean`）

F §19.115 把触边分离的缺口定位到"两张球对平凡化在重叠上相差一个可锥化 PL 同胚"，即 PL 球对的
相对 Alexander 技巧。本次交付该定理的核心，新模块 `ConePairExtension.lean`（无车道占用）。

先说测绘结论（全树 592 个 PL 模块，`sorry` 计数为 0）：

- **锥的集合层算子不存在**。全树没有 `cone : E → Set E → Set E`；锥只经
  `Geometry.SimplicialComplex ℝ E` 与 `insert p σ` 表达，`Set E` 图像只能事后由
  `ConeComplex.lean:199 mem_coneComplex_space_iff` 还原。
- **球对版本不存在**。没有 `IsPLBallPair`／`BallPair`／unknotted 任何形式；
  `SimplexBallPair.lean`、`StarPair.lean`、`CirclePair.lean`、`BallCyclePair.lean` 都是"两个球相交"
  而不是"子多面体嵌在球里"。最接近的 `ConeIntersection.lean:23 coneComplex_space_inter` 只是集合等式。
- **相对版本未导出**。`ConeAmbientExtension.lean:8` 确实带 `B ⊆ L` 与 `EqOn f id B.space`，
  并在证明内部第 40–49 行以 `have hconeFixed` 证出了"`h` 在子锥上恒等"，但**结论里没有这一条**，
  用完即丢。结论只有全悬垂之外的 `EqOn h id (…)ᶜ`。
- **塌陷（collapsing）整个不存在**：`collaps` 在全树 0 命中；`freeFace`／`FreeFace` 无标识符；
  `ConeFreeFace.lean` 只有两条 frontier 几何，与自由面无关，文件名是唯一的"自由面"内容。
  正则邻域唯一性、环境同痕（`ambientIsotop` 0 命中）同样不存在。
  折叠归纳只在二维／三维以 `htrace`/`hinter` 内联写死（`FreeTriangleNeighborhood.lean:946`），未抽象。
- 已有的 Alexander 技巧本体是 `ConeExtension.lean:70 exists_isPLHomeomorphOn_coneComplex`，
  其结论第四条**显式给出锥公式** `g (p + s • (z - p)) = q + s • (f z - q)`。这一条是本次能闭合的原因：
  球对版本不需要重做锥延拓，只需把锥公式转成像等式。

交付的定理：

- `coneSet p X := {x | x = p ∨ ∃ z ∈ X, ∃ s, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p)}`，
  集合层的锥算子（全树首次）。桥 `coneComplex_space_eq_coneSet : (coneComplex h).space = coneSet p L.space`
  由 `mem_coneComplex_space_iff` 直接 `Set.ext`，故与既有复形层完全兼容，不引入竞争层级。
  附 `mem_coneSet_iff`、`apex_mem_coneSet`、`subset_coneSet`、`coneSet_mono`、
  `coneSet_subset_coneComplex_space`。
- `image_coneSet_of_radial`：**核心**。设 `g p = q` 且 `g` 在 `S` 上满足锥公式，则对任意 `X ⊆ S` 有
  `g '' coneSet p X = coneSet q (f '' X)`。纯像计算，不要求 `g` 是同胚、不要求有限性、
  不要求 `DecidableEq`，故对 `ConeExtension` 与 `ConeAmbientExtension`／`ConeIsotopy` 的锥公式同样可用。
- `eqOn_id_coneSet_of_radial`：相对版本。`q = p`、`EqOn f id X` ⟹ `EqOn g id (coneSet p X)`。
  这正是 `ConeAmbientExtension.lean:40–49` 内部丢弃的那一条，现在是公开引理。
- `exists_isPLHomeomorphOn_coneComplex_pair`：把 `exists_isPLHomeomorphOn_coneComplex` 的四条结论
  原样保留，再加第五条 `∀ X ⊆ L.space, g '' coneSet p X = coneSet q (f '' X)`。
  **对 `X` 全称量化**，所以两张片与分支弧一次给全，不需要为每张片各证一次。
- `exists_isPLHomeomorphOn_coneComplex_sheets`：F 直接消费的形状。输入 `A B ⊆ L.space`、
  `f '' A = A'`、`f '' B = B'`，输出锥延拓 `g` 同时满足
  `g '' coneSet p A = coneSet q A'`、`g '' coneSet p B = coneSet q B'` 与
  `g '' coneSet p (A ∩ B) = coneSet q (A' ∩ B')`。第三条是**球三元组**条款：分支弧 `S = A ∩ B`
  被送到分支弧，用 `hf.bijOn.injOn.image_inter` 得到 `f '' (A ∩ B) = A' ∩ B'`（需要 `f` 在 `L.space` 上单射，
  由 `IsPLHomeomorphOn` 自带）。这是 F §19.115 里"沿公共横截盘对相等"那一步的确切内容。
- `exists_isPLHomeomorphOn_coneComplex_fixing`：相对 Alexander 技巧的成品。`q = p`、`EqOn f id Z` ⟹
  `EqOn g id (coneSet p Z)`，并同时保留球对条款。沿链归纳时"在已处理的一张面上固定"用这条。

聚焦检查 `ConePairExtension` exit=0（8.5 秒）、零 warning；`.lake/scratch/AuditHConePairExtension.lean`
七项仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。

坑：`EqOn g id` 的目标是 `g x = id x`，`rw [..., hfix hz, id_eq]` 只改写了 `id z` 而把外层
`id (p + s • (z - p))` 留下，末尾要显式 `rfl`。

### H-A2 — done，顶点处球对结构由链对唯一决定（同模块）

F §19.115 给的两个候选形状里，(a) 相对锥延拓由 H-A1 闭合；(b)"同一弧的两个 PL 球对结构相差一个
固定该弧的 PL 同胚"的**逐点形式**现在也闭合。桥是 `ConeComplex.lean:262`
`closedStar_eq_coneComplex_space`：顶点的闭星本来就是链上的锥。

- `closedStar_eq_coneSet : closedStar K p = coneSet p (geometricLink K {p}).space`。
  把闭星直接写成集合层的锥，于是 H-A1 的全部球对条款可以逐字用到闭星上。
- `geometricLink_singleton_faces_subset` / `geometricLink_singleton_space_subset`：
  `J.faces ⊆ K.faces` ⟹ 链与链空间的包含。由 `mem_geometricLink_singleton` 三条分量直接给出，
  不需要 `Gluing.lean` 的 `space_mono_of_faces_subset`，故本模块不新增导入。
- `exists_isPLHomeomorphOn_closedStar_pair`：设 `{p} ∈ K.faces`、`{p'} ∈ K'.faces`，
  `f` 是两条链空间之间的 PL 同胚，则存在 `g : closedStar K p → closedStar K' p'` 为 PL 同胚，
  在链上等于 `f`、`g p = p'`，且对**任意** `X ⊆ (geometricLink K {p}).space` 有
  `g '' coneSet p X = coneSet p' (f '' X)`。
  `Finite (geometricLink K s).faces` 是 `GeometricLink.lean:29` 的现成 instance，不用手工构造。
- `exists_isPLHomeomorphOn_closedStar_of_geometricLink_subcomplex`：**(b) 的成品**。
  再设子复形 `J ⊆ K`、`J' ⊆ K'`，`{p} ∈ J.faces`、`{p'} ∈ J'.faces`，且
  `f '' (geometricLink J {p}).space = (geometricLink J' {p'}).space`，
  则同一个 `g` 满足 `g '' closedStar J p = closedStar J' p'`。
  读作：**顶点处的球对 (star, sub-star) 完全由链对 (link, sub-link) 决定**。
  沿分支合并相邻图卡时，"两张平凡化在重叠上相差一个可锥化 PL 同胚"就是这一条；
  片是子复形时 `A ∩ closedStar K p` 的锥形状不是额外假设，而是 `closedStar_eq_coneSet` 的推论。

聚焦检查 `ConePairExtension` exit=0（8.3 秒）、零 warning；
`.lake/scratch/AuditHConePairExtension.lean` 十二项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 仍未闭合的确切义务（交回 F）

H-A1/H-A2 交付的是**锥/星层**的球对与相对 Alexander 技巧。F §19.115 的整条图卡定理**尚未闭合**，
剩下的确切缺口是把逐点的星对结论沿弧串起来，需要下面三件，都不在本树内：

1. **弧的正则邻域是球，且球对标准**。本树 `regularNeighborhood`（`RegularNeighborhood.lean:72`）
   只有 4 条平凡引理，没有任何"是球"的定理；`derivedNeighborhood` 的球定理只到单纯形
   （`SimplexDerivedNeighborhood.lean:141`，且只对边界复形的面）与边界二维盘
   （`DiskDerivedNeighborhood.lean:74`）。弧（1-复形）的版本没有。
2. **塌陷理论**。全树 `collaps` 零命中，无 `freeFace` 标识符；折叠归纳只在
   `FreeTriangleNeighborhood.lean:946` 以 `htrace`/`hinter` 内联写死于二／三维，未抽象。
   "可塌陷集的正则邻域是球"因此无法陈述。
3. **正则邻域唯一性本身**（两个正则邻域相差一个 PL 同胚）与**环境同痕**。
   `ambientIsotop`/`isotop` 在全树文件内容中零命中，每条结果都只产生**单个**同胚，
   没有 `I → (E ≃ₜ E)` 的族，也没有同痕延拓定理。

成本分解（按本树既有层级估计，不含风险缓冲）：抽象自由面与初等塌陷谓词、把
`FreeTriangleNeighborhood` 的归纳提取成一般维数形式 2k–4k 行；一维复形（弧）的正则邻域是球
1k–2k 行；球对版本的正则邻域唯一性（沿弧归纳，每步用 H-A2 的星对唯一性，外加重叠上的相容性）
3k–6k 行；再接到 §19.115 的图卡陈述（`OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`、两向逐片仿射、
`e.source` 不碰第三张片）1k–2k 行。合计约 7k–14k 行。
H-A1/H-A2 把其中"锥化/球对"那一块消掉了，它原本是唯一没有现成套路的一块；
剩下三件都是标准 PL 拓扑，路线明确但工作量实在。

### H-A3 — done，链对相符即可搬运 crossing（新模块 `ConePairCrossing.lean`）

测绘时发现树里**已经有一个正好吃 H-A2 输出的消费者**，此前没有生产者：
`CrossingNeighborhood.lean:71 HasPLCrossingAt.of_closedStar_pair`，它要的三条
（`IsPLHomeomorphOn g (closedStar K p) (closedStar K' q)`、`g p = q`、
`g '' closedStar M p = closedStar M' q`）逐字就是 H-A2 的结论。

- `HasPLCrossingAt.of_geometricLink_pair`：设 `M ⊆ K`、`M' ⊆ K'` 为子复形，
  `p`、`q` 分别是它们的顶点，`K.space ∈ 𝓝 p`；设链同胚 `f` 满足
  `f '' (geometricLink M {p}).space = (geometricLink M' {q}).space`（片的链对相符），
  第二张片 `B`、`B'` 在各自星里是锥
  （`closedStar K p ∩ B = coneSet p ((geometricLink K {p}).space ∩ B)`，`q` 侧同）
  且 `f` 把它们的链迹互相搬过去；则由 `HasPLCrossingAt M'.space B' q` 得
  `HasPLCrossingAt M.space B p`。
  读作：**某点的横截 crossing 性质完全由链上的数据决定**——链对相符加第二张片的链迹相符，
  就能把标准模型处的 crossing 搬到任意顶点。这是 §19.115 里"把两张局部平凡化对接"所缺的比较步骤。
- 证明只有四行：`exists_isPLHomeomorphOn_closedStar_pair` 给 `g` 与全称锥条款，
  两条 `rw` 分别用 `closedStar_eq_coneSet`（片）与假设 `hB`/`hB'`（第二张片）把两个像条款算掉。
  这里必须用 `exists_isPLHomeomorphOn_closedStar_pair` 而不是 H-A2 的子复形版本：
  后者丢掉了 `∀ X` 条款，而第二张片 `B` 是裸集合不是子复形，只能走全称版本。
- 第二张片"在星里是锥"写成显式假设而非内部推导，是因为 `B` 是 `Set E`；
  若 `B` 也是过 `p` 的子复形，该假设由 `closedStar_eq_coneSet` 给出，不是额外负担。
- 新模块单独放，不并进 `ConePairExtension.lean`：后者只导入 `ConeExtension`，很轻；
  `CrossingNeighborhood` 拉进 `SingularGeneralPosition`／`GeneralPosition` 的大锥体，
  不应让只需要锥引理的消费者付这个代价。

聚焦检查 `ConePairCrossing` exit=0（9.5 秒）、零 warning；
`.lake/scratch/AuditHConePairCrossing.lean` 一项仅 `propext`、`Classical.choice`、`Quot.sound`。

关于上面"仍未闭合的确切义务"：H-A3 不改变那三件（弧的正则邻域是球、塌陷理论、正则邻域唯一性）
的缺失状态，但把**逐点比较**这一步从"缺定理"变成"缺输入"：现在沿弧相邻两点之间要的不再是新定理，
而是两点链对之间的一个 PL 同胚 `f`。产生这个 `f` 仍需沿弧的正则邻域结构，即上述第 1、3 件。

## 10. 2026-09-18 H-A4：弧的正则邻域是三维球（`ArcDerivedNeighborhood.lean`，done）

上一节"仍未闭合的三件"里的**第 1 件已闭合**，成本比 §9 的估计低一个数量级：
估计 1k–2k 行，实际 **210 行**。原估计错在假设要自建折叠/塌陷归纳；实际上树里已经有
现成的链式黏合定理与逐格引理，弧的情形只是把它们接起来。**更正后的成本：0.2k 行。**

### 为什么这么便宜——测绘更正

§9 说"`derivedNeighborhood` 的球定理只到单纯形与边界二维盘"，这条**仍然正确**，但漏了两件关键事实：

1. `BallChain.lean:10 isPLBall_iUnion_of_chain` **已经把沿链归纳做完了**。它吃
   `C : Fin (n+1) → Set E`、每个 `IsPLBall 3`、相邻交是 `IsPLBall 2`、非相邻不交，
   直接吐 `IsPLBall 3 (⋃ i, C i)`。不需要任何新的归纳。
2. `DerivedNeighborhoodCells.lean:227 isPLBall_derivedNeighborhoodCell_inter` 已经给出
   **相邻交是二维球**：`IsCombinatorialManifoldWithBoundary (n+2) K` ⟹ 对 `s ≠ t` 且
   `s ⊆ t ∨ t ⊆ s` 有 `IsPLBall (n+1) (cell s ∩ cell t)`。取 `n := 1` 正是 `IsPLBall 2`。
   配 `:147 isPLBall_derivedNeighborhoodCell`（`n := 2`，每格是三维球）与
   `:236 disjoint_derivedNeighborhoodCell_space`（不可比较的面 ⟹ 格不交），链的四个前提全部现成。

即：`isPLBall_triangle_cells`（`SimplexDerivedNeighborhood.lean:41`）里那套"逐格黏"的套路
本来就是一般的，只是之前只被用在单个单纯形的面上。

另有一条相关但**不能直接用**的东西：`SurfaceTreeNeighborhood.lean:80`
`isPLBall_embeddedGraphDerivedNeighborhood_of_isTree` 是**树**的版本，但它是
`IsCombinatorialManifold 2`（闭曲面、二维）出 `IsPLBall 2`，走的是叶子归纳。
三维弧的情形走链式归纳更短，不必推广它。

### 交付的定理

- `IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain`：
  **抽象的面链黏合**。设 `F : Fin (m+1) → Finset E` 的每项是 `K` 的面，相邻两项互不相等且可比较
  （一个含于另一个），指标距离 ≥ 2 的两项互不可比较，则
  `IsPLBall 3 (⋃ j, (derivedNeighborhoodCell K (F j)).space)`。
  证明是 `isPLBall_iUnion_of_chain` 的一次直接喂参，无归纳。**这是本节真正可复用的那条**：
  任何"沿一串面串起来的对偶格"都能用，不限于弧。
- `arcChainFace v j := {v (j / 2), v ((j + 1) / 2)}`：交替的顶点／边面。
  **无 if-then-else 的统一公式**：`j = 2k` 时两个下标相等，Finset 自动塌成单点 `{v k}`；
  `j = 2k+1` 时得边 `{v k, v (k+1)}`。这一条是全节的关键技巧——把奇偶讨论从项层面
  推到了 `omega` 能处理的算术层面。配 `arcChainFace_two_mul`、`arcChainFace_two_mul_add_one`。
- `arcChainFace_subset_iff`：设 `v` 在 `[0,n]` 上单射，则对 `i, j ≤ 2n`
  `arcChainFace v i ⊆ arcChainFace v j` **当且仅当**
  `(i/2 = j/2 ∨ i/2 = (j+1)/2) ∧ ((i+1)/2 = j/2 ∨ (i+1)/2 = (j+1)/2)`。
  有了它，链的三个组合前提（互不相等、可比较、远处不可比较）**全部退化成 `omega`**。
- `IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace`：弧的定理，格并形式。
  输入 `hvert : ∀ i ≤ n, {v i} ∈ K.faces`、`hedge : ∀ i < n, {v i, v (i+1)} ∈ K.faces`、
  `hinj`（`v` 在 `[0,n]` 上单射），输出
  `IsPLBall 3 (⋃ j : Fin (2n+1), (derivedNeighborhoodCell K (arcChainFace v j.val)).space)`。
- `arcComplexIn K v n`：弧作为 `K` 的**子复形**，按 `regularNeighborhoodIn` 的模式定义
  （`faces := {s ∈ K.faces | ∃ j ≤ 2n, s = arcChainFace v j}`），因此 `indep` 与
  `inter_subset_convexHull` 由 `K` 继承，不需要几何论证。`isRelLowerSet_faces` 由
  `exists_eq_arcChainFace_of_subset` 给出，后者靠 `eq_of_subset_pair`
  （对子的非空子集只有三种：两个单点与整对；Finset 版 Mathlib 没有，只有 `Set.subset_pair_iff_eq`）。
  附 `Finite (arcComplexIn K v n).faces` instance 与 `arcComplexIn_faces_subset`。
- `iUnion_derivedNeighborhoodCell_arcChainFace_eq`：格并 = `(derivedNeighborhood K (arcComplexIn K v n)).space`，
  由 `iUnion_derivedNeighborhoodCell_space` 加两向包含。
- `IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn`：**成品端点**。
  `IsPLBall 3 (derivedNeighborhood K (arcComplexIn K v n)).space`。
  这是与 `DiskDerivedNeighborhood.lean:74`（边界二维盘）同形状的陈述，
  因而 `derivedNeighborhood_space_subset`、`closedStar_subset_derivedNeighborhood`、
  `DerivedNeighborhoodHomology` 的既有引理可以直接接上。

聚焦检查 `ArcDerivedNeighborhood` exit=0（10.5 秒）、零 warning；
`.lake/scratch/AuditHArcDerivedNeighborhood.lean` 十二项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 坑

- `Fin` 的 `castSucc`/`succ` 取 `val` 后，`simp only [Fin.coe_castSucc, Fin.val_succ]`
  **不会把所有位置都改写**（`Fin.castSucc` 本身以 `↑` 显示，漏掉的位置在 `omega` 眼里成了
  另一个原子，于是 `omega` 报出一个看似合理的反例而失败）。改用先 `have hc : j.castSucc.val = j.val`、
  `have hs : j.succ.val = j.val + 1`，再把它们放进 `rw` 链尾部，一次性统一改写。
  另：`Fin.coe_castSucc` 已废弃，用 `Fin.val_castSucc`。
- `eq_of_subset_pair` 作用在 `t ⊆ arcChainFace v j` 上时，`arcChainFace` 是普通 `def`，
  合一**不会**自动把它展开成 `{?a, ?b}`。先写 `have ht' : t ⊆ ({v (j/2), v ((j+1)/2)} : Finset E) := ht`
  （类型标注走 delta 归约）再用。
- 纯 `Finset`/算术的引理放在只有 `variable {E : Type*}` 的 section 里，
  否则 `unusedSectionVars` linter 报 warning；跨不掉的地方用 `omit [FiniteDimensional ℝ E] in`。

### 三件义务的当前状态

1. **弧的正则邻域是球** —— **已闭合**（本节）。仍未做的是"球**对**标准"那半句：
   即 `(N(arc), arc)` 作为球对与标准模型球对 PL 同胚。本节只给了 `N(arc)` 是球。
2. **塌陷理论** —— 仍不存在，但**本条已证明对第 1 件不是必需的**：链式归纳绕开了它。
   除非第 3 件确实需要，否则不建议再投入（§9 估的 2k–4k 行可以先不花）。
3. **正则邻域唯一性 / 环境同痕** —— 仍不存在，且仍是 F §19.115 的真正瓶颈。
   现在沿弧相邻两点之间要的输入（H-A3 的链对同胚 `f`）依然缺少生产者。

### H-A4 附加：直接可用的消费形状

- `IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn`：
  `∃ C, IsPLBall 3 C ∧ C ⊆ K.space ∧ (arcComplexIn K v n).space ⊆ C`。
  与 `DiskDerivedNeighborhood.lean:92 exists_isPLBall_containing_boundary_disk`（边界二维盘的版本）
  **完全同形状**，所以已经消费后者的地方可以照抄接法。
  用 `DerivedNeighborhoodAttachments.lean:56 space_subset_iUnion_derivedNeighborhoodCell_space`
  给包含关系；该模块的两个 import 本来就在闭包里，**加它不引入新的依赖锥**。

聚焦检查 exit=0（10.3 秒）、零 warning；审计十三项仅三条标准公理。

## 11. 2026-09-18 第 2、3 件的复核结论（在合并后的当前树上重新测绘，非沿用 §9）

### 第 2 件（抽象塌陷）：仍不存在，且**已证明第 1 件不需要它**

`freeFace`／`FreeFace`／`collaps` 在全树**文件内容**中仍然零命中——
只有三个**文件名**含 "FreeFace"（`ConeFreeFace.lean`、`PlanarFreeFace.lean`、`FreeFaceTransport.lean`），
内容里出现该词的行**全部是 import 行**。`FreeFaceTransport.lean` 只有一条定理
`exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar`，是二维平面情形"去掉一个自由三角形"的
具体步骤，不是抽象的初等塌陷。（§9 写的是"无标识符"，与此一致；此处补记文件名的存在，免得后来者误判。）

**结论：不要按 §9 估的 2k–4k 行去投抽象塌陷层。** 弧的球性质由链式归纳绕开了它；
是否需要塌陷，取决于第 3 件走哪条路线（见下）。

### 第 3 件（正则邻域唯一性 / 球对标准）：**仍然阻塞**，障碍已定位到一条具名引理

复核了三点，都在当前合并后的树上重新 grep 过：

1. **没有球对谓词**。`IsPLBallPair`／`BallPair`／`ballPair`／`unknot` 全树零命中。
   `SimplexBallPair.lean` 只有两条，其中 `exists_isPLBall_pair_with_disk_inter` 是
   "两个标准球交于一个盘"，仍然不是"子多面体嵌在球里"。
2. **没有同痕**。`ConeIsotopy.lean` 只有一条 `exists_isPLHomeomorphOn_coneComplex_of_continuous`，
   产出**单个**同胚，全文件没有时间参数（`Icc (0:ℝ) 1`／`unitInterval`／`I →` 零命中）。
   全树再无别的同痕材料。
3. **黏合定理对子多面体没有控制**。`PLPiece.lean:83 IsPLHomeomorphOn.piecewise` 要求
   `EqOn f g (P ∩ Q)`——两张同胚必须在重叠上**逐点相等**。而
   `BallGluing.lean:12 isPLBall_union_of_boundary_disk` 是先用
   `exists_isPLBall_pair_with_disk_inter` 取一对**任意的**标准球 `P, Q`，再用
   `exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex` 只在**盘上**对齐；
   盘之外没有任何控制，因此它**不能**搬运"弧落在哪里"。

于是第 3 件的障碍不是"缺很多定理"，而是**缺一条**：

> **相对球黏合**：设 `C`、`D` 是 `K` 中的三维球、`C ∩ D` 是二维球，`A ⊆ C ∪ D` 是多面体，
> 且 `(C, C ∩ A)`、`(D, D ∩ A)`、`(C ∩ D, C ∩ D ∩ A)` 都是标准对，
> 则 `(C ∪ D, A)` 是标准对。

有了它，**沿弧的归纳已经现成**：H-A4 的 `arcChainFace_subset_iff` 给出链的全部相交／不交簿记，
`isPLBall_iUnion_of_chain` 给出球的部分，逐格的对标准性由 H-A1
（`exists_isPLHomeomorphOn_coneComplex_sheets`／`_fixing`，对偶格本身就是锥）给出。
所以剩下的工作量集中在这一条，加上一个标准模型（带标准弧的三维球）的构造——
后者全树也不存在。

**修订估计**：第 3 件从 §9 的 3k–6k 行修订为 **1k–2.5k 行**（球对词汇 + 相对黏合 + 模型构造 + 归纳装配），
前提是走"逐格锥化 + 相对黏合"这条路，而不是经典的塌陷 + 正则邻域唯一性那条路。
这个修订**没有验证**，只是基于 H-A4 实际耗时（估 1k–2k、实际 0.21k）与上述障碍定位的重新估计。

**明确的未闭合义务（交回 F）**：上面框出的那条相对球黏合，外加"带标准弧的三维球模型"的构造。
本次**没有**为它引入任何谓词或条件定理——引入 `IsPLBallPair` 会是一个新的基础层级，
按 CLAUDE.md 需要先与用户确认，故未擅自开工。

## 10. 2026-09-18 H-B：PL 球对谓词、显式标准模型与相对黏合的确切缺口

协调者授权引入 `IsPLBallPair`（理由：全树 `IsPLBallPair`/`BallPair`/`unknot` 零命中，
是标准 PL 词汇且只有一个消费者，属普通局部定义，不改任何既有谓词）。

### H-B1 — done，`IsPLBallPair` 与锥形球对（`BallPair.lean`）

命名对齐既有 `IsPLBall`/`IsPLSphere`（`Polyhedron.lean:41,44`）。定义取**锥形式**：

    IsPLBallPair m k P Q := ∃ p L J (_ : IsConeBase p L),
      L.faces.Finite ∧ J.faces ⊆ L.faces ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      P = coneSet p L.space ∧ Q = coneSet p J.space

即"(P,Q) 是球面对上的锥"。取锥形式而非"与标准模型 PL 同胚"的理由：锥本来就是**非纽结**的
（从一点锥出去的弧必是平凡弧），所以锥形式已经把 standard 这一条捕获，同时让
H-A1 的球对定理可以直接消费，不必先反解模型。`IsPLBall k Q` 单列一条，使 `k = 0`
（球里一个内点）与 `k = 1`（球里一条正常嵌入弧）统一处理，不必给空复形开特例。

- `IsPLBallPair.subset`、`IsPLBallPair.isPLBall_sub`、`IsPLBallPair.isPLBall`（`IsPLBall (m+1) P`）。
- `isPLBallPair_coneSet`、`isPLBallPair_coneSet_of_isPLSphere`：后者是主生产者——
  **球面对 (S^m, S^k) 上的锥是球对 (B^{m+1}, B^{k+1})**。
- `exists_isPLHomeomorphOn_coneSet_pair`：**球对的 Alexander 技巧**。链球面之间的 PL 同胚 `f`
  若把子链搬到子链，则锥延拓 `g` 是球对之间的 PL 同胚、在链上等于 `f`、`g p = q`，
  且 `g '' coneSet p J.space = coneSet q J'.space`。直接由 H-A1 的
  `exists_isPLHomeomorphOn_coneComplex_pair` 加两次 `coneComplex_space_eq_coneSet` 得到。
- `exists_isPLHomeomorphOn_of_isPLSphere_pair`：同上并附带两侧的 `IsPLBallPair` 结论。

坑：`[DecidableEq E]` 只在证明里用到（`coneComplex`），不出现在陈述里，
`linter.unusedDecidableInType` 会报 warning；改成证明内 `classical` 即可，别保留该实例参数。

### H-B2 — done，显式标准模型（`BallPairModel.lean`）

- `coneSet_eq_iUnion_segment (hX : X.Nonempty) : coneSet p X = ⋃ z ∈ X, segment ℝ p z`。
  把集合层的锥写成线段并，锥顶对应 `s = 0`，用 `segment_eq_image` 与 `add_smul_sub_eq_combo`。
- `coneSet_pair_eq_union_segment : coneSet p {a, b} = segment ℝ p a ∪ segment ℝ p b`。
- `isPLBallPair_coneSet_arc`：**标准模型**。设 `hsph : IsPLSphere m L.space`、
  `J.space = {a, b}`、`a ≠ b`，则
  `IsPLBallPair m 1 (coneSet p L.space) (segment ℝ p a ∪ segment ℝ p b)`。
  `m = 2` 即"三维球里一条标准正常嵌入弧"：弧就是从锥顶到链上两个不同点的**两条直线段**，
  完全显式，不是存在性的。`IsPLSphere 0` 由 `GeneralPosition.lean:711 isPLSphere_zero_iff`
  （`IsPLSphere 0 P ↔ ∃ a b, a ≠ b ∧ P = {a,b}`）给出，所以模型模块单独放，
  不让 `BallPair.lean` 背上 `GeneralPosition` 的大锥体。

检查 `BallPair` exit=0（8.0 秒）、`BallPairModel` exit=0（8.8 秒），均零 warning；
`.lake/scratch/AuditHBallPair.lean` 十项仅 `propext`、`Classical.choice`、`Quot.sound`。

### H-B3 — 相对球对黏合：**未闭合**，缺的定理已定位到一条

按 `BallGluing.lean:11 isPLBall_union_of_boundary_disk` 的模板走：它之所以能取到在重叠上
**已经相同**的两个同胚，是因为 `SphericalDiskExtension.lean:59`
`exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex` 把**同一个** `g` 分别延拓到两个球上，
于是 `EqOn f₁ f₂` 是免费的。`PLPiece.lean:83 IsPLHomeomorphOn.piecewise` 要的
`EqOn f g (P ∩ Q)` 因此不是障碍，障碍在于**带弧的版本不存在**。

确切缺失的定理（记作 M2，是 `SphericalDiskExtension.lean:59` 的球对版）：

    theorem exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex_pair
        (K : SimplicialComplex ℝ E) [Finite K.faces] (L : SimplicialComplex ℝ F) [Finite L.faces]
        (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space)
        {A : Set E} {A' : Set F}
        (hKA : IsPLBallPair 2 1 K.space A) (hLA : IsPLBallPair 2 1 L.space A')
        {D : Set E} {D' : Set F} (hD : IsPLBall 2 D)
        (hDK : D ⊆ (boundaryComplex 3 K).space) (hD'L : D' ⊆ (boundaryComplex 3 L).space)
        {g : E → F} (hg : IsPLHomeomorphOn g D D') (hgA : g '' (D ∩ A) = D' ∩ A') :
        ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g D ∧ G '' A = A'

协调者问 H-A1 的 `exists_isPLHomeomorphOn_coneComplex_fixing` 是否给出这条延拓：**不给**。
该定理延拓的是**整条链**（边界球面）上的同胚，而 M2 给的只是边界球面上**一张子盘** `D` 上的同胚。
差的是"把 `g` 从 `D` 先延到整个 `∂K`，且把弧的第二个端点送对"。

这一步可以归约，归约后只缺一条（记作 M1）：

    M1（starring）：PL 球是从它**指定内点**出发、对其边界球面的锥。

有了 M1：`closure (∂K \ D)` 是含第二个端点 `y` 于内部的 2-球，由 M1 它是从 `y` 锥出的，
于是 `g` 在 `∂D` 上的限制经 `exists_isPLHomeomorphOn_coneComplex`（锥顶送锥顶）延到该补盘并把 `y ↦ y'`；
与 `g` 在 `D` 上拼起来得 `∂K → ∂L` 把两个端点送对；再由 M1 把 `K` 本身写成从弧上一内点出发的锥
（此时弧恰是该锥顶对两个端点的锥，正是 `IsPLBallPair`），用 H-B1 的
`exists_isPLHomeomorphOn_coneSet_pair` 锥化即得 M2。

M1 在本树**不存在**：`exists_coneComplex_inter_slab`（`ConeSlab.lean:123`）、
`exists_coneComplex_inter_fiber`（`ConeFiber.lean:39`）、
`exists_isConeBase_simplexAvoiding_*`（`SimplexCorner.lean:134,304`）都不是它；
`ClosedStarCone` 只把**闭星**写成锥，不把任意球从任意内点写成锥。
但 M1 有一条便宜的路线，不必重新三角剖分：标准单纯形本来就是从 `stdCenter` 出发的锥
（`StdSimplexCone.lean:78 isConeBase_std`、`:83 coneComplex_std_space`），
而 `AmbientPointMove.lean:35 exists_isPLHomeomorphOn_map_point_eqOn_compl`
（开集连通即可把任一点移到另一点、开集外恒等）可把内点移到 `stdCenter`，
取 `U = interior (stdSimplex ...)`（凸故连通、开），所得同胚在边界上恒等、把单纯形映到自身。
复合球的参数化即得 M1。

### 成本估计（未验证，区间；上次估计偏高约 8 倍，本次按已定位的现成工具给）

- M1（经 `exists_isPLHomeomorphOn_map_point_eqOn_compl` 的 starring）：0.3k–0.8k 行。
  主要成本是 interior/frontier 与"参数化把内点送到内点"的记账。
- M2（相对球对延拓）：0.8k–2k 行。需要 `closure (∂K \ D)` 是 2-球且与 `D` 交于圆周
  （`SphericalDiskExtension` 内部应已有可复用的分解），加两次锥化与一次 `piecewise`。
- 相对球对黏合本身（按 `BallGluing` 模板）：0.3k–0.8k 行。
- 沿弧的链归纳（用 `ArcDerivedNeighborhood.lean:73 arcChainFace_subset_iff` 记账）：0.5k–1.5k 行。

合计约 **1.9k–5.1k 行，未验证**。这比第 9 节末尾给的 7k–14k 低，原因是 H-A/H-B 已经把锥化与球对
那一块消掉，且 M1 找到了经 PL 齐性的便宜路线，不再需要塌陷理论与正则邻域唯一性的一般形式。
第 9 节里"塌陷理论"与"正则邻域唯一性"两项在这条路线上**不再是前置条件**。

## 11. 2026-09-18 更正：H-A2／H-A3 与既有 `StarPair`／`VertexCrossing` 重复，已删除

### 事故与原因

`ConePairExtension.lean` 曾声明 `exists_isPLHomeomorphOn_closedStar_pair`，与
`StarPair.lean:78` **同名同命名空间**。本模块只导入 `ConeExtension`，所以自身聚焦检查通过，
但任何同时导入 `StarPair` 的模块直接报

    import ...StarPair failed, environment already contains
    '...exists_isPLHomeomorphOn_closedStar_pair' from ...ConePairExtension

F 车道因此被迫绕开本模块。原因是我的操作失误：第一次写文件前确实按规则 11 grep 过当时用到的名字，
但 H-A2 的定理是在**后续一次 Edit 里新起的名字**，没有重新 grep。教训：**每新增一个名字就要重新
grep，不能只在建文件时 grep 一次**；而且导入面窄会让本地检查对撞名完全失明。

### 全量复查结果（按名字与按陈述形状各做一遍）

对本次新增的全部 22 个名字做了逐个 tree-wide grep（排除自己的四个文件）：**只有
`exists_isPLHomeomorphOn_closedStar_pair` 一个撞名**，其余名字唯一。按形状复查的结论如下。

**删除（被既有结果覆盖）：**

- `exists_isPLHomeomorphOn_closedStar_pair`：`StarPair.lean:78` 已有，且**严格更强**——
  它在我的三条结论之外还给 `g '' (closedStar K p ∩ {x | ℓ x = 0}) = closedStar K' q ∩ {x | ℓ' x = 0}`，
  即赤道条款，而这正是分支情形真正需要的那条（它携带第二张片）。
- `exists_isPLHomeomorphOn_closedStar_of_geometricLink_subcomplex`：可由 `StarPair.lean:78`
  取 `ℓ = ℓ' = 0` 得到（此时 `{x | 0 = 0} = univ`，赤道条款退化为 `hf.bijOn`），故冗余。
- `closedStar_eq_coneSet`、`geometricLink_singleton_faces_subset`、
  `geometricLink_singleton_space_subset`：前者是 `ConeComplex.lean:262` 的换写；
  后两者与 `StarPair.lean:71` 的 private 引理、`VertexCrossing.lean:110-114` 的内联代码重复。
  消费者随上面两条一起删除后已无用户。
- **整个 `ConePairCrossing.lean` 删除**。H-A3 声称"树里有消费者没有生产者"是**错的**：
  链条 `LinkPair.lean:53 exists_isPLHomeomorphOn_geometricLink_pair` →
  `StarPair.lean:78` → `CrossingNeighborhood.lean:71 HasPLCrossingAt.of_closedStar_pair`
  早已端到端接好，就在 `VertexCrossing.lean:12 hasPLCrossingAt_fiber_of_geometricLink_section`
  内部（接线在 `:115-121`），`VertexCrossingLevel.lean:57` 是更一般的变体。
  我的 `HasPLCrossingAt.of_geometricLink_pair` 是同一个合成，但第二张片取抽象集合 `B` 加锥假设，
  比既有的赤道版本弱，且无消费者。

**保留（经形状复查确认不重复）：**

- `coneSet` 及其基本 API（`mem_coneSet_iff`、`apex_mem_coneSet`、`subset_coneSet`、
  `coneSet_mono`、`coneComplex_space_eq_coneSet`、`coneSet_subset_coneComplex_space`）。
  全树没有集合层的锥算子，这一条测绘结论仍然成立。`BallPair`／`BallPairModel` 在用。
- `image_coneSet_of_radial`：**必须诚实说明**——它是 `StarPair.lean:11
  image_coneComplex_of_radial_eq` 的推广，不是全新内容。既有版本要求两边都是**子复形**
  并把目标子复形作为输入；我的版本对**任意子集** `X` 成立并直接算出像
  `coneSet q (f '' X)`，不需要先给目标。球对层用的是任意子集版本（第二张片是裸集合），
  所以推广有用，但功劳应记在既有引理上。
- `eqOn_id_coneSet_of_radial`：`StarPair` 无对应物；`ConeAmbientExtension.lean:40-49`
  在证明内部证过但未导出。保留。
- `exists_isPLHomeomorphOn_coneComplex_pair`／`_sheets`／`_fixing`：锥层（不是闭星层）的
  全称／双片／相对版本，`StarPair` 直接跳到闭星，没有这一层。`BallPair` 在用。保留。
- `BallPair.lean`／`BallPairModel.lean` 全部保留：`IsPLBallPair` 等名字全树唯一，
  球对概念确认不存在（协调者已据此授权）。

### 验证

跨导入证明（这才是能证明修好了的检查，单模块聚焦检查做不到）：
`.lake/scratch/AuditHCrossImport.lean` 同时导入 `StarPair`、`VertexCrossing`、
`ConePairExtension`、`BallPairModel` 并 `#check` 两侧的声明，**exit=0**；
`exists_isPLHomeomorphOn_closedStar_pair` 解析到 `StarPair` 的带赤道条款版本。

聚焦检查：`ConePairExtension` exit=0（9.4 秒）、`BallPair` exit=0（8.4 秒）、
`BallPairModel` exit=0（9.4 秒），均零 warning。
`.lake/scratch/AuditHConePairExtension.lean` 七项、`AuditHBallPair.lean` 十项，
仅 `propext`、`Classical.choice`、`Quot.sound`。

### 对第 10 节 H-B3 的影响

不变。M1（starring）与 M2（相对球对延拓）仍然缺失，`StarPair`／`VertexCrossing` 这条链是
**逐点**的横截性质，不提供沿弧黏合所需的球对延拓。但第 10 节里"经 PL 齐性做 starring"的估计
需要下修信心：`AmbientPointMove.lean:35` 要求 `IsOpen U`，对余维零的三维球成立，
对 `∂K` 里的二维盘**不成立**（它在环境里没有内点），所以补盘那一步不能直接用 PL 齐性，
需要内蕴齐性或三角剖分论证。第 10 节的 1.9k–5.1k 行区间因此偏低，**未验证**，
补盘那一步可能单独再加 0.5k–1.5k 行。

## 12. 2026-09-18 M1（starring）余维零情形 — done（`BallStarring.lean`）

第 10/11 节把整条栈的底部定位为 M1。余维零情形现已闭合，且**独立于球对应用**可复用。

### 交付

- `IsPLHomeomorphOn.image_openSimplex_eq_interior`：设
  `hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n+2))) P`，`P ⊆ EuclideanSpace ℝ (Fin (n+1))`（余维零），
  则 `f '' openSimplex (stdVertices n) = interior P`。
  由 `BallInterior.lean:11 image_openSimplex_stdVertices`（给 `P \ f '' stdSimplexBoundary`）
  与 `BallFrontier.lean:38 image_stdSimplexBoundary_eq_frontier`（给 `f '' stdSimplexBoundary = frontier P`）
  合成，再用 `IsClosed.frontier_eq` 与 `Set.sdiff_sdiff_cancel_left` 把 `P \ (P \ interior P)` 约掉。
- `isConnected_interior_of_isPLBall`：`IsPLBall (n+1) P → IsConnected (interior P)`，**任意维数**。
  注意 `DiskCrosscut.lean:17` 已有 `IsPLBall.isConnected_interior`，但只对二维且**经过 Jordan 曲线定理**；
  本条改名避让（名字不同，已跨导入验证二者共存），走的是
  `BallInterior.lean:32 isConnected_sdiff_image_stdSimplexBoundary`（开单形凸⟹连通，再取连续像），
  代价低得多，且覆盖全维数。二维那条可由本条取代，但 `DiskCrosscut` 不属本车道，未改。
- `IsPLBall.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq`：**M1 本体**。
  设 `IsPLBall (n+1) P`（`P ⊆ EuclideanSpace ℝ (Fin (n+1))`）、`p ∈ interior P`，则存在
  `f : (Fin (n+2) → ℝ) → EuclideanSpace ℝ (Fin (n+1))`，`IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n+2))) P`
  且 `f (stdCenter n) = p`。即**PL 球总能用标准单形参数化，并把重心送到任意指定内点**。
- `IsPLBall.exists_isPLHomeomorphOn_coneSet_of_mem_interior`：锥语言的等价形式。
  因为 `stdSimplex = coneSet (stdCenter n) (simplexBoundary (stdVertices n) _).space`
  （`StdSimplexCone.lean:83 coneComplex_std_space` 加第 9 节的 `coneComplex_space_eq_coneSet`），
  所以上一条就是"球 PL 同胚于它自己边界球面上的锥，锥顶落在指定内点"。

### 证明要点（供复用）

路线是 §10 说的 PL 齐性，但**不能**在标准单形自己的环境里做（`Fin (n+2) → ℝ` 里单形余维一，
`interior` 为空）。必须在 `P` 所在的余维零环境里做：

1. `f (stdCenter n) ∈ interior P`（由上面的像等式）。
2. `exists_isPLHomeomorphOn_map_point_eqOn_compl`（`AmbientPointMove.lean:35`）取
   `U = interior P`：`IsOpen` 免费，`IsPreconnected` 由 `isConnected_interior_of_isPLBall` 给。
   得 `h : E ≃ₜ E`，`IsPLHomeomorphOn h univ univ`、`EqOn h id (interior P)ᶜ`、
   `h (f (stdCenter n)) = p`。
3. `h '' interior P = interior P`。**这一步的论证值得记**：不用开映射，只用单射加"补集上恒等"。
   若 `h x ∉ interior P`，则 `hfix` 给 `h (h x) = h x`，单射得 `h x = x`，于是 `x ∉ interior P`，
   与 `x ∈ interior P` 矛盾；反向对 `h.symm y` 同样两行。
4. `h '' P = P`：由 `IsPLBall.closure_interior`（`BallFrontier.lean:60`）与 `Homeomorph.image_closure`
   夹出，`calc` 四步。
5. `IsPLHomeomorphOn h P P` 由 `PLImage.lean:168 IsPLHomeomorphOn.restrict` 加 `h '' P = P` 得；
   末尾 `PLHomeomorph.lean:78 IsPLHomeomorphOn.trans` 复合。

坑：`Set.diff_diff_cancel_left` 已废弃，用 `Set.sdiff_sdiff_cancel_left`；
`hfix hx` 的结论带 `id`，`rw [h.apply_symm_apply, id_eq] at h1` 才化得掉；
两处不要用 `▸`，方向会反，写 `by rw [...]; exact ...`。

聚焦检查 `BallStarring` exit=0（9.6 秒）、零 warning；
`.lake/scratch/AuditHBallStarring.lean` 同时导入 `DiskCrosscut` 与 `BallPairModel`
（撞名回归检查）exit=0，四项仅 `propext`、`Classical.choice`、`Quot.sound`。

### M1 任意余维情形 — done，补盘那一步的障碍消解

第 11 节末尾说补盘（`∂K` 里的二维盘）那一步因 `IsOpen U` 失效而需要内蕴齐性或三角剖分论证。
**不需要**：把问题搬到余维零的模型里即可，代价很小。

- `IsPLHomeomorphOn.exists_stdCenter_eq_of_mem_image_openSimplex`：设 `E` 任意有限维赋范空间、
  `hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (m+2))) P`（`P ⊆ E`，**余维任意**）、
  `x ∈ g '' openSimplex (stdVertices m)`，则存在 `f` 使
  `IsPLHomeomorphOn f (stdSimplex ℝ (Fin (m+2))) P` 且 `f (stdCenter m) = x`。
- 证明：在 `EuclideanSpace ℝ (Fin (m+1))`（对 `m+1` 维球而言是余维零）里用
  `SimplexBoundary.lean:400 exists_affineIndependent_openSimplex_subset` 取 `m+2` 个仿射无关点，
  `SimplexBall.lean:14 isPLBall_convexHull_of_affineIndependent` 给模型球 `C`，
  它的参数化 `u` 把 `openSimplex` 送进 `interior C`（本节第一条引理），
  于是余维零版 M1 适用；再用 `IsPLHomeomorphOn.symm`／`.trans` 把
  `g ∘ invFunOn u _ ∘ f₀` 拼回去。核心是**模型球的维数等于环境维数**，与原来的 `P` 无关。

聚焦检查 `BallStarring` exit=0（9.6 秒）、零 warning；审计五项仅
`propext`、`Classical.choice`、`Quot.sound`。

坑：`IsPLBall` 展开是 `∃`，所以 `obtain ⟨u, hu⟩ : IsPLBall _ _ := ...` 之后点记号会去找
`Exists.xxx`。要先 `have hC : IsPLBall ... := ...` 再 `obtain ⟨u, hu⟩ := id hC` 保住 `hC`。
`show` 若真改变目标会被 `linter.style.show` 报 warning，用 `change`。

**唯一遗留限定**：任意余维版本的假设 `x ∈ g '' openSimplex (stdVertices m)` 是**相对于给定参数化 `g`** 的。
数学上该集合与 `g` 无关（它是球的内蕴开胞腔），但本次没有证。要消掉这个限定，路线是
`BoundaryInvariance.lean:125 boundaryComplex_space_of_isPLHomeomorphOn` 加
`boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`：照 `BallFrontier.lean:9
IsPLHomeomorphOn.image_stdSimplexBoundary` 的写法，把 `g '' stdSimplexBoundary (m+1)` 证成
`(boundaryComplex (m+1) K).space`（`K.space = P` 的任意复形），即得 `g` 无关性。估 10–40 行，未验证。
余维零版本不受此限定影响：它的假设是真正的 `interior P`，完全内蕴。

### M1 的参数化限定已消除 — done（同模块）

第 12 节末尾留的那条限定（任意余维版本的假设相对于给定参数化 `g`）现已闭合，估计 10–40 行属实。

- `IsPLHomeomorphOn.image_stdSimplexBoundary_eq_boundaryComplex`：设 `K.space = P`，则
  `g '' stdSimplexBoundary (m+1) = (boundaryComplex (m+1) K).space`。两行：
  `BoundaryOfBall.lean:66 boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex` 加
  `SimplexBoundaryImage.lean:38 simplexBoundary_stdVertices_space`。
  `BallFrontier.lean:9` 末尾那段 `convert ... congr 2; Subsingleton.elim` 在这里**不需要**，
  因为不再把结果化成 `frontier P`（那一步才是余维零专有的）。
- `IsPLHomeomorphOn.image_openSimplex_eq_sdiff_boundaryComplex`：
  `g '' openSimplex (stdVertices m) = P \ (boundaryComplex (m+1) K).space`。右边只依赖 `K`，
  与参数化无关，这就是所要的 `g` 无关性。
- `IsPLBall.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq_of_notMem_boundaryComplex`：
  **内蕴版 M1**。假设改成 `x ∈ P \ (boundaryComplex (m+1) K).space`（`K` 是 `P` 的任意三角剖分），
  结论不变。至此 starring 在任意余维下都是内蕴陈述。

坑：`boundaryComplex` 出现在**陈述**里，所以要显式 `[DecidableEq E]` 参数，不能用证明内 `classical`；
这与第 10 节 `BallPair` 那边的情况相反（那里 `coneComplex` 只出现在证明里）。

聚焦检查 `BallStarring` exit=0（9.7 秒）、零 warning；审计八项仅
`propext`、`Classical.choice`、`Quot.sound`。

## 13. 2026-09-18 带标记点的 Alexander 技巧（`BallMarkedExtension.lean`）— M2 的新砖

M2 的路线是：先把 `g` 从子盘 `D` 延到整个边界球面并把弧的第二个端点送对，再锥化进球内。
第二步用第 10 节的 `exists_isPLHomeomorphOn_coneSet_pair`；第一步缺的那块就是本节。

- `exists_isPLHomeomorphOn_extension_marked`：设 `f`、`f'` 分别是 `A`、`A'`（任意维、任意余维的 PL 球）
  的标准单形参数化，`φ` 是两球**边界球面之间**的 PL 同胚（写成
  `f '' (simplexBoundary (stdVertices m) _).space → f' '' (…).space`），则存在 `G` 使
  `IsPLHomeomorphOn G A A'`、`EqOn G φ` 在边界球面上，且 **`G (f (stdCenter m)) = f' (stdCenter m)`**。
  即：**边界同胚锥化延拓时，可以额外要求把一个指定的内点送到指定的内点**——
  只要这两个内点分别是给定参数化的重心像。配合第 12 节的 M1（重心可以送到任意内点／开胞腔中的点），
  这就等于"带一个标记内点的 Alexander 技巧"。
  证明：把 `φ` 经两侧参数化拉回成边界球面模型 `(simplexBoundary (stdVertices m) _).space` 上的自同胚 `ψ`，
  用 `ConeExtension.lean:70 exists_isPLHomeomorphOn_coneComplex` 锥化成 `Φ`（锥顶送锥顶，
  这正是 `g p = q` 那一条），再 `f' ∘ Φ ∘ invFunOn f` 搬回去。
  `coneComplex_std_space` 把锥的空间换成 `stdSimplex`。
- `IsPLHomeomorphOn.image_stdSimplexBoundary_congr`：同一个球的**两个参数化**给出同一个边界球面，
  `f₁ '' stdSimplexBoundary (m+1) = f₂ '' stdSimplexBoundary (m+1)`。
  由本节上面那条参数化无关性经任一三角剖分两边夹出。这条是 M2 组装必需的：
  M1 造出来的参数化与树里既有盘引理（`inter_closure_sdiff_eq_image_stdSimplexBoundary`）
  用的参数化不是同一个，必须先认同它们的边界圆。

聚焦检查 `BallMarkedExtension` exit=0（10.2 秒）、零 warning；
`.lake/scratch/AuditHBallMarked.lean`（同时导入 `SphericalDiskExtension` 与 `BallPairModel`）
两项仅 `propext`、`Classical.choice`、`Quot.sound`。

坑：第二条里 `boundaryComplex` 只出现在证明中，所以要用证明内 `classical` 而不是
`[DecidableEq E]` 参数（与第 12 节末尾那条相反，那里它出现在陈述里）。

### M2 本体 — 未闭合，剩余组装已定尺

树里 `SphericalDiskExtension.lean:11 exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two`
**确实**给了球面层的延拓（`D ⊆ S` 上的 `g` 延到 `S → S'`），但它**不带标记点**：
补盘上的延拓是拼接产生的，无法指定第二个端点去哪。所以不能直接复用，
但它的证明骨架可以照抄——它内部已经用了
`IsPLSphere.isPLBall_closure_sdiff`（球面里盘的补是盘）与
`IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary`（两盘恰交于圆周），这两条都现成。

剩余两步：

1. **带标记点的球面延拓**：`A := closure (S \ D)`、`A' := closure (S' \ D')` 是 2-球；
   由 M1 取 `A` 的参数化把重心送到第二个端点 `y`（`A'` 同理送到 `y'`），
   由 `image_stdSimplexBoundary_congr` 把该参数化的边界圆认同成 `D ∩ A`，
   于是 `g` 限制到圆周后可喂给本节的 `exists_isPLHomeomorphOn_extension_marked`，
   得补盘上的延拓且 `y ↦ y'`；再用 `PLPiece.lean:83 IsPLHomeomorphOn.piecewise`
   沿圆周与 `D` 上的 `g` 拼起来。约 100–180 行，**未验证**。
2. **锥化进球内**：把 `IsPLBallPair 2 1 K.space A` 展开取锥数据（本谓词按定义就给锥结构，
   不需要再 star 一次），用第 1 步的球面同胚喂
   `exists_isPLHomeomorphOn_coneSet_pair`，其 `hfJ` 就是"两个端点送对"。约 80–150 行，**未验证**。

合计约 **180–330 行，未验证**。

需要在 M2 陈述里显式写出、否则不成立的条件：**弧的两个端点必须一个在 `D` 的开胞腔里、
一个在补盘 `A` 的开胞腔里**（不能落在公共圆周 `D ∩ A` 上），否则 M1 对补盘不适用。
这不是技术限制而是几何前提：子盘 `D` 必须把两个端点分开。

## 14. 2026-09-18 M2 已闭合（`SphereDiskMarked.lean`、`ConeDiskPairExtension.lean`）

### 第一步：带标记点的球面延拓（`SphereDiskMarked.lean`）

- `exists_isPLHomeomorphOn_extension_marked_stdSimplexBoundary`：把第 13 节的带标记延拓改用
  `stdSimplexBoundary (m+1)` 表述（经 `simplexBoundary_stdVertices_space` 一次改写），
  好让树里既有的盘引理直接对接。
- `exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two_marked`：设 `S`、`S'` 是 2-球面，
  `D ⊆ S`、`D' ⊆ S'` 是 2-球，`g : D → D'` 是 PL 同胚，
  `y ∈ closure (S \ D) \ D`、`y' ∈ closure (S' \ D') \ D'`，则存在 `G` 使
  `IsPLHomeomorphOn G S S'`、`EqOn G g D` 且 **`G y = y'`**。
  骨架照抄 `SphericalDiskExtension.lean:11`，只把其中
  `exists_isPLHomeomorphOn_of_stdSimplexBoundary`（无标记）换成第 13 节的带标记延拓，
  并先用 M1 把补盘的参数化重心挪到 `y`。
  **不需要**第 13 节的 `image_stdSimplexBoundary_congr`：
  `SphericalDiskComplement.lean:160 IsPLSphere.image_stdSimplexBoundary_complement`
  对**任意**参数化 `q` 都给 `q '' stdSimplexBoundary 2 = closure (S \ D) ∩ D`，
  所以 M1 造出来的参数化的边界圆自动就是 `D ∩ A`。这是又一次"障碍其实是找错引理形状"。
  `y` 落在补盘开胞腔的条件恰好化简成 `y ∉ D`：
  `a '' openSimplex = A \ (A ∩ D) = A \ D`（`Set.sdiff_self_inter`）。

### 第二步：锥化进球内（`ConeDiskPairExtension.lean`）

- `exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked`：**M2 本体**。输入锥数据
  `IsConeBase p Lc`、`J.faces ⊆ Lc.faces`、`IsPLSphere 2 Lc.space`（另一侧同），
  边界球面里的子盘 `D`、`D'` 与 `g`，端点分离数据 `y`、`y'`，以及
  `hJsplit : J.space = J.space ∩ D ∪ {y}`、`hJ'split`、`hgJ : g '' (J.space ∩ D) = J'.space ∩ D'`；
  输出 `G` 使 `IsPLHomeomorphOn G (coneSet p Lc.space) (coneSet q Lc'.space)`、
  `EqOn G g D`、`G p = q`、`G '' coneSet p J.space = coneSet q J'.space`。
  证明五行：带标记球面延拓给 `Gs`，`hJsplit` 把 `Gs '' J.space = J'.space` 算出来，
  再喂第 10 节的 `exists_isPLHomeomorphOn_coneSet_pair`。

### 端点分离假设：为什么写成 `hJsplit` 而不是别的

协调者要求把"弧的两个端点一个在 `D` 的开胞腔、一个在补盘开胞腔、都不在公共圆周上"写进陈述。
实际可用的形式是三条：`hy : y ∈ closure (Lc.space \ D) \ D`（第二个端点在补盘开胞腔）、
`hJsplit : J.space = J.space ∩ D ∪ {y}`（弧的链**恰好**由 `D` 内的部分加上 `y` 组成）、
以及 `hgJ`（`g` 把 `D` 内那部分送对）。
不能只写"两个端点"：`IsPLBallPair 2 1` 按定义只要求 `IsPLBall 1 A`，**不蕴含** `J.space` 是两个点，
所以要么额外假设 `IsPLSphere 0 J.space`，要么像这里一样直接假设链在 `D` 与 `{y}` 之间的分解。
后者更弱也更好用，`hJsplit` 正是"`D` 把两端点分开"的精确内容。

聚焦检查 `SphereDiskMarked` exit=0（9.9 秒）、`ConeDiskPairExtension` exit=0（9.8 秒），均零 warning；
`.lake/scratch/AuditHM2.lean`（同时导入 `SphericalDiskExtension` 与 `BallPairModel`）
三项仅 `propext`、`Classical.choice`、`Quot.sound`。

坑：`Set.diff_self_inter` 已废弃，用 `Set.sdiff_self_inter`（与第 12 节的
`diff_diff_cancel_left → sdiff_sdiff_cancel_left` 是同一批改名）。
本节两个定理里 `coneComplex` 都只出现在证明中，故用证明内 `classical`，不要留 `[DecidableEq]` 参数。

### 第 3、4 步未开始

第 3 步（相对球黏合，照 `BallGluing.lean:11` 模板）与第 4 步（沿弧的链归纳，
用 `ArcDerivedNeighborhood.lean:73 arcChainFace_subset_iff`）本次未开始，未估成本。
M2 已经把 `IsPLHomeomorphOn.piecewise` 所需的"两个同胚在重叠上逐点相等"这一条备好：
第二个同胚由 M2 延拓第一个而来，重叠上相等是构造给出的，不是额外义务。

## 15. 2026-09-18 `IsPLBallPair` 定义修正（锥形 ⟹ 与锥对 PL 同胚）

### 原定义错在哪里（**不要改回去**）

第 10 节的原定义要求 `P = coneSet p L.space`，即 `P` 在环境里**字面上就是一个锥**。
`coneSet p X` 的每个点都在从 `p` 出发的线段上，所以它必然**关于 `p` 星形**。
而一般的 PL 3-球对任何点都不星形（例如弯成香蕉形的球）。
因此原谓词严格强于"标准球对"，名不副实：它不是"较弱但够用"的版本，而是**另一个、错的**概念。

后果是第 3 步（相对球黏合）的结论 `(C ∪ D, A)` 是标准对**无法表达**——`C ∪ D` 一般不是字面的锥。
M1 只给"PL 同胚于一个锥"，不给"是一个锥"，所以绕不过去。
这个缺陷此前没暴露，是因为 M2 直接以锥数据为输入，从不经过谓词。

修正后的定义（协调者已批准；该谓词当时只有本车道自己的消费者）：

    IsPLBallPair m k P Q := ∃ p L J (_ : IsConeBase p L) (f : E → E),
      L.faces.Finite ∧ J.faces ⊆ L.faces ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      IsPLHomeomorphOn f (coneSet p L.space) P ∧ f '' coneSet p J.space = Q

即"**与**锥对 PL 同胚"。

### 改动

- `IsPLBallPair.subset`、`.isPLBall_sub`、`.isPLBall` 经共轭重证：
  `.subset` 用 `hf.image_eq` 加 `image_mono`；`.isPLBall` 先证锥是球再 `IsPLBall.of_isPLHomeomorphOn`。
- 两个生产者 `isPLBallPair_coneSet`、`isPLBallPair_coneSet_of_isPLSphere` 取 `f = id`，
  用 `IsPolyhedron.isPLHomeomorphOn_id` 与 `Set.image_id`；因此它们现在需要
  `[FiniteDimensional ℝ E]`（`isPolyhedron_space` 要），并且要手工给
  `Finite (coneComplex hL).faces := (coneComplex_faces_finite hL (Set.toFinite L.faces)).to_subtype`。
- 新增 `IsPLBallPair.of_isPLHomeomorphOn`：谓词在 PL 同胚下传递
  （`(hg : IsPLHomeomorphOn g P P')`、`g '' Q = Q'` ⟹ `IsPLBallPair m k P' Q'`）。
  这条是第 3 步必需的：黏合的结论要靠把模型沿 PL 同胚搬过去得到。旧定义下它不成立。
- `BallPairModel`、`ConeDiskPairExtension` **未改一行**即通过（它们只用生产者，不拆谓词）。

聚焦检查 `BallPair` exit=0（8.3 秒）、`BallPairModel` exit=0（9.0 秒）、
`ConeDiskPairExtension` exit=0（10.6 秒），均零 warning；
`.lake/scratch/AuditHBallPair.lean` 十项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 两条不要被"优化"掉的记录

1. **`hJsplit` 是对的弱形式，别强化回"两个端点"。**
   M2（第 14 节）的端点分离假设写成 `J.space = J.space ∩ D ∪ {y}` 而不是 `IsPLSphere 0 J.space`，
   是因为 `IsPLBallPair 2 1` 只保证 `IsPLBall 1 A`，**不蕴含**链是两个点。
   假设链是两点比谓词能提供的更强，会让 M2 在真实消费点用不上。
2. **动手前先查"障碍是不是环境／引理形状的假象"，这是常规动作不是偶发。**
   本任务内已命中三次：(a) 补盘 starring 说要内蕴齐性，实际只需把构造搬到维数相符的环境里（约 20 行，
   不是 0.5k–1.5k）；(b) M2 说要先比较两个参数化，实际
   `SphericalDiskComplement.lean:160` 对任意参数化都成立，`image_stdSimplexBoundary_congr` 白造；
   (c) 反向的一次：`ConePairCrossing` 以为"有消费者没生产者"，实际整条链已在
   `VertexCrossing.lean:115-121` 接好。报成本之前先做这一查。

### 第 3、4 步仍未开始

第 3 步缺的模型仍缺：`SimplexBallPair.lean:46 exists_isPLBall_pair_with_disk_inter`
给两个交于 2-盘的 3-球但**不带弧**，需要再造一条贯穿两球、与该盘交于一个内点的标准弧。
`coneSet_pair_eq_union_segment`（第 10 节）把标准弧写成从锥顶出发的两条直线段，
所以"两个锥、线段在公共盘上对接"的模型有望显式构造而非存在性给出。未开始，未估成本。

## 16. 2026-09-18 第 3 步模型：三项中的第 1 项已闭合，第 2、3 项给证据不给估计

### 第 1 项 — done：单纯形是从任意内点出发、对其边界球面的锥（`BallPairSimplex.lean`）

`isPLBallPair_convexHull_of_mem_openSimplex`：设 `T` 仿射无关、`T.card = n + 2`、
`p ∈ openSimplex T`、`J.faces ⊆ (simplexBoundary T hT).faces`、`J.space = {a, b}`、`a ≠ b`，则

    IsPLBallPair n 1 (convexHull ℝ T) (segment ℝ p a ∪ segment ℝ p b)

取 `n = 2`（`T.card = 4`，四面体）就是**三维球带一条标准正常嵌入弧**，完全显式：
弧是从内点 `p` 到边界球面上两个不同点的两条直线段。

三条使能事实**全部已在树中**，不需要新造：

- `SimplexPush.lean:13 coneComplex_simplexBoundary_space hT hcard hp`：**任意顶点**版本
  （不是只有 `stdCenter`），`(coneComplex (isConeBase_simplexBoundary hT hcard hp)).space = convexHull ℝ T`。
  之前第 12 节猜这条可能只有标准版，是错的；它在 `Homogeneity.lean:23`、`SimplexCornerChart.lean:75` 已被使用。
- `SimplexBoundary.lean:288 isPLSphere_biUnion_erase T hT (hcard : T.card = n + 2)` 加
  `SimplexBoundary.lean:159 simplexBoundary_space`：一般 `T` 的边界是 `IsPLSphere n`，
  不限于 `stdVertices`。
- `ConeBase.lean:89 isConeBase_simplexBoundary`：`p ∈ openSimplex T` 即锥基。

证明四行：拼出 `IsConeBase`、`IsPLSphere`，喂第 10 节的 `isPLBallPair_coneSet_arc`，
再用上面第一条把 `coneSet p (simplexBoundary T hT).space` 改写成 `convexHull ℝ T`。

聚焦检查 `BallPairSimplex` exit=0（10.4 秒）、零 warning；
`.lake/scratch/AuditHBallPairSimplex.lean`（同时导入 `SimplexBallPair`）一项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 第 2 项 — 证据，未测试，**不给估计**

目标：两个四面体沿一张三角面相接，交恰为该面。

- 树里**有**一个"两球交恰为 2-盘"的完整构造：`SimplexBallPair.lean:46
  exists_isPLBall_pair_with_disk_inter`，其交由
  `coneComplex_simplexAvoiding_inter_convexHull` 精确给出。但它的两个球是
  **`P` = 从重心对 `simplexAvoiding`（去掉一张面的边界，是 2-**盘**）的锥**、
  **`Q` = `convexHull (insert p F)`（四面体）**。
  `Q` 满足第 1 项，`P` **不满足**：它的锥基是盘不是球面，故不满足 `IsPLBallPair` 的
  `IsPLSphere m L.space` 条款。所以这条现成构造不能直接复用。
- 两个四面体共面的版本：grep 未找到现成引理（搜 `convexHull ... ∩ convexHull ... = convexHull`
  与 `inter_convexHull` 只命中 `IsGlueIso` 的边界迹与 `ConeFreeFace` 的锥交，都不是）。
- 数学论证是清楚的：取在公共面上为零、在两个对顶点上异号的线性泛函 `ℓ`，
  则两球分别落在 `{ℓ ≤ 0}`、`{ℓ ≥ 0}`，交落在 `{ℓ = 0}`；再用重心坐标证
  `convexHull T₁ ∩ {ℓ = 0} = convexHull F`（`x = Σλᵢvᵢ + λ₄a`，`ℓ x = λ₄ ℓ a = 0` 且 `ℓ a ≠ 0` 故 `λ₄ = 0`）。
  **未在 Lean 里试过**，故按要求不报行数区间。

### 第 3 项 — 证据，未测试，**不给估计**

目标：两段弧在公共面上恰好接在同一个内点 `z`。

- 需要 `coneSet p₁ {z, v} ∩ F = {z}`，即从 `p₁` 出发的两条线段只在 `z` 碰 `F`。
  这要求远端点 `v ∈ ∂T₁ \ F`，是对模型选点的约束，不是额外定理。
- 另外 `(C∩D, C∩D∩A)` 这一对是 `IsPLBallPair 1 0 F {z}`：`F` 是三角形（2-盘），`z` 内点，
  由第 1 项的 `n = 1` 情形给 `F = coneSet z (∂F)`；但子对要 `coneSet z J.space = {z}`，
  即 `J` 取**空复形**（`J.space = ∅`），且要 `IsPLBall 0 {z}`（单点是 0-球）。
  空复形与单点这两条细节**未查证**树中是否现成。
- 同样**未在 Lean 里试过**，不报区间。

### 关于弧的形状：确认是"一个穿越点"

协调者问模型该取一个穿越点还是两个。按第 3 步的三对来看：
`(C∩D, C∩D∩A)` 里 `C∩D` 是 2-球、`C∩D∩A` 必须是 `IsPLBall 0`，即**一个点**。
所以是**一个穿越点**：弧在公共盘上只穿一次，`A` 是 `v → p₁ → z → p₂ → w` 的折线。
两个穿越点的版本不是这里要的。

## 17. 2026-09-18 第 3 步模型：第 2、3 项已闭合（`BallPairTwoSimplices.lean`，全模块 88 行）

### 第 2 项 — done：两个单纯形被分离泛函切开后交恰为公共面

`convexHull_insert_inter_convexHull_insert_of_separating`：设 `ℓ : E →ₗ[ℝ] ℝ` 在 `F` 上恒零、
`ℓ a < 0 < ℓ b`，则

    convexHull ℝ (insert a F) ∩ convexHull ℝ (insert b F) = convexHull ℝ F

**实测 37 行**（上一轮按要求拒绝报区间，实际远小于任何我会猜的数）。两点比预期弱：

- **不需要仿射无关**。原以为要 `hT₁`、`hT₂` 两个 `AffineIndependent`，实际证明里一次都没用到。
- **不需要有限维**。`omit [FiniteDimensional ℝ E]` 通过。

证明就是原计划：`convexHull_min` 加 `convex_halfSpace_le/ge`（注意是**大写 S**，
且树里的用法是 `ℓ.isLinear` 而不是 `LinearMap.isLinear ℓ`）把两侧夹进半空间得 `ℓ x = 0`；
再用 `ConeComplex.lean:13 exists_combo_of_mem_convexHull_insert` 把 `x` 写成
`a + s • (z - a)`，算出 `ℓ x = (1 - s) * ℓ a`，由 `ℓ a ≠ 0` 得 `s = 1`，故 `x = z ∈ convexHull F`。

### 第 3 项 — done：公共面与穿越点这一对

上一轮列为"未查证"的两条**都在树里现成**（第五、六次 artifact 命中）：

- 空复形：`(⊥ : Geometry.SimplicialComplex ℝ E)` 加 `Geometry.SimplicialComplex.space_bot`
  （用例见 `ChartGlue.lean:194`、`LocallyFinitePieceTowerExistence.lean:53`）。
- 单点是 0-球：`affineIndependent_of_subsingleton ℝ _` 加
  `isPLBall_convexHull_of_affineIndependent` 取 `card = 0 + 1`，再 `convexHull_singleton`。
  这正是协调者猜的路线，`ConvexPolytope.lean:52` 已有同样写法。

交付三条：`coneSet_empty : coneSet p ∅ = {p}`（不需要有限维）、
`isPLBall_zero_singleton : IsPLBall 0 {z}`、
`isPLBallPair_convexHull_singleton_of_mem_openSimplex`：
`T` 仿射无关、`T.card = n + 2`、`p ∈ openSimplex T` ⟹ `IsPLBallPair n 0 (convexHull ℝ T) {p}`。
取 `n = 1`（三角形）即第 3 步要的 `(F, {z})` 这一对。子复形取 `⊥`，
`coneSet p ⊥.space = coneSet p ∅ = {p}`。

聚焦检查 `BallPairTwoSimplices` exit=0（9.5 秒）、零 warning；
`.lake/scratch/AuditHTwoSimplices.lean`（同时导入 `SimplexBallPair`）四项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 模型三项合计

第 1 项（`BallPairSimplex.lean`，第 16 节）+ 第 2、3 项（本节）= 两个文件、约 110 行，
三项全部闭合。剩下的是把它们拼成"两个四面体沿一张面相接、一条折线弧穿过"的具体模型
（选点、验证三对同时成立），以及第 3 步本身。**未开始，不报区间。**

拼装时要注意的一条：第 2 项给的是 `convexHull (insert a F) ∩ convexHull (insert b F) = convexHull F`，
而模型需要的是两个**四面体**（`card = 4`），所以 `F` 要取 `card = 3` 的三角形，
`insert a F`、`insert b F` 各自 `card = 4`，且各自仿射无关——后者不是第 2 项的假设，
但**是**第 1 项（`isPLBallPair_convexHull_of_mem_openSimplex`）的假设，拼装时要单独提供。

## 18. 2026-09-18 模型拼装：**设计更正**——不能用"两个四面体沿面相接"

本节只改文档，不含 Lean 代码。记录一条在动手前发现的结构性错误，免得下一个人照原计划施工到一半撞墙。

### 原计划错在哪里

协调者与我此前一致设想的模型是**两个四面体沿一张三角面相接**（`C₁ ∪ C₂` 是双锥／bipyramid）。
这个模型**用不了**，理由是循环依赖：

- 第 3 步（相对黏合）按 `BallGluing.lean:11` 的模板走，必须有一个模型，其**并**这一对
  `(C₁ ∪ C₂, A)` 已知是标准对——`BallGluing` 里对应的就是 `hPQ : IsPLBall 3 (P ∪ Q)`，
  它成立是因为那里 `P ∪ Q = convexHull T` 是个单纯形。
- 我们手上唯一的标准对生产者是第 16 节的 `isPLBallPair_convexHull_of_mem_openSimplex`，
  它只对**单纯形**成立。
- 两个四面体沿面相接，并是双锥，**不是单纯形**，所以拿不到并这一对的标准性。

### 更正后的模型形状

把一个单纯形**切成两个单纯形**，而不是把两个单纯形拼起来：

- 大四面体 `T = {A, B, C, D}`，`M` 取 `C`、`D` 的中点，切面过 `A, B, M`。
  两半 `C₁ = conv{A,B,C,M}`、`C₂ = conv{A,B,D,M}` **都是四面体**，公共面 `F = conv{A,B,M}`，
  并 `C₁ ∪ C₂ = conv T` **是单纯形**。于是并这一对可由第 16 节直接给出。
- 具体坐标（`EuclideanSpace ℝ (Fin 3)`，让第 2 项的线性泛函能用：`ker ℓ` 必须**过原点**，
  所以切面要摆在 `{x₀ = 0}` 上并让 `M` 就是原点）：
  `A = (0,1,0)`、`B = (0,0,1)`、`C = (-1,0,0)`、`D = (1,0,0)`、`M = (0,0,0)`、`ℓ = ` 第一坐标。
  `ℓ C = -1 < 0 < 1 = ℓ D`，`ℓ` 在 `A,B,M` 上为零，第 2 项
  `convexHull_insert_inter_convexHull_insert_of_separating` 直接适用，给 `C₁ ∩ C₂ = F`。
  三组仿射无关（`{A,B,C,D}`、`{A,B,C,M}`、`{A,B,D,M}`）都成立，行列式分别非零。
- **弧只有一个锥顶**：`A = coneSet p {v, w}`（从 `p` 出发的两条直线段），`p ∈ openSimplex{A,B,C,M}`。
  这样并这一对 `(conv T, coneSet p {v,w})` 恰是第 16 节的形状。
  `C₁` 一侧是 `coneSet p {v, z}`（`z` 是 `[p,w]` 穿过 `F` 的点），也是第 16 节的形状。
  `C₂` 一侧是**单段** `[z,w]`；它仍能套第 16 节，因为取 `q ∈ (z,w)` 有
  `coneSet q {z,w} = [q,z] ∪ [q,w] = [z,w]`。

### 拼装还缺的（**未开始，不报区间**）

1. **线段劈分**：`segment q z ∪ segment q w = segment z w`（`q` 在 `z`、`w` 之间）。
   已查：Mathlib 的 `Analysis/Convex/Segment.lean` **没有**这条，树里也没有
   （`PlanarFreeFace.lean:47` 是三角形边界的同形写法，不是劈分）。这是 `C₂` 一侧的必需品。
2. **并等式** `convexHull{A,B,C,M} ∪ convexHull{A,B,D,M} = convexHull{A,B,C,D}`。
   第 2 项只给交不给并。数学上直接：把 `x = αA+βB+γC+δD` 在 `γ ≥ δ` 时改写成
   `αA+βB+(γ-δ)C+2δM`（系数和仍为 1、仍非负），反之对称。
3. 三组仿射无关的 Lean 验证、三处 `openSimplex` 成员资格、以及三条"弧与各块的交恰为某段"的
   重心坐标计算。
4. 第 2 项**不要求** `insert a F` 仿射无关而第 16 节**要求**，拼装时要单独提供（上一节已记）。

以上都未在 Lean 里试过，按规则不报行数区间。第 3、4 步同样未开始。

## 19. 2026-09-18 模型子项 1 — done：线段在中间点处劈分（`SegmentSplit.lean`）

`segment_union_segment_of_mem_segment`：设 `q ∈ segment ℝ z w`，则

    segment ℝ q z ∪ segment ℝ q w = segment ℝ z w

**独立模块、无 PL 内容**，只要 `[AddCommGroup E] [Module ℝ E]`（不要有限维、不要范数），
端点情形也成立（`q = z` 时左边是 `{z} ∪ segment z w`）。上一节查到 Mathlib 的
`Analysis/Convex/Segment.lean` 没有这条，故按协调者要求放在自己的文件里而不是埋进模型文件。

证明：`⊆` 由 `(convex_segment z w).segment_subset` 两次；`⊇` 把 `x = a•z + b•w`、`q = c•z + d•w`
按 `b ≤ d` 与 `d ≤ b` 分两支，分别取权 `b/d` 与 `(1-b)/(1-d)`，退化支 `d = 0`／`d = 1` 单独处理。

坑（都是本文件不导入 PL 模块造成的，记下来免得再踩）：
- 只 `import Mathlib.Analysis.Convex.*` 时 **`ℝ` 不可用**（`autoImplicit=false` 下直接报未知标识符），
  要显式 `import Mathlib.Data.Real.Basic`。
- `match_scalars`、`linarith`、`field_simp`、`ring` 各自要导入
  `Mathlib.Tactic.Module`、`Mathlib.Tactic.Linarith`、`Mathlib.Tactic.FieldSimp`、`Mathlib.Tactic.Ring`。
  平时写在 PL 模块里不用管，是因为 PL 那边传递导入了全套。
- 树里惯用的 `match_scalars <;> field_simp <;> ring` 在这里会被
  `linter.unnecessarySeqFocus` 报 warning（第二个 `<;>` 可以是 `;`），但改成 `;` 之后
  `field_simp` 已把部分目标解掉，`ring` 报 "No goals"。可用的写法是
  `match_scalars <;> (field_simp; try ring)`。

聚焦检查 `SegmentSplit` exit=0（7.4 秒）、零 warning；
`.lake/scratch/AuditHSegmentSplit.lean` 一项仅 `propext`、`Classical.choice`、`Quot.sound`。

按协调者提醒，这条同时供模型的两处使用：`C₂` 一侧的单段 `[z,w]` 要写成
`coneSet q {z,w} = [q,z] ∪ [q,w] = [z,w]`，以及并这一对的弧分解，不要手写两遍。

## 20. 2026-09-18 模型子项 2 — done：中点切开的并等式（`BallPairTwoSimplices.lean`）

`convexHull_insert_union_convexHull_insert_of_midpoint`：设 `c + d = m + m`（即 `m` 是 `c`、`d` 的中点，
写成加法式避免 `midpoint` API），`c, d, m ∉ F` 且两两不同，则

    convexHull ℝ (insert c (insert m F)) ∪ convexHull ℝ (insert d (insert m F))
      = convexHull ℝ (insert c (insert d F))

与子项 1 一样**不需要有限维**（`omit [FiniteDimensional ℝ E]` 通过），也不需要仿射无关。

- `⊆` 是单调性：两边的生成点都落在右边的包里，`m` 用 `m = (1/2)•c + (1/2)•d` 加凸性。
  两侧对称，抽成一条 `hside` 参数化的辅助断言，不写两遍。
- `⊇` 是内容：由 `Barycentric.lean:9 mem_convexHull_iff_exists_weights` 取权 `w`，
  按 `w d ≤ w c` 与 `w c ≤ w d` 分支，新权取
  `c ↦ w c - w d`、`m ↦ 2 * w d`、其余不变（另一支对称）。
  向量恒等式由 `h2 : (2 * t) • m = t • c + t • d`（从 `hm` 得）加 `module` 收尾。

坑（Finset 权重改写的通用教训）：
- 新权写成 `fun v => if v = c then _ else if v = m then _ else w v` 之后，
  `simp only [hvc, if_pos rfl]` **不работает**：`simp` 会把条件化成 `True` 但不消 `ite`，
  留下 `if True then _ else _`。正确写法是 `dsimp only` 之后 `split_ifs with h1 h2`，三支分别处理。
- `rw [Finset.sum_insert ...]` 之后项仍是未 β 归约的 lambda 应用，
  `rw [if_pos rfl]` 会找不到模式。**向量**求和那一支要先 `dsimp only`；
  但**标量**求和那一支 `rw` 完就已经归约好了，再写 `dsimp only` 会报
  "dsimp made no progress"。两支不一样，别照抄。
- `Finset.sum_congr rfl hcongr` 里 `hcongr : ∀ v ∈ F, (if ...) = w v` 可直接用于标量和；
  向量和要包一层 `fun v hv => by rw [hcongr v hv]`（目标是 `(if ...) • v = w v • v`，
  改写后 `rfl` 自动收）。

聚焦检查 `BallPairTwoSimplices` exit=0（10.5 秒）、零 warning；
`.lake/scratch/AuditHTwoSimplices.lean`（同时导入 `SegmentSplit`）五项仅
`propext`、`Classical.choice`、`Quot.sound`。

子项 3（三组仿射无关、三处 `openSimplex` 成员、三条弧与各块的交）与子项 4
（第 16 节要而第 2 项不给的仿射无关）**未开始，不报区间**；第 3、4 步同样未开始。

## 21. 2026-09-18 第七次 artifact 命中：显式坐标根本不需要

### 结论

第 18 节说"第 2 项的线性泛函要求 `ker ℓ` 过原点，所以切面必须摆在 `{x₀ = 0}` 且 `M` 必须是原点，
因此模型要用显式坐标"。**这个约束是我自己造出来的**：它只源于第 2 项把水平值固定成了 `0`。

把 `convexHull_insert_inter_convexHull_insert_of_separating` 从"零水平集"推广到**任意水平** `r`：

    {r : ℝ} (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = r) (ha : ℓ a < r) (hb : r < ℓ b)

证明几乎不变：三处凸集换成 `{ℓ ≤ r}`、`{r ≤ ℓ}`、`{ℓ = r}`；
组合那一步由 `ℓ (a + s • (z - a)) = (1 - s) * ℓ a + s * r`，
再 `linear_combination hx0` 得 `(1 - s) * (ℓ a - r) = 0`，由 `ℓ a ≠ r` 得 `s = 1`。
`convex_hyperplane`／`convex_halfSpace_le`／`convex_halfSpace_ge` 本来就带水平参数，改一个参数而已。

于是切面不必过原点，**模型不需要显式坐标，子项 4 的三个行列式计算全部消失**：

- 由 `SimplexBoundary.lean:400 exists_affineIndependent_openSimplex_subset` 取任意四面体
  `T = {A,B,C,D}`（仿射无关、`card = 4`）；
- `M := ` `C`、`D` 的中点；切面取 `{A,B,M}` 的仿射包；
- 存在非零线性 `ℓ` 在该 2 维方向空间上为零（`Submodule.exists_dual_map_eq_bot_of_lt_top`，
  F 车道 §19.115 已用过同一条），取 `r := ℓ A`；
- `ℓ M = (ℓ C + ℓ D)/2 = r` 自动成立；`ℓ C ≠ r`，否则 `ℓ` 在 `{A,B,C,D}` 上恒为 `r`，
  而四点仿射无关其仿射包是全空间，与 `ℓ ≠ 0` 矛盾。必要时交换 `C`、`D` 使 `ℓ C < r < ℓ D`。

聚焦检查 `BallPairTwoSimplices` exit=0（11.1 秒）、零 warning；审计五项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 一条给本层的常驻提示（协调者要求记下）

**凸性／线段层的"几何味"假设通常是多余的。** 本轮连续四条如此：

| 定理 | 我以为要 | 实际要 |
|---|---|---|
| `convexHull_insert_inter_convexHull_insert_of_separating` | 仿射无关 + 有限维 + 零水平 | 都不要，任意水平 |
| `convexHull_insert_union_convexHull_insert_of_midpoint` | 仿射无关 + 有限维 | 都不要 |
| `segment_union_segment_of_mem_segment` | 范数 + 有限维 | 只要实模 |
| `coneSet_empty` | 有限维 | 不要 |

分离／取中这类陈述本质是模块论事实，带着几何假设只会让它们更难复用。
下一个车道不要凭反射把这些假设加回去；写完先试 `omit`。

### 另外两条（不重新发现的代价很高）

- `SegmentSplit.lean` 不导入任何 PL 模块，于是 `autoImplicit=false` 下 **`ℝ` 是未知标识符**，
  且 `match_scalars`／`linarith`／`field_simp`／`ring` 要各自导入
  `Mathlib.Tactic.Module`／`.Linarith`／`.FieldSimp`／`.Ring`。
- 对 linter 可用的写法是 `match_scalars <;> (field_simp; try ring)`：
  树里惯用的 `<;> field_simp <;> ring` 触发 `linter.unnecessarySeqFocus`，
  但改成 `;` 后 `field_simp` 已解掉部分目标、`ring` 报 "No goals"。

### 子项 4 — 作废；子项 3 大幅缩小

子项 4（三组显式仿射无关）**不再需要**。子项 3 里三处 `openSimplex` 成员资格也不再是坐标计算，
改由存在性引理与中点直接给出。剩下的只有三条"弧与各块的交"仍要算，**未开始，不报区间**。
顺带记录：树里**没有**显式点集仿射无关的写法（全部走
`exists_affineIndependent_openSimplex_subset` 或 `affineIndependent_of_subset`），
所以真要显式坐标的话是结构性摩擦而非 `norm_num` 级——这也是应当避开它的理由之一。

## 22. 2026-09-18 弧与各块的交 — done，作为可复用的线段引理（`SegmentSplit.lean`）

上一节把显式坐标消掉之后，"三条弧与各块的交"不再是坐标计算，而是**线段与半空间／超平面求交**。
交付五条，全部只要 `[AddCommGroup E] [Module ℝ E]`（承接第 21 节的常驻提示：不要加几何假设）：

- `segment_inter_le_eq_singleton`（`ℓ z = r`、`r < ℓ w`）：`segment ℝ z w ∩ {ℓ ≤ r} = {z}`。
- `segment_inter_ge_eq_singleton`（`ℓ z = r`、`ℓ p < r`）：`segment ℝ z p ∩ {r ≤ ℓ} = {z}`。
  由上一条对 `-ℓ`、`-r` 取负得到，不重证。
- `segment_inter_le_eq_segment`（`z ∈ segment p w`、`ℓ z = r`、`ℓ p ≤ r`、`r < ℓ w`）：
  `segment ℝ p w ∩ {ℓ ≤ r} = segment ℝ p z`。
  **证明复用第 19 节的劈分**：先 `← segment_union_segment_of_mem_segment` 把 `segment p w`
  拆成 `segment z p ∪ segment z w`，分配交，前半整个落在半空间（凸性），后半由第一条退成 `{z}`，
  并回去即得。这正是协调者提醒的"劈分只证一次、两处都用"。
- `segment_inter_ge_eq_segment`：同上取负，得 `segment ℝ p w ∩ {r ≤ ℓ} = segment ℝ z w`。
- `segment_inter_eq_singleton`（两侧严格）：`segment ℝ p w ∩ {ℓ = r} = {z}`，
  由 `{ℓ = r} = {ℓ ≤ r} ∩ {r ≤ ℓ}` 接前两条。

这三条恰好对应模型要的三处：`C₁ ∩ 弧`（le 版）、`C₂ ∩ 弧`（ge 版）、`公共面 ∩ 弧`（eq 版）。

坑：`segment ℝ z w ∩ {ℓ ≤ r} = {z}` 里的 `b = 0` 不能直接 `nlinarith`——
`a * r` 是两个变量的积，linarith 当原子，`hab` 代不进去。要先
`have ha' : a = 1 - b := by linarith; rw [ha'] at hx`，再
`nlinarith [mul_pos h (sub_pos.mpr hw)]`。另外 `Set.mem_setOf_eq` 已废弃，用 `Set.mem_ofPred_eq`。

聚焦检查 `SegmentSplit` exit=0（7.5 秒）、零 warning；
`.lake/scratch/AuditHSegmentSplit.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 组装还缺的一步（已定位，未开始，不报区间）

把上面三条接到模型上，还差一条"超平面截痕"引理：`C₂ ⊆ {r ≤ ℓ}` 只给单向，
要得到 `C₁ ∩ segment p w = segment p z` 还需要
**`convexHull (insert a F) ∩ {ℓ = r} = convexHull F`**（`ℓ` 在 `F` 上为 `r`、`ℓ a ≠ r`）。
它其实是第 17 节 `convexHull_insert_inter_convexHull_insert_of_separating` 证明**内部**已经做出来的那一步，
只是没单独导出；把它抽出来之后，分离定理本身也应当由它加两条半空间包含直接得到。
建议下次先做这个重构，再拼三对与并对。第 3、4 步仍未开始。

## 23. 2026-09-18 重构：把超平面截痕从分离定理里抽出来

第 22 节末尾定位的那一步现已导出。四条，全部 `omit [FiniteDimensional ℝ E]`：

- `convexHull_insert_inter_hyperplane`（`ℓ` 在 `F` 上为 `r`、`ℓ a ≠ r`）：
  `convexHull ℝ (insert a F) ∩ {ℓ = r} = convexHull ℝ F`。
  **这才是内容**：把 `x` 写成 `a + s • (z - a)`，`ℓ x = (1-s) * ℓ a + s * r = r` 经
  `linear_combination` 得 `(1-s)(ℓ a - r) = 0`，由 `ℓ a ≠ r` 得 `s = 1`。
  注意假设只要 `ℓ a ≠ r`（不分上下侧），比分离定理的 `ℓ a < r` 弱。
- `convexHull_insert_subset_halfSpace_le` / `_ge`：两条半空间包含，也单独导出。
- `convexHull_insert_inter_convexHull_insert_of_separating` 现在**由上面三条合成**，正文只剩六行：
  交点两侧夹出 `ℓ x = r`，再落进截痕引理。

### 常驻检查之二（协调者要求与第 21 节的假设表并列记录）

**证明内部做了实事而陈述没有暴露时，先抽出来再往上盖。**
今天三个车道共四例：本条（分离定理内部的截痕）、
`ConeAmbientExtension.lean:40-49`（内部证出"锥上恒等"却不写进结论，见第 9 节）、
以及 F 车道的两对包装（`PLImage.lean:113` 对 `:140`，`PLImage.lean:113` 对
`AffineImageTransport.lean:13`）。这条的收益仅次于 artifact 检查。
识别信号：证明里出现一个与结论形状不同的中间 `have`，且它本身是个可陈述的等式或包含关系。

聚焦检查 `BallPairTwoSimplices` exit=0（10.9 秒）、零 warning；
`.lake/scratch/AuditHTwoSimplices.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 组装状态

三对与并对**未开始**。手上已齐的零件：
第 16 节 `isPLBallPair_convexHull_of_mem_openSimplex`（单纯形＋内点＋两个边界点 ⟹ 标准对）、
第 17 节 `isPLBallPair_convexHull_singleton_of_mem_openSimplex`（`(F, {z})` 那一对）、
第 20 节并等式、第 21 节任意水平的分离、本节截痕与两条半空间、
第 19/22 节五条线段引理。缺的只是把它们按第 18 节的构型接起来（选点＋三对＋并对），
以及之后的第 3、4 步。**未开始，不报区间。**

## 24. 2026-09-18 组装受阻：`IsPLBallPair` 的子链条件过强（诊断，无 Lean 改动）

按第 18 节构型接线时撞上一个**真障碍**，不是工作量问题。记清楚，免得下次照着接。

### 矛盾

第 16 节 `isPLBallPair_convexHull_of_mem_openSimplex` 经 `isPLBallPair_coneSet_arc` 要求
子链 `J` 满足 `J.faces ⊆ L.faces`（`IsPLBallPair` 定义里的字段）。取 `L = simplexBoundary T₁` 时，
`SimplexBoundary.lean:37 simplexBoundaryFaces T = {τ | τ ⊆ T ∧ τ.Nonempty ∧ τ ≠ T}`，
所以 `J` 的面都是 `T₁` 的子集，`J.space` 只能是 `T₁` 若干面的并。
要 `J.space = {v, z}`（两点），就必须 **`v`、`z` 都是 `T₁` 的顶点**。

但 `z` 是弧穿过公共面 `F` 的点，而 `(C₁∩C₂, C₁∩C₂∩A) = (conv F, {z})` 这一对要成立，
第 17 节 `isPLBallPair_convexHull_singleton_of_mem_openSimplex` 要求 **`z ∈ openSimplex F`**，
即 `z` 在三角形 `F` 的**相对内部**，绝不是顶点。两条要求直接冲突。

`z` 不能改成顶点：若 `z` 是 `F` 的顶点，则 `conv F` 作为从 `z` 出发的锥，其底是对边——
是 1-**球**不是 1-**球面**，`IsPLBallPair 1 0` 的 `IsPLSphere m L.space` 条款就不成立。
所以 `z` 必须内部，矛盾是实的。

### 诊断：定义里的条件比内容强

查了 `BallPair.lean` 里 `hJL` 的全部三处用法：

- `IsPLBallPair.subset`（:21）只用 `space_mono_of_faces_subset hJL`，即**只要 `J.space ⊆ L.space`**；
- `IsPLBallPair.of_isPLHomeomorphOn`（:44）只是原样传递；
- `isPLBallPair_coneSet_of_isPLSphere`（:69–71）真用到面包含，用来导出
  `Finite J.faces` 与 `hL.of_faces_subset hJL : IsConeBase p J`。

所以**定义**里的 `J.faces ⊆ L.faces` 可以弱化成 `J.space ⊆ L.space`（甚至直接换成集合 `X ⊆ L.space`），
只有**生产者**需要把 `IsConeBase p J` 与 `Finite J.faces` 改成显式假设。
这与第 15 节"锥形 ⟹ 与锥对 PL 同胚"是同一类毛病：定义携带了比它的内容更强的条件，
下游构造因此被挡住。

### 两条出路（推荐 B）

- **A：细分链。** artifact 检查这次是**正命中**——树里**有**星形细分：
  `StellarSphere.lean:144 stellarComplex`，且 `:159 stellarComplex_space` 给
  `(stellarComplex …).space = (simplexBoundary (T.erase a) hT').space`，
  即细分后空间不变、而 `c ∈ openSimplex (T \ σ₀)` 成了顶点。正合所需。
  但还要 `IsConeBase p₁ (stellarComplex …)`，正确工具是
  `ConeBase.lean:56 IsConeBase.of_isSubdivision`，它要
  `IsSubdivision (stellarComplex …) (simplexBoundary …)`——**树里没有**（已 grep 确认）。
- **B：弱化定义**（推荐）。把 `IsPLBallPair` 的 `J.faces ⊆ L.faces` 换成集合层的
  `X ⊆ L.space`，生产者 `isPLBallPair_coneSet_of_isPLSphere` 补 `IsConeBase p J`、`Finite J.faces`
  两个显式假设。改动局限在 `BallPair.lean` 与四个消费者
  （`BallPairModel`、`BallPairSimplex`、`BallPairTwoSimplices`、`ConeDiskPairExtension`），
  不依赖任何尚不存在的细分引理。

两条都**未开始，不报区间**。第 3、4 步同样未开始，因此还没有能告诉 F 的输出形状。

## 25. 2026-09-18 路线 B — done：`IsPLBallPair` 的子链改成集合层

### 改动

定义里 `J : SimplicialComplex` ＋ `J.faces ⊆ L.faces` 换成 `X : Set E` ＋ `X ⊆ L.space`：

    IsPLBallPair m k P Q := ∃ p L (_ : IsConeBase p L) f (X : Set E),
      L.faces.Finite ∧ X ⊆ L.space ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      IsPLHomeomorphOn f (coneSet p L.space) P ∧ f '' coneSet p X = Q

**依据**（协调者要求以此形式记录）：查了 `hJL` 在 `BallPair.lean` 里的全部三处用法，
两处（`IsPLBallPair.subset`、`of_isPLHomeomorphOn`）只用到 `J.space ⊆ L.space`，
第三处 `isPLBallPair_coneSet_of_isPLSphere` 是**生产者**，是面包含的唯一消费者。
**定义携带一个只有某个生产者需要的条件，不是更强的定义，而是假设放错了位置**，并且会挡住下游构造。
本次会话第三次同类：第 15 节的锥形式、第 23 节分离定理多带的 `ℓ a < r`、以及这条。
三者是同一课的三个角度：**假设要放在用到它的地方，不是放在写起来顺手的地方。**

- `isPLBallPair_coneSet` 现在是集合层的原语（`{X : Set E} (hXL : X ⊆ L.space)`）；
  `isPLBallPair_coneSet_of_isPLSphere` 保持原签名，内部用
  `space_mono_of_faces_subset hJL` 转成集合包含。因此
  `isPLBallPair_coneSet_arc`、`isPLBallPair_convexHull_of_mem_openSimplex`、
  `exists_isPLHomeomorphOn_coneSet_pair(_of_disk_marked)`、`exists_isPLHomeomorphOn_of_isPLSphere_pair`
  **签名全部不变**，下游零改动。
- 副产品：`isPLBallPair_convexHull_singleton_of_mem_openSimplex` 不再需要空复形 `⊥`
  与 `space_bot`，直接取 `X := (∅ : Set E)`，`Set.empty_subset` 加 `coneSet_empty` 即可。
  第 17 节记的"空复形"那条依赖消失了。

五个模块全部 exit=0、零 warning：`BallPair`（8.6 秒）、`BallPairModel`（14.6 秒）、
`BallPairSimplex`（10.2 秒）、`BallPairTwoSimplices`（11.0 秒）、`ConeDiskPairExtension`（10.8 秒）。
`.lake/scratch/AuditHRouteB.lean` 十项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 路线 A 的缺口（留给可能需要星形细分的车道）

路线 A（细分链）数学上更好，但缺一条：树里**有** `StellarSphere.lean:144 stellarComplex`
与 `:159 stellarComplex_space`（细分后空间等于 `simplexBoundary (T.erase a)` 的空间，
且 `c ∈ openSimplex (T \ σ₀)` 成为顶点），**没有**
`IsSubdivision (stellarComplex …) (simplexBoundary …)`（已 grep 确认）。
`ConeBase.lean:56 IsConeBase.of_isSubdivision` 正等着它。
**这一条是本树与"一般星形细分论证"之间唯一的距离**，别的车道若要用星形细分，先补它。

### 组装还缺的一件（未开始，不报区间）

弱化之后 `C₁` 那一对的子链可以取集合 `{v, z}`（不必是顶点），但还需要
`IsPLBall 1 (coneSet p {v, z})` 的证书。现成路线：`{v,z}` 恰是 `simplexBoundary {v,z}` 的空间
（二元 `Finset` 的边界面就是两个顶点），于是 `isPLBallPair_coneSet_of_isPLSphere` 可用，
但要 `IsConeBase p (simplexBoundary {v,z})`，这需要 `p`、`v`、`z` **不共线**——
是构型上的真非退化条件，拼装时必须显式给出，不能省。

## 26. 2026-09-18 构型的非退化条件：一次列全（诊断，无 Lean 改动）

协调者要求"这一轮把兄弟条件一次查全，不要一轮一条"。查全了，并且**纠正了我自己上一节的提法**。

### 更正：不是"不共线"，是"径向单射"

上一节末尾我说 `C₁` 那一对要 `p`、`v`、`z` **不共线**。**这是错的**，而且如果照此施工，
`C₂` 那一对会直接做不下去。

`Cone.lean:10` 的定义是

    IsRadiallyInjective p S := ∀ x ∈ S, ∀ y ∈ S, ∀ t, 0 < t → y = p + t • (x - p) → y = x

对 `S = {v, z}`（`v ≠ z`）展开就是：**`v` 与 `z` 不在从 `p` 出发的同一条射线上**。

- `C₁`：顶点 `p` 在 `C₁` 内部，`v`、`z` 在 `∂C₁` 上。此时不共线蕴含径向单射，两者都行。
- `C₂`：顶点 `q` 取在线段 `(z, w)` **内部**，于是 `q`、`z`、`w` **恰恰共线**。
  "不共线"在这里是**假的**；但径向单射**成立**，因为 `z` 与 `w` 落在从 `q` 出发的**相反**两条射线上。

所以三对共用的非退化条件只有一条，就是 `IsRadiallyInjective p {v, z}`（外加 `p ∉ {v, z}`）。
它同时覆盖"顶点在外、两端点张开"与"顶点在两端点之间"两种情形，而"不共线"只覆盖前者。
按协调者的判据，这属于**限定模型覆盖哪些构型**而不是让定理不可陈述，故继续。

### 四对所需条件的完整清单

设大四面体 `T = {A,B,C,D}`、`M` 为 `C`、`D` 中点、`F = {A,B,M}`、`T₁ = insert C F`、`T₂ = insert D F`。

| 对 | 顶点 | 子链 | 所需条件 |
|---|---|---|---|
| 并 `(conv T, 弧)` | `p ∈ openSimplex T` | `{v, w} ⊆ ∂(conv T)` | `v ≠ w`；`IsRadiallyInjective p {v,w}`；`p ∉ {v,w}` |
| `(C₁, C₁∩弧)` | `p ∈ openSimplex T₁` | `{v, z} ⊆ ∂C₁` | `v ≠ z`；`IsRadiallyInjective p {v,z}`；`p ∉ {v,z}` |
| `(C₂, C₂∩弧)` | `q ∈ openSimplex T₂`，`q` 在 `(z,w)` 内 | `{z, w} ⊆ ∂C₂` | `z ≠ w`；径向单射由"`q` 在两点之间"**自动成立**；`q ∉ {z,w}` |
| `(conv F, {z})` | `z ∈ openSimplex F` | `∅` | 无额外条件（第 17 节已闭合） |

注意 `p ∈ openSimplex T₁` 蕴含 `p ∈ openSimplex T`？**不**自动，要分别给或单独证；
`C₁ ⊆ conv T` 只给包含，开胞腔的包含要另说。这一条也要在构型里写清楚。

### 一个生产者可覆盖前三对

三者形状相同：`IsPLBallPair m 1 (coneSet p L.space) (segment ℝ p v ∪ segment ℝ p z)`，
其中 `{v,z} ⊆ L.space`、`IsPLSphere m L.space`、`IsConeBase p L`。
经第 25 节弱化后子链可取**集合** `{v,z}`，不必是 `L` 的顶点，所以不需要细分。
缺的只是 `IsPLBall 1 (coneSet p {v,z})` 这一张证书，路线是
`{v,z} = (simplexBoundary ({v,z} : Finset E) _).space`（二元 Finset 的边界面就是两个顶点），
再 `isPLBallPair_coneSet_of_isPLSphere`，其 `IsConeBase p (simplexBoundary {v,z})` 的三个字段分别由
`p ∉ {v,z}`、两个二元集的仿射无关、以及上面的径向单射给出。

**未验证的一点**：`AffineIndependent ℝ ((↑) : ({v,z} : Finset E) → E)`（两个不同点仿射无关）
在本树里搜不到（只找到 `affineIndependent_of_subsingleton` 的单点版）。Mathlib 可能有成对版本，
**未确认**，不作为"缺失"记录，只标为待查。

本节未写 Lean，未开始三对的拼装，不报区间。

## 27. 2026-09-18 一个生产者覆盖三对弧（`BallPairArc.lean`）— done

第 26 节说三对形状相同、可共用一个生产者。现已建成，六条：

- `affineIndependent_coe_pair_set` / `affineIndependent_coe_pair`：两个不同点仿射无关，
  集合版与 `Finset` 版。上一节标为"待查"的那条**存在**：
  Mathlib `LinearAlgebra/AffineSpace/Independent.lean:795 affineIndependent_of_ne`
  （给 `![p₁, p₂]`），经 `.range` 与 `Set.range ![a,b] = {a,b}` 桥到 coe 版本。
- `simplexBoundary_pair_space`：`(simplexBoundary {v,z} _).space = {v, z}`。
  二元 `Finset` 的边界面就是两个顶点。
- `isConeBase_simplexBoundary_pair`：`v ≠ z`、`p ≠ v`、`p ≠ z`、
  `IsRadiallyInjective p {v,z}` ⟹ `IsConeBase p (simplexBoundary {v,z} _)`。
  三个字段分别由空间等式、两个二元集的仿射无关（面只能是两个单点，用 `Finset.card_eq_one`
  从"真非空子集"推出）、以及径向单射给出。
- `isPLBall_one_coneSet_pair`：`IsPLBall 1 (coneSet p {v, z})`。即**从一点对 0-球面的锥是 1-球**。
- `isPLBallPair_coneSet_arc_of_radial`：**三对共用的生产者**。设 `IsConeBase p L`、
  `IsPLSphere m L.space`、`{v,z} ⊆ L.space`，加第 26 节那四条非退化条件，则

      IsPLBallPair m 1 (coneSet p L.space) (segment ℝ p v ∪ segment ℝ p z)

  子链取**集合** `{v,z}`，不要求是 `L` 的顶点——这正是第 25 节弱化换来的，
  于是 `C₁`（`z` 在公共面内部）与 `C₂`（顶点 `q` 与两端点共线）都能套同一条。

坑：`Set.range ![a,b]` 经 `simp` 归一成 `{b,a}`，与 `{a,b}` 差一个 `Set.pair_comm`，
直接 `by simp` 不收；用 `ext` 加 `fin_cases i <;> simp` 与 `⟨0, rfl⟩`／`⟨1, rfl⟩` 最稳。
`Finset.erase_insert_of_ne` 的方向容易搞反（`(insert a s).erase b` 要 `a ≠ b`），
`{v,z}.erase z = {v}` 用 `ext` 加 `Finset.mem_erase` 手写反而省事；
`{v,z}.erase v = {z}` 则是现成的 `Finset.erase_insert`。
最后两条的 `[DecidableEq E]` 只在证明里用到，要用证明内 `classical`。

聚焦检查 `BallPairArc` exit=0（10.1 秒）、零 warning；
`.lake/scratch/AuditHBallPairArc.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 下一步与一个待定

三对与并对的拼装现在只差"选点并验证第 26 节那张表"。其中一条仍**未定**：
`p ∈ openSimplex T₁` 不蕴含 `p ∈ openSimplex T`（`C₁ ⊆ conv T` 只给包含）。
两种处理：(a) 在构型里把 `p ∈ openSimplex T` 与 `p ∈ openSimplex T₁` **都**写成假设；
(b) 证一条"切开后小单纯形的开胞腔含于大单纯形的开胞腔"。
(a) 是老实且够用的，建议先取 (a)，需要时再补 (b)。**未开始，不报区间。**

## 28. 2026-09-18 四对的生产者全部到位（`BallPairArc.lean`）

`isPLBallPair_convexHull_arc_of_radial`：设 `T` 仿射无关、`T.card = n + 2`、`p ∈ openSimplex T`、
`{v, z} ⊆ (simplexBoundary T hT).space`，加第 26 节的四条非退化条件，则

    IsPLBallPair n 1 (convexHull ℝ T) (segment ℝ p v ∪ segment ℝ p z)

证明与第 16 节同构：拼出 `IsConeBase`、`IsPLSphere`，喂上一节的
`isPLBallPair_coneSet_arc_of_radial`，再用 `coneComplex_simplexBoundary_space` 把锥换成 `convexHull`。
与第 16 节的差别只有一处，但是关键：子链是**集合** `{v,z}` 而不是子复形，
所以 `v`、`z` 不必是 `T` 的顶点。

**这一条把四对全部覆盖：**

| 对 | 用法 |
|---|---|
| 并 `(conv T, 弧)` | 本条，取 `T`、顶点 `p`、端点 `{v, w}` |
| `(C₁, C₁∩弧)` | 本条，取 `T₁ = insert c (insert m F)`、顶点 `p`、端点 `{v, z}` |
| `(C₂, C₂∩弧)` | 本条，取 `T₂ = insert d (insert m F)`、顶点 `q`、端点 `{z, w}` |
| `(conv Fm, {z})` | 第 17 节 `isPLBallPair_convexHull_singleton_of_mem_openSimplex` |

聚焦检查 `BallPairArc` exit=0（9.4 秒）、零 warning；
`.lake/scratch/AuditHBallPairArc.lean`（同时导入 `BallPairTwoSimplices`，四个生产者共存）
七项仅 `propext`、`Classical.choice`、`Quot.sound`。

审计文件本身踩了一次：`isPLBallPair_convexHull_singleton_of_mem_openSimplex` 在
`BallPairTwoSimplices` 里，`BallPairArc` 不导入它，于是 `#print axioms` 报 unknown constant。
**审计文件报 unknown constant 是导入不全，不是声明不存在**，别误判成代码问题。

### 组装还剩两件（未开始，不报区间）

1. **选点并核验**：给出满足第 26 节那张表的具体构型（`T`、`c`、`d`、`m`、`F`、`p`、`q`、`z`、`v`、`w`），
   四对即刻由上表得到。按第 27 节的决定，`p ∈ openSimplex T` 与 `p ∈ openSimplex T₁` 都写成假设。
2. **弧与各块的交**：还要证 `conv T₁ ∩ 弧 = segment p v ∪ segment p z` 等三条，
   才算"三对确实是 `(C, C∩A)` 那三对"。零件齐了：
   `conv T₁ ⊆ {ℓ ≤ r}`（第 23 节半空间）、`conv T₂ ∩ {ℓ = r} = conv Fm`（第 23 节截痕）、
   第 22 节五条线段交引理。第 3 步要的是这一件。

## 29. 2026-09-18 弧与三块的交 — done（`SegmentSplit.lean`），并发现一条构型条件

协调者要求"先做第 2 件，再选点"。做对了：**这三条恒等式逼出一条构型条件，而且它排除了一类选点。**

### 交付（六条，全部只要 `[AddCommGroup E] [Module ℝ E]`）

弧写成 `segment ℝ p c ∪ segment ℝ p d`（从顶点 `p` 出发到两个远端点），`z` 是 `segment p d` 与
`{ℓ = r}` 的交点。

- `segment_subset_of_mem_segment` / `segment_right_subset_of_mem_segment`：
  `z ∈ segment p d` ⟹ `segment p z ⊆ segment p d`、`segment z d ⊆ segment p d`。
- `segment_subset_halfSpace_lt`：两端 `ℓ < r` ⟹ 整段 `ℓ < r`。
- `inter_arc_of_subset_halfSpace_le`：`P ⊆ {ℓ ≤ r}`、`segment p c ⊆ P`、`segment p z ⊆ P` ⟹
  `P ∩ 弧 = segment ℝ p c ∪ segment ℝ p z`。（`C₁` 那一块）
- `inter_arc_of_subset_halfSpace_ge`：`P ⊆ {r ≤ ℓ}`、`segment z d ⊆ P` ⟹
  `P ∩ 弧 = segment ℝ z d`。（`C₂` 那一块）
- `inter_arc_of_subset_hyperplane`：`P ⊆ {ℓ = r}`、`z ∈ P` ⟹ `P ∩ 弧 = {z}`。（公共面那一块）

三条都靠第 22 节的线段交引理，再加"`P ∩ segment p c` 为空"（`ℓ` 在该段上恒 `< r`，而 `P` 在 `{r ≤ ℓ}` 或 `{ℓ = r}` 里）。

### 逼出来的构型条件：**远端点必须严格在各自一侧**

后两条都要 **`ℓ c < r` 严格**（不是 `≤`）。这直接排除了一类选点：
公共面 `Fm = insert m F` 的顶点上 `ℓ = r`，所以**远端点不能取 `F` 里的那两个顶点**。
取 `c` 与 `d`（被切开的那条棱的两个端点）就正好：`ℓ c < r < ℓ d` 已经是第 21 节分离条件的一部分。

于是构型里的 `v`、`w` 不再自由：**`v := c`、`w := d`**，弧就是 `c → p → z → d` 的折线。
这也让第 26 节表里"`{v,w} ⊆ (simplexBoundary T).space`"变得平凡（`c`、`d` 是 `T` 的顶点）。

三条恒等式所需的其余包含关系都能从构型直接给出：
`segment p c ⊆ conv T₁`（两端都在，凸）、`segment p z ⊆ conv T₁`（`z ∈ conv Fm ⊆ conv T₁`）、
`segment z d ⊆ conv T₂`、`z ∈ conv Fm`；`P` 的三个半空间／超平面包含由第 23 节给。

聚焦检查 `SegmentSplit` exit=0（7.6 秒）、零 warning；
`.lake/scratch/AuditHArcInter.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

坑：`P ⊆ {x | r ≤ ℓ x}` 应用后得到的是 `x ∈ {x | r ≤ ℓ x}`，
直接喂给 `not_le.mpr`／`ne_of_lt` 会类型不匹配（setOf 不自动展开）。
写成带类型标注的 `have h1 : r ≤ ℓ x := hP hxP` 再 `linarith` 即可。

### 下一步

第 1 件（选点并核验第 26 节的表，现在 `v`、`w` 已被钉成 `c`、`d`）与第 3 步。**未开始，不报区间。**

## 30. 2026-09-18 模型拼装：并对与 `C₁` 对已接通（`BallPairCutModel.lean`）

构型以 `section` 变量给出：`F` 两点、`c`、`d`、`m`（`c`、`d` 中点）、线性 `ℓ` 在 `insert m F` 上为 `r`、
`ℓ c < r < ℓ d`、`z ∈ openSimplex (insert m F)`、`z ∈ segment ℝ p d`，以及各 `Finset` 的仿射无关与不属于关系。
按第 29 节的结论，远端点已被钉成 `c` 与 `d`，弧就是 `segment ℝ p c ∪ segment ℝ p d`。

- `vertex_mem_simplexBoundary_space`：`v ∈ T`、`2 ≤ T.card` ⟹ `v ∈ (simplexBoundary T hT).space`。
  即"顶点在边界球面上"，反复要用。不需要 `DecidableEq`，也不需要有限维。
- `isPLBallPair_cut_union`：**并对**
  `IsPLBallPair 2 1 (convexHull (insert c (insert d F))) (segment ℝ p c ∪ segment ℝ p d)`。
- `isPLBallPair_cut_left`：**`C₁` 对加它的交恒等式**，一次给两条：

      IsPLBallPair 2 1 (convexHull (insert c (insert m F))) (segment ℝ p c ∪ segment ℝ p z)
      convexHull (insert c (insert m F)) ∩ 弧 = segment ℝ p c ∪ segment ℝ p z

  两条分别由第 28 节的生产者与第 29 节的 `inter_arc_of_subset_halfSpace_le` 给出；
  所需的 `ℓ z = r`、`ℓ p ≤ r`、两条线段落在 `conv T₁` 里，都由构型直接算出
  （`insert m F` 是 `T₁` 的真面，故 `z` 既在超平面上又在 `∂C₁` 上）。

聚焦检查 `BallPairCutModel` exit=0（10.5 秒）、零 warning；
`.lake/scratch/AuditHCutModel.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。

坑：`inter_arc_of_subset_halfSpace_le` 在 `SegmentSplit.lean`，而 `BallPairArc` 那条链不导入它，
于是报 `unknown identifier`。这正是第 28 节记下的那条——**未知标识符是导入不全，不是声明不存在**，
本轮自己撞了一次，补 `import ...SegmentSplit` 即解决。
另外 `include` 写成整节通用会让不用某假设的定理报 `unusedSectionVars`，要**逐定理** `include`。

### 为什么"先做交恒等式再选点"应当作为规则（协调者要求把理由而不只是规则写下来）

第 29 节的三条恒等式需要 `ℓ c < r` **严格**；公共面的两个顶点上 `ℓ = r` **恰好相等**。
如果先选点，很可能把弧的远端点选在公共面的顶点上——那样三条恒等式全部不成立，
而且要到拼装时才发现，届时坐标已经钉死、构型已经写满。
先做恒等式则相反：这条条件**直接把远端点定成 `c` 与 `d`**，构型少两个自由参数，
第 26 节表里"`{v,w} ⊆ (simplexBoundary T).space`"那一行也随之平凡化。
**早发现的约束会变成简化，晚发现的同一约束会变成返工。**

### 剩余

`C₂` 对（用第 28 节生产者取顶点 `q ∈ openSimplex T₂ ∩ segment ℝ z d`，再用第 19 节把
`segment q z ∪ segment q d` 并成 `segment z d`）与公共面对（第 17 节）尚未接，
两者与 `isPLBallPair_cut_left` 同型，属机械重复；
另外第 20/21 节的并等式与交等式尚未并入本模块的结论。第 3、4 步未开始。**不报区间。**

## 31. 2026-09-18 模型拼装完成：四对与两条集合等式（`BallPairCutModel.lean`）

在第 30 节的构型上补齐，新增一个构型条件 `hℓp : ℓ p < r`（顶点严格落在近侧），
这是 `C₂` 与公共面那两条交恒等式要的严格不等号，属于对 `p` 的选点条件。

- `isPLBallPair_cut_right`：**`C₂` 对加交恒等式**。生产者给的是
  `segment ℝ q z ∪ segment ℝ q d`，再由第 19 节 `segment_union_segment_of_mem_segment hqs`
  （`q ∈ segment ℝ z d`）并成 `segment ℝ z d`；交恒等式用第 29 节的 ge 版本。
- `isPLBallPair_cut_face`：**公共面对加交恒等式**，第 17 节加第 29 节的超平面版本。
- `convexHull_cut_union`：`conv T₁ ∪ conv T₂ = conv T`（第 20 节）。
  所需的 `c ∉ F`、`c ≠ m`、`d ≠ m`、`c ≠ d` 都从 `hcdF`／`hcmF`／`hdmF` 推出，不必另设变量。
- `convexHull_cut_inter`：`conv T₁ ∩ conv T₂ = conv Fm`（第 21 节）。
  这两条都不需要有限维，加 `omit`。

**四对与两条等式齐了**，即第 3 步要的模型数据全部到位。

聚焦检查 `BallPairCutModel` exit=0（15.7 秒）、零 warning；
`.lake/scratch/AuditHCutModel.lean` 七项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 两个坑

1. `unknown identifier` 那条**又踩了一次**，而且是在第 28 节刚把它写成教训之后、由我自己踩的：
   `inter_arc_of_subset_halfSpace_le` 在 `SegmentSplit.lean`，`BallPairArc` 那条导入链不含它。
   补 `import` 即解决，没有任何东西缺失。
   **记下来不等于免疫**——下次看到 `unknown identifier` 先查导入，再想别的。
2. `(hFm : AffineIndependent ℝ ((↑) : (insert m F : Finset E) → E))` 这个 binder
   **单独一个 `insert` 时**会报 `cannot coerce x to type Finset E → Finset E → E`，
   而两层 `insert`（`insert c (insert d F)`）写法相同却没问题。
   把到 Sort 的强制写成显式 `↥`（`((↑) : ↥(insert m F : Finset E) → E)`）即通过。
   不清楚根因，但现象与修法都确切，下次直接写 `↥`。

### 剩余

第 3 步（相对黏合，照 `BallGluing.lean:11` 模板，用 `IsPLBallPair.of_isPLHomeomorphOn` 把模型搬到
`(C ∪ D, A)`，用 M2 `exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` 提供
`PLPiece.lean:83` 要的逐点相等）与第 4 步（沿弧的链归纳，`arcChainFace_subset_iff`）
**未开始，不报区间**。给 F 的输出形状仍未定。

## 32. 2026-09-18 第 3 步的前置：M2 与锥对延拓也要把子链改成集合

动手拼第 3 步前先核对 M2 的形状，发现**同一个毛病还在上一层**：
`ConeDiskPairExtension.lean` 的 `exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` 与
`BallPair.lean` 的 `exists_isPLHomeomorphOn_coneSet_pair` 仍带
`hJLc : J.faces ⊆ Lc.faces`，即第 25 节从 `IsPLBallPair` 里拿掉的那个子复形条件。

查证：两者的证明里 `J` **只**经 `J.space` 出现（`hJsplit`、`hgJ`、结论的像等式），
而 `exists_isPLHomeomorphOn_coneSet_pair` 用 `hJL` 的唯一方式是
`space_mono_of_faces_subset hJL`。所以两者都可以直接换成集合 `X ⊆ Lc.space`。

这对第 3 步是**必需**的，不是整洁问题：第 3 步里 M2 的子链是弧与 `∂C` 的两个交点，
它们没有理由是 `∂C` 任何三角剖分的顶点——和第 24 节在 `C₁` 上遇到的完全同一件事。

改动：两条的 `{J J' : SimplicialComplex}` ＋ 面包含换成 `{X : Set E} {X' : Set F}` ＋
`X ⊆ Lc.space`；`exists_isPLHomeomorphOn_of_isPLSphere_pair` 内部补
`space_mono_of_faces_subset hJL` 转换，签名不变。

七个模块全部 exit=0、零 warning：`BallPair`（9.2 秒）、`ConeDiskPairExtension`（10.2 秒）、
`BallPairModel`（9.0 秒）、`BallPairSimplex`（9.6 秒）、`BallPairTwoSimplices`（11.7 秒）、
`BallPairArc`（10.0 秒）、`BallPairCutModel`（10.7 秒）。
`.lake/scratch/AuditHRouteB.lean` 十项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 第 3 步剩下的前置：模型的**存在性**

第 3 步照 `BallGluing.lean:11` 的模板，需要一个**存在性**的模型
（那里是 `exists_isPLBall_pair_with_disk_inter`），而第 31 节交付的四对是**参数化**的
（构型以 `section` 变量给出）。所以还差一条：

    ∃ (F : Finset E) (c d m p q z : E) (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ), <第 26/31 节的全部条件>

在 `finrank E = 3` 的空间里构造：由 `SimplexBoundary.lean:400
exists_affineIndependent_openSimplex_subset` 取四面体，取 `c`、`d` 为两个顶点、`m` 为中点、
`F` 为另两个顶点；`ℓ` 由 `Submodule.exists_dual_map_eq_bot_of_lt_top` 取（杀掉 `{A,B,m}` 的
二维方向空间），`r := ℓ A`；再选 `p`、`q`、`z` 并逐条验证第 26 节的表
（含三条 `IsRadiallyInjective` 与 `ℓ p < r`）。

这是一件**独立且不小**的构造，与第 3 步的黏合逻辑无关。**未开始，不报区间。**
第 4 步同样未开始；给 F 的输出形状仍未定。

## 33. 2026-09-18 补上第 26 节声称"自动成立"却没证的那一条

第 26 节说 `C₂` 那一对的径向单射"由 `q` 在 `z`、`d` 之间自动成立"。
**当时只是论证，没有证明。** 现已补上：

`isRadiallyInjective_pair_of_mem_openSegment`（`BallPairArc.lean`）：
`z ≠ d`、`q ∈ openSegment ℝ z d` ⟹ `IsRadiallyInjective q ({z, d} : Set E)`。

证明把两个交叉情形都化到 `d - z` 的倍数上：写 `q = a • z + b • d`（`a, b > 0`、`a + b = 1`），
则 `d - q = a • (d - z)`、`z - q = (-b) • (d - z)`；
由 `hxy` 经 `sub_eq_iff_eq_add'` 得 `d - q = t • (z - q)`，两边都是 `d - z` 的倍数，
用 `d - z ≠ 0` 与 `smul_eq_zero` 消去得 `a = t * (-b)`，与 `a, t, b > 0` 矛盾（`nlinarith`）。
另一支对称得 `-b = t * a`。

坑：`rw [hxy]` 在这里**不能用**——目标两边都含 `d`，改写会把 `d` 自身也换掉。
`sub_eq_iff_eq_add'.mpr hxy` 直接给出要的等式，不碰目标里的其他 `d`。
另：`omit [FiniteDimensional ℝ E]` 在本模块会报"did not match any variables"，
因为该实例是逐定理给的，不在 section 变量里。

聚焦检查 `BallPairArc` exit=0（10.6 秒）、零 warning；
`.lake/scratch/AuditHRadial.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 构型存在性：分解与评估（未开始，不报区间）

第 32 节列的存在性实例是一件**独立的大构造**。按已核对的 API 分成四层：

1. **中点的仿射无关三条**：设 `T = {A,B,c,d}` 仿射无关、`m = (c+d)/2`，要
   `{A,B,m}`、`{A,B,m,c}`、`{A,B,m,d}` 仿射无关。可用
   Mathlib `AffineSpace/FiniteDimensional.lean:205
   affineIndependent_iff_finrank_vectorSpan_eq`（是 iff，可反用）：
   card 与 `finrank (vectorSpan)` 对上即可。`{A,B,m,c}` 的 vectorSpan 含
   `{A,B,c,d}` 的（因 `d = 2m - c`），故 finrank = 3。
2. **泛函 `ℓ`**：`Submodule.exists_dual_map_eq_bot_of_lt_top` 杀掉 `{A,B,m}` 的二维方向空间，
   `r := ℓ A`；`ℓ m = r` 自动（`m` 在该仿射平面上），`ℓ c ≠ r` 由第 1 层的仿射无关推出，
   `ℓ c + ℓ d = 2r` 故两者关于 `r` 对称，必要时交换 `c`、`d`。
3. **选点 `p`、`q`、`z`**：协调者建议用重心坐标显式取。`z` 取 `Fm` 的重心（在 `openSimplex` 里）；
   `p` 取 `T₁` 的重心；`q` 由本节的新引理从 `q ∈ openSegment z d` 直接得径向单射。
   但 `z ∈ segment ℝ p d` 是一条**耦合条件**（`z` 必须在 `p`、`d` 的连线上），
   所以 `p`、`z` 不能各自独立取重心——这一条要先解，是第 3 层的关键。
4. **两条 `IsRadiallyInjective p {c,d}`、`p {c,z}`**：这两个顶点不在两端点之间，
   本节的引理用不上，要另证（`p` 在 `T₁` 内部、`c` 与 `d` 分居两侧，几何上显然）。

第 3 层的耦合（`z` 同时要在 `openSimplex Fm` 里和在 `segment p d` 上）是整件事里
唯一不是例行公事的地方：它把 `p` 与 `z` 绑在一起，应当**先解它再定其余的点**，
理由与第 29 节相同——早发现的约束会变成简化。

## 34. 2026-09-18 耦合已解：先定 `z` 再沿射线取 `p`（验算＋第二条径向判据）

### 协调者的参数化是对的，且区间可显式算出

在 `T₁ = {c, m, A, B}` 的重心坐标里验算（`Fm = {m,A,B}` 是 `c` 的对面，`d = 2m - c`）：

- `d` 的 `T₁` 重心坐标是 `(-1, 2, 0, 0)`（和为 1，`λ_c = -1 < 0`，故 `d` 在面 `λ_c = 0` 的另一侧）；
- `z ∈ openSimplex Fm` 写成 `(0, μ_m, μ_A, μ_B)`，三个 `μ` 全正；
- `p = d + t • (z - d)` 的坐标是 `(t - 1, 2 + t(μ_m - 2), t μ_A, t μ_B)`。

于是 `p ∈ openSimplex T₁` **当且仅当** `t ∈ (1, 2/(2 - μ_m))`，
区间非空等价于 `μ_m > 0`，而这正是 `z` 在**相对内部**给的。
所以耦合确实化成"先选 `z`（面内二参数），再在一个非空开区间里选 `t`（一参数）"。

两条附带结论，都是自动的，不必另设条件：

- `ℓ p = r + (t - 1)(ℓ c - r) < r`（重心坐标上 `ℓ` 是仿射的，`λ_c = t - 1 > 0`、`ℓ c - r < 0`），
  即第 31 节新加的 `hℓp` 自动成立，不是额外选点条件；
- `z ∈ segment ℝ p d`：由 `z - d = (1/t) • (p - d)` 且 `1/t ∈ (0,1)` 得，也是自动的。

两条径向条件 `IsRadiallyInjective p {c,d}` 与 `p {c,z}` **同时**归结为一件事：
**`c` 不在过 `p`、`d` 的直线上**。因为那条直线上 `λ_A = t μ_A`（`μ_A > 0`、`t > 0` 故非零），
而 `λ_A(c) = 0`。`z` 也在这条直线上，所以两条用同一个理由。

### 交付：第二条径向判据

`isRadiallyInjective_pair_of_linearIndependent`（`BallPairArc.lean`）：
`LinearIndependent ℝ ![x - p, y - p]` ⟹ `IsRadiallyInjective p ({x, y} : Set E)`。
与第 33 节的"顶点在两点之间"合起来，覆盖构型里全部三条径向条件：
`p {c,d}`、`p {c,z}` 用本条（`c` 与 `d`／`z` 对 `p` 不共线），`q {z,d}` 用第 33 节。

证明：交叉情形给出 `y - p = t • (x - p)`，即 `(-t) • (x-p) + 1 • (y-p) = 0`，
由 `LinearIndependent.pair_iff`（Mathlib `LinearIndependent/Lemmas.lean:270`）得 `1 = 0`。
需要两侧对称，故先自证一条 `hswap`：`LinearIndependent ℝ ![u,v] → LinearIndependent ℝ ![v,u]`
（Mathlib 无 `pair_symm`，用 `pair_iff` 两行即可）。

聚焦检查 `BallPairArc` exit=0（10.9 秒）、零 warning；
`.lake/scratch/AuditHRadial.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 剩余（未开始，不报区间）

存在性实例的第 1、2 层（中点仿射无关三条；泛函 `ℓ`，路线均已核对），
以及把本节的验算写成 Lean（重心坐标那一段是主要工作量）。之后是第 3 步黏合与第 4 步链归纳。

## 35. 2026-09-18 构型存在性第 1 层 — done（`MidpointIndependence.lean`）

第 33 节列的"中点仿射无关三条"已闭合，但**路线与那里写的不同，且更短**：不必对每条分别算
`vectorSpan` 的 `finrank`，一条"沿直线换顶点"的引理就覆盖全部。

- `affineIndependent_of_card_eq_of_subset_affineSpan`：`T` 仿射无关、`S.card = T.card = n+1`、
  `↑T ⊆ affineSpan ℝ ↑S` ⟹ `S` 仿射无关。用 Mathlib
  `affineIndependent_iff_finrank_vectorSpan_eq`（正用）与
  `affineIndependent_iff_le_finrank_vectorSpan`（反用，只要 `n ≤ finrank`），
  中间经 `affineSpan_le` ＋ `AffineSubspace.direction_le` ＋ `direction_affineSpan`
  把包含关系转成 `vectorSpan` 的包含，再 `Submodule.finrank_mono`。
- `affineIndependent_insert_of_mem_affineSpan_pair`：`insert a S` 仿射无关、`a ∉ S`、`b ∉ S`、
  `u ∈ S`、`a ∈ line[ℝ, u, b]` ⟹ `insert b S` 仿射无关。**换顶点引理**，上一条的直接推论。
- `affineIndependent_insert_midpoint_outer`：从 `T₁ = insert c (insert m F)` 得
  `T = insert c (insert d F)`（`m` 换成 `d`，用 `m ∈ line[ℝ, c, d]`）。
- `affineIndependent_insert_midpoint_inner`：从 `T₁` 得 `T₂ = insert d (insert m F)`
  （`c` 换成 `d`，用 `c ∈ line[ℝ, m, d]`）。
- `Fm = insert m F` 不必另证：它是 `T₁` 的子集，`affineIndependent_of_subset` 即可。

**方向更正**：第 33 节假定从 `T = {A,B,c,d}` 出发造 `m`。实际施工应当**反过来**：
先取仿射无关的 `T₁ = {c,m,A,B}`，再令 `d := m + m - c`。理由是层 2 的泛函 `ℓ` 也由 `T₁` 造，
于是 `d` 与 `c`、`m`、`A`、`B` 的互异性**全部由 `ℓ` 的取值读出**
（`ℓ d = r+1`，而 `ℓ c = r-1`、`ℓ m = ℓ A = ℓ B = r`），
不必用 `eq_on_of_sum_smul_eq` 逐条排除"`m` 恰好落在某个顶点上"。
按正向做则要单独证 `m ∉ {A,B}`，那才需要权重论证。

`line[ℝ, u, b]` 的成员用 `smul_vsub_vadd_mem_affineSpan_pair` 与
`smul_vsub_rev_vadd_mem_affineSpan_pair`，把 `2⁻¹ • (d -ᵥ c) +ᵥ c = m`、
`2 • (m -ᵥ d) +ᵥ d = c` 用 `simp only [vsub_eq_sub, vadd_eq_add]` 加 `module` 收掉。

坑：`Finset` 的插入交换是 `Finset.insert_comm`，不是 `Finset.Insert.comm`（后者不存在）；
`rintro y (rfl | rfl)` 在第二支会把 `b` 消掉再报 `unknown identifier b`，
改成 `Set.mem_singleton_iff.mp` 显式改写即可。

聚焦检查 `MidpointIndependence` exit=0（9.5 秒）、零 warning；
`.lake/scratch/AuditHMidpoint.lean` 四项仅 `propext`、`Classical.choice`、`Quot.sound`。

## 36. 2026-09-18 构型存在性第 2 层 — done（同模块）：泛函不必走对偶空间

第 33 节给的路线是 `Submodule.exists_dual_map_eq_bot_of_lt_top` 杀掉 `{A,B,m}` 的方向空间，
再另证 `ℓ c ≠ r`。**本树已有更短的东西**：`Star.lean:57 exists_affineMap_eqOn`
（仿射无关 `Finset` 上可任意规定仿射映射的取值）。于是

- `exists_linearMap_eq_add_const`：`S` 仿射无关、`q : E → ℝ` 任意 ⟹
  `∃ ℓ : E →ₗ[ℝ] ℝ, ∃ s, ∀ v ∈ S, ℓ v = s + q v`。
  证明取 `ℓ := g.linear`、`s := -g 0`，用 `AffineMap.linearMap_vsub g v 0`
  把 `g.linear v` 换成 `g v - g 0`。**线性泛函在仿射无关集上可以差一个常数地任意规定**。
- `exists_linearMap_separating_midpoint`：`insert c S` 仿射无关、`c ∉ S`、`m ∈ S`、`c + d = m + m`
  ⟹ `∃ ℓ r, (∀ v ∈ S, ℓ v = r) ∧ ℓ c = r - 1 ∧ ℓ d = r + 1`。
  取 `q v = if v = c then -1 else 0`；`ℓ d = ℓ m + ℓ m - ℓ c` 由线性直接给出。

这一条**一次给齐**第 31 节构型里的 `hℓ`、`hℓc`、`hℓd`，并且把归一化定死成 `r∓1`，
后面所有点的 `ℓ` 值都成了有理数算术。走对偶空间则还要额外证 `ker ℓ = vectorSpan {m,A,B}`
才能得到 `ℓ c ≠ r`，长且没有额外收益。

同一条还可以再用一次造第二个泛函 `ν`（取 `q v = if v = A then 1 else 0`），
第 34 节两条径向条件要的就是它——见下一节。

聚焦检查 `MidpointIndependence` exit=0（9.2 秒）、零 warning；
`.lake/scratch/AuditHMidpoint.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

## 37. 2026-09-18 构型存在性 — done（`BallPairCutConfig.lean`）：第 3 步的模型数据已是无条件定理

第 32 节要的"模型的存在性"已闭合。交付的**不是**第 26/31 节那张三十余条的构型清单
（作为 `∃` 写出来无人能消费），而是直接把四对喂完之后的结论打包：

    exists_isPLBallPair_cut_model (hn : finrank ℝ E = 3) :
      ∃ (C₁ C₂ arc : Set E) (z : E),
        IsPLBallPair 2 1 (C₁ ∪ C₂) arc ∧
        IsPLBallPair 2 1 C₁ (C₁ ∩ arc) ∧
        IsPLBallPair 2 1 C₂ (C₂ ∩ arc) ∧
        IsPLBallPair 1 0 (C₁ ∩ C₂) {z} ∧
        C₁ ∩ C₂ ∩ arc = {z}

`C₁ = conv{c,m,A,B}`、`C₂ = conv{d,m,A,B}`、`C₁ ∪ C₂ = conv{c,d,A,B}`、`C₁ ∩ C₂ = conv{m,A,B}`、
`arc = segment p c ∪ segment p d`。**没有假设、没有 section 变量**，第 3 步可以直接 `obtain`。

### 具体取点（第 34 节参数化的一个显式实例）

从 `SimplexBoundary.lean:400` 取四点仿射无关的 `T`，用 `Finset.card_eq_four` 命名成
`{c, m, A, B}`——注意**是 `T₁` 不是 `T`**（第 35 节的方向更正），再令

    d := m + m - c,  z := (1/3)(m + A + B),
    p := (1/10)c + (1/6)m + (11/30)A + (11/30)B,  q := (1/2)(z + d)

即第 34 节的 `μ_m = μ_A = μ_B = 1/3`、`t = 11/10`（区间是 `(1, 6/5)`）。核对过的坐标：

| 点 | `{c,m,A,B}` 重心坐标 | `{c,d,A,B}` | `{d,m,A,B}` | `ℓ` | `ν` |
|---|---|---|---|---|---|
| `p` | `(1/10, 1/6, 11/30, 11/30)` | `(11/60, 1/12, 11/30, 11/30)` | — | `r − 1/10` | `s + 11/30` |
| `z` | `(0, 1/3, 1/3, 1/3)` | — | `(0, 1/3, 1/3, 1/3)` | `r` | `s + 1/3` |
| `q` | — | — | `(1/2, 1/6, 1/6, 1/6)` | `r + 1/2` | `s + 1/6` |
| `c` | — | — | — | `r − 1` | `s` |
| `d` | — | — | — | `r + 1` | `s` |

`z ∈ segment p d` 的系数是 `(10/11, 1/11)`；`q ∈ openSegment z d` 的是 `(1/2, 1/2)`。

### 两个把工作量砍掉一半的做法

1. **互异性全部由 `ℓ` 读出**。八条 `c≠d`、`p≠c`、`p≠d`、`c≠z`、`p≠z`、`z≠d`、`q≠z`、`q≠d`
   以及 `d ∉ {m,A,B}` 等五条 `Finset` 不属于，都用同一条
   `hne : ℓ x ≠ ℓ y → x ≠ y` 加上表里的 `ℓ` 值，`linarith` 收尾。
   不必对任何一对做几何论证。
2. **两条径向条件用行列式判据**，不用手算线性无关：
   `linearIndependent_pair_of_det_ne_zero (φ ψ : E →ₗ[ℝ] ℝ) (φ u * ψ v - φ v * ψ u ≠ 0)`。
   取 `φ = ℓ`（第 36 节那条）、`ψ = ν`（同一条引理再用一次，`q v = if v = A then 1 else 0`）。
   两个行列式分别是 `11/15` 与 `1/15`，算出来就是 `norm_num`。
   第 34 节说"两条归结为同一件事（`c` 不在 `p`、`d` 的直线上）"是对的，
   但在 Lean 里**两条各写一个行列式比共用一个几何理由短**。

配套的两条组合引理 `mem_openSimplex_triple` / `mem_openSimplex_quadruple`
（给三点／四点的正权重与组合式即得开单纯形成员）与
`sum_triple_insert` / `sum_quadruple_insert` 一并交付，后面再选点可直接用。
权重函数用 `obtain ⟨w, wa, wb, wc, we⟩ : ∃ w : E → ℝ, w a = w₁ ∧ …` 造成**不透明但取值已知**的形式，
比 `set` 一个嵌套 `if` 再反复 `simp` 稳得多。

聚焦检查 `BallPairCutConfig` exit=0（14.4 秒）、零 warning
（`sum_*_insert` 两条要逐条 `omit [NormedAddCommGroup E] [NormedSpace ℝ E]`）；
`.lake/scratch/AuditHCutConfig.lean` 四项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 剩余

第 3 步（相对黏合）与第 4 步（沿弧的链归纳）。第 3 步的输入现在齐了。

## 38. 2026-09-18 第 3 步（相对球对黏合）— done（`BallPairRelativeGluing.lean`）

    isPLBallPair_union_of_coneSet_disk (hn : finrank ℝ E = 3)
      (hfin₁ hfin₂ hfin₀) (hL₁ : IsConeBase p₁ L₁) (hL₂ : IsConeBase p₂ L₂) (hL₀ : IsConeBase z L₀)
      (hS₁ hS₂ : IsPLSphere 2 …) (hS₀ : IsPLSphere 1 L₀.space)
      (hD₁ : coneSet z L₀.space ⊆ L₁.space) (hD₂ : … ⊆ L₂.space)
      (hy₁ : y₁ ∈ L₁.space) (hy₁D : y₁ ∉ coneSet z L₀.space) (hy₂ hy₂D 同)
      (hmeet : coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space = coneSet z L₀.space) :
      IsPLBallPair 2 1 (coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space)
        (coneSet p₁ {z, y₁} ∪ coneSet p₂ {z, y₂})

即：两块**锥形**球对沿公共边界盘黏合，盘的锥顶 `z` 就是弧的穿越点，两条弧的远端点各自落在自己那块的
边界球面上、盘外——则并仍是球对。非空：模型自身（第 37 节）恰好满足全部假设。

### 设计更正（这一条值得记下来）

原计划把第 3 步写成"给 `IsPLBallPair 2 1 C₁ (C₁ ∩ A)` 两份加黏合条件"。**不行**：
`IsPLBallPair` 只说 `C₁` 与**某个**锥对 PL 同胚，锥不在 `C₁` 里；而 M2
（`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked`）要的是 `D ⊆ Lc.space`、
`coneSet p Lc.space` 就是那一块——**原位**锥数据。两边都要原位。
所以第 3 步的源侧假设必须写成原位锥数据（对消费者不是负担：Moise 那边的块本来就是单纯形／星）。
同理模型侧也必须原位，因此第 37 节的打包结论不够用，本轮把模型加强成
`exists_cutModel_data`（23 条），`exists_isPLBallPair_cut_model` 退化成它的推论。
**早暴露的接口形状差异会变成一次加强，晚暴露会变成重写。**

### 证明骨架（六步，全部现成件）

1. `IsPLSphere.exists_isPLHomeomorphOn`（新，三行）：同维 PL 球面之间必有 PL 同胚——
   `IsPLSphere n S` 按定义就是"与 `stdSimplexBoundary (n+1)` PL 同胚"，两边复合即可。
   跨空间（`E → F`）也成立。
2. `exists_isPLHomeomorphOn_coneSet_pair hL₀ … hf₀`：把 1-球面的同胚锥化成盘的同胚 `g`，
   **且把锥顶送锥顶**，即 `g z = w`。这就是"盘上带标记点的同胚"，不需要另造
   Alexander 技巧或 `stdCenter` 参数化。
3. M2 两次，**都以同一个 `g` 为起点**：得 `G₁`、`G₂`，`EqOn Gᵢ g D` 是构造给出的，
   于是 `EqOn G₁ G₂ (C₁ ∩ C₂)` 免费（第 14 节已经预告过这一点）。
4. `IsPLHomeomorphOn.piecewise`：还要 `G₁ '' (C₁ ∩ C₂) = M₁ ∩ M₂`，由 `hmeet`＋模型的
   `hmeetM`＋`hg.image_eq` 得到。
5. 弧的像：`Φ '' (A₁ ∪ A₂) = Φ''A₁ ∪ Φ''A₂`，各用 `EqOn Φ Gᵢ Cᵢ` 化成 M2 的结论。
6. `IsPLBallPair.of_isPLHomeomorphOn hpairM hΦ.symm`：方向是**模型 → 源**，
   所需的 `invFunOn Φ '' 模型弧 = 源弧` 用 `BijOn.invOn_invFunOn.1.mono harcsub |>.image_image`。

两条小工具一并交付：`pair_inter_coneSet`（`{z,y} ∩ coneSet z X = {z}`，只要 `y ∉ coneSet z X`）
与 `pair_eq_inter_coneSet_union`（M2 的 `hJsplit` 形状）。
M2 的 `hy : y ∈ closure (S \ D) \ D` **不必算闭包**：`y ∈ S \ D` 经 `subset_closure` 即可。

坑：`rintro ⟨hx | hx, hxc⟩` 与 `rintro x (rfl | hx)` 在 `x = z`（`z` 是定理变量、`x` 是局部变量）
这一支会把 **`z` 消掉**，随后 `apex_mem_coneSet z X` 报 `unknown identifier z`。
改成 `rcases Set.mem_insert_iff.mp hx` ＋ 显式 `rw` 即可。

聚焦检查 `BallPairCutConfig` exit=0（14.7 秒）、`BallPairRelativeGluing` exit=0（11.0 秒），
均零 warning；`.lake/scratch/AuditHRelGluing.lean` 六项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 剩余

第 4 步（沿弧的链归纳）。给 F 的输出形状见下一节。

## 39. 2026-09-18 第 4 步的图卡链层 — done（`ArcChartChain.lean`），并报告 F 的一处接口缺陷

协调者已确认：**源侧 ⟹ 像侧为假**，像侧契约是最终形状。按此实现。

    exists_arcChartChain_of_imageContract (M N : SimplicialComplex ℝ E) (v : Fin (n+1) → E)
      (hvertex : ∀ i, ∃ N₁ φ a₁ b₁ U₀ V₀ Ψ,
          a₁ ≠ b₁ ∧
          (geometricLink N₁ {φ (v i)}).space ∩ {x | x.2.2 = (φ (v i)).2.2} = {a₁, b₁} ∧
          (两侧性两条) ∧
          IsOpen U₀ ∧ v i ∈ U₀ ∧ IsPLHomeomorphOn Ψ U₀ V₀ ∧ Ψ (v i) = 0 ∧
          ∀ᶠ y in 𝓝 (v i), (y ∈ M.space → (Ψ y).2.1 = 0) ∧ (y ∈ N.space → (Ψ y).2.2 = 0))
      (τ : Fin n → ZMod 2) :
      ∃ N₁ φ a₁ b₁ side U V Ψ ε, (逐顶点契约) ∧
        (∀ i, side i = if ε i = 0 then a₁ i else b₁ i) ∧
        (∀ i, side i ∈ (geometricLink (N₁ i) {φ i (v i)}).space ∩ {x | x.2.2 = …}) ∧
        (逐顶点图卡四条) ∧ (∀ i : Fin n, ε i.succ = ε i.castSucc + τ i)

即：沿分支的每个顶点带**像侧契约**与它产出的图卡，则整条链上存在**相容的侧选择** `ε`，
并由它在每个顶点的两点 `{a₁ i, b₁ i}` 里**选定一点** `side i`，选中的点确实落在
连接与平面的交里。`ε` 的跳变正是给定的过渡符号 `τ`（`exists_sideChoice_of_chain`，
`BranchSignChain.lean:13`，E3 的文件，只消费不修改）。

输出形状：**不是** `OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`，也不是纯 germ。
是**星形（逐顶点的开集图卡族）＋ 沿链的相容侧选择**：每个 `i` 给
`IsOpen (U i)`、`v i ∈ U i`、`IsPLHomeomorphOn (Ψ i) (U i) (V i)`、`Ψ i (v i) = 0`
与两片的 `∀ᶠ` 条款。把这族黏成单张 `OpenPartialHomeomorph` 需要 F 的
§19.134 第 4、5 条（覆盖级条款与 `S ⊆ ⋃ Φ_i.source ⊆ W`），那不在本车道。

### 给 F 的接口缺陷报告（必须改，否则链层用不上顶点定理）

我最初把 `hvertex` 写成"源侧数据 ＋ 一个契约供应器
`∀ K₁ N₁ φ, (F 的结构条款) → ∃ a₁ b₁, 契约`"，好让链层直接调用
`exists_chart_two_sheets_of_transverse_vertex`。**这个写法是空的**：
结构条款只说 `N₁` 有限、`N₁ ⊆ K₁`、`φ (v i) = 0`、`{φ (v i)} ∈ N₁.faces`、
`K₁.space ∈ 𝓝 (φ (v i))`、`link N₁` 是 1-球面——取 `link N₁ {0}` 为平面
`{x.2.2 = 0}` 内的一个三角形边界即满足全部结构条款，而它与该平面的交是整条 1-球面，
不是两点。于是契约供应器**无解**，整条定理空转。已弃用，改成现在的形状。

根因：`exists_chart_two_sheets_of_transverse_vertex` 的结论是
`∃ K₁ N₁ φ, … ∧ (∀ a₁ b₁, 契约 → … → ∃ 图卡)`，契约位于**存在量词内部的蕴含前件**。
消费者要用它就必须对 F 交付的**那一个** `N₁` 证契约，但 `N₁` 被存在量词藏住了；
任何在定理外部写得出的契约假设，要么与那个 `N₁` 无关（于是无用），
要么对所有 `N₁` 全称（于是为假）。**这是形状问题，不是强度问题。**

两条修法，任选其一即可让链层直接调用顶点定理：
- (α) 把 `(K₁, N₁, φ)` 从存在量词里提出来：做成一个具名定义（或让顶点定理接受它们作为输入
  并附带"它们是 `K, M, N, p` 的转写"这一条），契约就能对它们陈述；
- (β) 把像侧契约（`a₁ ≠ b₁`、交等于 `{a₁,b₁}`、两侧性两条）直接提升为
  `exists_chart_two_sheets_of_transverse_vertex` 的**顶层假设**，结论只留图卡。
  (β) 改动最小，且与"契约不可由源侧导出"的结论一致——不可导出的东西本来就该是假设。

在 F 采纳 (α) 或 (β) 之前，链层按本节的 `hvertex` 形状消费：
F 在每个顶点自己把顶点定理与该顶点的横截性合成，交出打包好的
"契约 ＋ 图卡"，链层负责 `choose` 与侧选择。**本节的输出不因 F 选哪条修法而改变。**

坑：`choose` 不接受 `-` 占位，要用 `_hpos`、`_hneg` 这样的下划线名；
`refine` 里用 `fun i => if … then … else …` 作见证后，目标里是未 β 归约的
`(fun i => …) i`，`rw [if_pos]` 不匹配，`by_cases … <;> simp [hεi]` 最稳。

聚焦检查 `ArcChartChain` exit=0（10.4 秒）、零 warning；
`.lake/scratch/AuditHArcChartChain.lean` 一项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 第 4 步的另一半（球对方向）仍未开始

`ArcDerivedNeighborhood.lean` 已有**绝对**版本（弧的导出邻域是 3-球）。
**相对**版本（导出邻域与弧构成球对）要把第 38 节的
`isPLBallPair_union_of_coneSet_disk` 沿 `arcChainFace` 归纳，
前置是把 `derivedNeighborhoodCell K (arcChainFace v j)` 认成**原位锥形球对**
（锥顶、边界 2-球面、弧在其中的那一段）。这一条尚未测绘，**未开始，不报区间**。

## 40. 2026-09-18 第 4 步球对方向的前置 2 — **测试通过**（`DerivedCellCone.lean`）

协调者要求先测再建。测了：**相接盘的锥顶正是弧的穿越点，且全部原位**，不必换顶点，
`hmeet` 的形状不变。零新几何，八条全是既有引理的换写：

- `derivedNeighborhoodCell_space_eq_coneSet`：`cell s = coneSet ĉ_s (upperLink K' {ĉ_s}).space`
  （`derivedNeighborhoodCell_eq_dualCell` ＋ `dualCell` 按定义就是 `coneComplex` ＋
  `coneComplex_space_eq_coneSet` ＋ `Finset.centroid_singleton`）。
- `isConeBase_centroid_upperLink`：其锥基证书；
  `IsCombinatorialManifold.isPLSphere_upperLink_centroid`：闭组合 3-流形时基是 2-球面
  （`isPLSphere_upperLink` 取 `k = 0`，经 `hK.barycentricSubdivision`）。
- `derivedNeighborhoodCell_inter_eq_coneSet`：`cell s ∩ cell t =
  coneSet (centroid {ĉ_s, ĉ_t}) (upperLink K' {ĉ_s, ĉ_t}).space`——
  `derivedNeighborhoodCell_space_inter` 早就把交写成 `dualCell K' {ĉ_s, ĉ_t}`，它按定义是锥。
- `IsCombinatorialManifold.isPLSphere_upperLink_pair_centroid`：该基是 1-球面（`k = 1`）。
- `coneSet_pair_centroid_subset_upperLink` / `_right`：相接盘落在两块各自的基球面里
  （`dualCell_faces_subset_upperLink`，`BoundaryDerivedNeighborhood.lean:16`，已有）。
- `centroid_ne_centroid_of_ne`：不同面的重心不同（`injOn_faces_of_mem_openSimplex`）。

所以第 38 节 `isPLBallPair_union_of_coneSet_disk` 要的 `hL₀ : IsConeBase z L₀`、`hS₀`、`hD₁`、`hD₂`、
`hmeet` 在导出邻域胞腔上**全部现成**，`z = centroid {ĉ_s, ĉ_t}`。

坑：定理名以 `IsCombinatorialManifold.` 开头时，陈述里裸写 `barycentricSubdivision K`
会解析成 `IsCombinatorialManifold.barycentricSubdivision`（命名空间被打开），报
"argument K expected to have type IsCombinatorialManifold"。写 `PiecewiseLinear.barycentricSubdivision K`。
另：`rw [Finset.centroid_singleton]` 留下 `id x`，`rw` 收尾的 `rfl` 不展开 `id`，要补一行 `rfl`。

合并后 `fresh.py` 报六个模块 STALE，但 `git diff` 显示只有 `VertexBranchSection.lean` 内容变了
（F 的文件，本车道不导入它）；其余只是 mtime 被合并碰过，olean 仍对应当前源码。

聚焦检查 `DerivedCellCone` exit=0（9.8 秒）、零 warning；
`.lake/scratch/AuditHDerivedCellCone.lean` 八项仅 `propext`、`Classical.choice`、`Quot.sound`。

## 41. 2026-09-18 第 4 步球对方向的前置 1 — done（`ArcCellTrace.lean`）：弧在胞腔里的迹是锥

按内容而不是按名字搜到了关键件：`StarIntersection.lean:10
closedStar_barycentricSubdivision_inter_space_eq (hL : L ⊆ K) (hxL : {x} ∈ L.faces) :
closedStar K' x ∩ L.space = closedStar L' x`——子复形的迹就是子复形自己的闭星。
对 `(K', L')` 用一次，胞腔 `closedStar K'' ĉ_s ∩ L.space` 就化成 `closedStar L'' ĉ_s`，
而 `closedStar L'' ĉ_s = (dualCell L' {ĉ_s}).space`（`DualCells.lean:163`）按定义是锥。
剩下的只是"一维复形的 `upperLink` 是有限个点"这一条组合事实：

- `IsFlag.card_le_two`：面的顶点数都 ≤ 2 时旗最多两层（`Finset.card_le_card_of_injOn` 打进 `{1,2}`）；
  `barycentricSubdivision_card_le_two`：一维复形的重心细分仍一维。
- `upperLink_singleton_space_of_card_le_two`：`(upperLink G {x}).space = {重心 e | e ∈ G, {x} ⊂ e}`。
- `closedStar_barycentricSubdivision_eq_coneSet_of_card_le_two`：
  `closedStar G' x = coneSet x {重心 e | e ∋ x 的边}`。
- `mem_barycentricSubdivision_ssubset_singleton_centroid_iff`：`G'` 里严格含 `{ĉ_s}` 的面恰是
  `{ĉ_s, ĉ_t}`，`t ≠ s` 与 `s` 可比。
- **`derivedNeighborhoodCell_inter_space_eq_coneSet`**（`L ⊆ K` 一维，`s ∈ L`）：

      cell s ∩ L.space = coneSet ĉ_s {centroid {ĉ_s, ĉ_t} | t ∈ L.faces, t ≠ s, s ⊆ t ∨ t ⊆ s}

  链接点**正是**第 40 节相接盘的锥顶 `centroid {ĉ_s, ĉ_t}`，不需要任何中点算术。

对弧复形 `arcComplexIn K v n` 与 `s = arcChainFace v j`（`1 ≤ j ≤ 2n−1`），可比的 `t` 恰是
`arcChainFace v (j∓1)`（`arcChainFace_subset_iff`），于是迹是两条线段 `coneSet ĉ_j {z_{j−1}, z_j}`。
两端的顶点胞腔（`j = 0, 2n`）只有一个链接点，迹是从锥顶出发的一条线段——
**弧的端点在胞腔内部**，`IsPLBallPair 2 1` 的子链必须碰到基球面，所以端点胞腔要排除在外：
第 4 步的球对陈述取 `N' = ⋃_{j=1}^{2n−1} cell_j`（去掉两端的顶点胞腔）与缩短的弧 `A ∩ N'`。

聚焦检查 `ArcCellTrace` exit=0（11.0 秒）、零 warning（`Set.mem_setOf_eq` 已弃用，改 `Set.mem_ofPred_eq`）；
`.lake/scratch/AuditHArcCellTrace.lean` 六项仅 `propext`、`Classical.choice`、`Quot.sound`。

## 42. 2026-09-18 中断时的状态（协调者要求：owner 会话结束）

**已落地（均 exit=0、零 warning、审计仅三公理，已提交并推送）：**
第 35–41 节全部：`MidpointIndependence`、`BallPairCutConfig`（含 `exists_cutModel_data`）、
`BallPairRelativeGluing`（`isPLBallPair_union_of_coneSet_disk`）、`ArcChartChain`、
`DerivedCellCone`（前置 2 测试通过）、`ArcCellTrace`（前置 1 闭合）。

**stash 里的一件**（`git stash list` 首条，untracked 文件 `ArcChainCells.lean`）：
弧链胞腔的专化层——`arcChainFace_card_le_two`、`arcChainFace_injective`、
`arcChainFace_comparable_iff`（可比 ⟺ `|i−j| ≤ 1`）、`arcChainFace_mem_arcComplexIn_faces`、
`disjoint_derivedNeighborhoodCell_arcChainFace`（`i+1 < j` 的胞腔不交）、
`derivedNeighborhoodCell_inter_arcComplexIn_space`（`1 ≤ j`、`j+1 ≤ 2n` 时
`cell_j ∩ A.space = coneSet ĉ_j {z_{j−1}, z_j}`，`z_j = centroid {ĉ_j, ĉ_{j+1}}`）。
聚焦检查 **exit=0，但前三条各报一个 `unusedSectionVars` warning**
（要在这三条前各加 `omit [NormedAddCommGroup E] [NormedSpace ℝ E] in`），未审计。
因为不是零 warning，按指令 stash 而不提交。`git stash pop` 后补三行 `omit`、复查、审计即可提交。

**中飞（未写 Lean）——第 4 步球对方向的施工方案，已定型，按此接：**
1. M2（`ConeDiskPairExtension.lean:11`，本车道文件）结论**追加** `G '' Lc.space = Lc'.space`
   （证明里已有 `hGeq.image_eq.trans hGs.image_eq`），并给 `BallPairRelativeGluing.lean`
   两处 `obtain ⟨G₁, hG₁, hG₁eq, -, hG₁X⟩` 各补一个 `-`。
2. `exists_cutModel_data` 追加并集的原位锥数据：`(L : SC)`，`L.faces.Finite`、`IsConeBase p₁ L`、
   `IsPLSphere 2 L.space`、`coneSet p₁ L.space = C₁ ∪ C₂`、
   `coneSet p₁ {y₁,y₂} = A₁ ∪ A₂`、`y₁ y₂ ∈ L.space`、
   **`L₂.space ⊆ L.space ∪ coneSet z L₀.space`**（`∂T₂ ⊆ ∂T ∪ conv Fm`，
   用 `simplexBoundary_space` 逐面：`T₂.erase d = Fm`，`T₂.erase m = T.erase c`，
   `conv (T₂.erase A) ⊆ conv (T.erase A)` 因 `m ∈ segment c d`，`B` 同）。
   见证 `L := simplexBoundary {c,d,A,B} hTout`，`hp : p ∈ openSimplex T` 已在构造里。
   两个消费者的 `obtain` 模式各加 `L` 与八个 `-`。
3. **归纳不变量**（模型固定，不需要边界保持引理，也不需要拓扑）：
   `Inv(k)`: `∃ Φ, IsPLHomeomorphOn Φ B_k (coneSet p₁ L₁.space) ∧ Φ '' A_k = coneSet p₁ {z,y₁}
   ∧ Φ '' D_k = coneSet z L₀.space ∧ Φ z_k = z ∧ Φ y₀ = y₁`，
   其中 `B_k = ⋃_{j=1}^{k} cell_j`，`A_k = B_k ∩ A.space`，`D_k = cell_k ∩ cell_{k+1}`，
   `z_k` 其锥顶，`y₀ = z_0` 弧的近端（第一个穿越点，在 `cell_1` 的基球面上）。
   一步 = M2 两次：(a) 源 `cell_{k+1}`（原位锥，第 40 节）→ 模型 `C₂`，以 `Φ|D_k` 为 `g`，
   得 `Φ'`，`piecewise Φ Φ' : B_{k+1} → coneSet p₁ L.space`；
   `Φ'(D_{k+1}) ⊆ L₂.space \ coneSet z L₀.space ⊆ L.space`（用 2 的最后一条与 `D_{k+1} ∩ D_k = ∅`）。
   (b) 再归一化：M2 源 `(p₁, L)`、`X = {y₁,y₂}`、`D = Φ'(D_{k+1})`、`y = y₁`，目标 `(p₁, L₁)`、
   `X' = {z,y₁}`、`D' = coneSet z L₀.space`，`g := g₀ ∘ Φ'⁻¹`，`g₀ : D_{k+1} → coneSet z L₀.space`
   由 `D_{k+1}` 的原位锥数据（第 40 节）锥化 1-球面同胚得到（锥顶送锥顶）。
   基例 `k = 1`：M2 一次（源 `cell_1`，目标 `C₁`，`X = {z_1, y₀}`）。
   终点：`Inv(2n−1)` 与模型的 `hpair₁` 经 `IsPLBallPair.of_isPLHomeomorphOn` 给
   `IsPLBallPair 2 1 (⋃_{j=1}^{2n−1} cell_j) (弧 ∩ 该并)`。**弧端点的顶点胞腔必须排除**（第 41 节）。
4. 需要的胞腔事实全部在第 40、41 节与 stash 里：原位锥、2-球面基、相接盘锥顶＝穿越点、
   盘在两基球面里、迹＝两条线段、远胞腔不交。假设用 `IsCombinatorialManifold 3 K`（闭），
   经 `IsCombinatorialManifold.isCombinatorialManifoldWithBoundary` 复用 `ArcDerivedNeighborhood`。

给 F 的端到端交付（截至本次中断）：`ArcChartChain.lean` 的星形图卡族＋相容侧选择（第 39 节），
以及第 39 节报告的接口缺陷（协调者已把修法 (β) 派给 F）。球对方向未闭合，未估行数。

## 43. 2026-09-18 Codex verified continuation

The ArcChainCells stash was recovered without dropping the stash, repaired with
three narrow `omit` scopes, and pushed as `ae58cf850`. Integration added its
required headers and root import in `f6a0b2dda`.

Step 1 of section 42 is now implemented: the conclusion of
`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` also exposes
`G '' Lc.space = Lc'.space`. This follows from the existing boundary agreement
and the sphere homeomorphism's image equality; no hypothesis was added. Both
consumers in `BallPairRelativeGluing.lean` were updated.

The two leaves are registered in the flat root and have the required copyright
and module headers, as explicitly authorized by the owner on 2026-09-18.
Both compiled with the standard syntax linter set, `style.header=true` and
`style.longLine=true`, exit 0 with no diagnostics. A silent external audit checked
all five declarations in the two leaves: every axiom lies in
`{propext, Classical.choice, Quot.sound}`, and all default environment linters
except `docBlame` and `docBlameThm` passed. Imported objects were reused for these
local checks; the separate integration source rebuild remains pending.

The next mathematical obligation is still section 42 step 2: expose the combined
cut model's cone data and the second base sphere's containment in the outer sphere
union the gluing disk. The trimmed arc-chain ball-pair induction is not complete.

## 44. 2026-09-18 Combined cut-model cone data — done

`exists_cutModel_data` now also returns the boundary complex `L` of the outer
tetrahedron together with all eight facts required by section 42 step 2:

- `L.faces.Finite`, `IsConeBase p₁ L`, and `IsPLSphere 2 L.space`;
- `coneSet p₁ L.space = coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space`;
- `coneSet p₁ {y₁, y₂} = coneSet p₁ {z, y₁} ∪ coneSet p₂ {z, y₂}`;
- `y₁ ∈ L.space`, `y₂ ∈ L.space`, and
  `L₂.space ⊆ L.space ∪ coneSet z L₀.space`.

The witness is `simplexBoundary {c, d, A, B} hTout`.  The cone and marked-ray
equalities reuse the already proved convex-hull cut and arc equalities.  The last
containment is proved facewise from `simplexBoundary_space`: deleting `d` gives
the gluing face, deleting `m` gives the opposite outer face, and the two remaining
faces map into outer faces because `m ∈ segment ℝ c d`.  No additional hypothesis
was added.  Both consumers of `exists_cutModel_data` were synchronized, and
`BallPairCutConfig` is now registered directly in the flat root aggregate.

Strict private checks used token `H-CutModel-Strict-20260918` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  In dependency
order, `BallPairCutConfig` and `BallPairRelativeGluing` both compiled with exit 0,
zero diagnostics, source-stable receipts, the standard linter set, and explicit
header and long-line checks.  An external silent audit covered all twelve
non-automatic declarations in the two modules; every axiom is in
`{propext, Classical.choice, Quot.sound}`, and all environment linters other than
`docBlame` and `docBlameThm` passed.  The strict checks wrote no shared artifact.

Before the strict run, the inherited `check-f.ps1` was mistakenly invoked three
times.  That obsolete helper disables the header and long-line checks and deletes
the shared target object before compiling; all three attempts failed, leaving the
shared `BallPairCutConfig.olean` and `.ilean` absent.  The coordinator rebuilt the
unchanged integration version with the strict flags and restored those two shared
objects before the final H checks.  The verified H objects and their receipts
remain private and were not copied into the shared library.

The remaining section 42 obligation is the trimmed arc-chain ball-pair induction
over the non-endpoint cells.  The old full-chain statement remains false and must
not be reinstated.

## 45. 2026-09-18 Interior arc-chain cell ball pair — done

`ArcCellBallPair.lean` proves
`IsCombinatorialManifold.isPLBallPair_derivedNeighborhoodCell_arcChainFace`.
For an injective simplicial arc chain in a closed combinatorial 3-manifold and an
index satisfying `1 ≤ j` and `j + 1 ≤ 2 * n`, the single derived-neighborhood
cell at `arcChainFace v j`, paired with its trace on `arcComplexIn K v n`, is an
`IsPLBallPair 2 1`.

The proof identifies the cell with the cone over the upper link at the face
centroid.  The two adjacent arc-chain faces give distinct marked points in that
upper-link 2-sphere.  Cone-base radial injectivity then supplies the standard
conical arc pair, while `derivedNeighborhoodCell_inter_arcComplexIn_space`
identifies its two radial segments with the actual arc trace.  The hypotheses
exclude the two endpoint vertex cells; no nondegeneracy hypothesis beyond those
index inequalities was added.

The module is registered directly in `DifferentialGeometry.lean`.  Strict private
verification used token `H-ArcCell-20260918` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module check
and external silent audit both exited 0 with zero diagnostics and unchanged
shared outputs.  The audit enumerated the module's single non-automatic
declaration, checked its direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all default environment
linters other than `docBlame` and `docBlameThm`.

This closes only the one-cell input.  The induction proving an `IsPLBallPair 2 1`
for the union of all non-endpoint cells `1 ≤ j ≤ 2 * n - 1` remains open; the
false full-chain statement including the endpoint cells remains forbidden.

## 46. 2026-09-18 Adjacent arc-cell gluing data — done

`ArcCellGluing.lean` supplies the geometric input for the trimmed-union
induction without assuming any union is already a ball pair.  It introduces the
natural objects `arcCellApex`, `arcCellCrossing`, `arcCellBase`, and
`arcCellInterfaceBase`, then proves:

- each cell and each adjacent-cell intersection has its exact conical form;
- cell bases are PL 2-spheres and interface bases are PL 1-spheres, with the
  required cone-base and finiteness data;
- the conical interface disk lies in both cell bases;
- the preceding and following crossing points lie in the corresponding
  `closure (base \ interface) \ interface`, as required by the marked relative
  extension theorem;
- the arc trace in an interior cell is exactly the cone on its preceding and
  following crossing points.

The nonmembership part is not a generic-position assumption.  A preceding
crossing belongs to cell `j - 1`; if it also belonged to the `j,j+1` interface,
it would lie in the disjoint nonadjacent cells `j - 1` and `j + 1`.  The following
crossing is treated symmetrically.  The hypotheses `1 ≤ j` and
`j + 2 ≤ 2 * n` are precisely the index conditions needed for these arguments.

The module is registered directly in `DifferentialGeometry.lean`.  Strict private
verification used token `H-ArcCellGluing-20260918` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module check
and external silent audit both exited 0 with zero diagnostics and unchanged
shared outputs.  The audit dynamically enumerated all twenty non-automatic
declarations, also checked sixteen direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all default environment
linters other than `docBlame` and `docBlameThm`.

The remaining obligation is to use these data with
`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` and the combined cut model
to carry out the normalized induction over cells `1` through `2 * n - 1`.

## 47. 2026-09-18 Marked-point equality from the relative cone extension — done

`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` now also returns
`G y = y'`.  The sphere-level marked extension already supplied this equality;
the cone extension agrees with that sphere map on the base.  The only extra
proof step observes that `y ∈ closure (Lc.space \ D)` lies in `Lc.space`, because
the PL sphere `Lc.space` is closed.  No hypothesis was added.

The two consumers in `BallPairRelativeGluing.lean` were synchronized with the
stronger result.  Strict private verification used token
`H-MarkedPoint-20260918` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
`ConeDiskPairExtension` and `BallPairRelativeGluing` compiled in dependency
order, and the external silent audit also passed; all three checks exited 0 with
zero diagnostics and unchanged shared outputs.  The audit dynamically enumerated
all five non-automatic declarations across the two modules, checked the two
direct extension producers, found only `{propext, Classical.choice, Quot.sound}`,
and passed all default environment linters other than `docBlame` and
`docBlameThm`.

This equality is the missing invariant field needed to keep the near endpoint of
the marked arc fixed while the trimmed-union induction repeatedly normalizes the
new outer interface.

## 48. 2026-09-18 Trimmed arc-cell union bookkeeping — done

`ArcCellUnion.lean` defines
`trimmedArcCellUnion K v k = ⋃ i : Fin k, cell (i + 1)`, so it contains exactly
the first `k` non-endpoint cells.  Its API proves the set identities and
disjointness facts needed by the normalized induction:

- the successor union is the previous union plus cell `k + 1`;
- for `1 ≤ k`, the previous union meets cell `k + 1` exactly in the standard
  interface cone at `arcCellCrossing v k`;
- the previous union is disjoint from the following interface between cells
  `k + 1` and `k + 2`;
- intersection with the arc complex distributes across the successor step;
- the fixed near crossing `arcCellCrossing v 0` and the current outgoing
  crossing `arcCellCrossing v k` lie in the appropriate trimmed union.

All far-intersection exclusions use
`disjoint_derivedNeighborhoodCell_arcChainFace`; no ball-pair conclusion or
hidden nondegeneracy assumption is used.  The module is registered directly in
`DifferentialGeometry.lean`.

Strict private verification used token `H-ArcCellUnion-20260918` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module check
and external silent audit both exited 0 with zero diagnostics and unchanged
shared outputs.  The audit dynamically enumerated all nine non-automatic
declarations, checked the three direct arc-cell intersection producers, found
only `{propext, Classical.choice, Quot.sound}`, and passed all default
environment linters other than `docBlame` and `docBlameThm`.

The remaining proof layer is now purely the relative-extension construction:
build the base normalized state at `k = 1`, advance it with the two marked cone
extensions at each successor, and extract the ball-pair conclusion at
`k = 2 * n - 1`.

## 49. 2026-09-18 Natural preceding-crossing bound — done

The upper index hypothesis of
`previous_arcCellCrossing_not_mem_interface` and
`previous_arcCellCrossing_mem_closure_diff_interface` is now the natural
`j + 1 ≤ 2 * n`.  Their proofs only use the three cells at indices `j - 1`,
`j`, and `j + 1`; the former `j + 2 ≤ 2 * n` assumption was unused.  This
weakening is essential at the base state `j = 1` when `n = 1`, where the two
non-endpoint cells consist of the single cell at index one.

There are no committed downstream call sites of these two declarations yet;
the source-ready normalized base state is their first consumer.  Strict private
verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
The module check and external silent audit both exited 0 with zero diagnostics
and unchanged shared outputs.  The audit dynamically enumerated all twenty
non-automatic declarations, checked sixteen direct reused declarations, found
only `{propext, Classical.choice, Quot.sound}`, and passed all thirteen
applicable environment linters.

## 50. 2026-09-18 Normalized first trimmed arc cell — done

`ArcCellNormalization.lean` proves
`exists_normalized_trimmedArcCellUnion_one`.  For every nonempty injective
simplicial arc chain in a finite closed combinatorial 3-manifold, it identifies
the first non-endpoint derived-neighborhood cell with the first lobe of the
three-dimensional cut model.  Simultaneously it sends the cell's arc trace to
the standard two-segment cone, its outgoing interface disk to the standard cut
disk, the outgoing crossing to the cut-disk apex, and the fixed near crossing
to the marked point off that disk.

The proof uses the natural `j + 1 ≤ 2 * n` preceding-crossing bound, so the
construction includes the actual `n = 1` instance.  It constructs the
interface map from a PL homeomorphism of its link circle and applies
`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked`; no normalized state or
ball-pair conclusion is assumed.  Exact cell and trace identities then replace
the source cone by `trimmedArcCellUnion K v 1` and its intersection with
`arcComplexIn K v n`.

The module is registered directly in `DifferentialGeometry.lean`.  Strict
private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
The module check and external silent audit both exited 0 with zero diagnostics
and unchanged shared outputs.  The audit dynamically enumerated the module's
single non-automatic declaration, checked twenty-three reused declarations,
found only `{propext, Classical.choice, Quot.sound}`, and passed all thirteen
applicable environment linters.

The remaining construction is the successor step: map the next cell to the
second cut-model lobe relative to the current outgoing disk, glue the two maps,
and normalize the resulting outer ball back to the first lobe while preserving
the fixed near marked point.

## 51. 2026-09-18 Normalization induction over trimmed arc cells — done

`ArcCellNormalizationInduction.lean` proves
`exists_normalized_trimmedArcCellUnion_of_cutModel`.  Given the geometric data
produced by `exists_cutModel_data`, every trimmed union with
`1 ≤ k` and `k + 1 ≤ 2 * n` admits a PL homeomorphism to the first cut-model
lobe.  It sends the arc trace to the standard marked arc, sends the outgoing
interface disk to the fixed cut disk, sends the current crossing to the cut
apex, and keeps the near crossing at the fixed marked point.

The theorem performs the finite induction internally; no normalized state or
ball-pair conclusion occurs among its hypotheses.  The base case uses the
verified `k = 1` normalization and aligns its model with the supplied fixed cut
model.  Each successor uses exactly two marked cone extensions.  The first
extends the current interface map across the next cell into the second lobe and
then glues it to the old map.  The second transports the new outgoing disk in
the outer sphere back to the fixed cut disk and normalizes the union to the
first lobe.  Injectivity of the glued homeomorphism proves that the near marked
point is outside the new outgoing disk, while the cut-model containment
`L₂.space ⊆ L.space ∪ coneSet z L₀.space` and disjointness from the old
interface put that disk in the outer sphere.

The module is registered directly in `DifferentialGeometry.lean`.  Strict
private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
The module check and external silent audit both exited 0 with zero diagnostics
and unchanged shared outputs.  The audit dynamically enumerated the module's
single non-automatic declaration, checked thirty-two reused declarations,
found only `{propext, Classical.choice, Quot.sound}`, and passed all thirteen
applicable environment linters.

The remaining layer is to instantiate this theorem with
`exists_cutModel_data` and extract `IsPLBallPair 2 1` for the final trimmed
union at `k = 2 * n - 1`.

## 52. 2026-09-18 Trimmed arc-cell union ball pair — done

`ArcCellUnionBallPair.lean` proves
`IsCombinatorialManifold.isPLBallPair_trimmedArcCellUnion`.  For a nonempty
injective simplicial arc chain in a finite closed combinatorial 3-manifold of
ambient dimension three, the union of exactly the non-endpoint cells
`1 ≤ j ≤ 2 * n - 1`, paired with its trace on `arcComplexIn K v n`, is an
`IsPLBallPair 2 1`.

The proof obtains the standard cut model, instantiates the verified finite
normalization induction at `k = 2 * n - 1`, and transports the first cut-model
lobe's ball-pair structure back along the inverse PL homeomorphism.  The
`n = 1` case is included: the trimmed union is then the single middle cell.
Neither endpoint cell is introduced, and no ball-pair or normalized-state
hypothesis is assumed.

The module is registered directly in `DifferentialGeometry.lean`.  Strict
private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
The module check and external silent audit both exited 0 with zero diagnostics
and unchanged shared outputs.  The audit dynamically enumerated the module's
single non-automatic declaration, checked the cut-model producer, the finite
normalization theorem, and ball-pair transport, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

This closes the assigned normalized arc-cell round: the natural preceding
crossing bound, the `k = 1` base, the two-extension successor induction, and
the final `IsPLBallPair 2 1` extraction are all source-complete, strictly
verified, and externally audited.

## 53. 2026-09-18 Interior-face links in manifolds with boundary — done

The realizability review invalidates one applicability claim in §§50–52.  A
finite closed combinatorial 3-manifold embedded in a three-dimensional normed
space has no intended geometric instance: its compact underlying space would
also have to be open.  Thus the three compiled closed-manifold theorems remain
valid conditional statements, but their hypotheses do not supply the actual
ambient-dimension-three `n = 1` case claimed there.  Those statements are not
accepted as the geometric arc-chain endpoint.  They are retained only as
stronger-hypothesis corollary candidates while the primary APIs are migrated to
finite combinatorial 3-manifolds with boundary and interior retained faces.

`BoundaryFaces.lean` and `DerivedCellCone.lean` now provide the reusable local
replacement.  If a face of a finite combinatorial manifold with boundary is not
a face of its boundary complex, then its geometric link and upper link are PL
spheres of the expected dimension.  In dimension three this gives a PL
2-sphere for the upper link of the barycentric vertex of an interior face.  For
two distinct comparable faces, interiority of the first face gives a PL
1-sphere for the upper link of their barycentric edge.  The latter proof uses
downward closure of the boundary complex, so no global closedness assumption is
introduced.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.
`BoundaryFaces` and `DerivedCellCone` compiled in dependency order with zero
diagnostics and unchanged shared outputs.  The external silent audit dynamically
enumerated all sixteen non-automatic declarations in the two modules, checked
six direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

The next closed result is a concrete nonvacuous `n = 1` chain in the
barycentric subdivision of a solid affine tetrahedron.  Its middle chain face
will be proved outside the boundary complex before any normalization theorem is
migrated.

## 54. 2026-09-18 A genuine one-edge interior arc — done

`ArcCellBoundaryExample.lean` proves
`exists_simplicialArc_one_with_interior_edge`.  In every finite-dimensional
real normed space of dimension three it constructs a finite combinatorial
3-manifold with boundary and an injective simplicial arc with `n = 1` whose
middle chain face is not in the boundary complex.

The complex is the barycentric subdivision of the simplex complex of an affine
tetrahedron.  The arc joins the tetrahedron barycenter to one original vertex.
The barycenter and the vertex are vertices of the subdivision, their pair is a
subdivision edge, and affine independence makes them distinct.  Boundary
subdivision invariance transports any hypothetical boundary membership of the
barycenter back to the original simplex boundary, contradicting that the
barycenter lies in the open simplex.  Downward closure of the boundary complex
then proves the whole arc edge is an interior face.

The new leaf is registered in `DifferentialGeometry.lean`.  Strict private
verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`; the module
compiled with zero diagnostics and unchanged shared outputs.  The external
silent audit dynamically enumerated its single non-automatic declaration,
checked eight direct geometric producers, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

This supplies the required nonvacuity witness before migration of the
normalization chain.  The primary boundary-manifold base theorem can now use
interiority of `arcChainFace v 1`; later successor stages use the corresponding
interiority assumption for every retained face.

## 55. 2026-09-18 Interior arc-cell links — done

`ArcCellGluing.lean` now exposes the boundary-manifold versions needed by the
normalization chain.  For a retained interior chain face,
`isPLSphere_arcCellBase_of_interior` proves that its cell base is a PL
2-sphere.  For two adjacent chain faces,
`isPLSphere_arcCellInterfaceBase_of_interior_left` proves that their interface
base is a PL 1-sphere when the left retained face is interior.  Both results
are direct specializations of the interior barycentric upper-link theorems from
§53; all conical identities, containments, and marked crossing facts remain
unchanged and require no manifold hypothesis.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module
compiled with zero diagnostics and unchanged shared outputs.  The external
silent audit dynamically enumerated all twenty-two non-automatic declarations,
checked the eighteen direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

The normalization base and successor can therefore replace global closedness
by `IsCombinatorialManifoldWithBoundary 3 K` plus interiority of the retained
chain faces.

## 56. 2026-09-18 Boundary-manifold normalization base — done

`ArcCellNormalization.lean` now makes
`exists_normalized_trimmedArcCellUnion_one_of_interior` the primary base
construction.  It assumes a finite combinatorial 3-manifold with boundary and
that `arcChainFace v 1` is outside the boundary complex.  The local results of
§55 provide exactly the PL 2-sphere cell base and PL 1-sphere outgoing
interface needed by the unchanged marked relative cone-extension argument.

The original `exists_normalized_trimmedArcCellUnion_one` is retained as a
stronger-hypothesis corollary.  A closed combinatorial manifold is a manifold
with boundary whose boundary-complex face set is empty, so the old statement
now delegates to the realizable primary theorem instead of carrying a separate
proof.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module
compiled with zero diagnostics and unchanged shared outputs.  The external
silent audit dynamically enumerated both non-automatic declarations, checked
the twenty-five direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

The remaining migration is the successor induction, with an interiority
hypothesis for every retained face `1 ≤ j ≤ 2 * n - 1`, followed by the final
ball-pair extraction.

## 57. 2026-09-18 Boundary-manifold normalization induction — done

`ArcCellNormalizationInduction.lean` now runs over a finite combinatorial
3-manifold with boundary under the natural hypothesis that every retained chain
face `arcChainFace v j`, `1 ≤ j ≤ 2 * n - 1`, is outside the boundary complex.
The base consumes §56.  At each successor, the new cell base and both incoming
and outgoing interface bases consume the appropriate local interior-face
hypothesis through §55.  The two marked cone extensions, piecewise gluing, and
normalization invariants are otherwise unchanged.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module
compiled with zero diagnostics and unchanged shared outputs.  Its external
silent audit dynamically enumerated the single non-automatic declaration,
checked thirty-two direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

## 58. 2026-09-18 Interior trimmed arc union ball pair — done

`ArcCellUnionBallPair.lean` now proves the primary endpoint
`IsCombinatorialManifoldWithBoundary.isPLBallPair_trimmedArcCellUnion_of_interior`.
For a nonempty injective simplicial arc in a finite combinatorial 3-manifold
with boundary, if every retained chain face is outside the boundary complex,
then the union of exactly the non-endpoint derived-neighborhood cells, paired
with its arc trace, is an `IsPLBallPair 2 1`.

The proof instantiates the migrated induction of §57 at `k = 2 * n - 1` and
transports the cut-model ball pair back through the resulting PL homeomorphism.
The previous closed-manifold endpoint is retained as a corollary by observing
that its boundary-complex face set is empty.  Unlike the old applicability
claim corrected in §53, the primary theorem has the concrete `n = 1` instance
constructed in §54.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module
compiled with zero diagnostics and unchanged shared outputs.  Its external
silent audit dynamically enumerated both non-automatic declarations, checked
five direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.

## 59. 2026-09-18 A genuine fully interior one-edge arc — done

`ArcCellBoundaryExample.lean` now proves
`exists_simplicialArc_one_with_all_faces_interior`.  It constructs an `n = 1`
injective simplicial arc in a finite combinatorial 3-manifold with boundary for
which all three chain faces, including both endpoint vertices, lie outside the
boundary complex.

The construction starts from §54 and retains both its interior barycenter
vertex and interior edge.  A further barycentric subdivision replaces them by
their two barycenters; their nested pair is an edge of the new subdivision.
Boundary-subdivision invariance shows that barycenters of the two old interior
faces are interior vertices of the new complex, and downward closure excludes
their connecting edge from the new boundary complex.  Thus this example does
not reuse the old boundary endpoint as a purported interior endpoint.  The
older example was strengthened to record that its barycenter endpoint, as well
as its middle edge, is interior.

Strict private verification used round token `h-round-20260919` and output root
`C:\Users\liao9\AppData\Local\Temp\codex-h-cutmodel-private`.  The module
compiled with zero diagnostics and unchanged shared outputs.  Its external
silent audit dynamically enumerated both non-automatic declarations, checked
twelve direct reused declarations, found only
`{propext, Classical.choice, Quot.sound}`, and passed all thirteen applicable
environment linters.
