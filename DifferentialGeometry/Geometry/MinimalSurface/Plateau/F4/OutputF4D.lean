import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexConsFIX2

/-!
# O-MY-F4D G1：F4（R9 producer）输出包骨架（`_F4D`）

设计文档：`docs/geometrization/chapter8/design-F4-producer-20261006.md`。本文件只含 `def` / `structure`
与已证小引理（无 sorry，无新 admission）：

* `collisionSet_F4D F`：源碰撞集（= FIX2 S6 右边的集合，逐字）；`tangencySet_F4D F`：非横截碰撞源点（= S7 前件）。
* `IsCollisionNodalAt_F4D F z w ρ`：`IsCollisionNodal_FIX2` 固定半径 `ρ` 的版本（`Iff.rfl` 对齐），给 F4-b 的
  finite nodal cover 用（chart 半径要能被引用）。
* `IsAnalyticArcGraph_F4D K V γ`：平面路线 (ii) 的输出形——有限顶点集 `V` + 有限条 embedded 正则弧
  `γ e : [0,1] → ℂ`（闭区间 `C^∞`，开区间实解析），弧只在顶点相交。
* `IsAdaptedTriangulation_F4D T α K V`：F4-b 的输出形——S1–S3 字段**逐字复用 FIX2 的类型**，外加
  `K = α(|S|)`（S6 形）与 `V ⊆ α(T.vertices)`（S7 形）。
* `IsThickeningOutput_F4D`：F4-c 的输出形（S5 八个字段 + S9 `local_product` + S10 `ambient_collar`）。
* `F4Output_F4D`：按车道分组的 24 字段包（输入 S4 / F4-a S8 / F4-b / F4-c），
  `f4Output_iff_prepared_F4D` 证明它与 `IsPreparedSheetComplex_FIX2` 等价（分组无信息损失）。

inhabitants：`segment_isAnalyticArcGraph_F4D`（一条线段）、平坦盘 `flatDisk_f4Output_F4D`
（由 `flatDisk_prepared_FIX2` 经等价得到；其 `.tri` / `.thick` 给另两个结构的 inhabitant）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

/-! ## 碰撞集与 tangency 集 -/

section Sets

variable {M : Type u}

/-- 源碰撞集：`z ∈ D̄` 且存在 `w ∈ D̄`、`w ≠ z`、`F w = F z`（= FIX2 S6 右边的集合）。 -/
def collisionSet_F4D (F : ℂ → M) : Set ℂ :=
  {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧
    ∃ w ∈ Metric.closedBall (0 : ℂ) 1, w ≠ z ∧ F w = F z}

theorem mem_collisionSet_F4D_symm {F : ℂ → M} {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (hwz : w ≠ z) (hF : F w = F z) :
    w ∈ collisionSet_F4D F :=
  ⟨hw, z, hz, hwz.symm, hF.symm⟩

end Sets

section Tangency

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- 非横截（tangential）碰撞源点：`z, w ∈ D°`、`z ≠ w`、`F z = F w`、`dF_z ⊕ (−dF_w)` 非满射（= S7 前件）。 -/
def tangencySet_F4D (F : ℂ → M) : Set ℂ :=
  {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ ∃ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w ∧ F z = F w ∧
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w)))}

/-- `IsCollisionNodal_FIX2` 固定半径 `ρ` 的版本（body 与 FIX2 逐字相同；`ρ` 从 `∃` 中取出）。 -/
def IsCollisionNodalAt_F4D (F : ℂ → M) (z w : ℂ) (ρ : ℝ) : Prop :=
  ∃ (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ), 0 < ρ ∧ 1 ≤ k ∧
    Disjoint (Metric.ball z ρ) (Metric.ball w ρ) ∧
    Metric.ball z ρ ⊆ Metric.ball 0 1 ∧ Metric.ball w ρ ⊆ Metric.ball 0 1 ∧
    InjOn F (Metric.ball z ρ) ∧ InjOn F (Metric.ball w ρ) ∧
    (∀ m, Γ m 0 = z ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
      HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) (Metric.ball z ρ)) ∧
    (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
      ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
    (∀ z' ∈ Metric.ball z ρ,
      (∃ w' ∈ Metric.ball w ρ, F z' = F w') ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z' = Γ m r) ∧
    ∀ m, ∀ r ∈ Ioo 0 ρ, ∀ w' ∈ Metric.ball w ρ, F (Γ m r) = F w' →
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (Γ m r)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w')))

/-- 对齐：`IsCollisionNodal_FIX2 = ∃ ρ, IsCollisionNodalAt_F4D`（定义层面相等）。 -/
theorem isCollisionNodal_FIX2_iff_F4D {F : ℂ → M} {z w : ℂ} :
    IsCollisionNodal_FIX2 (E := E) F z w ↔ ∃ ρ, IsCollisionNodalAt_F4D (E := E) F z w ρ :=
  Iff.rfl

variable {F : ℂ → M} {z w : ℂ} {ρ : ℝ}

theorem IsCollisionNodalAt_F4D.pos (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) : 0 < ρ := by
  obtain ⟨_, _, _, hρ, _⟩ := h
  exact hρ

theorem IsCollisionNodalAt_F4D.ball_left_subset (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) :
    Metric.ball z ρ ⊆ Metric.ball 0 1 := by
  obtain ⟨_, _, _, _, _, _, hz, _⟩ := h
  exact hz

theorem IsCollisionNodalAt_F4D.ball_right_subset (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) :
    Metric.ball w ρ ⊆ Metric.ball 0 1 := by
  obtain ⟨_, _, _, _, _, _, _, hw, _⟩ := h
  exact hw

theorem IsCollisionNodalAt_F4D.disjoint (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) :
    Disjoint (Metric.ball z ρ) (Metric.ball w ρ) := by
  obtain ⟨_, _, _, _, _, hd, _⟩ := h
  exact hd

theorem IsCollisionNodalAt_F4D.injOn_left (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) :
    InjOn F (Metric.ball z ρ) := by
  obtain ⟨_, _, _, _, _, _, _, _, hinj, _⟩ := h
  exact hinj

theorem IsCollisionNodalAt_F4D.injOn_right (h : IsCollisionNodalAt_F4D (E := E) F z w ρ) :
    InjOn F (Metric.ball w ρ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hinj, _⟩ := h
  exact hinj

end Tangency

/-! ## 平面路线 (ii)：有限解析弧图 -/

section ArcGraph

/-- **有限解析弧图**（平面路线 (ii) 的输出形）：`K = V ∪ ⋃ₑ γₑ([0,1])`，`V` 有限，边集 `ι` 有限；
每条边 `γ e` 在 `[0,1]` 上 `C^∞`（D-R-MY4-15 smooth-up-to-endpoint）、在 `(0,1)` 上实解析、正则、单射，
两端在 `V` 里；开边与 `V` 不交、与其它边（含端点）不交。允许多重边与同一顶点处相切（cusp），不允许 loop
（`InjOn` on `Icc` ⇒ 两端不同）。 -/
structure IsAnalyticArcGraph_F4D (K V : Set ℂ) {ι : Type*} (γ : ι → ℝ → ℂ) : Prop where
  V_finite : V.Finite
  edges_finite : Finite ι
  eq_union : K = V ∪ ⋃ e, γ e '' Icc 0 1
  ends : ∀ e, γ e 0 ∈ V ∧ γ e 1 ∈ V
  smooth : ∀ e, ContDiffOn ℝ ∞ (γ e) (Icc 0 1)
  analytic : ∀ e, AnalyticOnNhd ℝ (γ e) (Ioo 0 1)
  regular : ∀ e, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (γ e) (Icc 0 1) t ≠ 0
  inj : ∀ e, InjOn (γ e) (Icc 0 1)
  interior_disjoint : ∀ e e', e ≠ e' → Disjoint (γ e '' Ioo 0 1) (γ e' '' Icc 0 1)
  interior_avoid : ∀ e, Disjoint (γ e '' Ioo 0 1) V

/-- 弧图的 `K` 紧（有限个紧弧之并）。 -/
theorem IsAnalyticArcGraph_F4D.isCompact {K V : Set ℂ} {ι : Type*} {γ : ι → ℝ → ℂ}
    (hG : IsAnalyticArcGraph_F4D K V γ) : IsCompact K := by
  have := hG.edges_finite
  rw [hG.eq_union]
  exact hG.V_finite.isCompact.union
    (isCompact_iUnion fun e => isCompact_Icc.image_of_continuousOn (hG.smooth e).continuousOn)

/-- inhabitant：`[0,1] ⊂ ℂ` 一条线段，顶点 `{0, 1}`。 -/
theorem segment_isAnalyticArcGraph_F4D :
    IsAnalyticArcGraph_F4D ({0, 1} ∪ ⋃ _e : Unit, (fun t : ℝ => (t : ℂ)) '' Icc 0 1) {0, 1}
      (fun (_ : Unit) (t : ℝ) => (t : ℂ)) where
  V_finite := (Set.finite_singleton 1).insert 0
  edges_finite := inferInstance
  eq_union := rfl
  ends := fun _ => ⟨by simp, by simp⟩
  smooth := fun _ => Complex.ofRealCLM.contDiff.contDiffOn
  analytic := fun _ => Complex.ofRealCLM.analyticOnNhd _
  regular := fun _ t ht => by
    have hd : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)]
    exact one_ne_zero
  inj := fun _ => Complex.ofReal_injective.injOn
  interior_disjoint := fun e e' he => absurd (Subsingleton.elim e e') he
  interior_avoid := fun _ => by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hmem
    rcases hmem with h | h
    · exact ht0.ne' (Complex.ofReal_eq_zero.1 h)
    · exact ht1.ne (Complex.ofReal_eq_one.1 h)

end ArcGraph

/-! ## F4-b：adapted triangulation（S1–S3 逐字复用 FIX2 字段类型，+ S6 形 + S7 形） -/

section Triangulation

/-- **F4-b 输出形**：`T` 有限平面 2-复形、`α : |T| → D̄`（S1–S3，字段类型与 `IsPreparedSheetComplex_FIX2`
逐字相同：单向 Lipschitz、逐 2-面去顶点 `C^∞` 且导数单射——允许 cusp 顶点退化，D-R-MY4-16），
`K = α(|S|)`（`S` 子复形，S6 形），`V ⊆ α(T.vertices)`（S7 形）。 -/
structure IsAdaptedTriangulation_F4D (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ)
    (K V : Set ℂ) : Prop where
  faces_finite : T.faces.Finite
  dim_le : ∀ s ∈ T.faces, s.card ≤ 3
  alpha_bij : BijOn α T.space (Metric.closedBall 0 1)
  alpha_cont : ContinuousOn α T.space
  alpha_bdry : ∀ {z : ℂ}, z ∈ T.space → (‖α z‖ = 1 ↔ z ∈ frontier T.space)
  alpha_lip : ∃ L : ℝ≥0, LipschitzOnWith L α T.space
  alpha_smooth : ∀ s ∈ T.faces, s.card = 3 →
    ContDiffOn ℝ ∞ α (convexHull ℝ (s : Set ℂ) \ (s : Set ℂ))
  alpha_rank : ∀ s ∈ T.faces, s.card = 3 → ∀ z ∈ convexHull ℝ (s : Set ℂ) \ (s : Set ℂ),
    Function.Injective (fderivWithin ℝ α (convexHull ℝ (s : Set ℂ)) z)
  subcomplex : ∃ S ⊆ T.faces, α '' (⋃ s ∈ S, convexHull ℝ (s : Set ℂ)) = K
  vertices : V ⊆ α '' T.vertices

/-- 换 `K`、缩 `V`：两种调整都保持 adapted。 -/
theorem IsAdaptedTriangulation_F4D.mono {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {α : ℂ → ℂ} {K V V' : Set ℂ} (hT : IsAdaptedTriangulation_F4D T α K V) (hV : V' ⊆ V) :
    IsAdaptedTriangulation_F4D T α K V' :=
  { hT with vertices := hV.trans hT.vertices }

end Triangulation

/-! ## F4-c 输出形与 24 字段分组包 -/

section Output

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **F4-c 输出形**（对固定 `(T, α)`）：S5 八个字段 + S9 `local_product` + S10 `ambient_collar`
（同一个 `Nb = h(|A|)`，D-R-MY4-4/5/6：统一构造，消费者不得从 `collar` 之名推出乘积结构）。 -/
structure IsThickeningOutput_F4D (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) (N : ℕ)
    (A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (φ : ℂ → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N) → M) : Prop where
  A_finite : A.faces.Finite
  A_manifold : IsCombinatorialManifoldWithBoundary 3 A
  h_cont : ContinuousOn h A.space
  h_inj : InjOn h A.space
  face_map : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card
  factor : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z)
  bdry_frontier : ∀ θ, f (diskBoundary θ) ∈ frontier (h '' A.space)
  int_interior : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z ∈ interior (h '' A.space)
  local_product : HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space)
  ambient_collar : HasAmbientCollar_R10 (h '' A.space)

/-- **F4 producer 输出包**（24 字段按来源分组）：`ext/rank/collar`（S4，R8 已有输入）、
`nodal`（S8，F4-a）、`tri`（S1–S3 + S6 + S7，F4-b，`K = collisionSet_F4D F`、
`V = tangencySet_F4D F`）、`thick`（S5 + S9 + S10，F4-c）。 -/
structure F4Output_F4D (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) (N : ℕ)
    (A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (φ : ℂ → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N) → M) : Prop where
  ext : SmoothDiskExtension (E := E) f F
  rank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z)
  collar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w
  nodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
    IsCollisionNodal_FIX2 (E := E) F z w
  tri : IsAdaptedTriangulation_F4D T α (collisionSet_F4D F) (tangencySet_F4D (E := E) F)
  thick : IsThickeningOutput_F4D (E := E) f F T α N A φ h

variable {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
  {α : ℂ → ℂ} {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
  {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}

/-- **装配**：分组包 ⇒ 24 字段 `IsPreparedSheetComplex_FIX2`（字段逐一取出；S6 = `tri.subcomplex`，
S7 由 `tri.vertices` 读出）。 -/
theorem F4Output_F4D.prepared (hout : F4Output_F4D (E := E) f F T α N A φ h) :
    IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h where
  faces_finite := hout.tri.faces_finite
  dim_le := hout.tri.dim_le
  alpha_bij := hout.tri.alpha_bij
  alpha_cont := hout.tri.alpha_cont
  alpha_bdry := hout.tri.alpha_bdry
  alpha_lip := hout.tri.alpha_lip
  alpha_smooth := hout.tri.alpha_smooth
  alpha_rank := hout.tri.alpha_rank
  ext := hout.ext
  rank := hout.rank
  collar := hout.collar
  A_finite := hout.thick.A_finite
  A_manifold := hout.thick.A_manifold
  h_cont := hout.thick.h_cont
  h_inj := hout.thick.h_inj
  face_map := hout.thick.face_map
  factor := hout.thick.factor
  bdry_frontier := hout.thick.bdry_frontier
  int_interior := hout.thick.int_interior
  collision_subcomplex := hout.tri.subcomplex
  tangency_vertices := fun z hz w hw hzw hFzw hns => by
    obtain ⟨v, hv, hαv⟩ := hout.tri.vertices ⟨hz, w, hw, hzw, hFzw, hns⟩
    exact ⟨v, hv, hαv⟩
  nodal := hout.nodal
  local_product := hout.thick.local_product
  ambient_collar := hout.thick.ambient_collar

/-- 反向：24 字段 prepared ⇒ 分组包（分组无信息损失）。 -/
theorem IsPreparedSheetComplex_FIX2.f4Output_F4D
    (hprep : IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h) :
    F4Output_F4D (E := E) f F T α N A φ h where
  ext := hprep.ext
  rank := hprep.rank
  collar := hprep.collar
  nodal := hprep.nodal
  tri :=
    { faces_finite := hprep.faces_finite
      dim_le := hprep.dim_le
      alpha_bij := hprep.alpha_bij
      alpha_cont := hprep.alpha_cont
      alpha_bdry := hprep.alpha_bdry
      alpha_lip := hprep.alpha_lip
      alpha_smooth := hprep.alpha_smooth
      alpha_rank := hprep.alpha_rank
      subcomplex := hprep.collision_subcomplex
      vertices := by
        rintro z ⟨hz, w, hw, hzw, hFzw, hns⟩
        obtain ⟨v, hv, hαv⟩ := hprep.tangency_vertices z hz w hw hzw hFzw hns
        exact ⟨v, hv, hαv⟩ }
  thick :=
    { A_finite := hprep.A_finite
      A_manifold := hprep.A_manifold
      h_cont := hprep.h_cont
      h_inj := hprep.h_inj
      face_map := hprep.face_map
      factor := hprep.factor
      bdry_frontier := hprep.bdry_frontier
      int_interior := hprep.int_interior
      local_product := hprep.local_product
      ambient_collar := hprep.ambient_collar }

/-- 分组包 ⇔ 24 字段 notion。 -/
theorem f4Output_iff_prepared_F4D :
    F4Output_F4D (E := E) f F T α N A φ h ↔
      IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h :=
  ⟨F4Output_F4D.prepared, IsPreparedSheetComplex_FIX2.f4Output_F4D⟩

/-- **车道装配**（R9 producer 的拆分形）：S4 输入 + F4-a（S8）+ F4-b（对 `collisionSet` / `tangencySet` 的
adapted `(T, α)`）+ F4-c（该 `(T, α)` 上的 thickening）⇒ 24 字段 prepared。 -/
theorem prepared_of_lane_outputs_F4D (hext : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w)
    (hnodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
      IsCollisionNodal_FIX2 (E := E) F z w)
    (htri : IsAdaptedTriangulation_F4D T α (collisionSet_F4D F) (tangencySet_F4D (E := E) F))
    (hthick : IsThickeningOutput_F4D (E := E) f F T α N A φ h) :
    IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h :=
  F4Output_F4D.prepared ⟨hext, hrank, hcollar, hnodal, htri, hthick⟩

end Output

/-! ## inhabitants（平坦盘） -/

/-- 平坦盘的分组包（由 `flatDisk_prepared_FIX2` 经等价得到）。 -/
theorem flatDisk_f4Output_F4D :
    F4Output_F4D (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX radialGrid_FIX 3
      bipyramid_FIX (⇑flatAffine_FIX) bipyramidRealization_FIX :=
  flatDisk_prepared_FIX2.f4Output_F4D

/-- 平坦盘：adapted triangulation 的 inhabitant（碰撞集与 tangency 集都空）。 -/
theorem flatDisk_adaptedTriangulation_F4D :
    IsAdaptedTriangulation_F4D triComplex_FIX radialGrid_FIX
      (collisionSet_F4D (⇑flatCLM_FIX)) (tangencySet_F4D (E := E3_FIX) (⇑flatCLM_FIX)) :=
  flatDisk_f4Output_F4D.tri

/-- 平坦盘：thickening 输出的 inhabitant。 -/
theorem flatDisk_thickeningOutput_F4D :
    IsThickeningOutput_F4D (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX 3 bipyramid_FIX (⇑flatAffine_FIX) bipyramidRealization_FIX :=
  flatDisk_f4Output_F4D.thick

end DifferentialGeometry.Geometry
