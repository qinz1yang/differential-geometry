import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCollapse
import DifferentialGeometry.Topology.FundamentalGroup.Retraction

/-!
# O-MY-R10PL G1：R10.1 relative regular neighborhood（notion + producer，`_R10`）

D-R-MY2-16：`N` 是与 boundary trace 适配的紧连通 relative PL 3-neighborhood（`hb(|Ab|)`，`Ab` 组合 3-流形），
`L = f(D̄) ⊆ N`，`R : N → L` 是固定 `L` 的连续 retraction，且有 strong deformation retraction `H`，
显式 `π₁(L) ↠ π₁(N)`；**不**要求整个 ambient retract 到 `L`。

* `IsRelRegularNbhd_R10`：notion，∧-链与 scratch `MYD3/R10R14.lean:51` **逐字同序**（S-MY-R11PL 解包消费）。
* `IsRelRegularNbhd_R10.of_collapse`：从 compact + manifold 数据 + trace 条款 + retraction / deformation
  直接装配 notion；connectedness 与 `π₁` 满射由 deformation **推出**（不再是独立义务）。
* `relative_regular_nbhd_spine_R10`（producer）：prepared 数据（`IsPreparedSheetComplex_FIX`）⇒
  `N = h(|N(L, A'')|)`，`L` 是 `φ(T)` 在 `A` 里的像子复形，`N(L, A'')` 是 PL 库的 derived neighborhood
  （组合流形：`IsCombinatorialManifoldWithBoundary.derivedNeighborhood`；collapse：barycentric projection
  的直线 homotopy），再经 `h` 的 compact embedding 推到 `M`。
* consumer：`flatDisk_relRegularNbhd_R10`（对 `flatDisk_prepared_FIX` 实例化，非空）。

R-MY3（经 lead 转达）：一般 SDR 推不出 R10.2 的两侧结构；10.1 与 10.2 须**共同选择同一个 witness**，
见 `CollisionEdgeSidesR10.lean` 的 `IsSectorControlledCollapse_R10`。本文件的 producer 只给 10.1。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal unitInterval

namespace DifferentialGeometry.Geometry

universe u

/-! ## notion -/

section Notion

variable {M : Type u} [TopologicalSpace M]

/-- R10.1 的输出 notion（∧-链与 scratch `MYD3/R10R14.lean:51` 逐字同序）：`Nb` 紧连通、是嵌入的组合 3-流形
`hb(|Ab|)`；trace 在 frontier、内部盘在 interior；`R : Nb → L = range f` 连续 retraction，且有 strong
deformation retraction `H`（`H 0 = id`，`H 1 = R`，固定 `L`）；显式 `π₁(L) ↠ π₁(Nb)`。 -/
def IsRelRegularNbhd_R10 (f : C(closedDisk, M)) (Nb : Set M) (R : M → M) : Prop :=
  IsCompact Nb ∧ IsConnected Nb ∧
  (∃ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
    (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite ∧
    IsCombinatorialManifoldWithBoundary 3 Ab ∧
    ContinuousOn hb Ab.space ∧ InjOn hb Ab.space ∧ hb '' Ab.space = Nb) ∧
  (∀ θ, f (diskBoundary θ) ∈ frontier Nb) ∧
  (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z ∈ interior Nb) ∧
  ContinuousOn R Nb ∧ MapsTo R Nb (Set.range f) ∧ (∀ x ∈ Set.range f, R x = x) ∧
  (∃ H : unitInterval × M → M, ContinuousOn H (univ ×ˢ Nb) ∧ (∀ x ∈ Nb, H (0, x) = x) ∧
    (∀ x ∈ Nb, H (1, x) = R x) ∧ (∀ t, ∀ x ∈ Set.range f, H (t, x) = x) ∧
    ∀ t, MapsTo (fun x => H (t, x)) Nb Nb) ∧
  ∃ hLN : Set.range f ⊆ Nb, ∀ x₀ : Set.range f, Function.Surjective
    (FundamentalGroup.map (⟨Set.inclusion hLN, continuous_inclusion hLN⟩ : C(Set.range f, Nb)) x₀)

/-- deformation `H`（`H 0 = id`，`H 1 = R`，`H t` 保持 `Nb`）⇒ `Nb` 中每点经路径 `t ↦ H(t, x)` 连到 `R x`。 -/
theorem joinedIn_retraction_R10 {Nb : Set M} {R : M → M} {H : unitInterval × M → M}
    (hHc : ContinuousOn H (univ ×ˢ Nb)) (hH0 : ∀ x ∈ Nb, H (0, x) = x)
    (hH1 : ∀ x ∈ Nb, H (1, x) = R x) (hHm : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb)
    {x : M} (hx : x ∈ Nb) : JoinedIn Nb x (R x) := by
  let γ : Path x (R x) :=
    { toFun := fun t => H (t, x)
      continuous_toFun := hHc.comp_continuous (continuous_id.prodMk continuous_const)
        fun _ => ⟨mem_univ _, hx⟩
      source' := hH0 x hx
      target' := hH1 x hx }
  exact ⟨γ, fun t => hHm t hx⟩

/-- `S ⊆ Nb` path-connected 且 `Nb` deformation 到 `S` ⇒ `Nb` path-connected。 -/
theorem isPathConnected_of_deformation_R10 {S Nb : Set M} (hSN : S ⊆ Nb) (hS : IsPathConnected S)
    {R : M → M} (hRm : MapsTo R Nb S) {H : unitInterval × M → M}
    (hHc : ContinuousOn H (univ ×ˢ Nb)) (hH0 : ∀ x ∈ Nb, H (0, x) = x)
    (hH1 : ∀ x ∈ Nb, H (1, x) = R x) (hHm : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb) :
    IsPathConnected Nb := by
  obtain ⟨x₀, hx₀, hjoin⟩ := hS
  refine ⟨x₀, hSN hx₀, fun {y} hy => ?_⟩
  exact ((hjoin (hRm hy)).mono hSN).trans (joinedIn_retraction_R10 hHc hH0 hH1 hHm hy).symm

/-- deformation retraction ⇒ inclusion `S ↪ Nb` 在每个 basepoint 上 `π₁` 满射（经 homotopy equivalence；
只用 `R` 固定 `S`、`H 0 = id`、`H 1 = R`）。 -/
theorem surjective_fundamentalGroup_inclusion_R10 {S Nb : Set M} (hSN : S ⊆ Nb)
    {R : M → M} (hRc : ContinuousOn R Nb) (hRm : MapsTo R Nb S) (hRfix : ∀ x ∈ S, R x = x)
    {H : unitInterval × M → M} (hHc : ContinuousOn H (univ ×ˢ Nb))
    (hH0 : ∀ x ∈ Nb, H (0, x) = x) (hH1 : ∀ x ∈ Nb, H (1, x) = R x)
    (hHm : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb) (x₀ : S) :
    Function.Surjective
      (FundamentalGroup.map (⟨Set.inclusion hSN, continuous_inclusion hSN⟩ : C(S, Nb)) x₀) := by
  let ι : C(S, Nb) := ⟨Set.inclusion hSN, continuous_inclusion hSN⟩
  let ρ : C(Nb, S) := ⟨fun x => ⟨R x, hRm x.2⟩, hRc.domRestrict.subtype_mk _⟩
  let G : ContinuousMap.Homotopy (ContinuousMap.id Nb) (ι.comp ρ) :=
    { toFun := fun p => ⟨H (p.1, (p.2 : M)), hHm p.1 p.2.2⟩
      continuous_toFun := (hHc.comp_continuous
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
        fun p => ⟨mem_univ _, p.2.2⟩).subtype_mk _
      map_zero_left := fun x => Subtype.ext (hH0 x x.2)
      map_one_left := fun x => Subtype.ext (hH1 x x.2) }
  have hρι : ρ.comp ι = ContinuousMap.id S :=
    ContinuousMap.ext fun x => Subtype.ext (hRfix x.1 x.2)
  let e : ContinuousMap.HomotopyEquiv Nb S :=
    { toFun := ρ
      invFun := ι
      left_inv := ⟨G.symm⟩
      right_inv := by
        rw [hρι] }
  exact (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e ι
    (fun x => Subtype.ext (hRfix x.1 x.2)) x₀).2

/-- 装配：compact + manifold 数据 + trace 条款 + retraction `R` + deformation `H` ⇒ notion
（connectedness 与 `π₁` 满射由 `H` 推出）。 -/
theorem IsRelRegularNbhd_R10.of_collapse {f : C(closedDisk, M)} {Nb : Set M} {R : M → M}
    (hc : IsCompact Nb)
    (hman : ∃ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 Ab ∧
      ContinuousOn hb Ab.space ∧ InjOn hb Ab.space ∧ hb '' Ab.space = Nb)
    (hbd : ∀ θ, f (diskBoundary θ) ∈ frontier Nb)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z ∈ interior Nb)
    (hLN : Set.range f ⊆ Nb) (hRc : ContinuousOn R Nb) (hRm : MapsTo R Nb (Set.range f))
    (hRfix : ∀ x ∈ Set.range f, R x = x) (H : unitInterval × M → M)
    (hHc : ContinuousOn H (univ ×ˢ Nb)) (hH0 : ∀ x ∈ Nb, H (0, x) = x)
    (hH1 : ∀ x ∈ Nb, H (1, x) = R x) (hHfix : ∀ t, ∀ x ∈ Set.range f, H (t, x) = x)
    (hHm : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb) :
    IsRelRegularNbhd_R10 f Nb R :=
  ⟨hc, (isPathConnected_of_deformation_R10 hLN (isPathConnected_range f.continuous) hRm hHc hH0
      hH1 hHm).isConnected, hman, hbd, hint, hRc, hRm, hRfix,
    ⟨H, hHc, hH0, hH1, hHfix, hHm⟩,
    hLN, surjective_fundamentalGroup_inclusion_R10 hLN hRc hRm hRfix hHc hH0 hH1 hHm⟩

end Notion

/-! ## compact embedding 的连续逆 -/

/-- compact 集上连续单射到 Hausdorff 空间：`invFunOn` 在像上连续（闭集原像 = 紧集的像）。 -/
theorem exists_continuousOn_leftInverse_R10 {X Y : Type*} [TopologicalSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] {K : Set X} (hK : IsCompact K) {h : X → Y}
    (hc : ContinuousOn h K) (hi : InjOn h K) :
    ∃ g : Y → X, ContinuousOn g (h '' K) ∧ MapsTo g (h '' K) K ∧ (∀ x ∈ K, g (h x) = x) ∧
      ∀ y ∈ h '' K, h (g y) = y := by
  refine ⟨Function.invFunOn h K, ?_, fun y hy => Function.invFunOn_mem hy,
    fun x hx => hi.leftInvOn_invFunOn hx, fun y hy => Function.invFunOn_eq hy⟩
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨h '' (t ∩ K), ((hK.inter_left ht).image_of_continuousOn
    (hc.mono inter_subset_right)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hyt, hyK⟩
    refine ⟨⟨_, ⟨hyt, Function.invFunOn_mem hyK⟩, Function.invFunOn_eq hyK⟩, hyK⟩
  · rintro ⟨⟨x, ⟨hxt, hxK⟩, rfl⟩, hyK⟩
    refine ⟨?_, hyK⟩
    change Function.invFunOn h K (h x) ∈ t
    rw [hi.leftInvOn_invFunOn hxK]
    exact hxt

/-! ## PL 层：像子复形与 derived neighborhood collapse（一般 `E`，classical decidability） -/

section PL

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 有限复形的 space 是紧的。 -/
theorem isCompact_space_of_finite_R10 (K : _root_.Geometry.SimplicialComplex ℝ F)
    (hK : K.faces.Finite) : IsCompact K.space :=
  hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)

/-- `φ(T)` 在 `A` 里的像子复形：`A` 的面中包含在某个 `φ(s)`（`s ∈ T`）里的那些。 -/
def preparedImageComplex_R10 (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (φ : ℂ → F)
    (A : _root_.Geometry.SimplicialComplex ℝ F) : _root_.Geometry.SimplicialComplex ℝ F where
  faces := {t | t ∈ A.faces ∧ ∃ s ∈ T.faces, (t : Set F) ⊆ φ '' (s : Set ℂ)}
  isRelLowerSet_faces := by
    rintro t ⟨ht, s, hs, hts⟩
    refine ⟨A.nonempty_of_mem_faces ht, fun g hgt hg => ⟨A.down_closed ht hgt hg, s, hs, ?_⟩⟩
    exact (Finset.coe_subset.mpr hgt).trans hts
  indep h := A.indep h.1
  inter_subset_convexHull h₁ h₂ := A.inter_subset_convexHull h₁.1 h₂.1

theorem preparedImageComplex_faces_subset_R10 (T : _root_.Geometry.SimplicialComplex ℝ ℂ)
    (φ : ℂ → F) (A : _root_.Geometry.SimplicialComplex ℝ F) :
    (preparedImageComplex_R10 T φ A).faces ⊆ A.faces := fun _ ht => ht.1

/-- 像子复形的 space = `|φ|(|T|)`（逐面：`|φ|(conv s) = conv φ(s)`）。 -/
theorem preparedImageComplex_space_R10 (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (φ : ℂ → F)
    (A : _root_.Geometry.SimplicialComplex ℝ F)
    (hface : ∀ s ∈ T.faces, ∃ t ∈ A.faces, (t : Set F) = φ '' (s : Set ℂ)) :
    (preparedImageComplex_R10 T φ A).space = simplicialMap T φ '' T.space := by
  classical
  apply Subset.antisymm
  · intro y hy
    obtain ⟨t, ⟨-, s, hs, hts⟩, hyt⟩ :=
      _root_.Geometry.SimplicialComplex.mem_space_iff.mp hy
    have hy' : y ∈ convexHull ℝ (φ '' (s : Set ℂ)) := convexHull_mono hts hyt
    rw [← Finset.coe_image, ← image_convexHull_simplicialMap_of_finiteDimensional T φ hs] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, T.convexHull_subset_space hs hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hts⟩ := hface s hs
    have hmem : simplicialMap T φ x ∈ convexHull ℝ (t : Set F) := by
      rw [hts, ← Finset.coe_image, ← image_convexHull_simplicialMap_of_finiteDimensional T φ hs]
      exact mem_image_of_mem _ hxs
    exact (preparedImageComplex_R10 T φ A).convexHull_subset_space ⟨ht, s, hs, hts.subset⟩ hmem

variable [FiniteDimensional ℝ F]

open Classical in
/-- PL collapse（一般 `F`）：组合 3-流形 `A` 的子复形 `L` 的 derived neighborhood `Ab = N(L, A'')` 是有限组合
3-流形、`|L| ⊆ |Ab| ⊆ |A|`、`|Ab|` 是 `|L|` 在 `|A|` 里的邻域；barycentric projection `P` 是 `|Ab| → |L|` 的
retraction，直线 homotopy `Hm` 是固定 `|L|` 的 strong deformation retraction。 -/
theorem exists_derivedNbhd_collapse_R10 (A L : _root_.Geometry.SimplicialComplex ℝ F)
    (hAfin : A.faces.Finite) (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hL : L.faces ⊆ A.faces) :
    ∃ (Ab : _root_.Geometry.SimplicialComplex ℝ F) (P : F → F) (Hm : unitInterval × F → F),
      Ab.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 Ab ∧ Ab.space ⊆ A.space ∧
      L.space ⊆ Ab.space ∧ (∀ x ∈ L.space, Ab.space ∈ 𝓝[A.space] x) ∧
      ContinuousOn P Ab.space ∧ MapsTo P Ab.space L.space ∧ (∀ x ∈ L.space, P x = x) ∧
      ContinuousOn Hm (univ ×ˢ Ab.space) ∧ (∀ x ∈ Ab.space, Hm (0, x) = x) ∧
      (∀ x ∈ Ab.space, Hm (1, x) = P x) ∧ (∀ t, ∀ x ∈ L.space, Hm (t, x) = x) ∧
      ∀ t, MapsTo (fun x => Hm (t, x)) Ab.space Ab.space := by
  have : Finite A.faces := hAfin.to_subtype
  let P : F → F :=
    subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision L)
  have hPc : ContinuousOn P (derivedNeighborhood A L).space :=
    continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
  refine ⟨derivedNeighborhood A L, P,
    fun p => subcomplexBarycentricHomotopy (barycentricSubdivision A) (barycentricSubdivision L)
      p.1 p.2,
    derivedNeighborhood_faces_finite A L, hA.derivedNeighborhood L,
    derivedNeighborhood_space_subset A L, subcomplex_space_subset_derivedNeighborhood hL,
    fun x hx => derivedNeighborhood_mem_nhdsWithin hL hx, hPc,
    fun x hx => subcomplexBarycentricProjection_mem_subcomplex hL hx,
    fun x hx => subcomplexBarycentricProjection_eq_self_on_subcomplex hL hx, ?_, ?_, ?_, ?_,
    fun t x hx => subcomplexBarycentricHomotopy_mem_derivedNeighborhood hx t⟩
  · change ContinuousOn (fun p : unitInterval × F => (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • P p.2) _
    have h1 : Continuous fun p : unitInterval × F => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub h1).smul continuous_snd).continuousOn.add
      (h1.continuousOn.smul (hPc.comp continuousOn_snd fun p hp => hp.2))
  · intro x _
    simp [subcomplexBarycentricHomotopy]
  · intro x _
    simp [subcomplexBarycentricHomotopy, P]
  · intro t x hx
    have hPx : P x = x := subcomplexBarycentricProjection_eq_self_on_subcomplex hL hx
    change (1 - (t : ℝ)) • x + (t : ℝ) • P x = x
    rw [hPx, ← add_smul, sub_add_cancel, one_smul]

end PL

/-! ## producer：prepared 数据 ⇒ R10.1 -/

section Producer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- prepared 数据：`L = f(D̄)` 是像子复形经 `h` 的像（`h ∘ |φ| = f ∘ α`，`α : |T| ≅ D̄`）。 -/
theorem IsPreparedSheetComplex_FIX.range_eq_R10 {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) :
    Set.range f = h '' (preparedImageComplex_R10 T φ A).space := by
  rw [preparedImageComplex_space_R10 T φ A fun s hs =>
    ⟨s.image φ, (hprep.face_map s hs).1, Finset.coe_image⟩, image_image]
  have h1 : Set.range f = diskExtension f '' Metric.closedBall (0 : ℂ) 1 := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, diskExtension_coe f z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, (diskExtension_coe f ⟨z, hz⟩).symm⟩
  rw [h1, ← hprep.alpha_bij.image_eq, image_image]
  exact image_congr fun z hz => (hprep.factor z hz).symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **R10.1 producer**：prepared 数据 ⇒ `∃ Nb R, IsRelRegularNbhd_R10 f Nb R`，且 `Nb ⊆ h(|A|)`。
`Nb = h(|N(L, A'')|)`（`L` = 像子复形），`R = h ∘ P ∘ h⁻¹`（`P` = barycentric projection），
`H(t, y) = h(Hm(t, h⁻¹ y))`。 -/
theorem relative_regular_nbhd_spine_R10 [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) :
    ∃ (Nb : Set M) (R : M → M), IsRelRegularNbhd_R10 f Nb R ∧ Nb ⊆ h '' A.space := by
  set L := preparedImageComplex_R10 T φ A with hLdef
  have hLA : L.faces ⊆ A.faces := preparedImageComplex_faces_subset_R10 T φ A
  have hLAs : L.space ⊆ A.space := fun x hx => by
    obtain ⟨t, ht, hxt⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact A.convexHull_subset_space (hLA ht) hxt
  obtain ⟨Ab, P, Hm, hfin, hman, hsub, hLsub, hnhds, hPc, hPm, hPfix, hHc, hH0, hH1, hHfix,
    hHm⟩ := exists_derivedNbhd_collapse_R10 A L hprep.A_finite hprep.A_manifold hLA
  obtain ⟨g, hgc, hgm, hgh, hhg⟩ := exists_continuousOn_leftInverse_R10
    (isCompact_space_of_finite_R10 A hprep.A_finite) hprep.h_cont hprep.h_inj
  have hrange : Set.range f = h '' L.space := hprep.range_eq_R10
  have hNbA : h '' Ab.space ⊆ h '' A.space := image_mono hsub
  have hgNb : MapsTo g (h '' Ab.space) Ab.space := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hgh x (hsub hx)]
    exact hx
  have hgL : ∀ y ∈ Set.range f, g y ∈ L.space ∧ h (g y) = y := by
    intro y hy
    rw [hrange] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hgh x (hLAs hx)]
    exact ⟨hx, rfl⟩
  have hgcN : ContinuousOn g (h '' Ab.space) := hgc.mono hNbA
  have hLN : Set.range f ⊆ h '' Ab.space := by
    rw [hrange]
    exact image_mono hLsub
  refine ⟨h '' Ab.space, fun y => h (P (g y)), ?_, hNbA⟩
  refine IsRelRegularNbhd_R10.of_collapse
    ((isCompact_space_of_finite_R10 Ab hfin).image_of_continuousOn (hprep.h_cont.mono hsub))
    ⟨N, Ab, h, hfin, hman, hprep.h_cont.mono hsub, hprep.h_inj.mono hsub, rfl⟩ ?_ ?_ hLN ?_ ?_ ?_
    (fun p => h (Hm (p.1, g p.2))) ?_ ?_ ?_ ?_ ?_
  · -- trace ∈ frontier
    intro θ
    have hfr := hprep.bdry_frontier θ
    rw [frontier, Set.mem_sdiff] at hfr ⊢
    exact ⟨subset_closure (hLN ⟨_, rfl⟩), fun hi => hfr.2 (interior_mono hNbA hi)⟩
  · -- 内部盘 ∈ interior
    intro z hz
    have hU := hprep.int_interior z hz
    obtain ⟨hx₀L, hx₀⟩ := hgL (f z) ⟨z, rfl⟩
    obtain ⟨V, hVo, hx₀V, hVA⟩ := mem_nhdsWithin.mp (hnhds (g (f z)) hx₀L)
    obtain ⟨W, hWo, hW⟩ := continuousOn_iff'.mp hgc V hVo
    refine mem_interior.mpr ⟨W ∩ interior (h '' A.space), ?_, hWo.inter isOpen_interior, ?_, hU⟩
    · rintro y ⟨hyW, hyU⟩
      have hyA : y ∈ h '' A.space := interior_subset hyU
      have hy : y ∈ g ⁻¹' V ∩ h '' A.space := by
        rw [hW]
        exact ⟨hyW, hyA⟩
      rw [← hhg y hyA]
      exact mem_image_of_mem h (hVA ⟨hy.1, hgm hyA⟩)
    · have hy : f z ∈ g ⁻¹' V ∩ h '' A.space := ⟨hx₀V, interior_subset hU⟩
      rw [hW] at hy
      exact hy.1
  · -- `R` 连续
    exact hprep.h_cont.comp (hPc.comp hgcN hgNb) fun x hx => hLAs (hPm (hgNb hx))
  · -- `R` 映入 `L`
    intro y hy
    rw [hrange]
    exact mem_image_of_mem h (hPm (hgNb hy))
  · -- `R` 固定 `L`
    intro y hy
    obtain ⟨hyL, hhy⟩ := hgL y hy
    rw [hPfix _ hyL, hhy]
  · -- `H` 连续
    have hin : ContinuousOn (fun p : unitInterval × M => (p.1, g p.2)) (univ ×ˢ (h '' Ab.space)) :=
      continuousOn_fst.prodMk (hgcN.comp continuousOn_snd fun p hp => hp.2)
    exact hprep.h_cont.comp (hHc.comp hin fun p hp => ⟨mem_univ _, hgNb hp.2⟩)
      fun p hp => hsub (hHm p.1 (hgNb hp.2))
  · intro y hy
    change h (Hm (0, g y)) = y
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hH0 _ (hgNb ⟨x, hx, rfl⟩), hgh x (hsub hx)]
  · intro y hy
    change h (Hm (1, g y)) = h (P (g y))
    rw [hH1 _ (hgNb hy)]
  · intro t y hy
    obtain ⟨hyL, hhy⟩ := hgL y hy
    change h (Hm (t, g y)) = y
    rw [hHfix t _ hyL, hhy]
  · intro t y hy
    exact mem_image_of_mem h (hHm t (hgNb hy))

end Producer

end DifferentialGeometry.Geometry
