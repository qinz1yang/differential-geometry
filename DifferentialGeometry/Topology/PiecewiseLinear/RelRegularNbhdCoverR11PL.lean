import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverExistence
import DifferentialGeometry.Topology.PiecewiseLinear.HomologyCocycle
import DifferentialGeometry.Topology.Homology.BettiNumber
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Homotopy.Lifting
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk

/-!
# S-MY-R11PL G2（rev2 §A-5(c)）：真 relative regular neighborhood 上的 genuine connected double cover

D-R-MY2-21 的反例（实心环面 meridional 平盘）由 spine / `π₁` 条件排除；取与 `N` 同伦等价、含
`f(D̄)` 的连通开邻域 `O`，由非平凡 `π₁(N) → F₂`（PL 库的 `SimplicialBoolCocycle ε`，`¬ ε.IsCoboundary`）
造 **genuine connected double cover** `p : X' → M`（`IsCoveringMapOn p O`、`range p = O`），
并给 deck `τ`、`f` 的 lift `f'`、`p⁻¹(f(D̄))` 连通。

构造（纯拓扑，`M` 只要求 T2）：
1. `Nb = hb '' |Ab|` 与 `|Ab|` 同胚（紧 → T2）；
2. `O` 上的 strong deformation retraction `G : O → Nb`（**显式前提**，R10 notion 没有的 ambient 数据）
   给 `g = e⁻¹ ∘ G(1, ·) : O → |Ab|`；
3. `X' = Bundle.TotalSpace Bool (g *ᵖ Z.Fiber)`（Mathlib `Bundle.Pullback`，`Z` = PL 库 double cover 的
   `FiberBundleCore`），`FiberBundle.isCoveringMap` 给 covering；deck `τ(x, b) = (x, !b)`；
4. `p⁻¹(L)` 连通：`H` 的 homotopy lifting（`IsCoveringMap.liftHomotopy`）把 PL 库连通的 `A` 压到 `p⁻¹(L)`；
5. `X'` 连通：每点沿 `G` 的 path lift（`liftPath`）接到 `p⁻¹(Nb) = range j`（连通）；
6. `f'`：`D̄` 单连通且局部道路连通，`IsCoveringMap.existsUnique_continuousMap_lifts`。

**不含**（留给 R11-step 总装，需要微分几何输入）：`X'` 的 smooth 结构与 `p` 局部微分同胚、pullback
metric、`f'` 的 Morrey 性、prepared 数据 `A'`、`φ'`、`h'` 的传递——后者须是位于 `O` 内且与同一 `T`、`α`
兼容的 relative thickening（`O ⊇ N` 并不蕴含 `h(|A|) ⊆ O`，不能默认整个旧 `A` 可提升）。
`H₁(N;F₂) ≠ 0` ⇒ `ε` 非 coboundary 的两种入口：直接给 `ε`（主定理），或 `M : Type` 上给
`0 < b₁(Nb; F₂)`（`..._of_betti_R11PL`）。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Topology DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section PullbackCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (ε : SimplicialBoolCocycle K)
  {B : Type u} [TopologicalSpace B] (g : C(B, K.space))

/-- `Z.Fiber` 非空（`Bundle.Pullback` 的 `FiberBundle` 实例要求）。 -/
instance fiberNonempty_R11PL (b : K.space) :
    Nonempty (ε.toBoolCocycle.toFiberBundleCore.Fiber b) :=
  inferInstanceAs (Nonempty Bool)

/-- 沿 `g : B → |K|` 拉回 PL double cover 得到的总空间（`Bundle.Pullback` 的 total space）。 -/
abbrev PullbackCoverSpace_R11PL : Type u :=
  Bundle.TotalSpace Bool ((g : B → K.space) *ᵖ ε.toBoolCocycle.toFiberBundleCore.Fiber)

/-- 拉回 cover 的投影是 covering map（离散纤维 `Bool` 的 fiber bundle）。 -/
theorem isCoveringMap_pullbackCover_R11PL :
    IsCoveringMap (Bundle.TotalSpace.proj : PullbackCoverSpace_R11PL ε g → B) :=
  FiberBundle.isCoveringMap

/-- deck 对合 `(x, b) ↦ (x, !b)`。 -/
def pullbackDeck_R11PL (y : PullbackCoverSpace_R11PL ε g) : PullbackCoverSpace_R11PL ε g :=
  ⟨y.1, !y.2⟩

/-- deck 连续（`Pullback` 拓扑 = `(proj, lift)` 诱导，`lift ∘ deck = ε.deck ∘ lift`）。 -/
theorem continuous_pullbackDeck_R11PL : Continuous (pullbackDeck_R11PL ε g) := by
  rw [(inducing_pullbackTotalSpaceEmbedding Bool ε.toBoolCocycle.toFiberBundleCore.Fiber
    (g : B → K.space)).continuous_iff]
  exact (Pullback.continuous_proj Bool _ _).prodMk
    (ε.deck_continuous.comp (Pullback.continuous_lift Bool _ _))

/-- `τ ∘ τ = id`。 -/
theorem pullbackDeck_deck_R11PL (y : PullbackCoverSpace_R11PL ε g) :
    pullbackDeck_R11PL ε g (pullbackDeck_R11PL ε g y) = y := by
  obtain ⟨x, b⟩ := y
  cases b <;> rfl

/-- `τ` 无不动点（freeness）。 -/
theorem pullbackDeck_ne_R11PL (y : PullbackCoverSpace_R11PL ε g) :
    pullbackDeck_R11PL ε g y ≠ y := by
  obtain ⟨x, b⟩ := y
  intro h
  have h2 : (!b) = b := congrArg (fun w : PullbackCoverSpace_R11PL ε g => (w.2 : Bool)) h
  cases b <;> simp at h2

/-- 纤维恰为 `{x, τ x}`。 -/
theorem pullbackCover_fiber_cases_R11PL (y y' : PullbackCoverSpace_R11PL ε g)
    (h : y.proj = y'.proj) : y' = y ∨ y' = pullbackDeck_R11PL ε g y := by
  obtain ⟨x, b⟩ := y
  obtain ⟨x', b'⟩ := y'
  change x = x' at h
  subst h
  cases b <;> cases b' <;> simp [pullbackDeck_R11PL]

/-- 拉回 cover 的总空间 T2（covering ⇒ separated map，底空间 T2）。 -/
theorem t2Space_pullbackCover_R11PL [T2Space B] : T2Space (PullbackCoverSpace_R11PL ε g) := by
  refine ⟨fun y₁ y₂ hne => ?_⟩
  by_cases h : y₁.proj = y₂.proj
  · exact (isCoveringMap_pullbackCover_R11PL ε g).isSeparatedMap y₁ y₂ h hne
  · obtain ⟨u, v, hu, hv, hy₁, hy₂, huv⟩ := t2_separation h
    exact ⟨_, _, hu.preimage (Pullback.continuous_proj Bool _ _),
      hv.preimage (Pullback.continuous_proj Bool _ _), hy₁, hy₂, huv.preimage _⟩

/-- 拉回 cover 的点：`x : B` 与一个 `Bool`（层标）。 -/
def pbMk_R11PL (x : B) (b : Bool) : PullbackCoverSpace_R11PL ε g := ⟨x, b⟩

end PullbackCover

section Core

variable {M : Type u} [TopologicalSpace M] [T2Space M]

/-- G2 的核心（`e : |K| ≃ₜ Nb` 形）：见文件头与 `exists_double_cover_of_relRegularNbhd_R11PL`。 -/
theorem exists_double_cover_core_R11PL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [ConnectedSpace K.space]
    (ε : SimplicialBoolCocycle K) (hε : ¬ ε.IsCoboundary)
    {Nb : Set M} (e : K.space ≃ₜ Nb)
    {f : C(closedDisk, M)} (hLN : range f ⊆ Nb) {R : M → M} (hRmaps : MapsTo R Nb (range f))
    {H : unitInterval × M → M} (hHc : ContinuousOn H (univ ×ˢ Nb))
    (hH0 : ∀ x ∈ Nb, H (0, x) = x) (hH1 : ∀ x ∈ Nb, H (1, x) = R x)
    (hHfix : ∀ t, ∀ x ∈ range f, H (t, x) = x) (hHmaps : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb)
    {O : Set M} (hO : IsOpen O) (hNO : Nb ⊆ O) {G : unitInterval × M → M}
    (hGc : ContinuousOn G (univ ×ˢ O)) (hG0 : ∀ x ∈ O, G (0, x) = x)
    (hG1 : ∀ x ∈ O, G (1, x) ∈ Nb) (hGfix : ∀ t, ∀ x ∈ Nb, G (t, x) = x)
    (hGmaps : ∀ t, MapsTo (fun x => G (t, x)) O O) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X') (f' : C(closedDisk, X')),
      T2Space X' ∧ Continuous p ∧ range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧
      IsConnected O ∧ Continuous τ ∧ (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, τ x ≠ x) ∧ (∀ x y, p x = p y → y = x ∨ y = τ x) ∧
      IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) := by
  classical
  -- 沿 strong deformation retraction `G` 的末端映射 `O → Nb`，再用 `e.symm` 搬到 `K.space`
  have hc1 : Continuous (fun x : O => G (1, (x : M))) :=
    hGc.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun x => ⟨mem_univ _, x.2⟩)
  let r : C(O, Nb) := ⟨fun x => ⟨G (1, (x : M)), hG1 x x.2⟩, hc1.subtype_mk _⟩
  let g : C(O, K.space) := (⟨e.symm, e.symm.continuous⟩ : C(Nb, K.space)).comp r
  have hg : ∀ (x : O) (hx : (x : M) ∈ Nb), g x = e.symm ⟨x, hx⟩ := fun x hx => by
    change e.symm ⟨G (1, (x : M)), hG1 x x.2⟩ = e.symm ⟨x, hx⟩
    exact congrArg e.symm (Subtype.ext (hGfix 1 x hx))
  have hcov := isCoveringMap_pullbackCover_R11PL ε g
  let X' := PullbackCoverSpace_R11PL ε g
  let pO : X' → O := Bundle.TotalSpace.proj
  have hπc : Continuous pO := Pullback.continuous_proj Bool _ _
  let p : X' → M := fun y => (pO y : M)
  have hpc : Continuous p := continuous_subtype_val.comp hπc
  have hrange : range p = O := by
    ext x
    refine ⟨fun ⟨y, hy⟩ => hy ▸ (pO y).2, fun hx => ⟨pbMk_R11PL ε g ⟨x, hx⟩ false, rfl⟩⟩
  have hcovOn : IsCoveringMapOn p O :=
    IsCoveringMapOn.of_isCoveringMap_subtype hO (fun y => (pO y).2) hcov
  -- PL 库的 connected double cover `A → K.space`（总空间连通）
  let Z := ε.toBoolCocycle.toFiberBundleCore
  have hAconn : ConnectedSpace Z.TotalSpace := (ε.connectedSpace_iff).mpr hε
  have hprojc : Continuous Z.proj := ε.isCoveringMap.continuous
  let ι₀ : Z.TotalSpace → O := fun z => ⟨(e (Z.proj z) : M), hNO (e (Z.proj z)).2⟩
  have hι₀ : Continuous ι₀ :=
    (continuous_subtype_val.comp (e.continuous.comp hprojc)).subtype_mk _
  have hgι : ∀ z : Z.TotalSpace, g (ι₀ z) = Z.proj z := fun z => by
    rw [hg (ι₀ z) (e (Z.proj z)).2]
    exact e.symm_apply_apply _
  -- `A` 嵌入 `X'` 的 `Nb` 上部分
  let j : Z.TotalSpace → X' := fun z => pbMk_R11PL ε g (ι₀ z) z.2
  have hlift : ∀ z : Z.TotalSpace, Pullback.lift (g : O → K.space) (j z) = z := by
    intro z
    obtain ⟨a, b⟩ := z
    change (⟨g (ι₀ ⟨a, b⟩), b⟩ : Z.TotalSpace) = ⟨a, b⟩
    rw [hgι]
  have hjc : Continuous j := by
    rw [(inducing_pullbackTotalSpaceEmbedding Bool Z.Fiber (g : O → K.space)).continuous_iff]
    have : (pullbackTotalSpaceEmbedding (F := Bool) (E := Z.Fiber) (g : O → K.space)) ∘ j =
        fun z => (ι₀ z, z) := by
      funext z
      exact Prod.ext rfl (hlift z)
    rw [this]
    exact hι₀.prodMk continuous_id
  have hQ : ∀ y : X', (pO y : M) ∈ Nb → ∃ z : Z.TotalSpace, j z = y := by
    intro y hy
    obtain ⟨x, b⟩ := y
    refine ⟨⟨e.symm ⟨x, hy⟩, b⟩, ?_⟩
    have hx : ι₀ ⟨e.symm ⟨(x : M), hy⟩, b⟩ = x := Subtype.ext (by simp [ι₀])
    change pbMk_R11PL ε g (ι₀ ⟨e.symm ⟨(x : M), hy⟩, b⟩) b = pbMk_R11PL ε g x b
    rw [hx]
  -- `p⁻¹(L)` 连通：沿 `H` 把 `A` 的 `Nb`-部分用 homotopy lifting 压到 `p⁻¹(L)`
  have hHc' : Continuous fun w : unitInterval × Z.TotalSpace => H (w.1, (e (Z.proj w.2) : M)) :=
    hHc.comp_continuous (continuous_fst.prodMk
      (continuous_subtype_val.comp (e.continuous.comp (hprojc.comp continuous_snd))))
      (fun w => ⟨mem_univ _, (e (Z.proj w.2)).2⟩)
  let Hh : C(unitInterval × Z.TotalSpace, O) :=
    ⟨fun w => ⟨H (w.1, (e (Z.proj w.2) : M)), hNO (hHmaps w.1 (e (Z.proj w.2)).2)⟩,
      hHc'.subtype_mk _⟩
  let j' : C(Z.TotalSpace, X') := ⟨j, hjc⟩
  have hH_0 : ∀ z, Hh (0, z) = Bundle.TotalSpace.proj (j' z) := fun z =>
    Subtype.ext (hH0 _ (e (Z.proj z)).2)
  let Λ := hcov.liftHomotopy Hh j' hH_0
  have hΛlift : ∀ t z, Bundle.TotalSpace.proj (Λ (t, z)) = Hh (t, z) := fun t z =>
    congr_fun (hcov.liftHomotopy_lifts Hh j' hH_0) (t, z)
  have hΛzero : ∀ z, Λ (0, z) = j z := fun z => hcov.liftHomotopy_zero Hh j' hH_0 z
  have hKc : Continuous fun z => Λ (1, z) :=
    Λ.continuous.comp (continuous_const.prodMk continuous_id)
  have hKrange : ∀ z, p (Λ (1, z)) ∈ range f := fun z => by
    have h1 : p (Λ (1, z)) = H (1, (e (Z.proj z) : M)) := congrArg Subtype.val (hΛlift 1 z)
    rw [h1, hH1 _ (e (Z.proj z)).2]
    exact hRmaps (e (Z.proj z)).2
  have hKfix : ∀ z, (e (Z.proj z) : M) ∈ range f → Λ (1, z) = j z := fun z hz => by
    have key : (fun t : unitInterval => Λ (t, z)) = fun _ => j z := by
      refine hcov.eq_of_comp_eq (A := unitInterval)
        (Λ.continuous.comp (continuous_id.prodMk continuous_const)) continuous_const ?_ 0
        (hΛzero z)
      funext t
      exact Subtype.ext ((congrArg Subtype.val (hΛlift t z)).trans (hHfix t _ hz))
    exact congr_fun key 1
  have hpre : p ⁻¹' range f = range fun z => Λ (1, z) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hQ y (hLN hy)
      exact ⟨z, hKfix z hy⟩
    · rintro ⟨z, rfl⟩
      exact hKrange z
  have hconnL : IsConnected (p ⁻¹' range f) := by
    rw [hpre]
    exact isConnected_range hKc
  -- `X'` 连通：每个点沿 `G` 的 path lift 到 `Nb`-部分，而 `Nb`-部分 = `range j` 连通
  have hconnX : ConnectedSpace X' := by
    obtain ⟨z₀⟩ := (inferInstance : Nonempty Z.TotalSpace)
    refine connectedSpace_iff_univ.mpr ⟨⟨j z₀, mem_univ _⟩, ?_⟩
    refine isPreconnected_of_forall (j z₀) fun y _ => ?_
    have hγc : Continuous fun t : unitInterval => G (t, (pO y : M)) :=
      hGc.comp_continuous (continuous_id.prodMk continuous_const) (fun t => ⟨mem_univ _, (pO y).2⟩)
    let γ : C(unitInterval, O) := ⟨fun t => ⟨G (t, (pO y : M)), hGmaps t (pO y).2⟩,
      hγc.subtype_mk _⟩
    have hγ0 : γ 0 = Bundle.TotalSpace.proj y := Subtype.ext (hG0 _ (pO y).2)
    let Γ := hcov.liftPath γ y hγ0
    have hΓ1 : (pO (Γ 1) : M) ∈ Nb := by
      have h1 : Bundle.TotalSpace.proj (Γ 1) = γ 1 := congr_fun (hcov.liftPath_lifts γ y hγ0) 1
      rw [show (pO (Γ 1) : M) = (γ 1 : M) from congrArg Subtype.val h1]
      exact hG1 _ (pO y).2
    obtain ⟨z₁, hz₁⟩ := hQ (Γ 1) hΓ1
    refine ⟨range Γ ∪ range j, subset_univ _, Or.inr ⟨z₀, rfl⟩,
      Or.inl ⟨0, hcov.liftPath_zero γ y hγ0⟩, ?_⟩
    exact IsPreconnected.union (Γ 1) ⟨1, rfl⟩ ⟨z₁, hz₁⟩
      (isConnected_range Γ.continuous).isPreconnected
      (isConnected_range hjc).isPreconnected
  have hconnO : IsConnected O := hrange ▸ isConnected_range hpc
  -- `f` 的 lift（`D̄` 单连通且局部道路连通）
  have : LocallyPathConnectedSpace closedDisk :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  let fO : C(closedDisk, O) := ⟨fun z => ⟨f z, hNO (hLN ⟨z, rfl⟩)⟩, f.continuous.subtype_mk _⟩
  let a₀ : closedDisk := ⟨0, by simp⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts fO a₀
    (pbMk_R11PL ε g (fO a₀) false) rfl
  refine ⟨X', inferInstance, p, pullbackDeck_R11PL ε g, F, t2Space_pullbackCover_R11PL ε g,
    hpc, hrange, hcovOn, hconnX, hconnO, continuous_pullbackDeck_R11PL ε g, fun _ => rfl,
    pullbackDeck_deck_R11PL ε g, pullbackDeck_ne_R11PL ε g, fun x y h => ?_, hconnL, fun z => ?_⟩
  · exact pullbackCover_fiber_cases_R11PL ε g x y (Subtype.ext h)
  · exact congrArg Subtype.val (congr_fun hF z)

/-- 有限复形 `Ab` 经连续单射 `hb` 的像 `Nb` 与 `|Ab|` 同胚（紧 → T2）。 -/
theorem exists_homeomorph_of_presentation_R11PL {N' : ℕ}
    {Ab : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    (hAb : Ab.faces.Finite) {hb : EuclideanSpace ℝ (Fin N') → M}
    (hbc : ContinuousOn hb Ab.space) (hbi : InjOn hb Ab.space) {Nb : Set M}
    (hbN : hb '' Ab.space = Nb) : ∃ e : Ab.space ≃ₜ Nb, ∀ x, (e x : M) = hb x := by
  have : CompactSpace Ab.space := isCompact_iff_compactSpace.mp
    (hAb.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  have hcont : Continuous fun x : Ab.space => hb x := hbc.domRestrict
  have hinj : Function.Injective fun x : Ab.space => hb x := fun x y hxy =>
    Subtype.ext (hbi x.2 y.2 hxy)
  have hrange : range (fun x : Ab.space => hb x) = Nb := by
    rw [← hbN]
    ext x
    simp
  exact ⟨(hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange), fun _ => rfl⟩

/-- **G2**（`IsRelRegularNbhd` 解包字段 + `H₁ ≠ 0` witness ⇒ genuine connected double cover over `O`）。

前提 = scratch `IsRelRegularNbhd_MYD3`（`R10R14:51`）∧-链的**使用到的**字段：`Ab` 有限、`hb` 连续单射
且 `hb '' |Ab| = Nb`、`Nb` 连通、`H`/`R`（strong deformation retraction 到 `L = range f`）、`L ⊆ Nb`；
`π₁(L) ↠ π₁(N)` 由 `H` 推出，不重复要求；`H₁(N;F₂) ≠ 0` 的 witness 取成 `Ab` 上的非 coboundary
`SimplicialBoolCocycle`（即非平凡 `π₁(N) → F₂`）。**额外**的显式前提 `hO`（开 `O ⊇ Nb` + strong
deformation retraction `G : O → Nb`）是 R10 notion 没有的 ambient 数据，由 R11-step 总装 / R10 producer 提供。

输出（genuine connected double cover，同时含 `τ ∘ τ = id`、`τ x ≠ x`、`p ∘ τ = p`、纤维 `{x, τ x}`）：
`p : X' → M` 在 `O` 上是 `IsCoveringMapOn`、`range p = O`、`X'` 连通 T2、`p⁻¹(L)` 连通、
`f` 有 lift `f'`。**不**含 smooth 结构 / pullback metric / prepared 数据传递（见 R11-step 总装）。 -/
theorem exists_double_cover_of_relRegularNbhd_R11PL
    {N' : ℕ} {Ab : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    (hAb : Ab.faces.Finite) {hb : EuclideanSpace ℝ (Fin N') → M}
    (hbc : ContinuousOn hb Ab.space) (hbi : InjOn hb Ab.space) {Nb : Set M}
    (hbN : hb '' Ab.space = Nb) (hNb : IsConnected Nb)
    (ε : SimplicialBoolCocycle Ab) (hε : ¬ ε.IsCoboundary)
    {f : C(closedDisk, M)} (hLN : range f ⊆ Nb) {R : M → M} (hRmaps : MapsTo R Nb (range f))
    {H : unitInterval × M → M} (hHc : ContinuousOn H (univ ×ˢ Nb))
    (hH0 : ∀ x ∈ Nb, H (0, x) = x) (hH1 : ∀ x ∈ Nb, H (1, x) = R x)
    (hHfix : ∀ t, ∀ x ∈ range f, H (t, x) = x) (hHmaps : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb)
    {O : Set M} (hO : IsOpen O) (hNO : Nb ⊆ O) {G : unitInterval × M → M}
    (hGc : ContinuousOn G (univ ×ˢ O)) (hG0 : ∀ x ∈ O, G (0, x) = x)
    (hG1 : ∀ x ∈ O, G (1, x) ∈ Nb) (hGfix : ∀ t, ∀ x ∈ Nb, G (t, x) = x)
    (hGmaps : ∀ t, MapsTo (fun x => G (t, x)) O O) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X') (f' : C(closedDisk, X')),
      T2Space X' ∧ Continuous p ∧ range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧
      IsConnected O ∧ Continuous τ ∧ (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, τ x ≠ x) ∧ (∀ x y, p x = p y → y = x ∨ y = τ x) ∧
      IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) := by
  have : Finite Ab.faces := hAb.to_subtype
  obtain ⟨e, -⟩ := exists_homeomorph_of_presentation_R11PL hAb hbc hbi hbN
  have : ConnectedSpace Nb := isConnected_iff_connectedSpace.mp hNb
  have : ConnectedSpace Ab.space := e.symm.surjective.connectedSpace e.symm.continuous
  exact exists_double_cover_core_R11PL ε hε e hLN hRmaps hHc hH0 hH1 hHfix hHmaps hO hNO hGc hG0 hG1
    hGfix hGmaps

end Core

section Betti

/-- **G2（`H₁(N;F₂) ≠ 0` 的拓扑形）**：`M : Type` 上，`Nb` 的 presentation（有限复形 + 连续单射）、
连通、`0 < b₁(Nb; F₂)` 给出非 coboundary 的 `ε`，再套 G2 主定理。`hbetti` 经 `|Ab| ≃ₜ Nb` 的
同伦等价搬到 `|Ab|`，由 PL 库 `exists_not_isCoboundary_of_bettiNumber_one_pos` 给 `ε`。 -/
theorem exists_double_cover_of_relRegularNbhd_of_betti_R11PL {M : Type} [TopologicalSpace M]
    [T2Space M] {Nb : Set M}
    (hpres : ∃ (N' : ℕ) (Ab : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite ∧ ContinuousOn hb Ab.space ∧
      InjOn hb Ab.space ∧ hb '' Ab.space = Nb)
    (hNb : IsConnected Nb) (hbetti : 0 < Homology.bettiNumber (ZMod 2) (TopCat.of Nb) 1)
    {f : C(closedDisk, M)} (hLN : range f ⊆ Nb) {R : M → M} (hRmaps : MapsTo R Nb (range f))
    {H : unitInterval × M → M} (hHc : ContinuousOn H (univ ×ˢ Nb))
    (hH0 : ∀ x ∈ Nb, H (0, x) = x) (hH1 : ∀ x ∈ Nb, H (1, x) = R x)
    (hHfix : ∀ t, ∀ x ∈ range f, H (t, x) = x) (hHmaps : ∀ t, MapsTo (fun x => H (t, x)) Nb Nb)
    {O : Set M} (hO : IsOpen O) (hNO : Nb ⊆ O) {G : unitInterval × M → M}
    (hGc : ContinuousOn G (univ ×ˢ O)) (hG0 : ∀ x ∈ O, G (0, x) = x)
    (hG1 : ∀ x ∈ O, G (1, x) ∈ Nb) (hGfix : ∀ t, ∀ x ∈ Nb, G (t, x) = x)
    (hGmaps : ∀ t, MapsTo (fun x => G (t, x)) O O) :
    ∃ (X' : Type) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X') (f' : C(closedDisk, X')),
      T2Space X' ∧ Continuous p ∧ range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧
      IsConnected O ∧ Continuous τ ∧ (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, τ x ≠ x) ∧ (∀ x y, p x = p y → y = x ∨ y = τ x) ∧
      IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) := by
  obtain ⟨N', Ab, hb, hAb, hbc, hbi, hbN⟩ := hpres
  have : Finite Ab.faces := hAb.to_subtype
  obtain ⟨e, -⟩ := exists_homeomorph_of_presentation_R11PL hAb hbc hbi hbN
  have : ConnectedSpace Nb := isConnected_iff_connectedSpace.mp hNb
  have : ConnectedSpace Ab.space := e.symm.surjective.connectedSpace e.symm.continuous
  have hpos : 0 < Homology.bettiNumber (ZMod 2) (TopCat.of Ab.space) 1 := by
    rw [Homology.bettiNumber_eq_of_homotopyEquiv (ZMod 2) (X := TopCat.of Ab.space)
      (Y := TopCat.of Nb) e.toHomotopyEquiv 1]
    exact hbetti
  obtain ⟨ε, hε⟩ := SimplicialBoolCocycle.exists_not_isCoboundary_of_bettiNumber_one_pos Ab hpos
  exact exists_double_cover_core_R11PL ε hε e hLN hRmaps hHc hH0 hH1 hHfix hHmaps hO hNO hGc hG0 hG1
    hGfix hGmaps

end Betti

end DifferentialGeometry.Topology.PiecewiseLinear
