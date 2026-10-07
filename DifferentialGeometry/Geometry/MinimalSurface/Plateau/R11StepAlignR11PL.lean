import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFlatFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.RelRegularNbhdR10
import DifferentialGeometry.Topology.PiecewiseLinear.CollisionPairsDescentR11PL
import DifferentialGeometry.Topology.PiecewiseLinear.RelRegularNbhdCoverR11PL

/-!
# S-MY-R11PL G3：R11 纯 PL 半边与 `IsPreparedSheetComplex_FIX` / `IsRelRegularNbhd_R10` 的陈述对齐

* `vertexCollisionPairs_ssubset_of_prepared_R11PL` / `..._of_cover_R11PL`：G1 的 PL 层前提
  （`alpha_bij`、两层 `face_map`、`h_inj`、`factor`、`faces_finite`）逐字取自两份
  `IsPreparedSheetComplex_FIX`（**同一** `T`、`α`，不重细分）；`_of_cover` 的 deck / 纤维 / `p⁻¹(L)` 连通
  前提恰是 R11-step 契约（`TowerEngineR12.hR11`）输出里同名的那几条与 G2 输出逐条同型。
* `exists_double_cover_of_isRelRegularNbhd_R10_R11PL`：G2 对 `IsRelRegularNbhd_R10 f Nb R` 的消费形
  （∧-链解包；用到 `Nb` 的 presentation、`H`/`R`、`range f ⊆ Nb`，不用 trace 两条与 `π₁` 满射）；
  `H₁(N;F₂) ≠ 0` 取成「`Nb` 的每个 presentation 都带一个非 coboundary 的 `SimplicialBoolCocycle`」
  （universe-free；`M : Type` 上的 `b₁` 形见 `..._of_betti_R11PL`）。**额外**显式前提 `O`、`G`
  （strong deformation retraction `O → Nb`，与 `hR11` 输出里的 `HO` 同形）是 R10 notion 没有的 ambient
  数据，**不**由本文件产生：它是 R11-step 总装的开放义务（ambient collar of `∂N` in `M`）。
* `flatDisk_no_separated_pair_R11PL`：S-MY-FIX 平坦盘 witness 的实例化——`P_T(f, α) = ∅`，故 G1 的分离
  前提不可满足（G1 空真）；G2 对平坦盘**不**适用（`N` 是 3-球，`H₁ = 0`），只写形状对齐。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

universe u

section Prepared

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M M' : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace M'] [ChartedSpace E M']
  {f : C(closedDisk, M)} {F : ℂ → M} {f' : C(closedDisk, M')} {F' : ℂ → M'}
  {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N N' : ℕ}
  {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
  {A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
  {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
  {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}

/-- **G1 对齐（prepared 形）**：同 `T, α` 的两份 prepared 数据 + `pr ∘ f' = f` + 分离的点对
⇒ `P_T(f', α) ⊊ P_T(f, α)`。 -/
theorem vertexCollisionPairs_ssubset_of_prepared_R11PL [Finite T.faces]
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hprep' : IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h')
    (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z)
    (hsep : ∃ x y : closedDisk, f x = f y ∧ f' x ≠ f' y) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) :=
  vertexCollisionPairs_ssubset_of_separated_R11PL T α hprep.alpha_bij.surjOn pr hlift
    hprep.face_map hprep'.face_map hprep.h_inj hprep'.h_inj hprep.factor hprep'.factor hsep

/-- **G1 对齐（cover 形，D-22 全链）**：G2 / R11-step 输出的 genuine double cover 数据（`τ` 连续、
`p ∘ τ = p`、`τ` 无不动点、纤维 `{x, τ x}`、`p⁻¹(f(D̄))` 连通、`f'` 是 lift）+ 上层 prepared 数据
⇒ `P_T(f', α) ⊊ P_T(f, α)`。 -/
theorem vertexCollisionPairs_ssubset_of_cover_R11PL [Finite T.faces] [T2Space M']
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hprep' : IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h')
    (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M') (hτc : Continuous τ)
    (hτ₁ : ∀ x, pr (τ x) = pr x) (hτ₃ : ∀ x, τ x ≠ x)
    (hfib : ∀ x y, pr x = pr y → y = x ∨ y = τ x)
    (hconn : IsConnected (pr ⁻¹' Set.range f)) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) :=
  vertexCollisionPairs_ssubset_of_isConnected_R11PL T α hprep.alpha_bij.surjOn pr hlift τ hτc hτ₁
    hτ₃ hfib hconn hprep.face_map hprep'.face_map hprep.h_inj hprep'.h_inj hprep.factor
    hprep'.factor

/-- **G1 空真**：下层 `P_T(f, α) = ∅`（complexity 零，tower 的起点）⇒ 任何同 `T, α` 的上层 prepared lift
都没有分离的点对。 -/
theorem not_separated_of_complexity_zero_R11PL [Finite T.faces]
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hprep' : IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h')
    (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z)
    (hzero : (vertexCollisionPairs T (diskExtension f ∘ α)).card = 0) :
    ¬ ∃ x y : closedDisk, f x = f y ∧ f' x ≠ f' y := fun hsep => by
  have h0 := vertexCollisionPairs_ssubset_of_prepared_R11PL hprep hprep' pr hlift hsep
  rw [Finset.card_eq_zero.mp hzero] at h0
  exact Finset.not_ssubset_empty _ h0

end Prepared

/-- **G3 consumer（S-MY-FIX 平坦盘）**：`flatDisk_prepared_FIX` 的 `T = triComplex_FIX`、
`α = radialGrid_FIX` 上，任何同 `T, α` 的上层 prepared lift 都没有分离的点对（`P_T = ∅`，
`flatDisk_complexity_zero_FIX`）——G1 对平坦盘空真。 -/
theorem flatDisk_no_separated_pair_R11PL {M' : Type} [TopologicalSpace M'] [ChartedSpace E3_FIX M']
    {F' : ℂ → M'} {f' : C(closedDisk, M')} {N' : ℕ}
    {A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ' : ℂ → EuclideanSpace ℝ (Fin N')} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hprep' : IsPreparedSheetComplex_FIX (E := E3_FIX) f' F' triComplex_FIX radialGrid_FIX N' A'
      φ' h')
    (pr : M' → E3_FIX) (hlift : ∀ z, pr (f' z) = flatDisk_FIX z) :
    ¬ ∃ x y : closedDisk, flatDisk_FIX x = flatDisk_FIX y ∧ f' x ≠ f' y :=
  not_separated_of_complexity_zero_R11PL flatDisk_prepared_FIX hprep' pr hlift
    flatDisk_complexity_zero_FIX

section RelNbhd

variable {M : Type u} [TopologicalSpace M] [T2Space M]

/-- **G2 对齐**：`IsRelRegularNbhd_R10 f Nb R`（∧-链解包）+ `H₁(N;F₂) ≠ 0`（每个 presentation 带
非 coboundary 的 `ε`）+ ambient 数据 `O`、`G`（strong deformation retraction `O → Nb`）⇒ genuine
connected double cover `p : X' → M` over `O`（`IsCoveringMapOn`、deck `τ`、`p⁻¹(L)` 连通、`f` 的 lift）。 -/
theorem exists_double_cover_of_isRelRegularNbhd_R10_R11PL {f : C(closedDisk, M)} {Nb : Set M}
    {R : M → M} (hN : IsRelRegularNbhd_R10 f Nb R)
    (hε : ∀ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite → ContinuousOn hb Ab.space →
      InjOn hb Ab.space → hb '' Ab.space = Nb →
      ∃ ε : SimplicialBoolCocycle Ab, ¬ ε.IsCoboundary)
    {O : Set M} (hO : IsOpen O) (hNO : Nb ⊆ O) {G : unitInterval × M → M}
    (hGc : ContinuousOn G (univ ×ˢ O)) (hG0 : ∀ x ∈ O, G (0, x) = x)
    (hG1 : ∀ x ∈ O, G (1, x) ∈ Nb) (hGfix : ∀ t, ∀ x ∈ Nb, G (t, x) = x)
    (hGmaps : ∀ t, MapsTo (fun x => G (t, x)) O O) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X') (f' : C(closedDisk, X')),
      T2Space X' ∧ Continuous p ∧ range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧
      IsConnected O ∧ Continuous τ ∧ (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧
      (∀ x, τ x ≠ x) ∧ (∀ x y, p x = p y → y = x ∨ y = τ x) ∧
      IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) := by
  obtain ⟨-, hconn, ⟨N', Ab, hb, hAb, -, hbc, hbi, hbN⟩, -, -, -, hRm, -, ⟨H, hHc, hH0, hH1, hHfix,
    hHm⟩, hLN, -⟩ := hN
  obtain ⟨ε, hεn⟩ := hε N' Ab hb hAb hbc hbi hbN
  exact exists_double_cover_of_relRegularNbhd_R11PL hAb hbc hbi hbN hconn ε hεn hLN hRm hHc hH0 hH1
    hHfix hHm hO hNO hGc hG0 hG1 hGfix hGmaps

/-- **R11-step 的 PL 半边（G1 + G2 合成）**：下层 PL 数据（`α` 满、`φ` 逐面非退化、`h` 单射、factor）+
`IsRelRegularNbhd_R10` + `H₁ ≠ 0` + ambient `O, G` + **上层 prepared 数据的 PL 部分** `hup`
⇒ `O` 上 genuine connected double cover 与严格降的 `P_T(f', α) ⊊ P_T(f, α)`（同 `T, α`）。
`hup` 是 R11-step 总装剩下的开放义务（`O` 内、与同一 `T, α` 兼容的 relative thickening 上的 PL 数据：
两层 `face_map` 非退化、`h'` 单射、factor identity）；smooth 结构 / pullback metric / Morrey 性另算。 -/
theorem r11_pl_half_R11PL {T : _root_.Geometry.SimplicialComplex ℝ ℂ} [Finite T.faces]
    {α : ℂ → ℂ} (hα : SurjOn α T.space (Metric.closedBall 0 1)) {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M} {f : C(closedDisk, M)}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card)
    (hinj : InjOn h A.space)
    (hfac : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z))
    {Nb : Set M} {R : M → M} (hN : IsRelRegularNbhd_R10 f Nb R)
    (hε : ∀ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite → ContinuousOn hb Ab.space →
      InjOn hb Ab.space → hb '' Ab.space = Nb →
      ∃ ε : SimplicialBoolCocycle Ab, ¬ ε.IsCoboundary)
    {O : Set M} (hO : IsOpen O) (hNO : Nb ⊆ O) {G : unitInterval × M → M}
    (hGc : ContinuousOn G (univ ×ˢ O)) (hG0 : ∀ x ∈ O, G (0, x) = x)
    (hG1 : ∀ x ∈ O, G (1, x) ∈ Nb) (hGfix : ∀ t, ∀ x ∈ Nb, G (t, x) = x)
    (hGmaps : ∀ t, MapsTo (fun x => G (t, x)) O O)
    (hup : ∀ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (f' : C(closedDisk, X')),
      range p = O → IsCoveringMapOn p O → (∀ z, p (f' z) = f z) →
      ∃ (N' : ℕ) (A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
        (φ' : ℂ → EuclideanSpace ℝ (Fin N')) (h' : EuclideanSpace ℝ (Fin N') → X'),
        (∀ s ∈ T.faces, s.image φ' ∈ A'.faces ∧ (s.image φ').card = s.card) ∧
        InjOn h' A'.space ∧
        ∀ z ∈ T.space, h' (simplicialMap T φ' z) = diskExtension f' (α z)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X') (f' : C(closedDisk, X')),
      range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧ Continuous τ ∧
      (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
      (∀ x y, p x = p y → y = x ∨ y = τ x) ∧ IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) ∧
      vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
        vertexCollisionPairs T (diskExtension f ∘ α) := by
  obtain ⟨X', _, p, τ, f', hT2, -, hrange, hcov, hconnX, -, hτc, hτ₁, hτ₂, hτ₃, hfib, hconn,
    hlift⟩ := exists_double_cover_of_isRelRegularNbhd_R10_R11PL hN hε hO hNO hGc hG0 hG1 hGfix
    hGmaps
  obtain ⟨N', A', φ', h', hφ', hinj', hfac'⟩ := hup X' ‹_› p f' hrange hcov hlift
  exact ⟨X', ‹_›, p, τ, f', hrange, hcov, hconnX, hτc, hτ₁, hτ₂, hτ₃, hfib, hconn, hlift,
    vertexCollisionPairs_ssubset_of_isConnected_R11PL T α hα p hlift τ hτc hτ₁ hτ₃ hfib hconn hφ
      hφ' hinj hinj' hfac hfac'⟩

end RelNbhd

end DifferentialGeometry.Geometry
