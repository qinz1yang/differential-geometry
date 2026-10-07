/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFlatFIX
import DifferentialGeometry.Geometry.Measure.Area.PiecewiseAffineCellsAREA
import DifferentialGeometry.Geometry.Measure.Area.PiecewiseLipschitzAREA
import Mathlib.Analysis.Convex.Measure

/-!
# S-MY-AREA G4：piecewise area adapter 对 `IsPreparedSheetComplex_FIX` / `flatDisk_prepared_FIX` 的实例化

把 G1–G3 接到 R9 的 prepared 数据上（`α` 只有单向 Lipschitz，2-面去顶点后 `C^∞` 且 `fderivWithin` 单射）：

* `exists_nhds_lower_bound_of_hasStrictFDerivAt_AREA`：`α` 在 `x` 处严格可微且导数单射 ⇒ `x` 的邻域上有下界
  `edist y z ≤ L * edist (α y) (α z)`（G1 的 `hloc`）。
* `preparedOpenFaces_AREA T`：`U = ⋃_{3-face s} (interior (hull s) \\ s)`，开集（有限集零测、闭）。
* `prepared_area_precomp_AREA`：对任意 prepared 数据（只用 `alpha_bij / alpha_lip /
  alpha_smooth / alpha_rank`）：
  `A(u ∘ α, U) = A(u, α '' U)`，`u` 全局 Riemannian-Lipschitz。**没有**用 `α` 的全局左逆。
* `prepared_area_precomp_space_AREA`：若 `T` 是纯 2 维（每个面含于某个 3-face），则
  `A(u ∘ α, |T|) = A(u, D̄)`（`T.space ∖ U` 是有限个 3-face 的边界与顶点，零测；`α '' |T| = D̄`）。
* `flatDisk_pure_AREA` / `flatDisk_area_precomp_AREA`：对 `flatDisk_prepared_FIX` 的实例化。
* `cap_area_multiplicity_AREA`：10.3 形状 —— cap `a = u ∘ α' ∘ Λ`（`Λ` 在有限个开 cells 上 affine 且映入 `|T|`，
  `α'` 是 `α|_{|T|}` 的 Lipschitz 延拓），`A(a) = ∑_σ m_σ · A(u, α '' τ_σ)`，`τ_σ` 是 3-face `σ` 的开内部（去顶点）。
  两个 cap 各用一次即得 `A(a₊) + A(a₋) = ∑_σ (m₊,σ + m₋,σ) A_σ`（`cap_area_pair_AREA`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal ENNReal Manifold

namespace DifferentialGeometry.Geometry

section Analysis

/-- `α` 在 `x` 处严格可微、导数单射 ⇒ `x` 的邻域 `W` 与常数 `L` 使 `edist y z ≤ L * edist (α y) (α z)`
（`y z ∈ W`）。证明：导数的反 Lipschitz 常数 `K`，取 `ε = 1 / (2K)`，严格可微给 `W` 使
`‖α y - α z - α'(y - z)‖ ≤ ε ‖y - z‖`，于是 `‖y - z‖ ≤ 2K ‖α y - α z‖`。 -/
theorem exists_nhds_lower_bound_of_hasStrictFDerivAt_AREA {α : ℂ → ℂ} {f' : ℂ →L[ℝ] ℂ} {x : ℂ}
    (hα : HasStrictFDerivAt α f' x) (hinj : Function.Injective f') :
    ∃ W ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ W, ∀ z ∈ W,
      edist y z ≤ (L : ℝ≥0∞) * edist (α y) (α z) := by
  obtain ⟨K, hKpos, hK⟩ := (LinearMap.injective_iff_antilipschitz f'.toLinearMap).mp hinj
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hε : ∀ᶠ p : ℂ × ℂ in 𝓝 (x, x),
      ‖α p.1 - α p.2 - f' (p.1 - p.2)‖ ≤ 1 / (2 * K) * ‖p.1 - p.2‖ :=
    Asymptotics.isLittleO_iff.1 (hasStrictFDerivAt_iff_isLittleO.mp hα) (by positivity)
  rw [nhds_prod_eq] at hε
  obtain ⟨W, hW, hWε⟩ := (Filter.eventually_prod_self_iff
    (r := fun a b => ‖α a - α b - f' (a - b)‖ ≤ 1 / (2 * K) * ‖a - b‖)).mp hε
  refine ⟨W, hW, 2 * K, fun y hy z hz => ?_⟩
  have h1 := hWε y hy z hz
  have h2 : dist y z ≤ K * dist (f' y) (f' z) := hK.le_mul_dist y z
  rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
  have h3 : ‖f' (y - z)‖ ≤ ‖α y - α z‖ + 1 / (2 * K) * ‖y - z‖ := by
    calc ‖f' (y - z)‖ = ‖(α y - α z) - (α y - α z - f' (y - z))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖α y - α z‖ + ‖α y - α z - f' (y - z)‖ := norm_sub_le _ _
      _ ≤ _ := by gcongr
  have h4 : ‖y - z‖ ≤ 2 * K * ‖α y - α z‖ := by
    have h5 : ‖y - z‖ ≤ K * (‖α y - α z‖ + 1 / (2 * K) * ‖y - z‖) :=
      h2.trans (by gcongr)
    have h6 : K * (‖α y - α z‖ + 1 / (2 * K) * ‖y - z‖) = K * ‖α y - α z‖ + ‖y - z‖ / 2 := by
      field_simp
    linarith
  rw [edist_dist, edist_dist]
  have h7 : dist y z ≤ ((2 * K : ℝ≥0) : ℝ) * dist (α y) (α z) := by
    rw [dist_eq_norm, dist_eq_norm]
    push_cast
    exact h4
  calc ENNReal.ofReal (dist y z) ≤ ENNReal.ofReal (((2 * K : ℝ≥0) : ℝ) * dist (α y) (α z)) :=
        ENNReal.ofReal_le_ofReal h7
    _ = ((2 * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (dist (α y) (α z)) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

end Analysis

section Prepared

universe u

/-- 3-face `s` 的开内部去掉顶点：`interior (convexHull s) \ s`（`α` 在其上 `C^∞` 且导数可逆）。 -/
def openFace_AREA (s : Finset ℂ) : Set ℂ := interior (convexHull ℝ (s : Set ℂ)) \ (s : Set ℂ)

/-- prepared 复形所有 3-face 的开内部（去顶点）之并：G1 的 `U`。 -/
def preparedOpenFaces_AREA (T : _root_.Geometry.SimplicialComplex ℝ ℂ) : Set ℂ :=
  ⋃ s ∈ {s : Finset ℂ | s ∈ T.faces ∧ s.card = 3}, openFace_AREA s

theorem openFace_subset_preparedOpenFaces_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {s : Finset ℂ} (hs : s ∈ T.faces) (hc : s.card = 3) :
    openFace_AREA s ⊆ preparedOpenFaces_AREA T :=
  fun _ hx => mem_iUnion₂.mpr ⟨s, ⟨hs, hc⟩, hx⟩

theorem isOpen_openFace_AREA (s : Finset ℂ) : IsOpen (openFace_AREA s) :=
  isOpen_interior.sdiff s.finite_toSet.isClosed

theorem isOpen_preparedOpenFaces_AREA (T : _root_.Geometry.SimplicialComplex ℝ ℂ) :
    IsOpen (preparedOpenFaces_AREA T) :=
  isOpen_biUnion fun s _ => isOpen_openFace_AREA s

theorem openFace_subset_space_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {s : Finset ℂ}
    (hs : s ∈ T.faces) : openFace_AREA s ⊆ T.space :=
  (sdiff_subset.trans interior_subset).trans (T.convexHull_subset_space hs)

theorem preparedOpenFaces_subset_space_AREA (T : _root_.Geometry.SimplicialComplex ℝ ℂ) :
    preparedOpenFaces_AREA T ⊆ T.space :=
  iUnion₂_subset fun _ hs => openFace_subset_space_AREA hs.1

theorem isBounded_space_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    (hfin : T.faces.Finite) : Bornology.IsBounded T.space :=
  (Bornology.isBounded_biUnion hfin).2 fun s _ =>
    (s.finite_toSet.isCompact_convexHull ℝ).isBounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- prepared 数据在 3-face 的开内部（去顶点）里每点有邻域下界（G1 的 `hloc`）：
`alpha_smooth` 给 `ContDiffAt`，`alpha_rank` 给 `fderiv` 单射。 -/
theorem prepared_localBiLip_AREA {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {x : ℂ} (hx : x ∈ preparedOpenFaces_AREA T) :
    ∃ W ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ W, ∀ z ∈ W,
      edist y z ≤ (L : ℝ≥0∞) * edist (α y) (α z) := by
  obtain ⟨s, ⟨hs, hc⟩, hxs⟩ := mem_iUnion₂.mp hx
  have hopen : openFace_AREA s ∈ 𝓝 x := (isOpen_openFace_AREA s).mem_nhds hxs
  have hnhd : convexHull ℝ (s : Set ℂ) \ (s : Set ℂ) ∈ 𝓝 x :=
    Filter.mem_of_superset hopen fun y hy => ⟨interior_subset hy.1, hy.2⟩
  have hhull : convexHull ℝ (s : Set ℂ) ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxs.1
  have hcd : ContDiffAt ℝ ∞ α x := (hprep.alpha_smooth s hs hc).contDiffAt hnhd
  have hrank := hprep.alpha_rank s hs hc x ⟨interior_subset hxs.1, hxs.2⟩
  rw [fderivWithin_of_mem_nhds hhull] at hrank
  exact exists_nhds_lower_bound_of_hasStrictFDerivAt_AREA (hcd.hasStrictFDerivAt (by simp)) hrank

variable [T3Space M]

/-- **G4a**（G1 对 prepared 数据的实例化）：开集 `U ⊆ ⋃ 3-face 开内部` 上
`A(u ∘ α, U) = A(u, α '' U)`；`u` 全局 Riemannian-Lipschitz。只用 `alpha_bij / alpha_lip /
alpha_smooth / alpha_rank`，**没有**用 `α` 的全局左逆（顶点处 `α` 退化）。 -/
theorem prepared_area_precomp_of_subset_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {U : Set ℂ} (hU : IsOpen U) (hUF : U ⊆ preparedOpenFaces_AREA T) :
    riemannianArea g (u ∘ α) U = riemannianArea g u (α '' U) := by
  obtain ⟨K, hK⟩ := hprep.alpha_lip
  have hUS : U ⊆ T.space := hUF.trans (preparedOpenFaces_subset_space_AREA T)
  exact area_precomp_of_local_bilipschitz_exhaustion_AREA g hu hU
    ((isBounded_space_AREA hprep.faces_finite).subset hUS) (hK.mono hUS)
    (hprep.alpha_bij.injOn.mono hUS) fun x hx => prepared_localBiLip_AREA hprep (hUF hx)

/-- **G4a'**：`U = ⋃ 3-face 开内部` 整体。 -/
theorem prepared_area_precomp_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    riemannianArea g (u ∘ α) (preparedOpenFaces_AREA T) =
      riemannianArea g u (α '' preparedOpenFaces_AREA T) :=
  prepared_area_precomp_of_subset_AREA g hprep hu (isOpen_preparedOpenFaces_AREA T) subset_rfl

/-- `T` 纯 2 维（每个面含于某个 3-face）⇒ `|T|` 去掉 3-face 开内部后零测（有限个 3-face 的边界与顶点）。 -/
theorem volume_space_diff_openFaces_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    (hfin : T.faces.Finite) (hpure : ∀ s ∈ T.faces, ∃ s' ∈ T.faces, s'.card = 3 ∧ s ⊆ s') :
    volume (T.space \ preparedOpenFaces_AREA T) = 0 := by
  have hF3 : {s : Finset ℂ | s ∈ T.faces ∧ s.card = 3}.Finite := hfin.subset fun s hs => hs.1
  have hsub : T.space \ preparedOpenFaces_AREA T ⊆
      ⋃ s ∈ {s : Finset ℂ | s ∈ T.faces ∧ s.card = 3},
        ((s : Set ℂ) ∪ frontier (convexHull ℝ (s : Set ℂ))) := by
    intro x hx
    obtain ⟨s0, hs0, hxs0⟩ := T.mem_space_iff.mp hx.1
    obtain ⟨s', hs', hc', hss'⟩ := hpure s0 hs0
    have hxh : x ∈ convexHull ℝ (s' : Set ℂ) := convexHull_mono (Finset.coe_subset.mpr hss') hxs0
    refine mem_iUnion₂.mpr ⟨s', ⟨hs', hc'⟩, ?_⟩
    by_cases hxs : x ∈ (s' : Set ℂ)
    · exact Or.inl hxs
    · refine Or.inr ?_
      rw [(s'.finite_toSet.isCompact_convexHull ℝ).isClosed.frontier_eq]
      refine ⟨(s'.finite_toSet.isCompact_convexHull ℝ).isClosed.closure_eq ▸ subset_closure hxh, ?_⟩
      intro hint
      exact hx.2 (mem_iUnion₂.mpr ⟨s', ⟨hs', hc'⟩, ⟨hint, hxs⟩⟩)
  refine measure_mono_null hsub ((measure_biUnion_null_iff hF3.countable).mpr fun s _ => ?_)
  exact measure_union_null (s.finite_toSet.measure_zero _)
    (Convex.addHaar_frontier volume (convex_convexHull ℝ (s : Set ℂ)))

/-- **G4b**（`A(f ∘ α)` 的换元）：`T` 纯 2 维时 `A(u ∘ α, |T|) = A(u, D̄)`。
取 `u = diskExtension f` 即 `A(f ∘ α) = A(f)`（`α` 把 `|T|` 双射到 `D̄`，例外集零测）。 -/
theorem prepared_area_precomp_space_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hpure : ∀ s ∈ T.faces, ∃ s' ∈ T.faces, s'.card = 3 ∧ s ⊆ s')
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    riemannianArea g (u ∘ α) T.space = riemannianArea g u (closedBall 0 1) := by
  obtain ⟨K, hK⟩ := hprep.alpha_lip
  have := area_precomp_of_local_bilipschitz_null_AREA g hu (isOpen_preparedOpenFaces_AREA T)
    (preparedOpenFaces_subset_space_AREA T)
    (volume_space_diff_openFaces_AREA hprep.faces_finite hpure)
    (isBounded_space_AREA hprep.faces_finite) hK
    (hprep.alpha_bij.injOn.mono (preparedOpenFaces_subset_space_AREA T))
    fun x hx => prepared_localBiLip_AREA hprep hx
  rwa [hprep.alpha_bij.image_eq] at this

end Prepared

section Caps

universe v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- 闭凸块（10.3 的 `IsPiecewiseAffineIntoComplex` 给出的闭凸片）的内部之并 a.e. 等于并本身
（凸集的边界零测），所以 G2 的开 cells 取 `interior (q i)` 即可。 -/
theorem iUnion_interior_ae_eq_of_convex_AREA {ι : Type*} [Finite ι] (q : ι → Set ℂ)
    (hqc : ∀ i, Convex ℝ (q i)) : (⋃ i, interior (q i)) =ᵐ[volume] ⋃ i, q i := by
  refine EventuallyLE.antisymm
    (LE.le.eventuallySubset (iUnion_mono fun i => interior_subset)) (ae_le_set.mpr ?_)
  refine measure_mono_null (t := ⋃ i, frontier (q i)) ?_ ?_
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    exact mem_iUnion.mpr ⟨i, ⟨subset_closure hi, fun hin => hx.2 (mem_iUnion.mpr ⟨i, hin⟩)⟩⟩
  · exact (measure_iUnion_null_iff.mpr fun i => Convex.addHaar_frontier volume (hqc i))

open scoped Classical in
/-- **G4c**（10.3 形状：cap 面积的 multiplicity 恒等式）。cap `a = u ∘ α' ∘ Λ`：`α'` 是 `α|_{|T|}` 的
全局 Lipschitz 延拓，`Λ` 在有限个开 cells `s i`（a.e. disjoint、并集 a.e. 为 `P`）上是 affine map
`Aff i · + b i`，映入 `|T|`；每个满秩 cell 的像 a.e. 等于某个 3-face `face (σ i)` 的开内部。则
`A(a) = ∑_k m_k * A(u, α '' τ_k)`，`m_k` 是满秩且 `σ i = k` 的 cell 个数；`τ_k` 是 `face k` 的开内部。
低秩 cell 贡献 0；全程没有用 `α` 的全局左逆。 -/
theorem cap_area_multiplicity_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {α' : ℂ → ℂ} {K' : ℝ≥0} (hα' : LipschitzWith K' α') (hαα' : EqOn α α' T.space)
    {ι : Type*} [Fintype ι] {P : Set ℂ} (hP : volume P ≠ ⊤) (s : ι → Set ℂ)
    (hs : ∀ i, IsOpen (s i)) (hsP : ∀ i, s i ⊆ P)
    (hsdisj : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[volume] P) {Λ : ℂ → ℂ}
    (Aff : ι → ℂ →L[ℝ] ℂ) (b : ι → ℂ) (hΛ : ∀ i, EqOn Λ (fun z => Aff i z + b i) (s i))
    {κ : Type*} [Fintype κ] (face : κ → Finset ℂ)
    (hface : ∀ k, face k ∈ T.faces ∧ (face k).card = 3) (σ : ι → κ)
    (hmatch : ∀ i, Function.Injective (Aff i) →
      Λ '' s i =ᵐ[volume] openFace_AREA (face (σ i))) :
    riemannianArea g (u ∘ α' ∘ Λ) P =
      ∑ k, ((Finset.univ.filter fun i => Function.Injective (Aff i) ∧ σ i = k).card : ℝ) *
        riemannianArea g u (α '' openFace_AREA (face k)) := by
  classical
  have hV : ∀ x y, riemannianEDistOf g ((u ∘ α') x) ((u ∘ α') y) ≤
      ((C * K' : ℝ≥0) : ℝ≥0∞) * edist x y := by
    intro x y
    calc
      _ ≤ (C : ℝ≥0∞) * edist (α' x) (α' y) := hu _ _
      _ ≤ (C : ℝ≥0∞) * ((K' : ℝ≥0∞) * edist x y) := by
        gcongr
        exact hα' x y
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  have hmain := area_piecewise_affine_cells_multiplicity_AREA g hV hP s hs hsP hsdisj hcover
    Aff b hΛ (fun k => openFace_AREA (face k)) σ hmatch
  rw [show u ∘ α' ∘ Λ = (u ∘ α') ∘ Λ from rfl, hmain]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hk : openFace_AREA (face k) ⊆ preparedOpenFaces_AREA T :=
    openFace_subset_preparedOpenFaces_AREA (hface k).1 (hface k).2
  rw [← prepared_area_precomp_of_subset_AREA g hprep hu (isOpen_openFace_AREA _) hk]
  exact riemannianArea_congr_on_open g (isOpen_openFace_AREA _) fun z hz => by
    simp only [Function.comp_apply]
    rw [hαα' (openFace_subset_space_AREA (hface k).1 hz)]

/-- **10.3 的和恒等式**：两个 cap（各自的 cells / `Λ±`，共用同一族 3-face）满足
`A(a₊) + A(a₋) = ∑_k (m₊,k + m₋,k) * A(u, α '' τ_k)`。 -/
theorem cap_area_pair_AREA (Xp Xm : ℝ) {κ : Type*} [Fintype κ] (mp mm a : κ → ℝ)
    (hp : Xp = ∑ k, mp k * a k) (hm : Xm = ∑ k, mm k * a k) :
    Xp + Xm = ∑ k, (mp k + mm k) * a k := by
  rw [hp, hm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (add_mul _ _ _).symm

open scoped Classical in
/-- **10.3 的面积恒等式（R12 `hcaps` 的 `riemannianDiskArea` 形）**：cap `a : D̄ → M`，
`a z = u (α' (Λ z))`，`Λ` 在覆盖 `D̄` 的有限开 cells 上 affine 并映入 `|T|`（满秩 cell 的像 a.e. 等于
某个 3-face 的开内部）⇒ `riemannianDiskArea g a = ∑_k m_k * A(u, α '' τ_k)`。 -/
theorem cap_diskArea_multiplicity_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {α' : ℂ → ℂ} {K' : ℝ≥0} (hα' : LipschitzWith K' α') (hαα' : EqOn α α' T.space)
    {ι : Type*} [Fintype ι] (s : ι → Set ℂ)
    (hs : ∀ i, IsOpen (s i)) (hsP : ∀ i, s i ⊆ closedBall (0 : ℂ) 1)
    (hsdisj : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[volume] closedBall (0 : ℂ) 1) {Λ : ℂ → ℂ}
    (Aff : ι → ℂ →L[ℝ] ℂ) (b : ι → ℂ) (hΛ : ∀ i, EqOn Λ (fun z => Aff i z + b i) (s i))
    {κ : Type*} [Fintype κ] (face : κ → Finset ℂ)
    (hface : ∀ k, face k ∈ T.faces ∧ (face k).card = 3) (σ : ι → κ)
    (hmatch : ∀ i, Function.Injective (Aff i) →
      Λ '' s i =ᵐ[volume] openFace_AREA (face (σ i)))
    {a : closedDisk → M} (ha : ∀ z : closedDisk, a z = u (α' (Λ z))) :
    riemannianDiskArea g a =
      ∑ k, ((Finset.univ.filter fun i => Function.Injective (Aff i) ∧ σ i = k).card : ℝ) *
        riemannianArea g u (α '' openFace_AREA (face k)) := by
  rw [riemannianDiskArea_eq_of_extension g a (u ∘ α' ∘ Λ) fun z => (ha z).symm]
  exact cap_area_multiplicity_AREA g hprep hu hα' hαα'
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne s hs hsP hsdisj hcover Aff b hΛ face hface
    σ hmatch

end Caps

section Flat

theorem zero_notMem_triVerts_AREA : (0 : ℂ) ∉ triVerts_FIX := by
  simp only [triVerts_FIX, Finset.mem_insert, Finset.mem_singleton, triV1_FIX, triV2_FIX,
    triV3_FIX, Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  norm_num

/-- `triComplex_FIX` 是纯 2 维的：每个面含于某个 3-face（`{0} ∪ 一条边`）。 -/
theorem triComplex_pure_AREA :
    ∀ s ∈ triComplex_FIX.faces, ∃ s' ∈ triComplex_FIX.faces, s'.card = 3 ∧ s ⊆ s' := by
  classical
  have aux : ∀ σ : Finset ℂ, σ ⊆ triVerts_FIX → σ.card ≤ 2 →
      ∃ s' ∈ triComplex_FIX.faces, s'.card = 3 ∧ insert 0 σ ⊆ s' := by
    intro σ hσ hc
    obtain ⟨u, hσu, huT, hu2⟩ :=
      Finset.exists_subsuperset_card_eq hσ hc (by rw [triVerts_card_FIX]; omega)
    have hu : u ∈ triBoundary_FIX.faces := by
      refine ⟨huT, Finset.card_pos.mp (by omega), ?_⟩
      rintro rfl
      rw [triVerts_card_FIX] at hu2
      omega
    refine ⟨insert 0 u, (mem_coneComplex_faces_iff isConeBase_tri_FIX).mpr
      (Or.inr (Or.inr ⟨u, hu, rfl⟩)), ?_, Finset.insert_subset_insert _ hσu⟩
    rw [Finset.card_insert_of_notMem (fun h0 => zero_notMem_triVerts_AREA (huT h0)), hu2]
  have hcard : ∀ σ ∈ triBoundary_FIX.faces, σ.card ≤ 2 := by
    intro σ hσ
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hσ.1, hσ.2.2⟩)
    rw [triVerts_card_FIX] at this
    omega
  intro s hs
  rcases (mem_coneComplex_faces_iff isConeBase_tri_FIX).mp hs with h | h | ⟨σ, hσ, rfl⟩
  · obtain ⟨s', hs', hc', hss'⟩ := aux s h.1 (hcard s h)
    exact ⟨s', hs', hc', (Finset.subset_insert _ _).trans hss'⟩
  · obtain ⟨s', hs', hc', hss'⟩ := aux ∅ (Finset.empty_subset _) (by simp)
    exact ⟨s', hs', hc', by rw [h]; simpa using hss'⟩
  · exact aux σ hσ.1 (hcard σ hσ)

/-- **G4d**（`flatDisk_prepared_FIX` 的 `α = radialGrid_FIX` 实例化 G1）：
对任意全局 Riemannian-Lipschitz `u`，`A(u ∘ α, |T|) = A(u, D̄)`——`α` 在原点（cone 顶点）处退化、
逆不 Lipschitz，但面积换元仍成立。 -/
theorem flatDisk_area_precomp_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) E3_FIX)
    {u : ℂ → E3_FIX} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    riemannianArea g (u ∘ radialGrid_FIX) triComplex_FIX.space =
      riemannianArea g u (closedBall 0 1) :=
  prepared_area_precomp_space_AREA g flatDisk_prepared_FIX triComplex_pure_AREA hu

/-- **consumer**：平坦标准盘 `F = flatCLM_FIX`（标准欧氏度量）：`A(F ∘ α, |T|) = A(F, D̄)`。 -/
theorem flatDisk_euclidean_area_precomp_AREA :
    riemannianArea (standardEuclideanMetric E3_FIX) (⇑flatCLM_FIX ∘ radialGrid_FIX)
        triComplex_FIX.space =
      riemannianArea (standardEuclideanMetric E3_FIX) (⇑flatCLM_FIX) (closedBall 0 1) :=
  flatDisk_area_precomp_AREA (standardEuclideanMetric E3_FIX) (C := ‖flatCLM_FIX‖₊) fun x y => by
    rw [riemannianEDistOf_standardEuclideanMetric]
    exact flatCLM_FIX.lipschitzWith x y

end Flat

section CapsDisk

universe w

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **G3 的 consumer**（cap 的 global Lipschitz，10.3 的 `Lip g ap`）：`a : D̄ → M` 在有限个闭凸块
`q i ⊆ D̄`（覆盖 `D̄`）上等于 `V ∘ (Aff i · + b i)`（`V` 全局 Riemannian-Lipschitz），`C * ‖Aff i‖ ≤ K` ⇒
`a` 在整个闭盘上 `K`-Lipschitz。`Λ` 跨 sheet 的跳变不出现：只要求每块上的**复合**是 affine 的 `V`-像。 -/
theorem cap_lipschitz_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {V : ℂ → M} {C : ℝ≥0}
    (hV : ∀ x y, riemannianEDistOf g (V x) (V y) ≤ (C : ℝ≥0∞) * edist x y)
    {ι : Type*} [Finite ι] (q : ι → Set ℂ) (hq : ∀ i, IsClosed (q i))
    (hqc : ∀ i, Convex ℝ (q i)) (hqD : ∀ i, q i ⊆ closedBall (0 : ℂ) 1)
    (hcover : closedBall (0 : ℂ) 1 ⊆ ⋃ i, q i)
    (Aff : ι → ℂ →L[ℝ] ℂ) (b : ι → ℂ) {a : closedDisk → M}
    (ha : ∀ i, ∀ z : closedDisk, (z : ℂ) ∈ q i → a z = V (Aff i z + b i)) {K : ℝ≥0}
    (hK : ∀ i, C * ‖Aff i‖₊ ≤ K) :
    ∀ z w : closedDisk, riemannianEDistOf g (a z) (a w) ≤ (K : ℝ≥0∞) * edist z w := by
  let cg := g.toContinuousRiemannianMetric
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hc (i : ι) (z : ℂ) (hz : z ∈ q i) : diskExtension a z = V (Aff i z + b i) := by
    have hzD : z ∈ closedBall (0 : ℂ) 1 := hqD i hz
    have := diskExtension_coe a ⟨z, hzD⟩
    rw [← ha i ⟨z, hzD⟩ hz]
    exact this
  have hpiece (i : ι) : LipschitzOnWith K (diskExtension a) (q i) := by
    intro x hx y hy
    rw [hc i x hx, hc i y hy]
    calc edist (V (Aff i x + b i)) (V (Aff i y + b i))
        ≤ (C : ℝ≥0∞) * edist (Aff i x + b i) (Aff i y + b i) := hV _ _
      _ ≤ (C : ℝ≥0∞) * ((‖Aff i‖₊ : ℝ≥0∞) * edist x y) := by
        gcongr
        exact lipschitzWith_affine_AREA (Aff i) (b i) x y
      _ = ((C * ‖Aff i‖₊ : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
      _ ≤ (K : ℝ≥0∞) * edist x y := by gcongr; exact_mod_cast hK i
  have hglob := lipschitz_of_piecewise_lipschitz_AREA (convex_closedBall (0 : ℂ) 1) hq hqc hcover
    hpiece
  intro z w
  have h := hglob z.2 w.2
  rw [diskExtension_coe a z, diskExtension_coe a w] at h
  exact h

end CapsDisk

end DifferentialGeometry.Geometry
