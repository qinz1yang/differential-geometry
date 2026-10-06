import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexTriangleFIX
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage

/-!
# S-MY-FIX G2：平坦标准盘 fixture 的 ambient 侧（`A`、`φ`、`h`，`_FIX`）

`ℝ³ = EuclideanSpace ℝ (Fin 3)` 里的数据：

* **`K_flat = φ(T)`**：`simplicialImage T flat`（平面 `z = 0` 里的 2-复形），`φ = flat` 是线性嵌入
  `z ↦ (Re z, Im z, 0)`（作 affine map，便于 `simplicialMap_eqOn_affine`）。
* **`A`** = `K_flat` 的 suspension：两个 cone（apex `(0,0,±1)`）的 `unionComplex`。cone 的 `IsConeBase`
  由“`K_flat ⊆ {z = 0}`、apex 离开该平面”直接给；两个 cone 之间的交相容（`cone_cross_compat_FIX`）
  用线性泛函 `p₂` 把交点压到 `z = 0` 的子复形（`mem_hull_filter_FIX`）再用 `K_flat` 自身的相容性。
* **`|A| = {g(π p) + |p₂| ≤ 1}`**（`bipyramid_space_FIX`）是 6 个半空间的 H-多胞体，故由库里的
  `IsHPolytope.isPLBall` 是 PL 3-球，再由 `isPLSphere_or_isPLBall_geometricLink_of_isPLBall` 得
  `IsCombinatorialManifoldWithBoundary 3 A`（不手工验 vertex link）。
* **`h p = f(α(π p)) + p₂ e₃`**：在 `|A|` 上单射；像集是显式的 `W = {‖π q‖ + |q₂| ≤ 1}`（Euclidean 范数的
  双锥），所以 trace `∂D̄ × {0} ⊆ frontier W`、`D° × {0} ⊆ interior W` 是 sublevel 集的初等事实
  （不需要 invariance of domain）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Geometry

abbrev E3_FIX := EuclideanSpace ℝ (Fin 3)

/-- 坐标图 `ℝ³ → (Fin 3 → ℝ)`。 -/
def coord_FIX (p : E3_FIX) : Fin 3 → ℝ := EuclideanSpace.equiv (Fin 3) ℝ p

/-- `(x, y, z) ∈ ℝ³`。 -/
def mk3_FIX (x y z : ℝ) : E3_FIX := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x, y, z]

theorem coord_mk3_FIX (x y z : ℝ) : coord_FIX (mk3_FIX x y z) = ![x, y, z] :=
  (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _

theorem coord_injective_FIX : Function.Injective coord_FIX :=
  (EuclideanSpace.equiv (Fin 3) ℝ).injective

theorem mk3_coord_FIX (p : E3_FIX) :
    p = mk3_FIX (coord_FIX p 0) (coord_FIX p 1) (coord_FIX p 2) := by
  apply coord_injective_FIX
  rw [coord_mk3_FIX]
  ext i; fin_cases i <;> rfl

theorem coord_add_FIX (p q : E3_FIX) (i : Fin 3) :
    coord_FIX (p + q) i = coord_FIX p i + coord_FIX q i := by
  simp [coord_FIX]

theorem coord_smul_FIX (a : ℝ) (p : E3_FIX) (i : Fin 3) :
    coord_FIX (a • p) i = a * coord_FIX p i := by
  simp [coord_FIX]

/-- 平坦嵌入 `ℂ → ℝ³`，`z ↦ (Re z, Im z, 0)`。 -/
def flatCLM_FIX : ℂ →L[ℝ] E3_FIX :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ![Complex.reCLM, Complex.imCLM, 0] i)

theorem coord_flat_FIX (z : ℂ) : coord_FIX (flatCLM_FIX z) = ![z.re, z.im, 0] := by
  have : coord_FIX (flatCLM_FIX z) = ContinuousLinearMap.pi
      (fun i => ![Complex.reCLM, Complex.imCLM, 0] i) z :=
    (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _
  rw [this]
  ext i
  fin_cases i <;> simp

theorem flat_eq_mk3_FIX (z : ℂ) : flatCLM_FIX z = mk3_FIX z.re z.im 0 :=
  coord_injective_FIX (by rw [coord_flat_FIX, coord_mk3_FIX])

theorem flatCLM_injective_FIX : Function.Injective flatCLM_FIX := by
  intro z w hzw
  have h := congrArg coord_FIX hzw
  rw [coord_flat_FIX, coord_flat_FIX] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact Complex.ext (by simpa using h0) (by simpa using h1)


/-- 第三坐标泛函。 -/
def pzCLM_FIX : E3_FIX →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

theorem pzCLM_apply_FIX (p : E3_FIX) : pzCLM_FIX p = coord_FIX p 2 := rfl

/-- 投影 `π : ℝ³ → ℂ`，`p ↦ p₀ + p₁ i`。 -/
def proj12_FIX (p : E3_FIX) : ℂ := ⟨coord_FIX p 0, coord_FIX p 1⟩

theorem proj12_flat_FIX (z : ℂ) : proj12_FIX (flatCLM_FIX z) = z := by
  simp [proj12_FIX, coord_flat_FIX]

theorem pz_flat_FIX (z : ℂ) : pzCLM_FIX (flatCLM_FIX z) = 0 := by
  rw [pzCLM_apply_FIX, coord_flat_FIX]; rfl

theorem pz_mk3_FIX (x y z : ℝ) : pzCLM_FIX (mk3_FIX x y z) = z := by
  rw [pzCLM_apply_FIX, coord_mk3_FIX]; rfl

/-- `φ`：平坦线性嵌入（affine 版本）。 -/
def flatAffine_FIX : ℂ →ᵃ[ℝ] E3_FIX := flatCLM_FIX.toLinearMap.toAffineMap

theorem flatAffine_apply_FIX (z : ℂ) : flatAffine_FIX z = flatCLM_FIX z := rfl

theorem injOn_simplicialMap_flat_FIX :
    InjOn (simplicialMap triComplex_FIX (⇑flatAffine_FIX)) triComplex_FIX.space := by
  intro x hx y hy hxy
  rw [simplicialMap_eqOn_affine _ _ hx, simplicialMap_eqOn_affine _ _ hy] at hxy
  exact flatCLM_injective_FIX hxy

theorem affineIndependent_flat_faces_FIX :
    ∀ σ ∈ triComplex_FIX.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ σ.image (⇑flatAffine_FIX)} → E3_FIX) := fun _ hσ =>
  affineIndependent_image_of_injOn_convexHull flatAffine_FIX (triComplex_FIX.indep hσ)
    (flatCLM_injective_FIX.injOn)

/-- 平坦 2-复形 `K_flat = φ(T)`（在 `ℝ³` 里，位于平面 `z = 0`）。 -/
def Kflat_FIX : Geometry.SimplicialComplex ℝ E3_FIX :=
  simplicialImage triComplex_FIX (⇑flatAffine_FIX) affineIndependent_flat_faces_FIX
    injOn_simplicialMap_flat_FIX

theorem Kflat_space_FIX : Kflat_FIX.space = flatCLM_FIX '' triComplex_FIX.space := by
  rw [Kflat_FIX, simplicialImage_space]
  exact image_congr (simplicialMap_eqOn_affine _ _)

theorem Kflat_faces_finite_FIX : Kflat_FIX.faces.Finite :=
  haveI : Finite triComplex_FIX.faces := triComplex_faces_finite_FIX.to_subtype
  simplicialImage_faces_finite _ _ _ _

theorem pz_eq_zero_of_mem_Kflat_FIX {x : E3_FIX} (hx : x ∈ Kflat_FIX.space) : pzCLM_FIX x = 0 := by
  rw [Kflat_space_FIX] at hx
  obtain ⟨z, -, rfl⟩ := hx
  exact pz_flat_FIX z

theorem pz_eq_zero_of_mem_face_FIX {σ : Finset E3_FIX} (hσ : σ ∈ Kflat_FIX.faces) {v : E3_FIX}
    (hv : v ∈ σ) : pzCLM_FIX v = 0 :=
  pz_eq_zero_of_mem_Kflat_FIX
    (Kflat_FIX.convexHull_subset_space hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)))

theorem isConeBase_Kflat_FIX {a : E3_FIX} (ha : pzCLM_FIX a ≠ 0) : IsConeBase a Kflat_FIX where
  notMem_space := fun h => ha (pz_eq_zero_of_mem_Kflat_FIX h)
  indep := by
    intro σ hσ
    have haσ : a ∉ σ := fun h => ha (pz_eq_zero_of_mem_face_FIX hσ h)
    have h := (affineIndependent_insert_iff haσ (Kflat_FIX.indep hσ)).mpr (by
      rintro ⟨c, -, hc⟩
      have h2 := congrArg pzCLM_FIX hc
      rw [map_sum] at h2
      refine ha (h2.symm.trans (Finset.sum_eq_zero fun v hv => ?_))
      rw [map_smul, pz_eq_zero_of_mem_face_FIX hσ hv, smul_zero])
    refine AffineIndependent.mono (t := ((insert a σ : Finset E3_FIX) : Set E3_FIX)) h ?_
    rw [Finset.coe_insert]
  radial := by
    intro x hx y hy t _ hyx
    have h1 := congrArg pzCLM_FIX hyx
    rw [map_add, map_smul, map_sub, pz_eq_zero_of_mem_Kflat_FIX hx, pz_eq_zero_of_mem_Kflat_FIX hy,
      smul_eq_mul] at h1
    have ht : t = 1 := by
      have : (1 - t) * pzCLM_FIX a = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h ha
    rw [hyx, ht, one_smul, add_sub_cancel]


/-! ## apex `±e₃` 上的 cone 与 bipyramid `A` -/

theorem pz_ne_zero_apex_FIX {ε : ℝ} (hε : ε ≠ 0) : pzCLM_FIX (mk3_FIX 0 0 ε) ≠ 0 := by
  rw [pz_mk3_FIX]; exact hε

/-- 以 `(0, 0, ε)` 为 apex 的 `K_flat` 上的 cone。 -/
def coneKflat_FIX (ε : ℝ) (hε : ε ≠ 0) : Geometry.SimplicialComplex ℝ E3_FIX :=
  coneComplex (isConeBase_Kflat_FIX (pz_ne_zero_apex_FIX hε))

/-- 线性泛函 `λ ≥ 0` 的顶点集上，`λ p = 0` 的点落在 `λ = 0` 的子集的凸包里。 -/
theorem mem_hull_filter_FIX {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : ∀ v ∈ s, 0 ≤ lam v) {p : E}
    (hp : p ∈ convexHull ℝ (s : Set E)) (hlam : lam p = 0) :
    p ∈ convexHull ℝ ((s.filter (fun v => lam v = 0) : Finset E) : Set E) := by
  obtain ⟨w, hw0, hw1, hwp⟩ := mem_convexHull_iff_exists_weights.mp hp
  have hsum : ∑ v ∈ s, w v * lam v = 0 := by
    rw [← hlam, ← hwp, map_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [map_smul, smul_eq_mul]
  have hzero : ∀ v ∈ s, w v * lam v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun v hv => mul_nonneg (hw0 v hv) (hs v hv)).mp hsum
  have hw : ∀ v ∈ s, w v ≠ 0 → lam v = 0 := fun v hv hne =>
    (mul_eq_zero.mp (hzero v hv)).resolve_left hne
  refine mem_convexHull_iff_exists_weights.mpr ⟨w, fun v hv => hw0 v (Finset.mem_filter.mp hv).1,
    ?_, ?_⟩
  · rw [Finset.sum_filter_of_ne fun v hv hne => hw v hv hne, hw1]
  · rw [Finset.sum_filter_of_ne fun v hv hne => hw v hv (fun h => hne (by rw [h, zero_smul])), hwp]

theorem lam_nonneg_of_mem_hull_FIX {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : ∀ v ∈ s, 0 ≤ lam v) {p : E}
    (hp : p ∈ convexHull ℝ (s : Set E)) : 0 ≤ lam p := by
  obtain ⟨w, hw0, -, hwp⟩ := mem_convexHull_iff_exists_weights.mp hp
  rw [← hwp, map_sum]
  exact Finset.sum_nonneg fun v hv => by
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hw0 v hv) (hs v hv)


theorem coneKflat_face_FIX {ε : ℝ} (hε : ε ≠ 0) {s : Finset E3_FIX}
    (hs : s ∈ (coneKflat_FIX ε hε).faces) :
    (∀ v ∈ s, pzCLM_FIX v = 0 ∨ v = mk3_FIX 0 0 ε) ∧
      (∀ v ∈ s, v ≠ mk3_FIX 0 0 ε → pzCLM_FIX v = 0) ∧
      ((s.filter (fun v => pzCLM_FIX v = 0)).Nonempty →
        s.filter (fun v => pzCLM_FIX v = 0) ∈ Kflat_FIX.faces) := by
  have hbase : IsConeBase (mk3_FIX 0 0 ε) Kflat_FIX := isConeBase_Kflat_FIX (pz_ne_zero_apex_FIX hε)
  have hap : pzCLM_FIX (mk3_FIX 0 0 ε) ≠ 0 := pz_ne_zero_apex_FIX hε
  rcases (mem_coneComplex_faces_iff hbase).mp hs with h | h | ⟨σ, hσ, rfl⟩
  · refine ⟨fun v hv => Or.inl (pz_eq_zero_of_mem_face_FIX h hv),
      fun v hv _ => pz_eq_zero_of_mem_face_FIX h hv, fun _ => ?_⟩
    rwa [Finset.filter_true_of_mem fun v hv => pz_eq_zero_of_mem_face_FIX h hv]
  · subst h
    refine ⟨fun v hv => Or.inr (Finset.mem_singleton.mp hv), fun v hv hne => absurd
      (Finset.mem_singleton.mp hv) hne, fun hne => ?_⟩
    exfalso
    obtain ⟨v, hv⟩ := hne
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    rw [Finset.mem_singleton.mp hv1] at hv2
    exact hap hv2
  · have haσ : mk3_FIX 0 0 ε ∉ σ := fun h => hap (pz_eq_zero_of_mem_face_FIX hσ h)
    refine ⟨fun v hv => ?_, fun v hv hne => ?_, fun _ => ?_⟩
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inr rfl
      · exact Or.inl (pz_eq_zero_of_mem_face_FIX hσ hv)
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact absurd rfl hne
      · exact pz_eq_zero_of_mem_face_FIX hσ hv
    · rw [Finset.filter_insert]
      simp only [hap, ↓reduceIte]
      rw [Finset.filter_true_of_mem fun v hv => pz_eq_zero_of_mem_face_FIX hσ hv]
      exact hσ


theorem neg_one_ne_zero_FIX : (-1 : ℝ) ≠ 0 := by norm_num

theorem cone_cross_compat_FIX :
    ∀ s ∈ (coneKflat_FIX 1 one_ne_zero).faces, ∀ t ∈ (coneKflat_FIX (-1) neg_one_ne_zero_FIX).faces,
      convexHull ℝ (s : Set E3_FIX) ∩ convexHull ℝ (t : Set E3_FIX) ⊆
        convexHull ℝ ((s : Set E3_FIX) ∩ (t : Set E3_FIX)) := by
  intro s hs t ht p ⟨hps, hpt⟩
  obtain ⟨hs1, -, hs3⟩ := coneKflat_face_FIX one_ne_zero hs
  obtain ⟨ht1, -, ht3⟩ := coneKflat_face_FIX neg_one_ne_zero_FIX ht
  have hsn : ∀ v ∈ s, 0 ≤ pzCLM_FIX.toLinearMap v := by
    intro v hv
    rcases hs1 v hv with h | rfl
    · rw [ContinuousLinearMap.coe_coe, h]
    · rw [ContinuousLinearMap.coe_coe, pz_mk3_FIX]; norm_num
  have htn : ∀ v ∈ t, 0 ≤ (-pzCLM_FIX).toLinearMap v := by
    intro v hv
    rcases ht1 v hv with h | rfl
    · rw [ContinuousLinearMap.coe_coe, neg_apply, h]; norm_num
    · rw [ContinuousLinearMap.coe_coe, neg_apply, pz_mk3_FIX]; norm_num
  have hp0 : pzCLM_FIX p = 0 := by
    have h1 := lam_nonneg_of_mem_hull_FIX _ hsn hps
    have h2 := lam_nonneg_of_mem_hull_FIX _ htn hpt
    rw [ContinuousLinearMap.coe_coe] at h1
    rw [ContinuousLinearMap.coe_coe, neg_apply] at h2
    linarith
  have h1 := mem_hull_filter_FIX _ hsn hps (by rw [ContinuousLinearMap.coe_coe]; exact hp0)
  have h2 := mem_hull_filter_FIX _ htn hpt (by
    rw [ContinuousLinearMap.coe_coe, neg_apply, hp0, neg_zero])
  have e1 : s.filter (fun v => pzCLM_FIX.toLinearMap v = 0) = s.filter (fun v => pzCLM_FIX v = 0) :=
    Finset.filter_congr fun v _ => by rw [ContinuousLinearMap.coe_coe]
  have e2 : t.filter (fun v => (-pzCLM_FIX).toLinearMap v = 0) =
      t.filter (fun v => pzCLM_FIX v = 0) :=
    Finset.filter_congr fun v _ => by
      rw [ContinuousLinearMap.coe_coe, neg_apply, neg_eq_zero]
  rw [e1] at h1
  rw [e2] at h2
  have hne1 : (s.filter (fun v => pzCLM_FIX v = 0)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h1
    simp at h1
  have hne2 : (t.filter (fun v => pzCLM_FIX v = 0)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h2
    simp at h2
  have h3 := Kflat_FIX.inter_subset_convexHull (hs3 hne1) (ht3 hne2) ⟨h1, h2⟩
  exact convexHull_mono (inter_subset_inter (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    (Finset.coe_subset.mpr (Finset.filter_subset _ _))) h3

/-- thickening `A`：`K_flat` 的 suspension（两个 cone，apex `±e₃`）。 -/
def bipyramid_FIX : Geometry.SimplicialComplex ℝ E3_FIX :=
  unionComplex (coneKflat_FIX 1 one_ne_zero) (coneKflat_FIX (-1) neg_one_ne_zero_FIX)
    cone_cross_compat_FIX

theorem bipyramid_faces_finite_FIX : bipyramid_FIX.faces.Finite :=
  unionComplex_faces_finite _ _ _ (coneComplex_faces_finite _ Kflat_faces_finite_FIX)
    (coneComplex_faces_finite _ Kflat_faces_finite_FIX)


/-! ## `|A| = {g(π p) + |p₂| ≤ 1}`（多胞体） -/

/-- `|A|` 的 H-多胞体描述。 -/
def bipyramidSet_FIX : Set E3_FIX := {p | triGauge_FIX (proj12_FIX p) + |pzCLM_FIX p| ≤ 1}

theorem proj12_add_FIX (p q : E3_FIX) : proj12_FIX (p + q) = proj12_FIX p + proj12_FIX q := by
  refine Complex.ext ?_ ?_ <;> simp [proj12_FIX, coord_add_FIX]

theorem proj12_smul_FIX (a : ℝ) (p : E3_FIX) : proj12_FIX (a • p) = a • proj12_FIX p := by
  refine Complex.ext ?_ ?_ <;> simp [proj12_FIX, coord_smul_FIX]

theorem convex_bipyramidSet_FIX : Convex ℝ bipyramidSet_FIX := by
  intro x hx y hy a b ha hb hab
  rw [bipyramidSet_FIX, mem_ofPred_eq] at hx hy ⊢
  rw [proj12_add_FIX, proj12_smul_FIX, proj12_smul_FIX, map_add, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul]
  have h1 := triGauge_convex_FIX ha hb (proj12_FIX x) (proj12_FIX y)
  have h2 : |a * pzCLM_FIX x + b * pzCLM_FIX y| ≤ a * |pzCLM_FIX x| + b * |pzCLM_FIX y| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem mem_bipyramidSet_flat_FIX {z : ℂ} (hz : triGauge_FIX z ≤ 1) :
    flatCLM_FIX z ∈ bipyramidSet_FIX := by
  rw [bipyramidSet_FIX, mem_ofPred_eq, proj12_flat_FIX, pz_flat_FIX, abs_zero, add_zero]
  exact hz

theorem apex_mem_bipyramidSet_FIX {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    mk3_FIX 0 0 ε ∈ bipyramidSet_FIX := by
  have h0 : proj12_FIX (mk3_FIX 0 0 ε) = 0 := by
    refine Complex.ext ?_ ?_ <;> simp [proj12_FIX, coord_mk3_FIX]
  rw [bipyramidSet_FIX, mem_ofPred_eq, h0, pz_mk3_FIX, triGauge_zero_FIX]
  rcases hε with rfl | rfl <;> norm_num

theorem cone_space_subset_bipyramidSet_FIX {ε : ℝ} (hε0 : ε ≠ 0) (hε : ε = 1 ∨ ε = -1) :
    (coneKflat_FIX ε hε0).space ⊆ bipyramidSet_FIX := by
  refine coneComplex_space_subset_convex convex_bipyramidSet_FIX (apex_mem_bipyramidSet_FIX hε)
    (isConeBase_Kflat_FIX (pz_ne_zero_apex_FIX hε0)) ?_
  intro x hx
  rw [Kflat_space_FIX] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [triComplex_space_FIX] at hz
  exact mem_bipyramidSet_flat_FIX hz


theorem apex_combo_FIX (ε s x y : ℝ) :
    mk3_FIX 0 0 ε + s • (mk3_FIX x y 0 - mk3_FIX 0 0 ε) =
      mk3_FIX (s * x) (s * y) (ε + -(s * ε)) := by
  ext i
  fin_cases i <;> simp [mk3_FIX]

theorem proj12_mk3_FIX (x y z : ℝ) : proj12_FIX (mk3_FIX x y z) = ⟨x, y⟩ := by
  simp [proj12_FIX, coord_mk3_FIX]

theorem mk3_mem_cone_space_FIX {ε : ℝ} (hε0 : ε ≠ 0) (hε : ε = 1 ∨ ε = -1) (x y z : ℝ)
    (hp : mk3_FIX x y z ∈ bipyramidSet_FIX) (hpz : 0 ≤ ε * z) :
    mk3_FIX x y z ∈ (coneKflat_FIX ε hε0).space := by
  rw [bipyramidSet_FIX, mem_ofPred_eq, proj12_mk3_FIX, pz_mk3_FIX] at hp
  rw [coneKflat_FIX, mem_coneComplex_space_iff]
  have habs : |z| = ε * z := by
    rcases hε with rfl | rfl
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith)]; ring
  have hg0 := triGauge_nonneg_FIX (⟨x, y⟩ : ℂ)
  by_cases hone : |z| = 1
  · left
    have hu0 : (⟨x, y⟩ : ℂ) = 0 := by
      by_contra h
      have := triGauge_pos_FIX h
      linarith
    have hx : x = 0 := congrArg Complex.re hu0
    have hy : y = 0 := congrArg Complex.im hu0
    have hzε : z = ε := by
      rcases hε with rfl | rfl <;> linarith
    rw [hx, hy, hzε]
  · right
    have hlt : |z| < 1 := lt_of_le_of_ne (by linarith) hone
    have hs : 0 < 1 - |z| := by linarith
    have hs1 : 1 - |z| ≤ 1 := by linarith [abs_nonneg z]
    refine ⟨flatCLM_FIX ((1 - |z|)⁻¹ • (⟨x, y⟩ : ℂ)), ?_, 1 - |z|, hs, hs1, ?_⟩
    · rw [Kflat_space_FIX]
      refine ⟨(1 - |z|)⁻¹ • (⟨x, y⟩ : ℂ), ?_, rfl⟩
      rw [triComplex_space_FIX, mem_ofPred_eq, triGauge_smul_FIX (inv_nonneg.mpr hs.le),
        inv_mul_le_iff₀ hs]
      linarith
    · rw [flat_eq_mk3_FIX, apex_combo_FIX]
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      rw [mul_inv_cancel_left₀ hs.ne', mul_inv_cancel_left₀ hs.ne']
      congr 1
      rw [show ε + -((1 - |z|) * ε) = |z| * ε by ring, habs]
      rcases hε with rfl | rfl <;> ring


theorem bipyramid_space_FIX : bipyramid_FIX.space = bipyramidSet_FIX := by
  rw [bipyramid_FIX, unionComplex_space]
  refine Subset.antisymm (union_subset
    (cone_space_subset_bipyramidSet_FIX one_ne_zero (Or.inl rfl))
    (cone_space_subset_bipyramidSet_FIX neg_one_ne_zero_FIX (Or.inr rfl))) fun p hp => ?_
  rw [mk3_coord_FIX p] at hp ⊢
  have hz : coord_FIX p 2 = pzCLM_FIX p := rfl
  rcases le_total 0 (coord_FIX p 2) with h | h
  · exact Or.inl (mk3_mem_cone_space_FIX one_ne_zero (Or.inl rfl) _ _ _ hp (by linarith))
  · exact Or.inr (mk3_mem_cone_space_FIX neg_one_ne_zero_FIX (Or.inr rfl) _ _ _ hp (by linarith))

theorem isCompact_bipyramidSet_FIX : IsCompact bipyramidSet_FIX := by
  rw [← bipyramid_space_FIX]
  exact bipyramid_faces_finite_FIX.isCompact_biUnion
    (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)


/-- 坐标泛函。 -/
def coordCLM_FIX (i : Fin 3) : E3_FIX →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

theorem coordCLM_apply_FIX (i : Fin 3) (p : E3_FIX) : coordCLM_FIX i p = coord_FIX p i := rfl

theorem abs_coord_le_norm_FIX (p : E3_FIX) (i : Fin 3) : |coord_FIX p i| ≤ ‖p‖ := by
  have h := PiLp.norm_apply_le p i
  rwa [Real.norm_eq_abs] at h

/-- 六个半空间（`H`-多胞体的描述）。 -/
def hplanes_FIX : Fin 6 → E3_FIX →L[ℝ] ℝ :=
  ![-coordCLM_FIX 1 + coordCLM_FIX 2, -coordCLM_FIX 1 - coordCLM_FIX 2,
    coordCLM_FIX 0 + coordCLM_FIX 1 + coordCLM_FIX 2,
    coordCLM_FIX 0 + coordCLM_FIX 1 - coordCLM_FIX 2,
    -coordCLM_FIX 0 + coordCLM_FIX 2, -coordCLM_FIX 0 - coordCLM_FIX 2]

theorem hplanes_apply_FIX (p : E3_FIX) :
    hplanes_FIX 0 p = -coord_FIX p 1 + coord_FIX p 2 ∧
    hplanes_FIX 1 p = -coord_FIX p 1 - coord_FIX p 2 ∧
    hplanes_FIX 2 p = coord_FIX p 0 + coord_FIX p 1 + coord_FIX p 2 ∧
    hplanes_FIX 3 p = coord_FIX p 0 + coord_FIX p 1 - coord_FIX p 2 ∧
    hplanes_FIX 4 p = -coord_FIX p 0 + coord_FIX p 2 ∧
    hplanes_FIX 5 p = -coord_FIX p 0 - coord_FIX p 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hplanes_FIX, coordCLM_apply_FIX]

theorem bipyramidSet_eq_halfspaces_FIX :
    bipyramidSet_FIX =
      {p | ∀ i, (fun i => (hplanes_FIX i).toLinearMap) i p ≤ (fun _ => (1 : ℝ)) i} := by
  ext p
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hplanes_apply_FIX p
  have hz := abs_cases (coord_FIX p 2)
  constructor
  · intro hp i
    rw [bipyramidSet_FIX, mem_ofPred_eq] at hp
    have h1 := triGauge_ge_re_FIX (proj12_FIX p)
    have h2 := triGauge_ge_im_FIX (proj12_FIX p)
    have h3 := triGauge_ge_sum_FIX (proj12_FIX p)
    simp only [proj12_FIX] at h1 h2 h3 hp
    rw [pzCLM_apply_FIX] at hp
    fin_cases i
    · change hplanes_FIX 0 p ≤ 1
      rw [q0]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
    · change hplanes_FIX 1 p ≤ 1
      rw [q1]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
    · change hplanes_FIX 2 p ≤ 1
      rw [q2]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
    · change hplanes_FIX 3 p ≤ 1
      rw [q3]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
    · change hplanes_FIX 4 p ≤ 1
      rw [q4]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
    · change hplanes_FIX 5 p ≤ 1
      rw [q5]; rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  · intro h
    rw [bipyramidSet_FIX, mem_ofPred_eq, pzCLM_apply_FIX]
    have h0 : hplanes_FIX 0 p ≤ 1 := h 0
    have h1 : hplanes_FIX 1 p ≤ 1 := h 1
    have h2 : hplanes_FIX 2 p ≤ 1 := h 2
    have h3 : hplanes_FIX 3 p ≤ 1 := h 3
    have h4 : hplanes_FIX 4 p ≤ 1 := h 4
    have h5 : hplanes_FIX 5 p ≤ 1 := h 5
    rw [q0] at h0
    rw [q1] at h1
    rw [q2] at h2
    rw [q3] at h3
    rw [q4] at h4
    rw [q5] at h5
    unfold triGauge_FIX
    simp only [proj12_FIX]
    rw [← max_add_add_right, ← max_add_add_right]
    refine max_le (max_le ?_ ?_) ?_ <;> rcases hz with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith

theorem isHPolytope_bipyramidSet_FIX : IsHPolytope bipyramidSet_FIX :=
  ⟨isCompact_bipyramidSet_FIX, Fin 6, inferInstance, fun i => (hplanes_FIX i).toLinearMap,
    fun _ => 1, bipyramidSet_eq_halfspaces_FIX⟩

theorem zero_mem_interior_bipyramidSet_FIX : (0 : E3_FIX) ∈ interior bipyramidSet_FIX := by
  refine mem_interior.mpr ⟨ball 0 (1 / 4), fun p hp => ?_, isOpen_ball, mem_ball_self (by norm_num)⟩
  rw [mem_ball, dist_zero_right] at hp
  rw [bipyramidSet_FIX, mem_ofPred_eq, pzCLM_apply_FIX]
  have h0 := abs_coord_le_norm_FIX p 0
  have h1 := abs_coord_le_norm_FIX p 1
  have h2 := abs_coord_le_norm_FIX p 2
  have hg : triGauge_FIX (proj12_FIX p) ≤ |coord_FIX p 0| + |coord_FIX p 1| := by
    unfold triGauge_FIX
    simp only [proj12_FIX]
    refine max_le (max_le ?_ ?_) ?_
    · linarith [neg_le_abs (coord_FIX p 0), abs_nonneg (coord_FIX p 1)]
    · linarith [neg_le_abs (coord_FIX p 1), abs_nonneg (coord_FIX p 0)]
    · linarith [le_abs_self (coord_FIX p 0), le_abs_self (coord_FIX p 1)]
  linarith

theorem isPLBall_bipyramid_space_FIX : IsPLBall 3 bipyramid_FIX.space := by
  rw [bipyramid_space_FIX]
  have h := isHPolytope_bipyramidSet_FIX.isPLBall ⟨0, zero_mem_interior_bipyramidSet_FIX⟩
  rwa [finrank_euclideanSpace_fin] at h

theorem bipyramid_manifold_FIX : IsCombinatorialManifoldWithBoundary 3 bipyramid_FIX := by
  have : Finite bipyramid_FIX.faces := bipyramid_faces_finite_FIX.to_subtype
  have hball := isPLBall_bipyramid_space_FIX
  let _ : DecidableEq E3_FIX := fun a b => Classical.propDecidable (a = b)
  intro v hv
  exact isPLSphere_or_isPLBall_geometricLink_of_isPLBall bipyramid_FIX (n := 2) hball hv


/-! ## `h` 与像集 `W = {‖π q‖ + |q₂| ≤ 1}` -/

/-- 平坦标准盘。 -/
def flatDisk_FIX : C(closedDisk, E3_FIX) :=
  ⟨fun z => flatCLM_FIX z, flatCLM_FIX.continuous.comp continuous_subtype_val⟩

/-- `h(p) = f(α(π p)) + p₂ e₃`。 -/
def bipyramidRealization_FIX (p : E3_FIX) : E3_FIX :=
  diskExtension flatDisk_FIX (radialGrid_FIX (proj12_FIX p)) + pzCLM_FIX p • mk3_FIX 0 0 1

theorem mk3_add_smul_FIX (a b c : ℝ) : mk3_FIX a b 0 + c • mk3_FIX 0 0 1 = mk3_FIX a b c := by
  ext i
  fin_cases i <;> simp [mk3_FIX]

theorem diskExtension_flat_FIX {w : ℂ} (hw : ‖w‖ ≤ 1) :
    diskExtension flatDisk_FIX w = flatCLM_FIX w := by
  have := diskExtension_coe flatDisk_FIX ⟨w, by rwa [mem_closedBall, dist_zero_right]⟩
  simpa [flatDisk_FIX] using this

theorem realization_eq_FIX {p : E3_FIX} (hp : p ∈ bipyramidSet_FIX) :
    bipyramidRealization_FIX p = mk3_FIX (radialGrid_FIX (proj12_FIX p)).re
      (radialGrid_FIX (proj12_FIX p)).im (pzCLM_FIX p) := by
  have hp' := hp
  rw [bipyramidSet_FIX, mem_ofPred_eq] at hp'
  have hn : ‖radialGrid_FIX (proj12_FIX p)‖ ≤ 1 := by
    rw [norm_radialGrid_FIX]
    linarith [abs_nonneg (pzCLM_FIX p)]
  rw [bipyramidRealization_FIX, diskExtension_flat_FIX hn, flat_eq_mk3_FIX, mk3_add_smul_FIX]

/-- 像集 `W`。 -/
def realizationImage_FIX : Set E3_FIX := {q | ‖proj12_FIX q‖ + |pzCLM_FIX q| ≤ 1}

theorem proj12_eq_FIX (q : E3_FIX) : proj12_FIX q = ⟨coord_FIX q 0, coord_FIX q 1⟩ := rfl

theorem realization_image_FIX :
    bipyramidRealization_FIX '' bipyramid_FIX.space = realizationImage_FIX := by
  rw [bipyramid_space_FIX]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := hp
    rw [bipyramidSet_FIX, mem_ofPred_eq] at hp'
    rw [realizationImage_FIX, mem_ofPred_eq, realization_eq_FIX hp, proj12_mk3_FIX, pz_mk3_FIX]
    have : ‖(⟨(radialGrid_FIX (proj12_FIX p)).re, (radialGrid_FIX (proj12_FIX p)).im⟩ : ℂ)‖ =
        triGauge_FIX (proj12_FIX p) := by
      rw [← norm_radialGrid_FIX]
    rw [this]
    exact hp'
  · intro hq
    rw [realizationImage_FIX, mem_ofPred_eq] at hq
    have hu : proj12_FIX q ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]
      linarith [abs_nonneg (pzCLM_FIX q)]
    obtain ⟨z₀, hz₀, hαz⟩ := radialGrid_surjOn_FIX hu
    rw [mem_ofPred_eq] at hz₀
    have hpmem : mk3_FIX z₀.re z₀.im (pzCLM_FIX q) ∈ bipyramidSet_FIX := by
      rw [bipyramidSet_FIX, mem_ofPred_eq, proj12_mk3_FIX, pz_mk3_FIX]
      have : (⟨z₀.re, z₀.im⟩ : ℂ) = z₀ := rfl
      rw [this, ← norm_radialGrid_FIX, hαz]
      exact hq
    refine ⟨_, hpmem, ?_⟩
    rw [realization_eq_FIX hpmem, proj12_mk3_FIX, pz_mk3_FIX]
    have : (⟨z₀.re, z₀.im⟩ : ℂ) = z₀ := rfl
    rw [this, hαz]
    exact (mk3_coord_FIX q).symm

theorem realization_injOn_FIX : InjOn bipyramidRealization_FIX bipyramid_FIX.space := by
  rw [bipyramid_space_FIX]
  intro p hp q hq hpq
  rw [realization_eq_FIX hp, realization_eq_FIX hq] at hpq
  have h := congrArg coord_FIX hpq
  rw [coord_mk3_FIX, coord_mk3_FIX] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  have hα : radialGrid_FIX (proj12_FIX p) = radialGrid_FIX (proj12_FIX q) := Complex.ext h0 h1
  have hmem : ∀ r : E3_FIX, r ∈ bipyramidSet_FIX → proj12_FIX r ∈ {z : ℂ | triGauge_FIX z ≤ 1} := by
    intro r hr
    rw [bipyramidSet_FIX, mem_ofPred_eq] at hr
    rw [mem_ofPred_eq]
    linarith [abs_nonneg (pzCLM_FIX r)]
  have hπ : proj12_FIX p = proj12_FIX q := radialGrid_injective_FIX hα
  rw [mk3_coord_FIX p, mk3_coord_FIX q]
  have e0 : coord_FIX p 0 = coord_FIX q 0 := congrArg Complex.re hπ
  have e1 : coord_FIX p 1 = coord_FIX q 1 := congrArg Complex.im hπ
  have e2 : coord_FIX p 2 = coord_FIX q 2 := h2
  rw [e0, e1, e2]


theorem continuous_coord_FIX (i : Fin 3) : Continuous fun p : E3_FIX => coord_FIX p i :=
  (continuous_apply i).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous

theorem continuous_proj12_FIX : Continuous proj12_FIX := by
  have : proj12_FIX =
      fun q => ((coord_FIX q 0 : ℝ) : ℂ) + ((coord_FIX q 1 : ℝ) : ℂ) * Complex.I := by
    funext q
    refine Complex.ext ?_ ?_ <;> simp [proj12_FIX]
  rw [this]
  exact (Complex.continuous_ofReal.comp (continuous_coord_FIX 0)).add
    ((Complex.continuous_ofReal.comp (continuous_coord_FIX 1)).mul continuous_const)

theorem continuous_realization_FIX : Continuous bipyramidRealization_FIX := by
  unfold bipyramidRealization_FIX
  exact ((flatDisk_FIX.continuous.comp diskRetraction_lipschitz.continuous).comp
    (radialGrid_continuous_FIX.comp continuous_proj12_FIX)).add
    (pzCLM_FIX.continuous.smul continuous_const)

theorem continuous_realizationGauge_FIX :
    Continuous fun q : E3_FIX => ‖proj12_FIX q‖ + |pzCLM_FIX q| :=
  (continuous_proj12_FIX.norm).add pzCLM_FIX.continuous.abs

theorem flat_mem_interior_FIX {z : ℂ} (hz : ‖z‖ < 1) :
    flatCLM_FIX z ∈ interior realizationImage_FIX := by
  refine mem_interior.mpr ⟨{q : E3_FIX | ‖proj12_FIX q‖ + |pzCLM_FIX q| < 1},
    fun q hq => by
      rw [realizationImage_FIX, mem_ofPred_eq]
      exact le_of_lt hq,
    isOpen_lt continuous_realizationGauge_FIX continuous_const, ?_⟩
  rw [mem_ofPred_eq, proj12_flat_FIX, pz_flat_FIX, abs_zero, add_zero]
  exact hz

theorem flat_mem_frontier_FIX {w : ℂ} (hw : ‖w‖ = 1) :
    flatCLM_FIX w ∈ frontier realizationImage_FIX := by
  refine mem_frontier_sublevel_FIX (F := fun q : E3_FIX => ‖proj12_FIX q‖ + |pzCLM_FIX q|)
    continuous_realizationGauge_FIX (fun t q ht => ?_) ?_
  · simp only [proj12_smul_FIX, map_smul, smul_eq_mul, norm_smul, abs_mul, Real.norm_eq_abs,
      abs_of_nonneg ht]
    ring
  · simp only [proj12_flat_FIX, pz_flat_FIX, abs_zero, add_zero]
    exact hw


end DifferentialGeometry.Geometry
