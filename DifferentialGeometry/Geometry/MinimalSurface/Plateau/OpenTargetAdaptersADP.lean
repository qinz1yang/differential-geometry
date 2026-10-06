import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConvexContainerR6A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.NoTransverseTransportR15T
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Embedding.TransverseIntersectionLimit

/-!
# S-MY-ADAPT G1–G4（rev2 A-2）：三个 carrier 之间的 adapter 包

rev2 D-2′：原 ambient `(M_amb, g)`（`hcpt`、R6a）、`U = {ρ < a}` 的 `(U, G)`（R1–R5、终点）、
`K°`（R7–R14）三个 carrier 分开；之间只经显式 adapter，不经「沿 `q` 的 local metric clause」。
本文件的 `M`、`O` 都是**一般**的 `M` 与 `O : Opens M`：
* R6a carrier：`M := M_amb`；
* K° glue / R15T open-target：`M := ↥U`、`O := K° : Opens ↥U`（`U ↪ M_amb` 另走 G1 的 `val ⁻¹'` 搬运）。

* **G1** `convex_container_in_carrier_ADP`：R6a（`strictly_convex_container_R6A`）在**原 carrier 与
  原度量 `g`** 上生产 `K = connectedComponentIn {ρ ≤ −b} x₀`（保留 `IsCompact (closure {ρ < a})`），再加
  `K ⊆ {ρ < a}`（`K` 放进 `U`）与 `K ⊆ {ρ ≤ 0}`（`G = g.restrictOpen U` 在 `K` 上由 cutoff 定义逐点给，
  不是沿 `q` 的 local clause）。`U` 内的紧性由 `M_amb` 中紧 + `K ⊆ U` 给：
  `isCompact_preimage_val_of_subset_ADP`、`frontier_preimage_val_subset_ADP`、
  `preimage_val_interior_subset_ADP`；层严格凸条款的 transfer：`convex_layer_restrictOpen_ADP`
  （`hessFun_restrictOpen_of_contMDiff` + `hessFun_apply_congr_metric`）；
  打包 `convex_container_carrier_U_ADP`。
* **G2** `morrey_of_open_inclusion_one_sided_ADP`：`u` 是 `O`-Morrey（度量 `g.restrictOpen O`）、
  `q` 是 `M`-Morrey、`q` 的 lift `qO` 光滑到边界 ⇒ `ι ∘ u` 是 `M`-Morrey；**单侧比较**
  `A_M(ι∘u) = A_O(u) ≤ A_O(qO) = A_M(q) ≤ A_M(v)`，**不**把任意 Morrey 盘当 Lipschitz competitor
  （`qO` 是光滑到边界的 competitor，`SmoothDiskExtension.lipschitz` 给 Lipschitz）。
  反方向 `morrey_restrictOpen_of_range_ADP`：`M`-Morrey 且像在 `O` ⇒ `O`-Morrey（`O`-Lipschitz competitor
  经 `riemannianEDistOf_le_restrictOpen` 推成 `M`-Lipschitz）。
* **G3** `smoothDiskExtension_liftToOpen_ADP`：`SmoothDiskExtension v V` 且像在 `O` ⇒ lift
  `liftToOpen_AT v` 有 `SmoothDiskExtension`（`exists_open_corestriction`）；
  `smoothDiskExtension_trimmed_liftToOpen_ADP`：`q₂ = affineSubdisk q 0 r₂`（`r₂ < 1`）的 lift 到 `K°`。
* **G4** `noTransverse_open_inclusion_ADP`：`K° ↪ U` 的 tangent isomorphism
  （`mfderiv_subtypeVal_comp`）下
  `(dv_x, −dv_y)` 满射双向等价；谓词级 `noTransverse_pred_open_inclusion_ADP`；consumer
  `noTransverse_of_trimmed_open_ADP`：与 `noTransverse_of_trimmed_R15T` 串起来，`K°` 上 trimmed 盘的 K13 谓词 ⇒
  `U` 上原盘的 hNT 谓词。

不含新 Prop / structure；每个 theorem 的假设都被用到。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-! ## G3：`liftToOpen` 版 `SmoothDiskExtension` -/

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G3**：像在开集 `O` 内且有闭盘 smooth extension 的盘，lift 到 `O` 后仍有闭盘 smooth extension
（`V` 与原 `V₀` 在闭盘邻域上 `Subtype.val ∘ V = V₀`）。 -/
theorem smoothDiskExtension_liftToOpen_ADP {O : Opens M} {v : C(closedDisk, M)} {V₀ : ℂ → M}
    (hV : SmoothDiskExtension (E := E) v V₀) (hO : Set.range v ⊆ O) :
    ∃ V : ℂ → O, SmoothDiskExtension (E := E) (liftToOpen_AT v hO) V ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Subtype.val ∘ V) =ᶠ[𝓝 z] V₀ :=
  SmoothDiskExtension.exists_open_corestriction O (u := liftToOpen_AT v hO) (U := V₀) hV

/-- **G3**（trimmed 版）：`q` 在 `‖z‖ < 1` 内光滑、`q₂ := affineSubdisk q 0 r₂`（`0 ≤ r₂ < 1`）的像在
`O` 内 ⇒ `q₂` 的 lift 到 `O`（`K°`）有闭盘 smooth extension。 -/
theorem smoothDiskExtension_trimmed_liftToOpen_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) {O : Opens M} {r₂ : ℝ}
    (hr₀ : 0 ≤ r₂) (hr₁ : r₂ < 1) (hO : Set.range (affineSubdisk q 0 r₂) ⊆ O) :
    ∃ V : ℂ → O, SmoothDiskExtension (E := E) (liftToOpen_AT (affineSubdisk q 0 r₂) hO) V :=
  (smoothDiskExtension_liftToOpen_ADP
    (hq.smoothDiskExtension_affineSubdisk 0 r₂ hr₀ (by simpa using hr₁)) hO).imp
      fun _ h => h.1

/-! ## G2：`K°` glue（单侧比较） -/

section Glue

variable [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- 弱 Jordan trace 沿 `ι : O ↪ M` 反推：`ι ∘ q` 的 trace 类是 `ι ∘ Γ` ⇒ `q` 的 trace 类是 `Γ`
（`Subtype.val` 单射）。 -/
theorem diskWeakJordanTrace_of_comp_val_ADP {O : Opens M} {Γ : freeLoop O} {γ : freeLoop M}
    (hγγ : ∀ θ, (Γ θ : M) = γ θ) {q : C(closedDisk, O)}
    (hw : DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp q)) :
    DiskWeakJordanTrace Γ q := by
  obtain ⟨σ, hσ, htr⟩ := hw
  refine ⟨σ, hσ, ?_⟩
  ext θ
  have h := congrArg (fun f : freeLoop M => f θ) htr
  change (q (diskBoundary θ) : M) = γ (σ θ) at h
  change (q (diskBoundary θ) : M) = (Γ (σ θ) : M)
  rw [h, hγγ]

/-- **G2**（scratch `morrey_of_open_inclusion_one_sided_MYD3` 逐字形）：`u` 是 `O`-Morrey（度量
`g.restrictOpen O`），`q` 是 `M`-Morrey 且 `q` 在 `O` 中的 lift `qO` 光滑到边界（`O`-competitor）⇒
`ι ∘ u` 是 `M`-Morrey。单侧链 `A_M(ι∘u) = A_O(u) ≤ A_O(qO) = A_M(q) ≤ A_M(v)`；等面积留到唯一性之后；
**不**把任意 Morrey 盘当 `M`-Lipschitz competitor。 -/
theorem morrey_of_open_inclusion_one_sided_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (O : Opens M)
    {Γ : freeLoop O} {u : C(closedDisk, O)} (hu : IsMorreyDisk (g.restrictOpen O) Γ u)
    {qO : C(closedDisk, O)} {QO : ℂ → O} (hQO : SmoothDiskExtension (E := E) qO QO)
    (hqOΓ : DiskWeakJordanTrace Γ qO)
    (hq : IsMorreyDisk g ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp Γ)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp qO)) :
    IsMorreyDisk g ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp Γ)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp u) := by
  let ι : C(O, M) := ⟨Subtype.val, continuous_subtype_val⟩
  have harea : ∀ w : C(closedDisk, O),
      riemannianDiskArea (g.restrictOpen O) w = riemannianDiskArea g (ι.comp w) :=
    fun w => riemannianDiskArea_restrictOpen g O w
  refine isMorreyDisk_of_minimizesLipschitz g ?_ ?_ ?_ ?_ ?_ ?_
  · exact (diskSmoothInterior_open_inclusion_iff O u).mpr hu.smoothInterior
  · intro z hz
    exact (diskMapConformalAt_restrictOpen g O (diskExtension u) z).mp (hu.conformal z hz)
  · intro z hz
    have hc : ContinuousAt (diskExtension u) z :=
      (u.continuous.comp diskRetraction_lipschitz.continuous).continuousAt
    exact (diskMapTension_restrictOpen g O (diskExtension u) z hc).symm.trans
      (hu.harmonic z hz)
  · have h := hu.finiteEnergy
    have e : diskMapEnergyDensity (g.restrictOpen O) (diskExtension u) =
        diskMapEnergyDensity g (diskExtension (ι.comp u)) :=
      funext fun z => diskMapEnergyDensity_restrictOpen g O (diskExtension u) z
    rw [e] at h
    exact h
  · exact diskWeakJordanTrace_comp_val_AT (fun _ => rfl) hu.trace
  · intro v hv hvL
    calc riemannianDiskArea g (ι.comp u) = riemannianDiskArea (g.restrictOpen O) u :=
          (harea u).symm
      _ ≤ riemannianDiskArea (g.restrictOpen O) qO :=
          hu.minimizesLipschitz qO hqOΓ (hQO.lipschitz (g.restrictOpen O))
      _ = riemannianDiskArea g (ι.comp qO) := harea qO
      _ ≤ riemannianDiskArea g v := hq.minimizesLipschitz v hv hvL

/-- **G2′**（反方向）：`M`-Morrey 且像在开集 `O` ⇒ `O`-Morrey（lift，度量 `g.restrictOpen O`）。
`O`-Lipschitz competitor `v` 经 `riemannianEDistOf_le_restrictOpen` 推成 `M`-Lipschitz competitor。 -/
theorem morrey_restrictOpen_of_range_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (O : Opens M) {γ : freeLoop M} {Γ : freeLoop O}
    (hγγ : ∀ θ, (Γ θ : M) = γ θ) {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hqO : Set.range q ⊆ O) :
    IsMorreyDisk (g.restrictOpen O) Γ (liftToOpen_AT q hqO) := by
  let ι : C(O, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let u : C(closedDisk, O) := liftToOpen_AT q hqO
  have harea : ∀ w : C(closedDisk, O),
      riemannianDiskArea (g.restrictOpen O) w = riemannianDiskArea g (ι.comp w) :=
    fun w => riemannianDiskArea_restrictOpen g O w
  refine isMorreyDisk_of_minimizesLipschitz (g.restrictOpen O) ?_ ?_ ?_ ?_ ?_ ?_
  · exact (diskSmoothInterior_open_inclusion_iff O u).mp hq.smoothInterior
  · intro z hz
    exact (diskMapConformalAt_restrictOpen g O (diskExtension u) z).mpr (hq.conformal z hz)
  · intro z hz
    have hc : ContinuousAt (diskExtension u) z :=
      (u.continuous.comp diskRetraction_lipschitz.continuous).continuousAt
    exact (diskMapTension_restrictOpen g O (diskExtension u) z hc).trans (hq.harmonic z hz)
  · have h := hq.finiteEnergy
    have e : diskMapEnergyDensity g (diskExtension q) =
        diskMapEnergyDensity (g.restrictOpen O) (diskExtension u) :=
      funext fun z => (diskMapEnergyDensity_restrictOpen g O (diskExtension u) z).symm
    rw [e] at h
    exact h
  · exact diskWeakJordanTrace_liftToOpen_AT hγγ hq.trace hqO
  · intro v hv hvL
    have hvM : DiskWeakJordanTrace γ (ι.comp v) := diskWeakJordanTrace_comp_val_AT hγγ hv
    have hvLM : ∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g ((ι.comp v) z) ((ι.comp v) w) ≤ (L : ℝ≥0∞) * edist z w := by
      obtain ⟨L, hL⟩ := hvL
      exact ⟨L, fun z w =>
        (riemannianEDistOf_le_restrictOpen g O (v z) (v w)).trans (hL z w)⟩
    calc riemannianDiskArea (g.restrictOpen O) u = riemannianDiskArea g q := harea u
      _ ≤ riemannianDiskArea g (ι.comp v) := hq.minimizesLipschitz _ hvM hvLM
      _ = riemannianDiskArea (g.restrictOpen O) v := (harea v).symm

/-- **G2 consumer（G1′/G3 + G2 串起来）**：`q` 是 `M`-Morrey、像在 `O`（`K°`）、有闭盘 smooth extension
`Q`，`u` 是 `O`-Morrey（同 trace 类 `Γ`）⇒ `ι ∘ u` 是 `M`-Morrey。`qO := liftToOpen_AT q` 的 smooth
extension 由 G3 给，其 trace 类由 `diskWeakJordanTrace_of_comp_val_ADP` 给——即 R7 里 `uₙ` 经 `K° ↪ U`
（单侧比较，不把任意 `u` 当 Lipschitz competitor）回到 `U`-Morrey。 -/
theorem morrey_of_open_inclusion_of_smooth_morrey_ADP
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (O : Opens M) {γ : freeLoop M} {Γ : freeLoop O}
    (hγγ : ∀ θ, (Γ θ : M) = γ θ) {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q) (hqO : Set.range q ⊆ O)
    {u : C(closedDisk, O)} (hu : IsMorreyDisk (g.restrictOpen O) Γ u) :
    IsMorreyDisk g γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp u) := by
  obtain ⟨QO, hQO, -⟩ := smoothDiskExtension_liftToOpen_ADP hQ hqO
  have hγ : (⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp Γ = γ :=
    ContinuousMap.ext hγγ
  have hqΓ : DiskWeakJordanTrace Γ (liftToOpen_AT q hqO) :=
    diskWeakJordanTrace_of_comp_val_ADP hγγ hq.trace
  have h := morrey_of_open_inclusion_one_sided_ADP O hu hQO hqΓ (by rw [hγ]; exact hq)
  rwa [hγ] at h

end Glue

/-! ## G4：R15T open-target adapter -/

section NoTransverse

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G4**（scratch `noTransverse_open_inclusion_MYD3`）：`K° ↪ U`（这里 `O ↪ M`）的 tangent isomorphism 下，
`v : ℂ → O` 的 `(dv_x, −dv_y)` 在 `O` 中满射 ⇔ `ι ∘ v` 的在 `M` 中满射。`mfderiv_subtypeVal_comp`
对可微与不可微两种情形都成立，故不需要 `MDifferentiableAt` 假设（scratch 里的 `hvx hvy` 去掉）。 -/
theorem noTransverse_open_inclusion_ADP {O : Opens M} {v : ℂ → O} {x y : ℂ} :
    Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v y))) ↔
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) y))) := by
  have hx := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) O v x
  have hy := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) O v y
  have e : (fun z => (v z : M)) = Subtype.val ∘ v := rfl
  rw [e, hx, hy]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 单射性同样在 `O ↪ M` 下不变。 -/
theorem injective_mfderiv_open_inclusion_ADP {O : Opens M} {v : ℂ → O} {x : ℂ} :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v x) := by
  have hx := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) O v x
  have e : (fun z => (v z : M)) = Subtype.val ∘ v := rfl
  rw [e, hx]
  exact Iff.rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G4 谓词级**：K13 `hNoTransverse` 谓词（在 `S ⊆ ℂ` 上）沿 `O ↪ M` 双向传递。 -/
theorem noTransverse_pred_open_inclusion_ADP {O : Opens M} {v : ℂ → O} {S : Set ℂ} :
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → v x = v y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) v y)))) ↔
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → (v x : M) = (v y : M) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z => (v z : M)) y)))) := by
  constructor
  · intro h x hx y hy hxy hv hix hiy hsurj
    exact h x hx y hy hxy (Subtype.ext hv)
      ((injective_mfderiv_open_inclusion_ADP (O := O) (v := v) (x := x)).mp hix)
      ((injective_mfderiv_open_inclusion_ADP (O := O) (v := v) (x := y)).mp hiy)
      ((noTransverse_open_inclusion_ADP (O := O) (v := v) (x := x) (y := y)).mpr hsurj)
  · intro h x hx y hy hxy hv hix hiy hsurj
    exact h x hx y hy hxy (congrArg Subtype.val hv)
      ((injective_mfderiv_open_inclusion_ADP (O := O) (v := v) (x := x)).mpr hix)
      ((injective_mfderiv_open_inclusion_ADP (O := O) (v := v) (x := y)).mpr hiy)
      ((noTransverse_open_inclusion_ADP (O := O) (v := v) (x := x) (y := y)).mp hsurj)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G4 consumer**：`K°`（`O`）上 trimmed 盘 `qO`（`ι ∘ qO = affineSubdisk q 0 r`）的 K13 谓词（在
`ball 0 1` 上，目标 `O`）+ R1 collar ⇒ 原盘 `diskExtension q`（目标 `M = U`）上逐字的 K13 `hNoTransverse`。
即 `O ↪ M` adapter（G4）与 `noTransverse_of_trimmed_R15T` 串起来。 -/
theorem noTransverse_of_trimmed_open_ADP {q : C(closedDisk, M)} {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r) {O : Opens M} {qO : C(closedDisk, O)}
    (hqO : (⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp qO = affineSubdisk q 0 r)
    (hO : ∀ u ∈ Metric.ball (0 : ℂ) 1, ∀ v ∈ Metric.ball (0 : ℂ) 1,
      u ≠ v → diskExtension qO u = diskExtension qO v →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension qO) u) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension qO) v) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension qO) u).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension qO) v)))) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))) := by
  have hfun' : ∀ z, ((diskExtension qO z : O) : M) = diskExtension (affineSubdisk q 0 r) z :=
    fun z => by
      rw [← hqO]
      rfl
  have hfun : (fun z => ((diskExtension qO z : O) : M)) = diskExtension (affineSubdisk q 0 r) :=
    funext hfun'
  have h := (noTransverse_pred_open_inclusion_ADP (O := O) (v := diskExtension qO)
    (S := Metric.ball 0 1)).mp hO
  rw [hfun] at h
  refine noTransverse_of_trimmed_R15T hcol hr hρr ?_
  intro u hu v hv huv heq hiu hiv
  exact h u hu v hv huv ((hfun' u).trans (heq.trans (hfun' v).symm)) hiu hiv

/-- **G4 consumer（R8 + R15 + G4 + R15T 的终端接口，open-target 形）**：`K° = O` 上 trimmed 盘 `qO`
（`ι ∘ qO = affineSubdisk q 0 r`、闭盘 smooth extension）的 `diskExtension` 在 `ball 0 1` 上是 `O`-值单射
映射 `v n` 的 chartwise `C¹` 极限（MY-13 的 `hval / hchart / hder`，对 `O` 的每个 target chart）⇒ 原盘
`diskExtension q` 在 `M = U` 上逐字的 K13 `hNoTransverse`。同 target 版
`noTransverse_of_c1_limit_trimmed_R15T` 的 `K° ↪ U` 对应物（三个 carrier 分开）。 -/
theorem noTransverse_of_c1_limit_open_trimmed_ADP {q : C(closedDisk, M)} {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r) {O : Opens M} {qO : C(closedDisk, O)} {QO : ℂ → O}
    (hQO : SmoothDiskExtension (E := E) qO QO)
    (hqO : (⟨Subtype.val, continuous_subtype_val⟩ : C(O, M)).comp qO = affineSubdisk q 0 r)
    {v : ℕ → ℂ → O}
    (hv : ∀ᶠ n in atTop, MDifferentiableOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (v n) (Metric.ball (0 : ℂ) 1))
    (hinj : ∀ᶠ n in atTop, InjOn (v n) (Metric.ball (0 : ℂ) 1))
    (hval : ∀ p : O, ∀ x ∈ Metric.ball (0 : ℂ) 1,
      diskExtension qO x ∈ (extChartAt 𝓘(ℝ, E) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, E) p (v n x)) atTop
        (𝓝 (extChartAt 𝓘(ℝ, E) p (diskExtension qO x))))
    (hchart : ∀ p : O, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension qO ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      ∀ᶠ n in atTop, MapsTo (v n) K (extChartAt 𝓘(ℝ, E) p).source)
    (hder : ∀ p : O, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension qO ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (v n z)) x)
        (fun x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension qO z)) x) atTop K) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y))) := by
  have hf₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension qO) (Metric.ball (0 : ℂ) 1) :=
    (show ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension qO) (Metric.ball (0 : ℂ) 1) from
      hQO.smoothUpToBoundary.interior).of_le (by simp)
  refine noTransverse_of_trimmed_open_ADP hcol hr hρr hqO ?_
  intro u hu w hw huw heq _ _
  exact DifferentialGeometry.Topology.Manifold.not_surjective_coprod_mfderiv_of_injective_c1_limit
    Metric.isOpen_ball hv hf₀ hinj hval hchart hder hu hw huw heq

end NoTransverse

/-! ## G1：R6a carrier adapter -/

section Carrier

variable [T2Space M]

/-- **G1**（scratch `convex_container_in_carrier_MYD3` 逐字形）：R6a 在**原** carrier `M` 与**原**度量 `g`
上（`hcpt : IsCompact (closure {ρ < a})` 在此成立）造 `K = connectedComponentIn {ρ ≤ −b} x₀`，再加
`K ⊆ {ρ < a}`（`K` 放进 `U`）与 `K ⊆ {ρ ≤ 0}`（于是 `G = g.restrictOpen U` 在 `K` 上由 cutoff 定义逐点成立）。 -/
theorem convex_container_in_carrier_ADP (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {S : Set M} (hS : IsCompact S) (hSconn : IsPreconnected S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ (∀ x ∈ S, ρ x < -b - δ) ∧
      (∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v) ∧
      ∀ x₀ ∈ S, IsCompact (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
        S ⊆ interior (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
        frontier (connectedComponentIn {x | ρ x ≤ -b} x₀) ⊆ {x | ρ x = -b} ∧
        connectedComponentIn {x | ρ x ≤ -b} x₀ ⊆ {x | ρ x < a} ∧
        connectedComponentIn {x | ρ x ≤ -b} x₀ ⊆ {x | ρ x ≤ 0} := by
  obtain ⟨b, δ, hb, hδ, hSb, hlayer, hcomp⟩ :=
    strictly_convex_container_R6A g hρ ha hcpt hcvx hS hSconn hneg
  refine ⟨b, δ, hb, hδ, hSb, hlayer, fun x₀ hx₀ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hcomp x₀ hx₀
  have hsub : connectedComponentIn {x | ρ x ≤ -b} x₀ ⊆ {x | ρ x ≤ -b} :=
    connectedComponentIn_subset _ _
  refine ⟨h1, h2, h3, fun x hx => ?_, fun x hx => ?_⟩
  · have hx' : ρ x ≤ -b := hsub hx
    change ρ x < a
    linarith
  · have hx' : ρ x ≤ -b := hsub hx
    change ρ x ≤ 0
    linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- `K ⊆ U` 在 `M` 中紧 ⇒ `val ⁻¹' K` 在 `↥U` 中紧（`U` 内的紧性不靠 `closure {ρ < a}`）。 -/
theorem isCompact_preimage_val_of_subset_ADP {U : Opens M} {K : Set M} (hK : IsCompact K)
    (hKU : K ⊆ U) : IsCompact (Subtype.val ⁻¹' K : Set U) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
    Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)]
  exact hK

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- 边界在 `val` 下只会变小。 -/
theorem frontier_preimage_val_subset_ADP {U : Opens M} (K : Set M) :
    frontier (Subtype.val ⁻¹' K : Set U) ⊆ Subtype.val ⁻¹' frontier K :=
  continuous_subtype_val.frontier_preimage_subset K

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- 内部在 `val` 下只会变大。 -/
theorem preimage_val_interior_subset_ADP {U : Opens M} (K : Set M) :
    Subtype.val ⁻¹' interior K ⊆ interior (Subtype.val ⁻¹' K : Set U) :=
  preimage_interior_subset_interior_preimage continuous_subtype_val

/-- 层严格凸条款的 carrier transfer：`G = g.restrictOpen U` 在 `{ρ < d}` 上逐点成立 ⇒ `M` 里
`g` 的 `dρ ≠ 0` + 全 Hessian 正定传到 `U` 里 `G` 与 `ρ ∘ val`。
（`hessFun_apply_congr_metric` 换度量 + `hessFun_restrictOpen_of_contMDiff` 换 carrier。） -/
theorem convex_layer_restrictOpen_ADP (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : Opens M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {d : ℝ}
    (hG : ∀ x : U, ρ (x : M) < d → G.inner x = (g.restrictOpen U).inner x) {x : U}
    (hx : ρ (x : M) < d)
    (hlayer : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ (x : M) ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) (x : M), v ≠ 0 → 0 < hessFun g ρ (x : M) v v) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y : U => ρ (y : M)) x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 →
        0 < hessFun G (fun y : U => ρ (y : M)) x v v := by
  have hW : IsOpen {y : U | ρ (y : M) < d} :=
    isOpen_lt (hρ.continuous.comp continuous_subtype_val) continuous_const
  refine ⟨fun h0 => hlayer.1 ?_, fun v hv => ?_⟩
  · have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, ℝ)) x
      (hρ.mdifferentiable (by simp) (x : M))
      (hasMFDerivAt_subtype_val (I := 𝓘(ℝ, E)) U x).mdifferentiableAt
    rw [mfderiv_subtype_val] at hc
    have h0' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (ρ ∘ (Subtype.val : U → M)) x = 0 := h0
    rw [hc] at h0'
    exact h0'
  · rw [DifferentialGeometry.hessFun_apply_congr_metric (g.restrictOpen U) G hW hG
      (fun y : U => ρ (y : M)) hx v v,
      hessFun_restrictOpen_of_contMDiff g U ρ hρ x v v, mfderiv_subtype_val_apply]
    exact hlayer.2 v hv

/-- **G1 打包（三个 carrier 分开）**：`M` = 原 ambient carrier（`hcpt`、R6a、`g`）；`U = {ρ < a}`；
`G` 是 `U` 上的度量（canonical positive-domain metric），`hG` 是 `ρ ≤ 0` 处与 `g.restrictOpen U` 逐点相等
（树里 `canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY` 的形状，由 cutoff 定义而非沿 `q` 的 local
clause）。结论在 `↥U` 里：`val ⁻¹' K` 紧（由 `M` 中紧 + `K ⊆ U`）、`val ⁻¹' S ⊆ interior`、frontier ⊆
`{ρ = −b}`、`⊆ {ρ ≤ −b}`、`G = g.restrictOpen U` 在 `val ⁻¹' K` 上逐点成立，并且层 `[−b−δ, −b]` 对 `G` 与
`ρ ∘ val` 全 Hessian 严格凸 + `dρ ≠ 0`——正是 R6b 的 `hK`/`hconv` 与 R7-E 的 `hKρ`/`hfr` 的入口形（`M := ↥U`）。 -/
theorem convex_container_carrier_U_ADP (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {U : Opens M} (hU : (U : Set M) = {x | ρ x < a}) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (hG : ∀ x : U, ρ (x : M) ≤ 0 → G.inner x = (g.restrictOpen U).inner x)
    {S : Set M} (hS : IsCompact S) (hSconn : IsPreconnected S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ (∀ x ∈ S, ρ x < -b - δ) ∧
      (∀ x : U, -b - δ ≤ ρ (x : M) → ρ (x : M) ≤ -b →
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y : U => ρ (y : M)) x ≠ 0 ∧
          ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 →
            0 < hessFun G (fun y : U => ρ (y : M)) x v v) ∧
      ∀ x₀ ∈ S, IsCompact (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ : Set U) ∧
        (Subtype.val ⁻¹' S : Set U) ⊆
          interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ : Set U) ∧
        frontier (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ : Set U) ⊆
          {x : U | ρ (x : M) = -b} ∧
        (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ : Set U) ⊆
          {x : U | ρ (x : M) ≤ -b} ∧
        ∀ x ∈ (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ : Set U),
          G.inner x = (g.restrictOpen U).inner x := by
  obtain ⟨b, δ, hb, hδ, hSb, hlayer, hcomp⟩ :=
    convex_container_in_carrier_ADP g hρ ha hcpt hcvx hS hSconn hneg
  refine ⟨b, δ, hb, hδ, hSb, fun x h1 h2 => ?_, fun x₀ hx₀ => ?_⟩
  · exact convex_layer_restrictOpen_ADP g U G hρ (d := 0) (fun y hy => hG y hy.le)
      (by linarith) (hlayer _ h1 h2)
  · obtain ⟨hKc, hSK, hfr, hKa, hK0⟩ := hcomp x₀ hx₀
    have hKU : connectedComponentIn {x | ρ x ≤ -b} x₀ ⊆ U := by
      intro x hx
      rw [hU]
      exact hKa hx
    have hKb : connectedComponentIn {x | ρ x ≤ -b} x₀ ⊆ {x | ρ x ≤ -b} :=
      connectedComponentIn_subset _ _
    refine ⟨isCompact_preimage_val_of_subset_ADP hKc hKU,
      fun x hx => preimage_val_interior_subset_ADP _ (hSK hx),
      fun x hx => frontier_preimage_val_subset_ADP _ hx |> fun h => hfr h, fun x hx => hKb hx,
      fun x hx => hG x (hK0 hx)⟩

end Carrier

end DifferentialGeometry.Geometry
