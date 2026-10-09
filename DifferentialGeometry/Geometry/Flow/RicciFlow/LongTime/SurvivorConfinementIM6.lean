import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

/-!
# c5：survivor confinement（O-W-IMS06 G2，后缀 `_IM6`）

IMS06′ + IMS07 左侧的拓扑一步（REMAINING-OBLIGATIONS c5）：pre-surgery 时刻 `s` 的盘 `v`
（Route W 里是 `_HC2` 盘 `ι ∘ q_s`）不碰任何 cutting neck 的中间球面 `Σ_b = {x ∈ N_b | Z_b x = 0}`
（S-W-NECK G4 `not_mem_middle_sphere_of_stability_bound_NK` 的结论形状），且 `∂v = γ_s` 在存活侧，
则 `range v ⊆ K₀`（存活侧 ⊆ `K₀ = ι_s '' interior KD`，SURGERY 的 window 像的紧部分）。

拓扑输入（R3，S-A14-SURGERY 认领，到前为显式前提）：`M_s ∖ ⋃_b Σ_b ⊆ U ∪ V`，`U`、`V` 开且不交，
`U ⊆ K₀`，`γ_s ⊆ U`。证明只用 `closedDisk` 连通（`ContractibleSpace`）与
`IsPreconnected.subset_left_of_subset_union`。

* `range_subset_of_separation_IM6`：抽象分离引理（`S` 任意）。
* **`confined_in_survivor_of_neck_exclusion_IM6`**（G2 主定理）：neck 族 `(N b, Z b)` 版 +
  `DiskWeakJordanTrace γ v`。
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry

namespace GC.LongTime

variable {X : Type*} [TopologicalSpace X]

/-- 抽象分离：连通盘的像不碰 `S`、`Sᶜ ⊆ U ∪ V`（`U`、`V` 开且不交）、像与 `U` 相交 ⇒ 像 `⊆ U`。 -/
theorem range_subset_of_separation_IM6 (v : C(closedDisk, X)) {S U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hsep : ∀ x, x ∉ S → x ∈ U ∪ V)
    (hS : ∀ ζ, v ζ ∉ S) {ζ₀ : closedDisk} (hζ₀ : v ζ₀ ∈ U) : range v ⊆ U := by
  refine (isPreconnected_range v.continuous).subset_left_of_subset_union hU hV hUV ?_
    ⟨v ζ₀, ⟨ζ₀, rfl⟩, hζ₀⟩
  rintro _ ⟨ζ, rfl⟩
  exact hsep _ (hS ζ)

/-- 弱 Jordan 迹 `γ` 落在 `U` 里 ⇒ 盘的某个边界点落在 `U` 里。 -/
theorem exists_boundary_mem_of_weakTrace_IM6 {γ : freeLoop X} {v : C(closedDisk, X)}
    (htr : DiskWeakJordanTrace γ v) {U : Set X} (hγ : ∀ θ, γ θ ∈ U) :
    ∃ ζ₀ : closedDisk, v ζ₀ ∈ U := by
  obtain ⟨σ, -, hσ⟩ := htr
  refine ⟨diskBoundary 0, ?_⟩
  have h : diskTrace v 0 = γ (σ 0) := congrArg (fun c : freeLoop X => c 0) hσ
  change diskTrace v 0 ∈ U
  rw [h]
  exact hγ _

/-- **c5（G2 主定理）**：盘 `v` 不碰 neck 族的中间球面 `{x ∈ N b | Z b x = 0}`
（`hNK`：S-W-NECK G4 的结论，逐 neck）、弱 Jordan 迹 `γ ⊆ U`、分离事实 `hsep`（R3：去掉所有中间球面后
落在 `U ∪ V`，`U`、`V` 开不交）、`U ⊆ K₀` ⇒ `range v ⊆ K₀`。 -/
theorem confined_in_survivor_of_neck_exclusion_IM6 {ι : Type*} (v : C(closedDisk, X))
    (N : ι → Set X) (Z : ι → X → ℝ) {U V K₀ : Set X} {γ : freeLoop X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ U ∪ V) (hUK : U ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ U) (htr : DiskWeakJordanTrace γ v)
    (hNK : ∀ b, ∀ ζ : closedDisk, ¬ (v ζ ∈ N b ∧ Z b (v ζ) = 0)) : range v ⊆ K₀ := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_boundary_mem_of_weakTrace_IM6 htr hγ
  have hS : ∀ ζ, v ζ ∉ {x | ∃ b, x ∈ N b ∧ Z b x = 0} := by
    rintro ζ ⟨b, hb⟩
    exact hNK b ζ hb
  have hsep' : ∀ x, x ∉ {x | ∃ b, x ∈ N b ∧ Z b x = 0} → x ∈ U ∪ V := fun x hx =>
    hsep x fun b hb => hx ⟨b, hb⟩
  exact (range_subset_of_separation_IM6 v hU hV hUV hsep' hS hζ₀).trans hUK

/-- consumer：单个 neck（`ι = Unit`）且 `V = ∅`（中间球面外全在存活侧）时退化为
"不碰中间球面 ⇒ 落在 `U`"。 -/
example (v : C(closedDisk, X)) (N : Set X) (Z : X → ℝ) {U : Set X} {γ : freeLoop X}
    (hU : IsOpen U) (hsep : ∀ x, ¬ (x ∈ N ∧ Z x = 0) → x ∈ U) (hγ : ∀ θ, γ θ ∈ U)
    (htr : DiskWeakJordanTrace γ v) (hNK : ∀ ζ : closedDisk, ¬ (v ζ ∈ N ∧ Z (v ζ) = 0)) :
    range v ⊆ U :=
  confined_in_survivor_of_neck_exclusion_IM6 (ι := Unit) v (fun _ => N) (fun _ => Z)
    (V := ∅) hU isOpen_empty (disjoint_empty _)
    (fun x hx => Or.inl (hsep x (hx ()))) le_rfl hγ htr (fun _ => hNK)

end GC.LongTime
