import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarInfimumR7E
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetAdaptersADP

/-!
# O-MY-R7E consumer（`_HC2` 实例，`M := ↥U`、`K° : Opens ↥U`）：R7-E 在 R6a carrier 上落地

入口与 S-MY-ADAPT G1 `convex_container_carrier_U_ADP` 的输出逐字对齐：原 ambient `M`（`hcpt`、`hcvx` 在此）、
`U = {ρ < a}`、`U` 上度量 `G`（`= g.restrictOpen U` on `{ρ ≤ 0}`）、紧预连通 `S ⊆ {ρ < 0}`；ADP 给
`b δ > 0`、`S ⊆ {ρ < −b−δ}`、`U` 上整层 `[−b−δ, −b]` 的 `dρ ≠ 0` + `Hess_G ρ > 0`、
`Kc = val ⁻¹' connectedComponentIn {ρ ≤ −b} x₀`（紧、`frontier ⊆ {ρ = −b}`、`⊆ {ρ ≤ −b}`）。

* `exists_confined_morrey_disk_HC_R7E`（G5 实例）：`K° := interior Kc`，对 `K°` 里的光滑嵌入 `Γ`
  （`ρ ∘ Γ < −b−δ`、有光滑 spanning disk）∃ `u`，`IsMorreyDisk (G.restrictOpen K°) Γ u ∧ ρ ∘ u ≤ −b−δ`；
* `inf_K_eq_inf_Ko_HC_R7E`（G4 实例）：`Kc`- 与 `K°`-competitor 的 infimum 相等（`Kc` 的连通闭性质由
  component 给出）；
* `example`：MYD3 `exists_confined_morrey_disks_MYD3` 的入口形（度量序列 `Gn`、`∀ᶠ n`）去掉三点归一后由
  G5 逐 `n` 给出——偏差：collar 条款在整层（不只 `x ∈ K`）、`{ρ ≤ −b+η}` 紧代替 `IsCompact K`（ADP 都给）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [SecondCountableTopology M]

omit [T3Space M] [SecondCountableTopology M] in
/-- `Kc = val ⁻¹' (component)` 的「连通闭」性质。 -/
theorem preimage_component_isPreconnected_subset_R7E {U : Opens M} {ρ : M → ℝ} {c : ℝ} (x₀ : M)
    (S : Set U) (hS : IsPreconnected S) (hSρ : S ⊆ {x : U | ρ x ≤ c})
    (hSK : (S ∩ Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ c} x₀).Nonempty) :
    S ⊆ Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ c} x₀ := by
  obtain ⟨y, hyS, hyK⟩ := hSK
  have himg : IsPreconnected (Subtype.val '' S) := hS.image _ continuous_subtype_val.continuousOn
  have hsub : Subtype.val '' S ⊆ {x | ρ x ≤ c} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hSρ hz
  have hcomp := himg.subset_connectedComponentIn (x := (y : M)) ⟨y, hyS, rfl⟩ hsub
  rw [← connectedComponentIn_eq hyK] at hcomp
  exact fun z hz => hcomp ⟨z, hz, rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [SecondCountableTopology M] in
/-- ADP carrier 上 `{ρ ≤ 0}` 在 `↥U` 里紧（`U = {ρ < a}`、`closure {ρ < a}` 紧）。 -/
theorem isCompact_sublevel_zero_U_R7E {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {a : ℝ} (ha : 0 < a) (hcpt : IsCompact (closure {x | ρ x < a})) {U : Opens M}
    (hU : (U : Set M) = {x | ρ x < a}) :
    IsCompact {x : U | ρ (x : M) ≤ 0} := by
  have hK : IsCompact {x : M | ρ x ≤ 0} :=
    hcpt.of_isClosed_subset (isClosed_le hρ.continuous continuous_const)
      (fun x hx => subset_closure (show ρ x < a by
        have : ρ x ≤ 0 := hx
        linarith))
  exact isCompact_preimage_val_of_subset_ADP hK (fun x hx => by
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hU]
    change ρ x < a
    have : ρ x ≤ 0 := hx
    linarith)

/-- **G5 实例**（`M := ↥U`）：见文件头。 -/
theorem exists_confined_morrey_disk_HC_R7E (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {a : ℝ} (ha : 0 < a) (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {U : Opens M} (hU : (U : Set M) = {x | ρ x < a}) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (hG : ∀ x : U, ρ (x : M) ≤ 0 → G.inner x = (g.restrictOpen U).inner x)
    {S : Set M} (hS : IsCompact S) (hSconn : IsPreconnected S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ (∀ x ∈ S, ρ x < -b - δ) ∧ ∀ x₀ ∈ S,
      ∃ Ko : Opens U,
        (Ko : Set U) = interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
        (Subtype.val ⁻¹' S : Set U) ⊆ Ko ∧
        ∀ (Γ : freeLoop Ko), IsSmoothEmbeddedLoop (E := E) Γ →
          (∀ θ, ρ ((Γ θ : U) : M) < -b - δ) →
          (∃ v : C(closedDisk, Ko), DiskSmoothUpToBoundary (E := E) v ∧ diskTrace v = Γ) →
          ∃ u : C(closedDisk, Ko), IsMorreyDisk (G.restrictOpen Ko) Γ u ∧
            ∀ z, ρ ((u z : U) : M) ≤ -b - δ := by
  obtain ⟨b, δ, hb, hδ, hSb, hcoll, hcomp⟩ :=
    convex_container_carrier_U_ADP g hρ ha hcpt hcvx hU G hG hS hSconn hneg
  refine ⟨b, δ, hb, hδ, hSb, fun x₀ hx₀ => ?_⟩
  obtain ⟨hKc, hSK, hfr, hKρ, -⟩ := hcomp x₀ hx₀
  refine ⟨⟨interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀),
    isOpen_interior⟩, rfl, hSK, fun Γ hΓ hΓρ hspan => ?_⟩
  have hcpt' : IsCompact {x : U | ρ (x : M) ≤ -b + b} := by
    have h := isCompact_sublevel_zero_U_R7E hρ ha hcpt hU
    simpa only [neg_add_cancel] using h
  exact exists_confined_morrey_disk_R7E hdim G (hρ.comp contMDiff_subtype_val) hδ hb hcpt'
    hcoll hKc.isClosed hKρ hfr _ rfl hΓ hΓρ hspan

/-- **G4 实例**（`M := ↥U`）：`Kc`- 与 `K°`-competitor 的 infimum 相等。 -/
theorem inf_K_eq_inf_Ko_HC_R7E (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {U : Opens M} (hU : (U : Set M) = {x | ρ x < a}) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (hG : ∀ x : U, ρ (x : M) ≤ 0 → G.inner x = (g.restrictOpen U).inner x)
    {S : Set M} (hS : IsCompact S) (hSconn : IsPreconnected S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ ∀ x₀ ∈ S,
      ∀ (Γ : freeLoop (⟨interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀),
          isOpen_interior⟩ : Opens U)), (∀ θ, ρ ((Γ θ : U) : M) < -b - δ) →
      let Ko : Opens U := ⟨interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀),
        isOpen_interior⟩
      let ι : C(Ko, U) := ⟨Subtype.val, continuous_subtype_val⟩
      sInf ((fun v : C(closedDisk, U) => riemannianDiskArea G v) ''
          {v | Set.range v ⊆ Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b} x₀ ∧
            DiskWeakJordanTrace (ι.comp Γ) v ∧
            ∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w}) =
        sInf ((fun w : C(closedDisk, Ko) => riemannianDiskArea (G.restrictOpen Ko) w) ''
          {w | DiskWeakJordanTrace Γ w ∧ ∃ L : ℝ≥0, ∀ z z',
            riemannianEDistOf (G.restrictOpen Ko) (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z'}) := by
  obtain ⟨b, δ, hb, hδ, -, hcoll, hcomp⟩ :=
    convex_container_carrier_U_ADP g hρ ha hcpt hcvx hU G hG hS hSconn hneg
  refine ⟨b, δ, hb, hδ, fun x₀ hx₀ Γ hΓρ => ?_⟩
  obtain ⟨hKc, -, hfr, hKρ, -⟩ := hcomp x₀ hx₀
  have hcpt' : IsCompact {x : U | ρ (x : M) ≤ -b + b} := by
    have h := isCompact_sublevel_zero_U_R7E hρ ha hcpt hU
    simpa only [neg_add_cancel] using h
  exact (inf_K_eq_inf_Ko_R7E G (hρ.comp contMDiff_subtype_val) hδ hb hcpt' hcoll hKc.isClosed hKρ
    hfr (fun S hSc hSρ hSK => preimage_component_isPreconnected_subset_R7E x₀ S hSc hSρ hSK)
    _ rfl hΓρ).2.2

/-- MYD3 `exists_confined_morrey_disks_MYD3` 入口形（度量序列、`∀ᶠ n`）去掉三点归一：由 G5 逐 `n` 给出。 -/
example (hdim : Module.finrank ℝ E = 3)
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hcpt : IsCompact {x | ρ x ≤ -b + η})
    {K : Set M} (hKcl : IsClosed K) (hKρ : K ⊆ {x | ρ x ≤ -b})
    (hfr : frontier K ⊆ {x | ρ x = -b})
    (hconvn : ∀ᶠ n in atTop, ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun (Gn n) ρ x v v)
    (Ko : Opens M) (hKo : (Ko : Set M) = interior K)
    {Γ : freeLoop Ko} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hΓρ : ∀ θ, ρ (Γ θ : M) < -b - δ)
    (hspan : ∃ v : C(closedDisk, Ko), DiskSmoothUpToBoundary (E := E) v ∧ diskTrace v = Γ) :
    ∀ᶠ n in atTop, ∃ u : C(closedDisk, Ko), IsMorreyDisk ((Gn n).restrictOpen Ko) Γ u ∧
      ∀ z, ρ (u z : M) ≤ -b - δ :=
  hconvn.mono fun n hn =>
    exists_confined_morrey_disk_R7E hdim (Gn n) hρ hδ hη hcpt hn hKcl hKρ hfr Ko hKo hΓ hΓρ hspan

end GC.LongTime.CuspP1
