import DifferentialGeometry.Geometry.Hyperbolic.Truncation.ProducerHG03

/-!
# HG03 派生项 G1a：depth tower（S-HG-DERIV G1，后缀 `_HGD`）

`HyperbolicTruncation` 结构**没有深度字段**：截断深度 = donor 的
`exists_hyperbolicTruncation_of_translation_lattices` 的参数 `R : D.centers → ℝ`。
本文件对给定 thick–thin 分解 `D`（与 O-HG-HG03 G1 `exists_truncation_of_thick_thin_HG03`
同一组前提）造 **depth tower**：取参考截断 `Tr₀`（`R ≡ 1`），对每个 `S ≥ 0` 用 `R ≡ 1 + S/2`
再调 donor，得 `Tr_S` 满足

  `(range Tr_S.inclusion)ᶜ = ⋃ i, Tr₀.cuspMap i '' {p | S < p.2.val 0}`。

证明：两侧都等于 `e '' ⋃ ξ, horoballCylinderMap ξ '' {q | 1 + S/2 < q.2.val}`；左边来自 donor 的
`range` 等式（`cylindricalCore` 取补），右边来自 donor 的 `cuspMap` 公式
`Tr₀.cuspMap i p = e (f (σ₀ i) (F₀ (σ₀ i) p.1, 1 + p.2/2))` 与 `F₀` 满射、`σ₀` 重索引。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Set MeasureTheory

namespace DifferentialGeometry.Geometry.Hyperbolic

open ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)
open GC.Endpoint

universe u

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

/-- `Diffeomorph` 的满射性；charted-space 实例取 implicit，以便直接复用 donor 输出类型里的实例。 -/
private theorem diffeomorph_surjective_HGD
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] {_ : ChartedSpace H M}
    {M' : Type*} [TopologicalSpace M'] {_ : ChartedSpace H' M'} {n : WithTop ℕ∞}
    (F : Diffeomorph I I' M M' n) : Function.Surjective F :=
  F.toEquiv.surjective

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

/-- depth tower（thick–thin 分解 `D` 显式）：存在参考截断 `Tr₀`，使得对每个 `S ≥ 0` 有截断
`Tr`，其核心的补 = `Tr₀` 的各 cusp 在深度 `> S` 的尾部之并。 -/
theorem exists_depth_tower_of_thick_thin_HGD (H : FiniteVolumeHyperbolicModel.{u})
    {Γ : Subgroup (PO 3 1)} [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper 3)] {r : ℝ}
    (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)
    (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (hper : ∀ ξ : D.centers, ∃ a : PO 3 1,
      (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ.val =
        MobiusBoundary.ptInfty ∧
      ∃ (Λ : Submodule ℤ (Horizontal 2)) (hΛ : DiscreteTopology Λ),
        letI := hΛ
        IsZLattice ℝ Λ ∧
          (endStabilizer (Nat.le_add_left 1 2) Γ {ξ.val}).map (MulAut.conj a).toMonoidHom =
            TranslationLattices.latticeGroup Λ) :
    ∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      (range Tr.inclusion)ᶜ =
        ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0} := by
  classical
  have hΓ : IsDiscrete (SetLike.coe Γ) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  choose a ha Λ hΛd hΛ hP using hper
  -- 尾部集合 `W R = e '' ⋃ ξ, f ξ '' {z > R}`
  obtain ⟨W, hW⟩ : ∃ W : ℝ → Set H.Carrier, ∀ R, W R =
      e '' ⋃ ξ : D.centers, D.horoballCylinderMap hΓ ξ '' {q | R < q.2.val} :=
    ⟨_, fun _ => rfl⟩
  -- donor 的 `range` 等式 ⇒ 核心的补 = 尾部集合
  have hcompl : ∀ (Tr : HyperbolicTruncation H) (R : ℝ),
      range Tr.inclusion = e '' DifferentialGeometry.Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) (fun _ => R) → (range Tr.inclusion)ᶜ = W R := by
    intro Tr R h
    rw [h, hW]
    unfold DifferentialGeometry.Topology.cylindricalCore
    rw [← e.image_compl, compl_compl]
  -- 参考截断（深度 `R ≡ 1`）
  obtain ⟨_, F₀, _, _, Tr₀, σ₀, _, _, _, hcusp₀, _, _⟩ :=
    D.exists_hyperbolicTruncation_of_translation_lattices H e he hmetric a ha Λ hP
      (fun _ => 1) (fun _ => one_pos)
  -- `Tr₀` 的 cusp 尾部 = `W (1 + S/2)`
  have hshift : ∀ S : ℝ, 0 ≤ S →
      (⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0}) = W (1 + S / 2) := by
    intro S hS
    ext x
    rw [hW]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨p, hp, rfl⟩ := hi
      refine ⟨D.horoballCylinderMap hΓ (σ₀ i)
        (F₀ (σ₀ i) p.1, ⟨1 + p.2.val 0 / 2, by
          have h0 : 0 ≤ p.2.val 0 := p.2.property
          exact add_nonneg zero_le_one (div_nonneg h0 two_pos.le)⟩),
        mem_iUnion.mpr ⟨σ₀ i, _, ?_, rfl⟩, (hcusp₀ i p).symm⟩
      have hp' : S < p.2.val 0 := hp
      change 1 + S / 2 < 1 + p.2.val 0 / 2
      linarith
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hy
      obtain ⟨⟨s, z⟩, hq, rfl⟩ := hξ
      change 1 + S / 2 < z.val at hq
      obtain ⟨i, rfl⟩ := σ₀.surjective ξ
      have hz : 0 ≤ 2 * (z.val - 1) := by linarith
      have hlift : (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (2 * (z.val - 1))).val 0 = 2 * (z.val - 1) := max_eq_left hz
      obtain ⟨u, hu⟩ := diffeomorph_surjective_HGD (F₀ (σ₀ i)) s
      refine mem_iUnion.mpr ⟨i, (u,
        DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (2 * (z.val - 1))),
        ?_, ?_⟩
      · change S < (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (2 * (z.val - 1))).val 0
        rw [hlift]
        linarith
      · rw [hcusp₀]
        congr 2
        refine Prod.ext hu (Subtype.ext ?_)
        change 1 + (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
          (2 * (z.val - 1))).val 0 / 2 = z.val
        rw [hlift]
        ring
  refine ⟨Tr₀, fun S hS => ?_⟩
  obtain ⟨_, _, _, _, Tr, _, _, _, hrange, _, _, _⟩ :=
    D.exists_hyperbolicTruncation_of_translation_lattices H e he hmetric a ha Λ hP
      (fun _ => 1 + S / 2) (fun _ => by linarith)
  exact ⟨Tr, (hcompl Tr (1 + S / 2) hrange).trans (hshift S hS).symm⟩

end DifferentialGeometry.Geometry.Hyperbolic
