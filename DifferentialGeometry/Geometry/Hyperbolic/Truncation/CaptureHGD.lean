import DifferentialGeometry.Geometry.Hyperbolic.Truncation.DepthTowerGlobalHGD
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

/-!
# HG03 派生项 G2：任意紧集 ⊆ 某截断核心（S-HG-DERIV G2，后缀 `_HGD`）

* `exists_truncation_core_superset_HGD`：`K ⊆ H.Carrier` 紧 ⇒ `∃ Tr, K ⊆ range Tr.inclusion`。
  证明：`Tr₀.cuspMap i` 是 closed embedding（`cuspMap_isClosedEmbedding`）⇒ `K` 的原像紧 ⇒
  深度有界 `b i`；取 `S = ∑ |b i|`，depth tower 在 `S` 的截断核心覆盖 `K`。
* `exists_truncation_dist_HGD`：G1 的度量形式——核心之外的点到任意 `o` 的距离 `> R`
  （闭球紧 = Hopf–Rinow `closedEBall_isCompact`，取 `K` = 闭球）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open Set MeasureTheory Filter GC.Endpoint

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- **G2**：任意紧集 `K ⊆ H.Carrier` 含于某截断的核心。 -/
theorem exists_truncation_core_superset_HGD (H : FiniteVolumeHyperbolicModel.{u})
    {K : Set H.Carrier} (hK : IsCompact K) :
    ∃ Tr : HyperbolicTruncation H, K ⊆ range Tr.inclusion := by
  obtain ⟨Tr₀, hT⟩ := exists_depth_tower_HGD H
  have hdepth : ∀ i : Fin Tr₀.count, ∃ b : ℝ,
      ∀ p ∈ Tr₀.cuspMap i ⁻¹' K, p.2.val 0 ≤ b := by
    intro i
    have hc : IsCompact (Tr₀.cuspMap i ⁻¹' K) :=
      (Tr₀.cuspMap_isClosedEmbedding i).isCompact_preimage hK
    have hcont : Continuous (fun p : CuspHalfSpace => p.2.val 0) :=
      (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_subtype_val.comp continuous_snd)
    obtain ⟨b, hb⟩ := (hc.image hcont).bddAbove
    exact ⟨b, fun p hp => hb ⟨p, hp, rfl⟩⟩
  choose b hb using hdepth
  set S : ℝ := ∑ i, |b i| with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (b i)
  have hbS : ∀ i, b i ≤ S := fun i =>
    (le_abs_self (b i)).trans (Finset.single_le_sum (f := fun i => |b i|)
      (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i))
  obtain ⟨Tr, hTr⟩ := hT S hS
  refine ⟨Tr, fun x hx => ?_⟩
  by_contra hxn
  have hxT : x ∈ (range Tr.inclusion)ᶜ := hxn
  rw [hTr] at hxT
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxT
  obtain ⟨p, hp, rfl⟩ := hi
  have hpK : p ∈ Tr₀.cuspMap i ⁻¹' K := hx
  have := hb i p hpK
  have hp' : S < p.2.val 0 := hp
  linarith [hbS i]

/-- **G1（度量深度）**：对任意 `o` 与 `R`，存在截断使核心之外的点到 `o` 的距离 `> R`
（核心包含开球 `B(o, R)`；闭球紧，Hopf–Rinow）。 -/
theorem exists_truncation_dist_HGD (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
    (R : ℝ) :
    ∃ Tr : HyperbolicTruncation H, ∀ x, x ∉ range Tr.inclusion →
      ENNReal.ofReal R < riemannianEDistOf H.metric o x := by
  obtain ⟨Tr, hTr⟩ := exists_truncation_core_superset_HGD H
    (H.complete.closedEBall_isCompact o R)
  exact ⟨Tr, fun x hx => lt_of_not_ge fun hle => hx (hTr hle)⟩

/-- consumer：ch12 D-R3-20 的“任意紧集捕获”形状。 -/
example : type_of% @exists_truncation_core_superset_HGD.{u} =
    (∀ (H : FiniteVolumeHyperbolicModel.{u}) {K : Set H.Carrier}, IsCompact K →
      ∃ Tr : HyperbolicTruncation H, K ⊆ range Tr.inclusion) := rfl

end DifferentialGeometry.Geometry.Hyperbolic
