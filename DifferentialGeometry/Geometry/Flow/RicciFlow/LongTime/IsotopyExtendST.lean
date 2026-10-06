import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryStaticSG

/-!
# 沿开嵌入把紧支撑 isotopy 用恒等延拓到整个流形（lane S-A14-STATIC，G6a）

`ι : D → X` 是开嵌入（`IsOpenEmbedding` + `IsLocalDiffeomorph`），`Φ : ℝ → ℝ → D → D` 是 joint
`C^∞` 的 isotopy（`Φ s s = id`、cocycle），且在紧集 `C ⊆ D` 外是恒等。`isotopyExtend_ST ι Φ s t`
在 `range ι` 上是 `ι ∘ Φ s t ∘ ι⁻¹`，在 `range ι` 外是恒等；它仍然 joint `C^∞`
（`contMDiff_isotopyExtend_ST`：`range ι` 与 `(ι '' C)ᶜ` 两个开集上分别光滑），
并且每个 `(s, t)` 给出 `X` 的 diffeo（`isotopyDiffeo_ST`）。S-A14-SURGERY 的 CP1-D5 isotopy
住在 survivor domain `D` 上（stage 的开子集）；这个延拓把它变成全 stage 上的 diffeo 族，
供 G6 的 window 数据使用。
-/

set_option autoImplicit false
noncomputable section

open Set Function Manifold DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.LongTime

section Extend

variable {X D : Type*}

/-- 沿单射 `ι : D → X` 把 `D` 上的 `Φ s t` 用恒等延拓到 `X`。 -/
def isotopyExtend_ST (ι : D → X) (Φ : ℝ → ℝ → D → D) (s t : ℝ) : X → X :=
  Function.extend ι (fun w => ι (Φ s t w)) id

variable {ι : D → X} {Φ : ℝ → ℝ → D → D}

/-- 延拓在 `range ι` 上就是 `ι ∘ Φ s t`。 -/
theorem isotopyExtend_apply_ST (hι : Injective ι) (s t : ℝ) (w : D) :
    isotopyExtend_ST ι Φ s t (ι w) = ι (Φ s t w) :=
  hι.extend_apply _ _ w

/-- 延拓在 `range ι` 外是恒等。 -/
theorem isotopyExtend_of_not_range_ST (s t : ℝ) {x : X} (hx : x ∉ range ι) :
    isotopyExtend_ST ι Φ s t x = x := by
  have h : ¬ ∃ w, ι w = x := fun ⟨w, hw⟩ => hx ⟨w, hw⟩
  simp only [isotopyExtend_ST, Function.extend_apply' _ _ _ h, id]

/-- `Φ` 在 `C` 外恒等 ⇒ 延拓在 `ι '' C` 外恒等。 -/
theorem isotopyExtend_of_not_mem_image_ST (hι : Injective ι) {C : Set D}
    (hsupp : ∀ s t y, y ∉ C → Φ s t y = y) (s t : ℝ) {x : X} (hx : x ∉ ι '' C) :
    isotopyExtend_ST ι Φ s t x = x := by
  by_cases hr : x ∈ range ι
  · obtain ⟨w, rfl⟩ := hr
    rw [isotopyExtend_apply_ST hι, hsupp s t w (fun hw => hx ⟨w, hw, rfl⟩)]
  · exact isotopyExtend_of_not_range_ST s t hr

/-- `Φ s s = id` ⇒ 延拓的 `(s, s)` 切片是恒等。 -/
theorem isotopyExtend_self_ST (hι : Injective ι) (hself : ∀ s y, Φ s s y = y) (s : ℝ)
    (x : X) : isotopyExtend_ST ι Φ s s x = x := by
  by_cases hr : x ∈ range ι
  · obtain ⟨w, rfl⟩ := hr
    rw [isotopyExtend_apply_ST hι, hself]
  · exact isotopyExtend_of_not_range_ST s s hr

/-- cocycle 性质传给延拓。 -/
theorem isotopyExtend_comp_ST (hι : Injective ι)
    (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) (s t u : ℝ) (x : X) :
    isotopyExtend_ST ι Φ t u (isotopyExtend_ST ι Φ s t x) = isotopyExtend_ST ι Φ s u x := by
  by_cases hr : x ∈ range ι
  · obtain ⟨w, rfl⟩ := hr
    rw [isotopyExtend_apply_ST hι, isotopyExtend_apply_ST hι, isotopyExtend_apply_ST hι, hcoc]
  · rw [isotopyExtend_of_not_range_ST s t hr, isotopyExtend_of_not_range_ST t u hr,
      isotopyExtend_of_not_range_ST s u hr]

end Extend

section ExtendSmooth

variable {X D : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [T2Space X] [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D]
  {ι : D → X} {Φ : ℝ → ℝ → D → D}

/-- 紧支撑的 joint `C^∞` isotopy 沿 open embedding 的恒等延拓仍 joint `C^∞`。 -/
theorem contMDiff_isotopyExtend_ST [Nonempty D] (hι : Topology.IsOpenEmbedding ι)
    (hιld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ι)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × D => Φ q.1.1 q.1.2 q.2))
    {C : Set D} (hC : IsCompact C) (hsupp : ∀ s t y, y ∉ C → Φ s t y = y) :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × X => isotopyExtend_ST ι Φ q.1.1 q.1.2 q.2) := by
  obtain ⟨ψ, hψs, -, hψ⟩ := GC.LongTime.CuspP1.exists_partialDiffeomorph_of_open_embeddings_SG
    ι (id : D → D) hιld (Diffeomorph.refl (𝓡 3) D ∞).isLocalDiffeomorph hι.injective
    Function.injective_id
  refine contMDiff_of_locally_contMDiffOn fun q => ?_
  by_cases hq : q.2 ∈ range ι
  · refine ⟨univ ×ˢ range ι, isOpen_univ.prod hι.isOpen_range, ⟨mem_univ _, hq⟩, ?_⟩
    have hg : ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × X => ι (Φ q.1.1 q.1.2 (ψ q.2))) (univ ×ˢ range ι) := by
      refine hιld.contMDiff.comp_contMDiffOn ?_
      refine hsm.comp_contMDiffOn (f := fun q : (ℝ × ℝ) × X => (q.1, ψ q.2)) ?_
      have h1 : ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : (ℝ × ℝ) × X => q.1) (univ ×ˢ range ι) := contMDiff_fst.contMDiffOn
      have h2 : ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : (ℝ × ℝ) × X => ψ q.2) (univ ×ˢ range ι) := by
        refine ψ.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn ?_
        rintro q ⟨-, hq2⟩
        rw [hψs]
        exact hq2
      exact h1.prodMk h2
    refine hg.congr ?_
    rintro q ⟨-, w, hw⟩
    rw [← hw, hψ w, isotopyExtend_apply_ST hι.injective]
    rfl
  · have hcl : IsClosed (ι '' C) := (hC.image hιld.contMDiff.continuous).isClosed
    refine ⟨univ ×ˢ (ι '' C)ᶜ, isOpen_univ.prod hcl.isOpen_compl,
      ⟨mem_univ _, fun h => hq (image_subset_range _ _ h)⟩, ?_⟩
    refine contMDiff_snd.contMDiffOn.congr ?_
    rintro q ⟨-, hx⟩
    exact isotopyExtend_of_not_mem_image_ST hι.injective hsupp _ _ hx

/-- 延拓后的 isotopy 在时刻 `(s, t)` 的 diffeo（逆是 `(t, s)` 切片）。 -/
def isotopyDiffeo_ST (hι : Function.Injective ι) (hself : ∀ s y, Φ s s y = y)
    (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × X => isotopyExtend_ST ι Φ q.1.1 q.1.2 q.2)) (s t : ℝ) :
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X where
  toFun := isotopyExtend_ST ι Φ s t
  invFun := isotopyExtend_ST ι Φ t s
  left_inv x := by rw [isotopyExtend_comp_ST hι hcoc, isotopyExtend_self_ST hι hself]
  right_inv x := by rw [isotopyExtend_comp_ST hι hcoc, isotopyExtend_self_ST hι hself]
  contMDiff_toFun :=
    hsm.comp (f := fun y => ((s, t), y)) (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    hsm.comp (f := fun y => ((t, s), y)) (contMDiff_const.prodMk contMDiff_id)

end ExtendSmooth

end GC.LongTime
