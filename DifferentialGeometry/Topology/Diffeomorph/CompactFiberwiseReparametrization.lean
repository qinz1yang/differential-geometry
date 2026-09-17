import DifferentialGeometry.Topology.Diffeomorph.FiberwiseReparametrization
import DifferentialGeometry.Topology.Diffeomorph.CompactLocalIsotopy

open Set
open scoped ContDiff Manifold

namespace Diffeomorph

section Fiberwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_compact_isotopy_eqOn_fiberwiseStraightening
    (A : (E × ℝ) ≃ₘ[ℝ] (F × ℝ)) (hA : ∀ z, (A z).2 = z.2) (c : ℝ)
    {K : Set (F × ℝ)} (hK : IsCompact K) {J : Set ℝ} (hJ : IsOpen J)
    (hKJ : K ⊆ univ ×ˢ J) :
    ∃ V : Set (F × ℝ), IsOpen V ∧ K ⊆ V ∧
      ∃ T : ℝ → ((F × ℝ) ≃ₘ[ℝ] (F × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (F × ℝ) => T z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (F × ℝ) => (T z.1).symm z.2) ∧
        T 0 = Diffeomorph.refl 𝓘(ℝ, F × ℝ) (F × ℝ) ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, EqOn (T t) (A.fiberwiseStraightening hA c t) V) ∧
        (∀ t x, (T t x).2 = x.2) ∧
        (∀ t x, T t (x, c) = (x, c)) ∧
        ∃ S : Set (F × ℝ), IsCompact S ∧ S ⊆ univ ×ˢ J ∧ ∀ t,
          EqOn (T t) id Sᶜ ∧ EqOn (T t).symm id Sᶜ := by
  obtain ⟨V, hV, hKV, T, hT, hTi, hT0, htrack, hfixed, hheight, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_preserving_linear_map
      (A.fiberwiseStraightening hA c) (A.contDiff_fiberwiseStraightening hA c)
      (A.contDiff_fiberwiseStraightening_symm hA c)
      (ContinuousLinearMap.snd ℝ F ℝ) (fun _ _ => rfl)
      (A := univ ×ˢ {c}) (fun t x hx => by
        have hc : x.2 = c := hx.2
        rw [← Prod.eta x, hc]
        exact A.fiberwiseStraightening_apply_base hA c t x.1)
      hK (isOpen_univ.prod hJ) (fun _ _ x hx => ⟨mem_univ _, (hKJ hx).2⟩)
  refine ⟨V, hV, hKV, T, hT, hTi, hT0, ?_, hheight, ?_, hsupport⟩
  · intro t ht x hx
    simpa only [A.fiberwiseStraightening_zero, Diffeomorph.coe_refl, id_eq] using
      htrack t ht x hx
  · intro t x
    exact (hfixed t).1 ⟨mem_univ x, rfl⟩

end Fiberwise

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

theorem exists_compact_isotopy_straightening_graph
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    (c : ℝ) (hfix : ∀ x, A (x, c) = (x, c))
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F)
    {k : X → F} {x : X → E} {g : X → ℝ} {U K : Set X}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcoord : ContinuousOn (fun z => (x z, g z)) U)
    (hgraph : ∀ z ∈ U, k z = Ψ (A (x z, g z)))
    {J : Set ℝ} (hJ : IsOpen J) (hKJ : ∀ z ∈ K, g z ∈ J) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ T : ℝ → (F ≃ₘ[ℝ] F),
        ContDiff ℝ ∞ (fun z : ℝ × F => T z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × F => (T z.1).symm z.2) ∧
        T 0 = Diffeomorph.refl 𝓘(ℝ, F) F ∞ ∧
        (∀ t y, (Ψ.symm (T t y)).2 = (Ψ.symm y).2) ∧
        (∀ t y, T t (Ψ (y, c)) = Ψ (y, c)) ∧
        (∀ z ∈ V, T 1 (k z) = Ψ (x z, g z)) ∧
        ∃ S : Set F, IsCompact S ∧ S ⊆ Ψ '' (univ ×ˢ J) ∧ ∀ t,
          EqOn (T t) id Sᶜ ∧ EqOn (T t).symm id Sᶜ := by
  let q := fun z => A (x z, g z)
  have hq : ContinuousOn q U := A.continuous.comp_continuousOn hcoord
  obtain ⟨W, hW, hKW, R, hR, hRi, hR0, htrack, hheight, hbase, S, hS, hSJ, hsupport⟩ :=
    A.exists_compact_isotopy_eqOn_fiberwiseStraightening hA c
      (hK.image_of_continuousOn (hq.mono hKU)) hJ (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨mem_univ _, by change (A (x z, g z)).2 ∈ J; rw [hA]; exact hKJ z hz⟩)
  let T := fun t => Ψ.symm.trans ((R t).trans Ψ)
  have hi : ContDiff ℝ ∞ (fun z : ℝ × F => (z.1, Ψ.symm z.2)) :=
    contDiff_fst.prodMk (Ψ.symm.contDiff.comp contDiff_snd)
  refine ⟨U ∩ q ⁻¹' W, hq.isOpen_inter_preimage hU hW,
    fun z hz => ⟨hKU hz, hKW ⟨z, hz, rfl⟩⟩, inter_subset_left,
    T, ?_, ?_, ?_, ?_, ?_, ?_, Ψ '' S, hS.image Ψ.continuous, image_mono hSJ, ?_⟩
  · change ContDiff ℝ ∞ (fun z : ℝ × F => Ψ (R z.1 (Ψ.symm z.2)))
    have hj := hR.comp hi
    exact Ψ.contDiff.comp hj
  · change ContDiff ℝ ∞ (fun z : ℝ × F => Ψ ((R z.1).symm (Ψ.symm z.2)))
    have hj := hRi.comp hi
    exact Ψ.contDiff.comp hj
  · apply Diffeomorph.ext
    intro y
    change Ψ (R 0 (Ψ.symm y)) = y
    rw [hR0]
    exact Ψ.apply_symm_apply y
  · intro t y
    change (Ψ.symm (Ψ (R t (Ψ.symm y)))).2 = _
    rw [Ψ.symm_apply_apply, hheight]
  · intro t y
    change Ψ (R t (Ψ.symm (Ψ (y, c)))) = Ψ (y, c)
    rw [Ψ.symm_apply_apply, hbase]
  · intro z hz
    change Ψ (R 1 (Ψ.symm (k z))) = _
    rw [hgraph z hz.1, Ψ.symm_apply_apply,
      htrack 1 (by norm_num) hz.2, A.fiberwiseStraightening_one_apply_comp, hfix]
  · intro t
    have hnot {y : F} (hy : y ∉ Ψ '' S) : Ψ.symm y ∉ S :=
      fun h => hy ⟨Ψ.symm y, h, Ψ.apply_symm_apply y⟩
    constructor
    · intro y hy
      change Ψ (R t (Ψ.symm y)) = y
      rw [(hsupport t).1 (hnot hy)]
      exact Ψ.apply_symm_apply y
    · intro y hy
      change Ψ ((R t).symm (Ψ.symm y)) = y
      rw [(hsupport t).2 (hnot hy)]
      exact Ψ.apply_symm_apply y

end Diffeomorph
