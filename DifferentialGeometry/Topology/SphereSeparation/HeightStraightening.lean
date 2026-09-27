import DifferentialGeometry.Topology.SphereSeparation.HeightLevel
import DifferentialGeometry.Topology.Morse.CriticalSet
import DifferentialGeometry.Topology.Morse.RegularLevel.Family
import DifferentialGeometry.Topology.Embedding.LevelFamily
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit

open Set Manifold
open scoped ContDiff
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def heightLift (t : ℝ) (z : EuclideanThree) : EuclideanThree :=
  (EuclideanSpace.equivProdLast 2).symm ((EuclideanSpace.equivProdLast 2 z).1, t)

@[simp] theorem heightLift_height (t : ℝ) (z : EuclideanThree) : heightLift t z 2 = t := by
  exact EuclideanSpace.equivProdLast_symm_last 2 _

theorem preimage_height_section_eq {S : Set EuclideanThree} {D : EuclideanThree → EuclideanThree}
    (hD : Function.Injective D) (hheight : ∀ z, D z 2 = z 2) {a t : ℝ}
    (hlevels : D '' (heightLift t '' (S ∩ {z | z 2 = a})) = S ∩ {z | z 2 = t}) :
    (fun y : EuclideanSpace ℝ (Fin 2) => D ((EuclideanSpace.equivProdLast 2).symm (y, t))) ⁻¹' S =
      (fun y : EuclideanSpace ℝ (Fin 2) => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' S := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  ext y
  constructor
  · intro hy
    have hheight : D (L.symm (y, t)) 2 = t :=
      (hheight _).trans (EuclideanSpace.equivProdLast_symm_last 2 _)
    obtain ⟨w, ⟨z, hz, rfl⟩, hze⟩ := hlevels.symm.subset ⟨hy, hheight⟩
    have heq := hD hze
    change L.symm ((L z).1, t) = L.symm (y, t) at heq
    have hxy : (L z).1 = y := congrArg Prod.fst (L.symm.injective heq)
    have hzL : L.symm (y, a) = z := by
      apply L.injective
      rw [L.apply_symm_apply]
      exact Prod.ext hxy.symm hz.2.symm
    change L.symm (y, a) ∈ S
    rw [hzL]
    exact hz.1
  · intro hy
    have hlift : heightLift t (L.symm (y, a)) = L.symm (y, t) := by
      change L.symm ((L (L.symm (y, a))).1, t) = _
      rw [L.apply_symm_apply]
    have h := hlevels.subset
      ⟨L.symm (y, t), ⟨L.symm (y, a),
        ⟨hy, EuclideanSpace.equivProdLast_symm_last 2 _⟩, hlift⟩, rfl⟩
    exact h.1

theorem exists_height_preserving_regular_slab_diffeomorph_at
    {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {a b c : ℝ} (hc : c ∈ Icc a b)
    (hr : ∀ x, e x 2 ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (habW : Icc a b ⊆ W) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      (∀ z, D z 2 = z 2) ∧
      (∀ z, z 2 = c → D z = z) ∧
      (∀ t ∈ Icc a b,
        D '' (heightLift t '' (range e ∩ {z | z 2 = c})) = range e ∩ {z | z 2 = t}) ∧
      ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ EqOn D id Kᶜ := by
  let f : SphereTwo → ℝ := fun x => e x 2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hcompact : IsCompact (f ⁻¹' Icc a b) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  obtain ⟨Φ, hΦ, _, _, htrans⟩ := exists_diffeomorph_family_level_transport hf hcompact hr
  have hra (x : SphereTwo) (hx : e x 2 = a) := hr x (by rw [hx]; exact ⟨le_rfl, hc.1.trans hc.2⟩)
  obtain ⟨C, S, hinc, _, _, _⟩ := exists_height_level_manifold he a hra
  let _ := C
  let _ := S
  let L := {x : SphereTwo // f x = a}
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let H : ℝ × L → EuclideanSpace ℝ (Fin 2) × ℝ := fun p => A (e (Φ p.1 p.2.val))
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MorseModel 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ H :=
    A.contDiff.contMDiff.comp (he.contMDiff.comp (hΦ.comp (contMDiff_fst.prodMk
      (hinc.contMDiff.comp contMDiff_snd))))
  have hHemb (t : ℝ) : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun x => H (t, x)) := by
    have hD :=
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (Φ t).isLocalDiffeomorph (Φ t).injective
    exact (he.comp (hD.comp hinc (by simp)) (by simp)).continuousLinearEquiv_comp A
  have hheight (t : ℝ) (ht : t ∈ Icc a b) (x : L) : (H (t, x)).2 = t :=
    (htrans t ht).1.subset ⟨x.val, x.property, rfl⟩
  obtain ⟨P, hPheight, hPc, hPe, _, K, hK, hKW, hPfix⟩ :=
    exists_height_preserving_diffeomorph_of_level_family_at hc hH.contMDiffOn
      (fun t _ => hHemb t) hheight
      isOpen_univ (subset_univ _) hW habW
  let D := A.toDiffeomorph.trans (P.trans A.symm.toDiffeomorph)
  have hDe (t : ℝ) (ht : t ∈ Icc a b) (x : L) :
      D (heightLift t (e (Φ c x.val))) = e (Φ t x.val) := by
    change A.symm (P (A (A.symm ((A (e (Φ c x.val))).1, t)))) = _
    rw [A.apply_symm_apply]
    change A.symm (P ((H (c, x)).1, t)) = _
    rw [hPe t ht x]
    exact A.symm_apply_apply _
  refine ⟨D, ?_, ?_, ?_, A.symm '' K, hK.image A.symm.continuous, ?_, ?_⟩
  · intro z
    change (A.symm (P (A z))) 2 = z 2
    exact (EuclideanSpace.equivProdLast_symm_last 2 _).trans (hPheight (A z))
  · intro z hz
    change A.symm (P (A z)) = z
    have hAz : A z = ((A z).1, c) := Prod.ext rfl hz
    rw [hAz, hPc, ← hAz, A.symm_apply_apply]
  · intro t ht
    ext z
    constructor
    · rintro ⟨_, ⟨_, ⟨⟨x, rfl⟩, hx⟩, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := (htrans c hc).1.symm.subset hx
      rw [← hyx, hDe t ht ⟨y, hy⟩]
      exact ⟨mem_range_self _, hheight t ht ⟨y, hy⟩⟩
    · rintro ⟨⟨x, rfl⟩, hx⟩
      obtain ⟨y, hy, hyx⟩ := (htrans t ht).1.symm.subset hx
      refine ⟨heightLift t (e (Φ c y)),
        ⟨e (Φ c y), ⟨mem_range_self _, hheight c hc ⟨y, hy⟩⟩, rfl⟩, ?_⟩
      rw [hDe t ht ⟨y, hy⟩, hyx]
  · rintro z ⟨y, hy, rfl⟩
    change ((EuclideanSpace.equivProdLast 2).symm y) (Fin.last 2) ∈ W
    rw [EuclideanSpace.equivProdLast_symm_last]
    exact (hKW hy).2
  · intro z hz
    have hzK : A z ∉ K := fun h => hz ⟨A z, h, A.symm_apply_apply z⟩
    change A.symm (P (A z)) = z
    rw [hPfix hzK]
    exact A.symm_apply_apply z

theorem exists_height_preserving_regular_slab_diffeomorph
    {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {a b : ℝ} (hab : a ≤ b)
    (hr : ∀ x, e x 2 ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (habW : Icc a b ⊆ W) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      (∀ z, D z 2 = z 2) ∧
      (∀ z, z 2 = a → D z = z) ∧
      (∀ t ∈ Icc a b,
        D '' (heightLift t '' (range e ∩ {z | z 2 = a})) = range e ∩ {z | z 2 = t}) ∧
      ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ EqOn D id Kᶜ := by
  exact exists_height_preserving_regular_slab_diffeomorph_at he ⟨le_rfl, hab⟩ hr hW habW

theorem exists_height_preserving_regular_level_diffeomorph
    {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {a : ℝ}
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
        (∀ z, D z 2 = z 2) ∧
        (∀ z, z 2 = a → D z = z) ∧
        (∀ t ∈ Icc (a - ε) (a + ε),
          D '' (heightLift t '' (range e ∩ {z | z 2 = a})) = range e ∩ {z | z 2 = t}) ∧
        ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ EqOn D id Kᶜ := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hregular := isOpen_setOf_regular_values (𝓡 2) (hf.of_le (by simp))
    hf.continuous.isClosedMap
  have hnear : IsOpen (W ∩ {t : ℝ | ∀ x, e x 2 = t →
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}) := hW.inter hregular
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hnear a ⟨haW, hr⟩
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hsub : Icc (a - ε) (a + ε) ⊆
      W ∩ {t : ℝ | ∀ x, e x 2 = t → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x} := by
    intro t ht
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound : |t - a| ≤ ε := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hbound.trans_lt (half_lt_self hδ)
  have hreg (x : SphereTwo) (hx : e x 2 ∈ Icc (a - ε) (a + ε)) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0 := (hsub hx).2 x rfl
  have ha : a ∈ Icc (a - ε) (a + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨D, hD, hDa, hlevels, K, hK, hKW, hfix⟩ :=
    exists_height_preserving_regular_slab_diffeomorph_at he ha hreg hW
      (fun _ ht => (hsub ht).1)
  exact ⟨ε, hε, fun _ ht => (hsub ht).1, D, hD, hDa, hlevels, K, hK, hKW, hfix⟩

end DifferentialGeometry.Topology.SphereSeparation
