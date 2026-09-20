/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.FiberPreservingGerm
import DifferentialGeometry.Topology.Manifold.FiberAffineInterpolation
import DifferentialGeometry.Topology.Manifold.RegularSurfaceChart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.IsotopyExtension

/-! Relative straightening of transitions between charts of a regular level function. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}

theorem exists_level_preserving_isotopy_straightening_transition
    (c d : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞) {f : M → ℝ}
    (hc : ∀ x ∈ c.source, (c x).im = f x)
    (hd : ∀ x ∈ d.source, (d x).im = f x)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source)
    {O : Set M} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ A : ℂ ≃L[ℝ] ℂ,
      (A : ℂ →L[ℝ] ℂ) = fderiv ℝ (c.symm.trans d) (c x) ∧
      (∀ z, (A z).im = z.im) ∧
      ∃ Φ : ℝ → Diffeomorph I I M M ∞,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ p y, f (Φ p y) = f y) ∧ (∀ p, Φ p x = x) ∧
        (∀ᶠ z in 𝓝 (c x), Φ 1 (d.symm (A (z - c x) + d x)) = c.symm z) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ c.source ∩ d.source ∩ O ∧
          ∀ p y, y ∉ K → Φ p y = y ∧ (Φ p).symm y = y := by
  let φ := c.symm.trans d
  have hl : c.symm (c x) = x := c.left_inv hxc
  have hsrc : c x ∈ φ.source := by
    refine ⟨c.map_source hxc, ?_⟩
    change c.symm (c x) ∈ d.source
    rw [hl]
    exact hxd
  have hpoint : φ (c x) = d x := by change d (c.symm (c x)) = d x; rw [hl]
  have hfiber (z : ℂ) (hz : z ∈ φ.source) : (φ z).im = z.im := by
    change z ∈ c.target ∧ c.symm z ∈ d.source at hz
    change (d (c.symm z)).im = z.im
    rw [hd (c.symm z) hz.2, ← hc (c.symm z) (c.map_target hz.1)]
    have hr : c (c.symm z) = z := c.right_inv hz.1
    rw [hr]
  let A : ℂ ≃L[ℝ] ℂ :=
    (φ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ hsrc).mfderivToContinuousLinearEquiv (by simp)
  have hAe : (A : ℂ →L[ℝ] ℂ) = fderiv ℝ φ (c x) := mfderiv_eq_fderiv
  have hA : HasFDerivAt φ (A : ℂ →L[ℝ] ℂ) (c x) := by
    rw [hAe]
    have hsm := φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)
    exact (hsm.differentiableAt (by simp)).hasFDerivAt
  let W := d.target ∩ d.symm ⁻¹' (c.source ∩ O)
  have hW : IsOpen W :=
    d.symm.contMDiffOn.continuousOn.isOpen_inter_preimage d.open_target (c.open_source.inter hO)
  have hW₀ : φ (c x) ∈ W := by
    rw [hpoint]
    have hr : d.symm (d x) = x := d.left_inv hxd
    refine ⟨d.map_source hxd, ?_⟩
    change d.symm (d x) ∈ c.source ∩ O
    rw [hr]
    exact ⟨hxc, hxO⟩
  obtain ⟨hAi, D, hD, hDi, hD0, hDe, hDpoint, hDlevel, K, hK, hKW, hDfix⟩ :=
    exists_compact_isotopy_straightening_fiber_germ φ.open_source hsrc
      φ.contMDiffOn.contDiffOn A hA
      (fun z hz => by rw [hfiber z hz, hfiber (c x) hsrc]; ring) hW hW₀
  have hDm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun z : ℝ × ℂ => D z.1 z.2) :=
    hD.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  have hDim : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun z : ℝ × ℂ => (D z.1).symm z.2) :=
    hDi.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  obtain ⟨Φ, hΦ, hΦi, hΦs, hΦe, hΦc, hΦ0, hΦK, hΦKs, hΦfix⟩ :=
    d.exists_isotopy_extension_of_isCompact D hDm hDim hK
      (fun z hz => (hKW hz).1) (fun p z hz => (hDfix p z hz).1)
  have hpreserve (p : ℝ) (y : M) : f (Φ p y) = f y := by
    by_cases hy : y ∈ d.source
    · have hym : Φ p y ∈ d.source := hΦs p ▸ mem_image_of_mem (Φ p) hy
      rw [← hd _ hym, ← hd _ hy, hΦc p y hy, hDlevel]
    · rw [(hΦfix p y (fun h => hy (hΦKs h))).1]
  refine ⟨A, hAe, hAi, Φ, hΦ, hΦi, hΦ0 0 hD0, hpreserve, ?_, ?_,
    d.symm '' K, hΦK, ?_, hΦfix⟩
  · intro p
    have hh := hΦe p (d x) (d.map_source hxd)
    have hr : d.symm (d x) = x := d.left_inv hxd
    have hp : D p (d x) = d x := hpoint ▸ hDpoint p
    rw [hr, hp, hr] at hh
    exact hh
  · have hn : ∀ᶠ z in 𝓝 (c x), A (z - c x) + d x ∈ d.target := by
      have ht : Continuous (fun z => A (z - c x) + d x) :=
        (A.continuous.comp (continuous_id.sub continuous_const)).add continuous_const
      have ht₀ : A (c x - c x) + d x ∈ d.target := by
        rw [sub_self, map_zero, zero_add]
        exact d.map_source hxd
      exact ht.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds ht₀)
    filter_upwards [hDe, hn, φ.open_source.mem_nhds hsrc] with z he hz hzφ
    rw [hpoint] at he
    rw [hΦe 1 _ hz, he]
    change d.symm (d (c.symm z)) = c.symm z
    exact d.left_inv hzφ.2
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨(hKW hz).2.1, d.map_target (hKW hz).1⟩, (hKW hz).2.2⟩


theorem exists_level_preserving_isotopy_in_coordinates
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hF : Module.finrank ℝ F = 2) (hG : Module.finrank ℝ G = 2)
    (c : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    (d : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hxc : x ∈ c.source) (hxd : x ∈ d.source)
    (hregular : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ (ℓ : F →L[ℝ] ℝ) (m : G →L[ℝ] ℝ)
      (r : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞)
      (s : PartialDiffeomorph 𝓘(ℝ, G) 𝓘(ℝ, ℂ) G ℂ ∞),
      let a := c.trans r
      let b := d.trans s
      x ∈ a.source ∧ x ∈ b.source ∧ a.source ⊆ c.source ∩ O ∧
        b.source ⊆ d.source ∩ O ∧
        (∀ y ∈ a.source, (a y).im = f y) ∧ (∀ y ∈ b.source, (b y).im = f y) ∧
        (∀ y, (a y).re = ℓ (c y - c x)) ∧ (∀ y, (b y).re = m (d y - d x)) ∧
        ∃ A : ℂ ≃L[ℝ] ℂ,
          (A : ℂ →L[ℝ] ℂ) = fderiv ℝ (a.symm.trans b) (a x) ∧
          (∀ z, (A z).im = z.im) ∧
          ∃ Φ : ℝ → Diffeomorph I I M M ∞,
            ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
            ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
            Φ 0 = Diffeomorph.refl I M ∞ ∧
            (∀ p y, f (Φ p y) = f y) ∧ (∀ p, Φ p x = x) ∧
            (∀ᶠ z in 𝓝 (a x), Φ 1 (b.symm (A (z - a x) + b x)) = a.symm z) ∧
            ∃ K : Set M, IsCompact K ∧ K ⊆ c.source ∩ d.source ∩ O ∧
              ∀ p y, y ∉ K → Φ p y = y ∧ (Φ p).symm y = y := by
  obtain ⟨ℓ, r, _, _, _, hrealc, _, hxa, haO, har⟩ :=
    exists_level_chart_in_coordinates hF c hf hxc hregular hO hxO
  obtain ⟨m, s, _, _, _, hreald, _, hxb, hbO, hbr⟩ :=
    exists_level_chart_in_coordinates hG d hf hxd hregular hO hxO
  obtain ⟨A, hA, hAi, Φ, hΦ, hΦi, hΦ0, hΦf, hΦx, hmatch, K, hK, hKO, hfix⟩ :=
    exists_level_preserving_isotopy_straightening_transition
      (c.trans r) (d.trans s) har hbr hxa hxb hO hxO
  exact ⟨ℓ, m, r, s, hxa, hxb, fun y hy => ⟨hy.1, haO hy⟩,
    fun y hy => ⟨hy.1, hbO hy⟩, har, hbr,
    fun y => hrealc (c y), fun y => hreald (d y),
    A, hA, hAi, Φ, hΦ, hΦi, hΦ0, hΦf, hΦx, hmatch, K, hK,
    fun y hy => ⟨⟨(hKO hy).1.1.1, (hKO hy).1.2.1⟩, (hKO hy).2⟩, hfix⟩

theorem exists_positive_level_transition
    (c d : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞) {f : M → ℝ}
    (hc : ∀ y ∈ c.source, (c y).im = f y)
    (hd : ∀ y ∈ d.source, (d y).im = f y)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source)
    {O : Set M} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ (a b k : ℝ) (R : ℂ ≃L[ℝ] ℂ), 0 < a ∧ (∀ z, (R z).im = z.im) ∧
      ∃ Φ : ℝ → Diffeomorph I I M M ∞,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ p y, f (Φ p y) = f y) ∧ (∀ p, Φ p x = x) ∧
        (∀ᶠ y in 𝓝 x, (Φ 1).symm y ∈ d.source ∧
          R (d ((Φ 1).symm y)) = ⟨a * (c y).re + b * (c y).im + k, (c y).im⟩) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ c.source ∩ d.source ∩ O ∧
          ∀ p y, y ∉ K → Φ p y = y ∧ (Φ p).symm y = y := by
  obtain ⟨A, _, hAi, Φ, hΦ, hΦi, hΦ0, hΦf, hΦx, hmatch, K, hK, hKO, hfix⟩ :=
    exists_level_preserving_isotopy_straightening_transition c d hc hd hxc hxd hO hxO
  obtain ⟨R, hRi, a, b, k, ha, hform⟩ :=
    exists_positive_fiber_affine_normalization A hAi ((hd x hxd).trans (hc x hxc).symm)
  have hn : ∀ᶠ z in 𝓝 (c x), A (z - c x) + d x ∈ d.target := by
    have ht : Continuous (fun z => A (z - c x) + d x) :=
      (A.continuous.comp (continuous_id.sub continuous_const)).add continuous_const
    have ht₀ : A (c x - c x) + d x ∈ d.target := by
      rw [sub_self, map_zero, zero_add]
      exact d.map_source hxd
    exact ht.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds ht₀)
  refine ⟨a, b, k, R, ha, hRi, Φ, hΦ, hΦi, hΦ0, hΦf, hΦx, ?_, K, hK, hKO, hfix⟩
  have ht := (c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hxc)).continuousAt.tendsto
  filter_upwards [ht.eventually (hmatch.and hn), c.open_source.mem_nhds hxc] with y hy hyc
  have hm : Φ 1 (d.symm (A (c y - c x) + d x)) = y :=
    hy.1.trans (c.left_inv hyc)
  have hinv : (Φ 1).symm y = d.symm (A (c y - c x) + d x) := by
    apply (Φ 1).injective
    exact ((Φ 1).apply_symm_apply y).trans hm.symm
  refine ⟨hinv.symm ▸ d.map_target hy.2, ?_⟩
  rw [hinv]
  have hr : d (d.symm (A (c y - c x) + d x)) = A (c y - c x) + d x := d.right_inv hy.2
  rw [hr]
  exact hform (c y)

end DifferentialGeometry.Topology.Manifold
