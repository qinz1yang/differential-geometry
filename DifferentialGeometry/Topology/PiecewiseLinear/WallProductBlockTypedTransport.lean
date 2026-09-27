/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlocksOfWallProductBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemCellTopology

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem lineMap_mem_openSimplex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : Finset E} {p b : E} (hp : p ∈ convexHull ℝ (c : Set E)) (hb : b ∈ openSimplex c)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : AffineMap.lineMap p b s ∈ openSimplex c := by
  obtain ⟨wp, hwp0, hwp1, hwpp⟩ := (Finset.mem_convexHull' (R := ℝ)).mp hp
  obtain ⟨wb, hwb0, hwb1, hwbb⟩ := hb
  refine ⟨fun v => (1 - s) * wp v + s * wb v, fun v hv => ?_, ?_, ?_⟩
  · have h1 := hwp0 v hv
    have h2 := hwb0 v hv
    have h3 : 0 ≤ 1 - s := by linarith
    positivity
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hwp1, hwb1]
    ring
  · rw [AffineMap.lineMap_apply_module]
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hwpp, hwbb]

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_mem_wallSystemCellInt_of_mem_nhds [CompactSpace M]
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} (hcont : Continuous ρ)
    (hinj : Function.Injective ρ) (hrange : Set.range ρ = Q.space) {c : Finset Ea}
    (hc : c ∈ wallSystemCells Q) {y : M} (hy : y ∈ wallSystemCell ρ c) {U : Set M}
    (hU : U ∈ 𝓝 y) : (U ∩ wallSystemCellInt ρ c).Nonempty := by
  have hemb := hcont.isClosedEmbedding hinj
  have hmap : ρ '' U ∈ 𝓝[Set.range ρ] (ρ y) := by
    rw [← hemb.isInducing.map_nhds_eq]
    exact Filter.image_mem_map hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hmap
  have hne : c.Nonempty := Finset.card_pos.mp (by rw [hc.2]; norm_num)
  set b : Ea := c.centroid ℝ id
  have hb : b ∈ openSimplex c := centroid_mem_openSimplex hne
  set s : ℝ := min 1 (ε / (2 * (‖b - ρ y‖ + 1))) with hsdef
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hq : AffineMap.lineMap (ρ y) b s ∈ openSimplex c := lineMap_mem_openSimplex hy hb hs0 hs1
  have hdist : dist (AffineMap.lineMap (ρ y) b s) (ρ y) < ε := by
    rw [dist_lineMap_left, Real.norm_of_nonneg hs0.le]
    have h1 : s ≤ ε / (2 * (‖b - ρ y‖ + 1)) := min_le_right _ _
    have h2 : dist (ρ y) b = ‖b - ρ y‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [h2]
    have h3 : s * ‖b - ρ y‖ ≤ ε / (2 * (‖b - ρ y‖ + 1)) * ‖b - ρ y‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h4 : ε / (2 * (‖b - ρ y‖ + 1)) * ‖b - ρ y‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (b - ρ y)]
    linarith
  have hrng : AffineMap.lineMap (ρ y) b s ∈ Set.range ρ := by
    rw [hrange]
    exact Q.convexHull_subset_space hc.1 (openSimplex_subset_convexHull c hq)
  obtain ⟨z, hzU, hzq⟩ := hball ⟨mem_ball.mpr hdist, hrng⟩
  refine ⟨z, hzU, ?_⟩
  change ρ z ∈ openSimplex c
  rw [hzq]
  exact hq

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.tlo_eq_neg_of_center_notMem {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y : M} (hys : y ∈ ec.source)
    (hA0 : A (ec y) = 0) (hyB : y ∉ BdM) : tlo = -r := by
  obtain ⟨-, -, -, -, -, -, -, hside, -⟩ := h
  rcases hside with ⟨ht, -⟩ | ⟨-, hz, -⟩
  · exact ht
  · exfalso
    apply hyB
    rw [hBd y hys, ← hz, hA0]
    rfl

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.tlo_eq_zero_of_center_mem {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hys : y ∈ ec.source) (hA0 : A (ec y) = 0) (hyB : y ∈ BdM) :
    tlo = 0 ∧ ∀ z, (A z).2.2 = ℓ z := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -⟩ := h
  rcases hside with ⟨ht, hdis⟩ | ⟨ht, hz, -⟩
  · exfalso
    refine Set.disjoint_left.mp hdis ⟨hys, ?_⟩ hyB
    rw [mem_preimage, mem_preimage, hA0]
    change |(0 : ℝ)| ≤ r ∧ |(0 : ℝ)| ≤ r ∧ tlo ≤ 0 ∧ (0 : ℝ) ≤ r
    rw [abs_zero, ht]
    exact ⟨hr.le, hr.le, by linarith, hr.le⟩
  · exact ⟨ht, hz⟩

theorem WallProductBlock.exists_wallProductBlock_at_wall [CompactSpace M] [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C N : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {y : M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {j i₀ : ι}
    (hstab : IsStableCrossingBlock f S (ec j) (ℓ j) BdM A r tlo SA SB a b La Lb η)
    (hskel : Disjoint (chartBlock (ec j) A r tlo) (wallSystemSkeleton Q ρ))
    {w cm cp : Finset Ea} (hw : w ∈ wallSystemWalls Q) (hcm : cm ∈ wallSystemCells Q)
    (hcp : cp ∈ wallSystemCells Q) (htl : tlo = -r) (hne : cm ≠ cp) (hwm : w ⊆ cm)
    (hwp : w ⊆ cp)
    (hcov : chartBlock (ec j) A r tlo ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp)
    (hwalls : ∀ w' ∈ wallSystemWalls Q,
      chartBlock (ec j) A r tlo ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w)
    (hzero : ∀ x ∈ chartBlock (ec j) A r tlo, x ∈ wallSystemCell ρ w ↔ (A (ec j x)).2.2 = 0)
    (hsm : ∀ x ∈ chartBlock (ec j) A r tlo ∩ wallSystemCell ρ cm, (A (ec j x)).2.2 ≤ 0)
    (hsp : ∀ x ∈ chartBlock (ec j) A r tlo ∩ wallSystemCell ρ cp, 0 ≤ (A (ec j x)).2.2)
    (hE : chartBlock (ec j) A r tlo ⊆ Eb j) (hyd : y ∈ doublePointSet f S)
    (hy : y ∈ innerChartBlock (ec j) A r tlo) (hy' : y ∈ Eb i₀) (hN : IsOpen N)
    (hyN : y ∈ N) (hw0 : (A (ec j y)).2.2 = 0) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
      (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
      WallProductBlock f S (ec i₀) (ℓ i₀) BdM C Q ρ A' r' tlo' SA' SB' a' b' La Lb η ∧
        A' (ec i₀ y) = 0 ∧ chartBlock (ec i₀) A' r' tlo' ⊆ N := by
  classical
  obtain ⟨hr, -, -, -, -, -, -, hside0, -⟩ := id hstab
  set w₀ := A (ec j y) with hw₀
  have htle : tlo ≤ 0 := by
    rw [htl]
    linarith
  have ht0 : tlo ≠ 0 := by
    rw [htl]
    exact (neg_neg_of_pos hr).ne
  have hyB : y ∈ chartBlock (ec j) A r tlo := chartBlock_mono_of_half (ec j) A hr.le htle hy
  have hyj : y ∈ (ec j).source := hyB.1
  have hyi₀ : y ∈ (ec i₀).source := hsys.layerSource i₀ (hsys.layerSubset i₀ hy')
  have hyEj : y ∈ Eb j := hE hyB
  have hw₀in : w₀ ∈ blockBox (r / 2) (tlo / 2) := hy.2
  have hw₀1 : |w₀.1| ≤ r / 2 := hw₀in.1
  have hw₀2 : |w₀.2.1| ≤ r / 2 := hw₀in.2.1
  have hcoord : ContinuousOn (fun z => A (ec j z)) (ec j).source :=
    A.toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec j).continuousOn
  let OV : Set (ℝ × ℝ × ℝ) → Set M := fun V =>
    (ec j).source ∩ (fun z => A (ec j z)) ⁻¹' V ∩ (ec i₀).source ∩ N
  have hOVo : ∀ V, IsOpen V → IsOpen (OV V) := fun V hV =>
    ((hcoord.isOpen_inter_preimage (ec j).open_source hV).inter (ec i₀).open_source).inter hN
  have hOVsrc : ∀ V, OV V ⊆ (ec j).source ∩ (ec i₀).source :=
    fun V z hz => ⟨hz.1.1.1, hz.1.2⟩
  have hOVN : ∀ V, OV V ⊆ N := fun V z hz => hz.2
  let Bx : Set (ℝ × ℝ × ℝ) := {w | |w.1| < r ∧ |w.2.1| < r ∧ |w.2.2| < r}
  have hBxo : IsOpen Bx :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const))
  have hw₀Bx : w₀ ∈ Bx := by
    have h3 : |w₀.2.2| < r := by
      rw [hw0, abs_zero]
      exact hr
    exact ⟨by linarith, by linarith, h3⟩
  have hinB : ∀ z ∈ OV Bx, z ∈ chartBlock (ec j) A r tlo := by
    intro z hz
    obtain ⟨⟨⟨hzs, h1, h2, h3⟩, -⟩, -⟩ := hz
    refine ⟨hzs, ?_⟩
    change |(A (ec j z)).1| ≤ r ∧ |(A (ec j z)).2.1| ≤ r ∧ tlo ≤ (A (ec j z)).2.2 ∧
      (A (ec j z)).2.2 ≤ r
    rw [abs_lt] at h3
    refine ⟨h1.le, h2.le, ?_, h3.2.le⟩
    rw [htl]
    exact h3.1.le
  have hU₀ : IsOpen ((fun z => A (ec j z)) '' OV Bx) := by
    have h1 : IsOpen ((ec j) '' OV Bx) :=
      (ec j).isOpen_image_of_subset_source (hOVo Bx hBxo) (fun z hz => (hOVsrc Bx hz).1)
    have heq : (fun z => A (ec j z)) '' OV Bx = A.symm ⁻¹' ((ec j) '' OV Bx) := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (A.symm_apply_apply _).symm⟩
      · rintro ⟨z, hz, hzq⟩
        exact ⟨z, hz, by simp only [hzq, A.apply_symm_apply]⟩
    rw [heq]
    exact h1.preimage A.symm.toAffineMap.continuous_of_finiteDimensional
  have hyO : y ∈ OV Bx := ⟨⟨⟨hyj, hw₀Bx⟩, hyi₀⟩, hyN⟩
  have hOm : ∀ z ∈ OV Bx, (A (ec j z)).2.2 ≤ 0 → z ∈ wallSystemCell ρ cm := by
    intro z hz ht
    rcases hcov (hinB z hz) with h1 | h1
    · exact h1
    · have h2 := hsp z ⟨hinB z hz, h1⟩
      have h3 : (A (ec j z)).2.2 = 0 := le_antisymm ht h2
      exact convexHull_mono (Finset.coe_subset.mpr hwm) ((hzero z (hinB z hz)).2 h3)
  have hOp : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 → z ∈ wallSystemCell ρ cp := by
    intro z hz ht
    rcases hcov (hinB z hz) with h1 | h1
    · have h2 := hsm z ⟨hinB z hz, h1⟩
      have h3 : (A (ec j z)).2.2 = 0 := le_antisymm h2 ht
      exact convexHull_mono (Finset.coe_subset.mpr hwp) ((hzero z (hinB z hz)).2 h3)
    · exact h1
  have hyw : y ∈ wallSystemCell ρ w := (hzero y hyB).2 hw0
  have hycm : y ∈ wallSystemCell ρ cm := convexHull_mono (Finset.coe_subset.mpr hwm) hyw
  have hycp : y ∈ wallSystemCell ρ cp := convexHull_mono (Finset.coe_subset.mpr hwp) hyw
  obtain ⟨Tm, hTm⟩ := hsys.exists_transition hcm (hsys.starLayer j cm hcm ⟨y, hycm, hyEj⟩)
    (hsys.starLayer i₀ cm hcm ⟨y, hycm, hy'⟩)
  obtain ⟨Tp, hTp⟩ := hsys.exists_transition hcp (hsys.starLayer j cp hcp ⟨y, hycp, hyEj⟩)
    (hsys.starLayer i₀ cp hcp ⟨y, hycp, hy'⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU₀ w₀ ⟨y, hyO, rfl⟩
  let H : ℝ × ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ × ℝ :=
    (A.symm.trans (Tp.trans (Tm.symm.trans A))).toAffineMap
  have hHapp : ∀ q, H q = A (Tm.symm (Tp (A.symm q))) := fun q => rfl
  have hHz : ∀ z ∈ OV Bx, 0 ≤ (A (ec j z)).2.2 →
      H (A (ec j z)) = A (Tm.symm (ec i₀ z)) := by
    intro z hz ht
    rw [hHapp, A.symm_apply_apply, ← hTp z (hOp z hz ht)]
  have hfix : ∀ q ∈ ball w₀ δ, q.2.2 = 0 → H q = q := by
    intro q hq hq0
    obtain ⟨z, hz, rfl⟩ := hball hq
    beta_reduce at hq0 ⊢
    rw [hHz z hz hq0.symm.le, hTm z (hOm z hz hq0.le), Tm.symm_apply_apply]
  have hform := AffineMap.eq_add_smul_of_eqOn_plane H hw0 hδ hfix
  set v₃ : ℝ × ℝ × ℝ := H.linear (0, 0, 1) - (0, 0, 1) with hv₃
  have hκ : -1 < v₃.2.2 := by
    by_contra hle
    rw [not_lt] at hle
    have hn : 0 < ‖H.linear (0, 0, 1)‖ + 1 := by positivity
    set δ' : ℝ := δ / (2 * (‖H.linear (0, 0, 1)‖ + 1)) with hδ'
    have hδ'pos : 0 < δ' := by positivity
    have hδ'n : δ' * (‖H.linear (0, 0, 1)‖ + 1) = δ / 2 := by
      rw [hδ']
      field_simp
    have he₃ : ‖((0, 0, 1) : ℝ × ℝ × ℝ)‖ = 1 := by simp
    have hq₁ : w₀ + δ' • ((0, 0, 1) : ℝ × ℝ × ℝ) ∈ ball w₀ δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδ'pos.le, he₃, mul_one]
      nlinarith [norm_nonneg (H.linear (0, 0, 1))]
    obtain ⟨z₁, hz₁, hq₁'⟩ := hball hq₁
    beta_reduce at hq₁'
    have ht₁ : (A (ec j z₁)).2.2 = δ' := by
      rw [hq₁']
      simp [hw0]
    have hHq₁ : H (A (ec j z₁)) = w₀ + δ' • H.linear (0, 0, 1) := by
      rw [hform, ht₁, hq₁', hv₃, smul_sub]
      abel
    have hq₂ : H (A (ec j z₁)) ∈ ball w₀ δ := by
      rw [hHq₁, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδ'pos.le]
      nlinarith [norm_nonneg (H.linear (0, 0, 1))]
    obtain ⟨z₂, hz₂, hq₂'⟩ := hball hq₂
    beta_reduce at hq₂'
    have ht₂ : (A (ec j z₂)).2.2 = δ' * (1 + v₃.2.2) := by
      rw [hq₂', hform, ht₁]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hq₁']
      simp [hw0]
      ring
    have ht₂le : (A (ec j z₂)).2.2 ≤ 0 := by
      rw [ht₂]
      nlinarith
    have h1 : A (ec j z₂) = A (Tm.symm (ec i₀ z₁)) := by
      rw [hq₂', hHz z₁ hz₁ (by rw [ht₁]; exact hδ'pos.le)]
    have h2 : ec j z₂ = Tm.symm (ec i₀ z₁) := A.injective h1
    have h3 : ec i₀ z₂ = ec i₀ z₁ := by
      rw [hTm z₂ (hOm z₂ hz₂ ht₂le), h2, Tm.apply_symm_apply]
    have h4 : z₂ = z₁ := (ec i₀).injOn (hOVsrc Bx hz₂).2 (hOVsrc Bx hz₁).2 h3
    rw [h4, ht₁] at ht₂
    have : δ' * v₃.2.2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h5 | h5
    · linarith
    · linarith
  let A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
    Tm.symm.trans (A.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-w₀)))
  have hA'app : ∀ x, A' x = -w₀ + A (Tm.symm x) := fun x => rfl
  have hA'y : A' (ec i₀ y) = 0 := by
    rw [hA'app, hTm y hycm, Tm.symm_apply_apply, neg_add_cancel]
  have hrelF : ∀ z ∈ OV Bx, A' (ec i₀ z) =
      ((A (ec j z)).1 + kinkOffset (-w₀.1) v₃.1 w₀.2.2 (A (ec j z)).2.2,
        (A (ec j z)).2.1 + kinkOffset (-w₀.2.1) v₃.2.1 w₀.2.2 (A (ec j z)).2.2,
        kinkHeight w₀.2.2 v₃.2.2 (A (ec j z)).2.2) := by
    intro z hz
    rw [hA'app]
    rcases le_total (A (ec j z)).2.2 0 with ht | ht
    · rw [hTm z (hOm z hz ht), Tm.symm_apply_apply]
      exact neg_add_eq_kink_of_nonpos v₃ hw0 ht
    · rw [← hHz z hz ht, hform]
      exact neg_add_add_smul_eq_kink v₃ hw0 ht
  obtain ⟨r', tlo', a', b', hr', hblk, hsubO⟩ :=
    IsStableCrossingBlock.exists_kink_recentre (α₁ := v₃.1) (β₁ := v₃.2.1) (κ := v₃.2.2)
      (ℓ' := ℓ i₀) (A' := A') hstab (hsys.chartBd j) hyd hy hκ (hOVo Bx hBxo) hyO
      (hOVsrc Bx) (fun z _ ht => absurd ht ht0) hA'y (fun z hz _ => hrelF z hz)
      (fun ht => absurd ht ht0)
  have hyBd : y ∉ BdM := by
    rcases hside0 with ⟨-, hdis⟩ | ⟨ht, -⟩
    · exact fun hyBd => Set.disjoint_left.mp hdis hyB hyBd
    · exact absurd ht ht0
  have htlo' : tlo' = -r' := hblk.tlo_eq_neg_of_center_notMem (hsys.chartBd i₀) hyi₀ hA'y hyBd
  have hsub' : chartBlock (ec i₀) A' r' tlo' ⊆ chartBlock (ec j) A r tlo := fun z hz =>
    hinB z (hsubO hz)
  have hA'c : ContinuousOn (fun z => A' (ec i₀ z)) (ec i₀).source :=
    A'.toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec i₀).continuousOn
  have hUo : IsOpen ((ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹' ball 0 r') :=
    hA'c.isOpen_inter_preimage (ec i₀).open_source isOpen_ball
  have hyU : y ∈ (ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹' ball 0 r' := by
    refine ⟨hyi₀, ?_⟩
    change A' (ec i₀ y) ∈ ball 0 r'
    rw [hA'y]
    exact mem_ball_self hr'
  have hUsub : (ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹' ball 0 r' ⊆
      chartBlock (ec i₀) A' r' tlo' := by
    rintro z ⟨hzs, hzb⟩
    have hn : ‖A' (ec i₀ z)‖ < r' := mem_ball_zero_iff.mp hzb
    have h1 := (norm_fst_le (A' (ec i₀ z))).trans_lt hn
    have h2 := ((norm_fst_le (A' (ec i₀ z)).2).trans (norm_snd_le (A' (ec i₀ z)))).trans_lt hn
    have h3 := ((norm_snd_le (A' (ec i₀ z)).2).trans (norm_snd_le (A' (ec i₀ z)))).trans_lt hn
    rw [Real.norm_eq_abs] at h1 h2 h3
    refine ⟨hzs, ?_⟩
    change |(A' (ec i₀ z)).1| ≤ r' ∧ |(A' (ec i₀ z)).2.1| ≤ r' ∧ tlo' ≤ (A' (ec i₀ z)).2.2 ∧
      (A' (ec i₀ z)).2.2 ≤ r'
    rw [htlo']
    exact ⟨h1.le, h2.le, by linarith [(abs_lt.mp h3).1], (abs_lt.mp h3).2.le⟩
  have hmeet : ∀ c ∈ wallSystemCells Q, y ∈ wallSystemCell ρ c →
      (chartBlock (ec i₀) A' r' tlo' ∩ wallSystemCellInt ρ c).Nonempty := by
    intro c hc hyc
    obtain ⟨z, hzU, hzc⟩ := exists_mem_wallSystemCellInt_of_mem_nhds hsys.continuous
      hsys.injective hsys.rangeEq hc hyc (hUo.mem_nhds hyU)
    exact ⟨z, hUsub hzU, hzc⟩
  have hkink : ∀ z ∈ chartBlock (ec i₀) A' r' tlo',
      (A' (ec i₀ z)).2.2 = kinkHeight w₀.2.2 v₃.2.2 (A (ec j z)).2.2 := by
    intro z hz
    rw [hrelF z (hsubO hz)]
  refine ⟨A', r', tlo', _, _, a', b', ⟨hblk, hskel.mono_left hsub', Or.inr (Or.inl
    ⟨w, hw, cm, hcm, cp, hcp, htlo', hne, hwm, hwp, hsub'.trans hcov, hmeet cm hcm hycm,
      hmeet cp hcp hycp, fun w' hw' => (inter_subset_inter_left _ hsub').trans (hwalls w' hw'),
      ?_, ?_, ?_⟩)⟩, hA'y, hsubO.trans (hOVN Bx)⟩
  · intro x hx
    rw [hzero x (hsub' hx), hkink x hx, hw0, kinkHeight_eq_zero_iff hκ]
  · rintro x ⟨hx, hxm⟩
    have h1 := hsm x ⟨hsub' hx, hxm⟩
    rw [hkink x hx, hw0]
    by_contra hpos
    rw [not_le] at hpos
    have h2 := (kinkHeight_nonneg_iff hκ _).mp hpos.le
    have h3 : (A (ec j x)).2.2 = 0 := le_antisymm h1 h2
    rw [h3, kinkHeight_self] at hpos
    exact lt_irrefl 0 hpos
  · rintro x ⟨hx, hxp⟩
    rw [hkink x hx, hw0]
    exact (kinkHeight_nonneg_iff hκ _).mpr (hsp x ⟨hsub' hx, hxp⟩)

theorem WallProductBlock.exists_wallProductBlock_at [CompactSpace M] [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C N : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {y : M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {j i₀ : ι}
    (h : WallProductBlock f S (ec j) (ℓ j) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hE : chartBlock (ec j) A r tlo ⊆ Eb j) (hyd : y ∈ doublePointSet f S)
    (hy : y ∈ innerChartBlock (ec j) A r tlo) (hy' : y ∈ Eb i₀) (hN : IsOpen N)
    (hyN : y ∈ N) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
      (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
      WallProductBlock f S (ec i₀) (ℓ i₀) BdM C Q ρ A' r' tlo' SA' SB' a' b' La Lb η ∧
        A' (ec i₀ y) = 0 ∧ chartBlock (ec i₀) A' r' tlo' ⊆ N := by
  classical
  obtain ⟨hstab, hskel, htype⟩ := h
  obtain ⟨hr, -, -, -, -, -, -, hside0, -⟩ := id hstab
  have htle : tlo ≤ 0 := by
    rcases hside0 with ⟨ht, -⟩ | ⟨ht, -⟩
    · rw [ht]
      linarith
    · exact ht.le
  have hyB : y ∈ chartBlock (ec j) A r tlo := chartBlock_mono_of_half (ec j) A hr.le htle hy
  have hyj : y ∈ (ec j).source := hyB.1
  have hyi₀ : y ∈ (ec i₀).source := hsys.layerSource i₀ (hsys.layerSubset i₀ hy')
  have hnotBd : tlo = -r → y ∉ BdM := by
    intro ht hyBd
    rcases hside0 with ⟨-, hdis⟩ | ⟨ht', -⟩
    · exact Set.disjoint_left.mp hdis hyB hyBd
    · rw [ht] at ht'
      linarith
  have hcellCase : ∀ c ∈ wallSystemCells Q, y ∈ wallSystemCellInt ρ c → y ∉ BdM →
      ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
        (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
        WallProductBlock f S (ec i₀) (ℓ i₀) BdM C Q ρ A' r' tlo' SA' SB' a' b' La Lb η ∧
          A' (ec i₀ y) = 0 ∧ chartBlock (ec i₀) A' r' tlo' ⊆ N := by
    intro c hc hyc hyBd
    have hco : IsOpen (wallSystemCellInt ρ c) := isOpen_wallSystemCellInt hsys.finiteFaces
      hsys.continuous hsys.rangeEq hsys.dimLe hc
    obtain ⟨A', r', tlo', SA', SB', a', b', hblk, hA'y, hsubN⟩ :=
      WallProductBlock.exists_isStableCrossingBlock_at hsys ⟨hstab, hskel, htype⟩ hE hyd hy hy'
        (hN.inter hco) ⟨hyN, hyc⟩
    have htlo' := hblk.tlo_eq_neg_of_center_notMem (hsys.chartBd i₀) hyi₀ hA'y hyBd
    exact ⟨A', r', tlo', SA', SB', a', b', ⟨hblk,
      (disjoint_wallSystemCellInt_wallSystemSkeleton hc).mono_left
        (hsubN.trans inter_subset_right),
      Or.inl ⟨c, hc, htlo', hsubN.trans inter_subset_right⟩⟩, hA'y, hsubN.trans inter_subset_left⟩
  have hint : ∀ c ∈ wallSystemCells Q, y ∈ wallSystemCell ρ c →
      (∀ w' ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w') → y ∈ wallSystemCellInt ρ c := by
    intro c hc hyc hyw
    by_contra hyi
    obtain ⟨w', hw', hyw'⟩ := mem_iUnion₂.mp (wallSystemCell_sdiff_subset_iUnion_wall hc ⟨hyc, hyi⟩)
    exact hyw w' hw' hyw'
  rcases htype with ⟨c, hc, htl, hcell⟩ |
      ⟨w, hw, cm, hcm, cp, hcp, htl, hne, hwm, hwp, hcov, -, -, hwalls, hzero, hsm, hsp⟩ |
      ⟨c, hc, w, hw, htl, hwc, hheight, hCc, hnc, hBdw, hwalls⟩
  · exact hcellCase c hc (hcell hyB) (hnotBd htl)
  · rcases lt_trichotomy (A (ec j y)).2.2 0 with hw0 | hw0 | hw0
    · have hym : y ∈ wallSystemCell ρ cm := by
        rcases hcov hyB with h1 | h1
        · exact h1
        · exact absurd (hsp y ⟨hyB, h1⟩) (not_le.mpr hw0)
      refine hcellCase cm hcm (hint cm hcm hym fun w' hw' hyw' => ?_) (hnotBd htl)
      exact hw0.ne ((hzero y hyB).1 (hwalls w' hw' ⟨hyB, hyw'⟩))
    · exact WallProductBlock.exists_wallProductBlock_at_wall hsys hstab hskel hw hcm hcp htl hne
        hwm hwp hcov hwalls hzero hsm hsp hE hyd hy hy' hN hyN hw0
    · have hyp : y ∈ wallSystemCell ρ cp := by
        rcases hcov hyB with h1 | h1
        · exact absurd (hsm y ⟨hyB, h1⟩) (not_le.mpr hw0)
        · exact h1
      refine hcellCase cp hcp (hint cp hcp hyp fun w' hw' hyw' => ?_) (hnotBd htl)
      exact hw0.ne' ((hzero y hyB).1 (hwalls w' hw' ⟨hyB, hyw'⟩))
  · have ht0 : 0 ≤ (A (ec j y)).2.2 := by
      have h1 : tlo ≤ (A (ec j y)).2.2 := hyB.2.2.2.1
      rwa [htl] at h1
    have hCiff : ∀ z ∈ (ec j).source, z ∈ C ↔ 0 ≤ (A (ec j z)).2.2 := by
      intro z hz
      rw [hheight]
      exact hsys.chartC j z hz
    have hBdiff : ∀ z ∈ (ec j).source, z ∈ BdM ↔ (A (ec j z)).2.2 = 0 := by
      intro z hz
      rw [hheight]
      exact hsys.chartBd j z hz
    have hcoord : ContinuousOn (fun z => A (ec j z)) (ec j).source :=
      A.toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec j).continuousOn
    rcases ht0.lt_or_eq with hw0 | hw0
    · have hyBd : y ∉ BdM := fun h => hw0.ne' ((hBdiff y hyj).1 h)
      have hyc : y ∈ wallSystemCell ρ c := hCc ⟨hyB, (hCiff y hyj).2 hw0.le⟩
      let N₂ : Set M := (ec j).source ∩ (fun z => A (ec j z)) ⁻¹'
        {q : ℝ × ℝ × ℝ | |q.1| < r ∧ |q.2.1| < r ∧ 0 < q.2.2 ∧ q.2.2 < r}
      have hN₂o : IsOpen N₂ := hcoord.isOpen_inter_preimage (ec j).open_source
        ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
            ((isOpen_lt continuous_const continuous_snd.snd).inter
              (isOpen_lt continuous_snd.snd continuous_const))))
      have hyN₂ : y ∈ N₂ := by
        have hb := hy.2
        obtain ⟨h1, h2, -, h4⟩ := hb
        exact ⟨hyj, by linarith, by linarith, hw0, by linarith⟩
      have hN₂c : ∀ z ∈ N₂, z ∈ wallSystemCell ρ c := by
        rintro z ⟨hzs, h1, h2, h3, h4⟩
        refine hCc ⟨⟨hzs, ?_⟩, (hCiff z hzs).2 h3.le⟩
        change |(A (ec j z)).1| ≤ r ∧ |(A (ec j z)).2.1| ≤ r ∧ tlo ≤ (A (ec j z)).2.2 ∧
          (A (ec j z)).2.2 ≤ r
        rw [htl]
        exact ⟨h1.le, h2.le, h3.le, h4.le⟩
      have hnotw : y ∉ wallSystemCell ρ w := by
        intro hyw
        obtain ⟨cm, hcm, cp, hcp, hne, hwm, hwp, -⟩ := hsys.wallSides w hw
        have hside : ∀ c' ∈ wallSystemCells Q, w ⊆ c' → c' = c := by
          intro c' hc' hwc'
          have hyc' : y ∈ wallSystemCell ρ c' :=
            convexHull_mono (Finset.coe_subset.mpr hwc') hyw
          obtain ⟨z, hzN, hzi⟩ := exists_mem_wallSystemCellInt_of_mem_nhds hsys.continuous
            hsys.injective hsys.rangeEq hc' hyc' (hN₂o.mem_nhds hyN₂)
          by_contra hne'
          exact Set.disjoint_left.mp (disjoint_wallSystemCellInt_wallSystemCell hc' hc hne')
            hzi (hN₂c z hzN)
        exact hne ((hside cm hcm hwm).trans (hside cp hcp hwp).symm)
      refine hcellCase c hc (hint c hc hyc fun w' hw' hyw' => ?_) hyBd
      exact hnotw (hwalls w' hw' ⟨hyB, hyw'⟩)
    · have hyBd : y ∈ BdM := (hBdiff y hyj).2 hw0.symm
      let Bx : Set (ℝ × ℝ × ℝ) := {q | |q.1| < r ∧ |q.2.1| < r ∧ |q.2.2| < r}
      let N₁ : Set M := (ec j).source ∩ (fun z => A (ec j z)) ⁻¹' Bx
      have hN₁o : IsOpen N₁ := hcoord.isOpen_inter_preimage (ec j).open_source
        ((isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
            (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const)))
      have hyN₁ : y ∈ N₁ := by
        obtain ⟨h1, h2, -, h4⟩ := hy.2
        refine ⟨hyj, by linarith, by linarith, ?_⟩
        change |(A (ec j y)).2.2| < r
        rw [← hw0, abs_zero]
        exact hr
      obtain ⟨A', r', tlo', SA', SB', a', b', hblk, hA'y, hsubN⟩ :=
        WallProductBlock.exists_isStableCrossingBlock_at hsys
          ⟨hstab, hskel, Or.inr (Or.inr ⟨c, hc, w, hw, htl, hwc, hheight, hCc, hnc, hBdw,
            hwalls⟩)⟩ hE hyd hy hy' (hN.inter hN₁o) ⟨hyN, hyN₁⟩
      obtain ⟨htlo', hA'ℓ⟩ := hblk.tlo_eq_zero_of_center_mem hyi₀ hA'y hyBd
      have hr' : 0 < r' := hblk.1
      have hsub' : chartBlock (ec i₀) A' r' tlo' ⊆ chartBlock (ec j) A r tlo := by
        intro z hz
        obtain ⟨hzs, hzb⟩ := hz
        obtain ⟨-, hzN₁⟩ := hsubN ⟨hzs, hzb⟩
        obtain ⟨hzj, h1, h2, h3⟩ := hzN₁
        have ht' : 0 ≤ (A' (ec i₀ z)).2.2 := by
          have := hzb.2.2.1
          rwa [htlo'] at this
        rw [hA'ℓ] at ht'
        have hzC : z ∈ C := (hsys.chartC i₀ z hzs).2 ht'
        have ht : 0 ≤ (A (ec j z)).2.2 := (hCiff z hzj).1 hzC
        refine ⟨hzj, ?_⟩
        change |(A (ec j z)).1| ≤ r ∧ |(A (ec j z)).2.1| ≤ r ∧ tlo ≤ (A (ec j z)).2.2 ∧
          (A (ec j z)).2.2 ≤ r
        rw [htl]
        exact ⟨h1.le, h2.le, ht, (abs_lt.mp h3).2.le⟩
      have hcC : wallSystemCell ρ c ⊆ C := by
        obtain ⟨z₀, hz₀B, hz₀i⟩ := hnc
        have hz₀C : z₀ ∈ C := by
          refine (hCiff z₀ hz₀B.1).2 ?_
          have := hz₀B.2.2.2.1
          rwa [htl] at this
        rw [hsys.eqC] at hz₀C ⊢
        obtain ⟨c', hc', hz₀c'⟩ := mem_iUnion₂.mp hz₀C
        have hcc' : c = c' := by
          by_contra hne'
          exact Set.disjoint_left.mp (disjoint_wallSystemCellInt_wallSystemCell hc
            (hsys.facesC hc') hne') hz₀i hz₀c'
        intro x hx
        exact mem_iUnion₂.mpr ⟨c', hc', hcc' ▸ hx⟩
      have hyc : y ∈ wallSystemCell ρ c :=
        convexHull_mono (Finset.coe_subset.mpr hwc) (hBdw ⟨hyB, hyBd⟩)
      have hA'c : ContinuousOn (fun z => A' (ec i₀ z)) (ec i₀).source :=
        A'.toAffineMap.continuous_of_finiteDimensional.comp_continuousOn (ec i₀).continuousOn
      have hUo : IsOpen ((ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹' ball 0 r') :=
        hA'c.isOpen_inter_preimage (ec i₀).open_source isOpen_ball
      have hyU : y ∈ (ec i₀).source ∩ (fun z => A' (ec i₀ z)) ⁻¹' ball 0 r' := by
        refine ⟨hyi₀, ?_⟩
        change A' (ec i₀ y) ∈ ball 0 r'
        rw [hA'y]
        exact mem_ball_self hr'
      obtain ⟨z, ⟨hzs, hzb⟩, hzi⟩ := exists_mem_wallSystemCellInt_of_mem_nhds hsys.continuous
        hsys.injective hsys.rangeEq hc hyc (hUo.mem_nhds hyU)
      have hmeet : (chartBlock (ec i₀) A' r' tlo' ∩ wallSystemCellInt ρ c).Nonempty := by
        refine ⟨z, ⟨hzs, ?_⟩, hzi⟩
        have hn : ‖A' (ec i₀ z)‖ < r' := mem_ball_zero_iff.mp hzb
        have h1 := (norm_fst_le (A' (ec i₀ z))).trans_lt hn
        have h2 := ((norm_fst_le (A' (ec i₀ z)).2).trans (norm_snd_le (A' (ec i₀ z)))).trans_lt hn
        have h3 := ((norm_snd_le (A' (ec i₀ z)).2).trans (norm_snd_le (A' (ec i₀ z)))).trans_lt hn
        rw [Real.norm_eq_abs] at h1 h2 h3
        have hzC : z ∈ C := hcC (wallSystemCellInt_subset_wallSystemCell ρ c hzi)
        have ht' : 0 ≤ (A' (ec i₀ z)).2.2 := by
          rw [hA'ℓ]
          exact (hsys.chartC i₀ z hzs).1 hzC
        change |(A' (ec i₀ z)).1| ≤ r' ∧ |(A' (ec i₀ z)).2.1| ≤ r' ∧
          tlo' ≤ (A' (ec i₀ z)).2.2 ∧ (A' (ec i₀ z)).2.2 ≤ r'
        rw [htlo']
        exact ⟨h1.le, h2.le, ht', (abs_lt.mp h3).2.le⟩
      exact ⟨A', r', tlo', SA', SB', a', b', ⟨hblk, hskel.mono_left hsub', Or.inr (Or.inr
        ⟨c, hc, w, hw, htlo', hwc, hA'ℓ, (inter_subset_inter_left _ hsub').trans hCc, hmeet,
          (inter_subset_inter_left _ hsub').trans hBdw,
          fun w' hw' => (inter_subset_inter_left _ hsub').trans (hwalls w' hw')⟩)⟩, hA'y,
        hsubN.trans inter_subset_left⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
