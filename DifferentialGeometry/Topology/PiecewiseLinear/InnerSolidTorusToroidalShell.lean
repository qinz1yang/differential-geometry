/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem isCompact_revolutionOf_of_isCompact {X : Set E3} (hX : IsCompact X) :
    IsCompact (revolutionOf X) := by
  obtain ⟨R, hR⟩ := hX.isBounded.subset_closedBall 0
  have hC : IsCompact ({z : E3 × E3 | z.1 ∈ X} ∩
      ({z | z.1 2 = 0} ∩ ({z | 0 ≤ z.1 0} ∩
        ({z | z.1 1 = z.2 1} ∩ {z | z.1 0 ^ 2 = z.2 0 ^ 2 + z.2 2 ^ 2})))) := by
    refine (hX.prod (isCompact_closedBall (0 : E3) R)).of_isClosed_subset
      ((hX.isClosed.preimage continuous_fst).inter
        ((isClosed_eq (by fun_prop) continuous_const).inter
          ((isClosed_le continuous_const (by fun_prop)).inter
            ((isClosed_eq (by fun_prop) (by fun_prop)).inter
              (isClosed_eq (by fun_prop) (by fun_prop)))))) ?_
    rintro ⟨q, p⟩ ⟨hqX, hq2, -, hq1, hqsq⟩
    have hq2' : q 2 = 0 := hq2
    have hq1' : q 1 = p 1 := hq1
    have hqsq' : q 0 ^ 2 = p 0 ^ 2 + p 2 ^ 2 := hqsq
    have hqR : ‖q‖ ≤ R := mem_closedBall_zero_iff.mp (hR hqX)
    refine ⟨hqX, mem_closedBall_zero_iff.mpr (le_trans ?_ hqR)⟩
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    change ‖p‖ ^ 2 ≤ ‖q‖ ^ 2
    have h1 := EuclideanSpace.real_norm_sq_eq p
    have h2 := EuclideanSpace.real_norm_sq_eq q
    rw [Fin.sum_univ_three] at h1 h2
    rw [hq2', hq1', hqsq', zero_pow two_ne_zero, add_zero] at h2
    linarith
  convert hC.image continuous_snd using 1
  ext p
  constructor
  · rintro ⟨q, hq, h2, h0, h1, hsq⟩
    exact ⟨(q, p), ⟨hq, h2, h0, h1, hsq⟩, rfl⟩
  · rintro ⟨⟨q, p'⟩, ⟨hq, h2, h0, h1, hsq⟩, rfl⟩
    exact ⟨q, hq, h2, h0, h1, hsq⟩

private theorem smul_mem_closedBall_zero_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {v : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ ≤ 1) :
    t • v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg v]

theorem IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior
    {Y K : Set E3} (hY : IsTopologicalSolidTorus Y) (hK : IsCompact K)
    (hKY : K ⊆ interior Y) :
    ∃ S₁ : Set E3, IsTopologicalSolidTorus S₁ ∧ K ⊆ interior S₁ ∧ S₁ ⊆ interior Y ∧
      IsToroidalShell (closure (Y \ S₁)) (frontier S₁) (frontier Y) := by
  obtain ⟨φ⟩ := hY
  have hYcl : IsClosed Y := by
    have : CompactSpace Y := φ.symm.compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → E3, ∀ z, Ψ z = φ.symm z :=
    ⟨fun z => φ.symm z, fun _ => rfl⟩
  have hΨc : Continuous Ψ := by
    rw [show Ψ = fun z => (φ.symm z : E3) from funext hΨ]
    exact continuous_subtype_val.comp φ.symm.continuous
  have hΨi : Function.Injective Ψ := fun a b hab =>
    φ.symm.injective (Subtype.ext (by rw [← hΨ, ← hΨ]; exact hab))
  have hΨY : ∀ z, Ψ z ∈ Y := fun z => by
    rw [hΨ]
    exact (φ.symm z).2
  have hYΨ : ∀ x ∈ Y, ∃ z, Ψ z = x := fun x hx =>
    ⟨φ ⟨x, hx⟩, by rw [hΨ, φ.symm_apply_apply]⟩
  have hfrY : ∀ z, Ψ z ∈ frontier Y ↔ ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    intro z
    have h := mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere hYcl φ
      (φ.symm z)
    rw [φ.apply_symm_apply, ← hΨ] at h
    exact h
  have hintY : ∀ z, ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ < 1 → Ψ z ∈ interior Y := fun z hz => by
    rw [hΨ]
    exact mem_interior_of_homeomorph_closedBall_prod_sphere φ z.1 z.2 hz
  obtain ⟨m, hm0, hm1, hKm⟩ : ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧
      ∀ z, Ψ z ∈ K → ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ ≤ m := by
    rcases (Ψ ⁻¹' K).eq_empty_or_nonempty with he | hne
    · refine ⟨0, le_rfl, zero_lt_one, fun z hz => ?_⟩
      have hz' : z ∈ Ψ ⁻¹' K := hz
      rw [he] at hz'
      exact absurd hz' (notMem_empty z)
    · obtain ⟨z₀, hz₀, hmax⟩ :=
        ((hΨc.isClosedEmbedding hΨi).isCompact_preimage hK).exists_isMaxOn hne
          (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).continuousOn
      refine ⟨‖(z₀.1 : EuclideanSpace ℝ (Fin 2))‖, norm_nonneg _,
        lt_of_le_of_ne (mem_closedBall_zero_iff.mp z₀.1.2) fun heq => ?_,
        fun z hz => isMaxOn_iff.mp hmax z hz⟩
      exact Set.disjoint_left.mp disjoint_interior_frontier (hKY hz₀) ((hfrY z₀).mpr heq)
  obtain ⟨r, hr0, hr1, hmr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ m < r :=
    ⟨(1 + m) / 2, by linarith, by linarith, by linarith⟩
  let f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → E3 := fun w =>
    Ψ (⟨r • (w.1 : EuclideanSpace ℝ (Fin 2)), smul_mem_closedBall_zero_one hr0.le hr1.le
      (mem_closedBall_zero_iff.mp w.1.2)⟩, w.2)
  have hfc : Continuous f := by
    refine hΨc.comp (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
    fun_prop
  have hfi : Function.Injective f := by
    intro w w' hww
    have h := hΨi hww
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Prod.ext (Subtype.ext (smul_right_injective _ hr0.ne' h.1)) h.2
  have hfemb := hfc.isClosedEmbedding hfi
  let φ₁ : range f ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := hfemb.isEmbedding.toHomeomorph.symm
  have hfrf : ∀ w, f w ∈ frontier (range f) ↔ ‖(w.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    intro w
    have h := mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere
      hfemb.isClosed_range φ₁ (φ₁.symm w)
    rw [φ₁.apply_symm_apply] at h
    exact h
  have hsc : ∀ z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ ≤ r →
      ∃ w, f w = Ψ z ∧ ‖(w.1 : EuclideanSpace ℝ (Fin 2))‖ =
        r⁻¹ * ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ := by
    intro z hz
    have hmem : r⁻¹ • (z.1 : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0),
        inv_mul_le_iff₀ hr0, mul_one]
      exact hz
    refine ⟨(⟨_, hmem⟩, z.2), ?_, ?_⟩
    · change Ψ _ = Ψ z
      congr 1
      exact Prod.ext (Subtype.ext (smul_inv_smul₀ hr0.ne' _)) rfl
    · change ‖r⁻¹ • (z.1 : EuclideanSpace ℝ (Fin 2))‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
  have hmemS₁ : ∀ z, Ψ z ∈ range f ↔ ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ ≤ r := by
    intro z
    constructor
    · rintro ⟨w, hw⟩
      obtain rfl := hΨi hw
      change ‖r • (w.1 : EuclideanSpace ℝ (Fin 2))‖ ≤ r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [mem_closedBall_zero_iff.mp w.1.2, norm_nonneg (w.1 : EuclideanSpace ℝ (Fin 2))]
    · intro hz
      obtain ⟨w, hw, -⟩ := hsc z hz
      exact ⟨w, hw⟩
  have hKS₁ : K ⊆ interior (range f) := by
    intro x hx
    obtain ⟨z, rfl⟩ := hYΨ x (interior_subset (hKY hx))
    obtain ⟨w, hw, hwn⟩ := hsc z ((hKm z hx).trans hmr.le)
    have hlt : ‖(w.1 : EuclideanSpace ℝ (Fin 2))‖ < 1 := by
      rw [hwn, inv_mul_lt_iff₀ hr0, mul_one]
      exact (hKm z hx).trans_lt hmr
    have h := mem_interior_of_homeomorph_closedBall_prod_sphere φ₁ w.1 w.2 hlt
    rw [← hw]
    exact h
  have hS₁Y : range f ⊆ interior Y := by
    rintro _ ⟨w, rfl⟩
    refine hintY _ ?_
    change ‖r • (w.1 : EuclideanSpace ℝ (Fin 2))‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [mem_closedBall_zero_iff.mp w.1.2, norm_nonneg (w.1 : EuclideanSpace ℝ (Fin 2))]
  have hmemg : ∀ p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × Icc (0 : ℝ) 1,
      (r + (p.2 : ℝ) * (1 - r)) • (p.1.1 : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun p =>
    smul_mem_closedBall_zero_one (by nlinarith [p.2.2.1]) (by nlinarith [p.2.2.2])
      (mem_sphere_zero_iff_norm.mp p.1.1.2).le
  have hpos : ∀ s : Icc (0 : ℝ) 1, 0 < r + (s : ℝ) * (1 - r) := fun s => by
    nlinarith [s.2.1]
  let g : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × Icc (0 : ℝ) 1 → E3 := fun p =>
    Ψ (⟨_, hmemg p⟩, p.1.2)
  have hgc : Continuous g := by
    refine hΨc.comp (Continuous.prodMk (Continuous.subtype_mk ?_ _)
      (continuous_snd.comp continuous_fst))
    fun_prop
  have hgi : Function.Injective g := by
    rintro ⟨⟨u, θ⟩, s⟩ ⟨⟨u', θ'⟩, s'⟩ h
    have h' := hΨi h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have hn := congrArg norm h1
    rw [norm_smul, norm_smul, mem_sphere_zero_iff_norm.mp u.2, mem_sphere_zero_iff_norm.mp u'.2,
      mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpos s),
      abs_of_pos (hpos s')] at hn
    have hss : (s : ℝ) = s' :=
      mul_right_cancel₀ (sub_pos.mpr hr1).ne' (by linarith)
    rw [hn] at h1
    exact Prod.ext (Prod.ext (Subtype.ext (smul_right_injective _ (hpos s').ne' h1)) h2)
      (Subtype.ext hss)
  have hrangeg : ∀ z, Ψ z ∈ range g ↔ r ≤ ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ := by
    intro z
    constructor
    · rintro ⟨⟨⟨u, θ⟩, s⟩, hp⟩
      obtain rfl := hΨi hp
      change r ≤ ‖(r + (s : ℝ) * (1 - r)) • (u : EuclideanSpace ℝ (Fin 2))‖
      rw [norm_smul, mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs,
        abs_of_pos (hpos s)]
      nlinarith [s.2.1]
    · intro hz
      have hz0 : 0 < ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ := hr0.trans_le hz
      have hu : ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖⁻¹ • (z.1 : EuclideanSpace ℝ (Fin 2)) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz0.ne']
      have hs : (‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ - r) / (1 - r) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr
          (by linarith [mem_closedBall_zero_iff.mp z.1.2])⟩
      have hcoef : r + (‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ - r) / (1 - r) * (1 - r) =
          ‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ := by
        rw [div_mul_cancel₀ _ (sub_pos.mpr hr1).ne']
        ring
      refine ⟨((⟨_, hu⟩, z.2), ⟨_, hs⟩), ?_⟩
      change Ψ _ = Ψ z
      congr 1
      refine Prod.ext (Subtype.ext ?_) rfl
      change (r + (‖(z.1 : EuclideanSpace ℝ (Fin 2))‖ - r) / (1 - r) * (1 - r)) •
        (‖(z.1 : EuclideanSpace ℝ (Fin 2))‖⁻¹ • (z.1 : EuclideanSpace ℝ (Fin 2))) = z.1
      rw [hcoef, smul_inv_smul₀ hz0.ne']
  have hsub : Y \ range f ⊆ range g := by
    rintro x ⟨hxY, hxf⟩
    obtain ⟨z, rfl⟩ := hYΨ x hxY
    exact (hrangeg z).mpr (le_of_lt (not_le.mp fun h => hxf ((hmemS₁ z).mpr h)))
  have hgemb := hgc.isClosedEmbedding hgi
  have hout : ∀ (u θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (t : Icc (0 : ℝ) 1),
      0 < (t : ℝ) → g ((u, θ), t) ∈ Y \ range f := by
    intro u θ t ht
    refine ⟨hΨY _, fun hmem => ?_⟩
    have hle := (hmemS₁ _).mp hmem
    change ‖(r + (t : ℝ) * (1 - r)) • (u : EuclideanSpace ℝ (Fin 2))‖ ≤ r at hle
    rw [norm_smul, mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs,
      abs_of_pos (hpos t)] at hle
    nlinarith
  have hcl : range g = closure (Y \ range f) := by
    refine Subset.antisymm ?_ (closure_minimal hsub hgemb.isClosed_range)
    rintro _ ⟨⟨⟨u, θ⟩, s⟩, rfl⟩
    rcases eq_or_lt_of_le s.2.1 with hs | hs
    · let c : ℝ → E3 := fun t => g ((u, θ), projIcc 0 1 zero_le_one t)
      have hc : Continuous c := hgc.comp (continuous_const.prodMk continuous_projIcc)
      have hc0 : c 0 = g ((u, θ), s) := congrArg (fun t => g ((u, θ), t))
        (Subtype.ext (by rw [projIcc_left]; exact hs))
      rw [← hc0]
      refine mem_closure_of_tendsto
        ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))) ?_
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      refine hout u θ _ ?_
      rw [projIcc_of_mem zero_le_one ⟨ht.1.le, ht.2.le⟩]
      exact ht.1
    · exact subset_closure (hout u θ s hs)
  let ψ := hgemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hcl)
  have hψ : ∀ B, Subtype.val '' (ψ '' B) = g '' B := fun B => by
    rw [image_image]
    rfl
  refine ⟨range f, ⟨φ₁⟩, hKS₁, hS₁Y, ψ, ?_, ?_⟩
  · rw [hψ]
    ext x
    constructor
    · intro hx
      obtain ⟨w, rfl⟩ := hfemb.isClosed_range.frontier_subset hx
      have hw := (hfrf w).mp hx
      refine ⟨((⟨w.1, mem_sphere_zero_iff_norm.mpr hw⟩, w.2),
        ⟨0, left_mem_Icc.2 zero_le_one⟩), rfl, ?_⟩
      change Ψ _ = Ψ _
      congr 1
      refine Prod.ext (Subtype.ext ?_) rfl
      change (r + (0 : ℝ) * (1 - r)) • (w.1 : EuclideanSpace ℝ (Fin 2)) =
        r • (w.1 : EuclideanSpace ℝ (Fin 2))
      rw [zero_mul, add_zero]
    · rintro ⟨⟨⟨u, θ⟩, s⟩, hs, rfl⟩
      have hs' : (s : ℝ) = 0 := hs
      have heq : g ((u, θ), s) = f (⟨u, Metric.sphere_subset_closedBall u.2⟩, θ) := by
        change Ψ _ = Ψ _
        congr 1
        refine Prod.ext (Subtype.ext ?_) rfl
        change (r + (s : ℝ) * (1 - r)) • (u : EuclideanSpace ℝ (Fin 2)) =
          r • (u : EuclideanSpace ℝ (Fin 2))
        rw [hs', zero_mul, add_zero]
      rw [heq]
      exact (hfrf _).mpr (mem_sphere_zero_iff_norm.mp u.2)
  · rw [hψ]
    have hone : r + (1 : ℝ) * (1 - r) = 1 := by ring
    ext x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := hYΨ x (hYcl.frontier_subset hx)
      have hz := (hfrY z).mp hx
      refine ⟨((⟨z.1, mem_sphere_zero_iff_norm.mpr hz⟩, z.2),
        ⟨1, right_mem_Icc.2 zero_le_one⟩), rfl, ?_⟩
      change Ψ _ = Ψ z
      congr 1
      refine Prod.ext (Subtype.ext ?_) rfl
      change (r + (1 : ℝ) * (1 - r)) • (z.1 : EuclideanSpace ℝ (Fin 2)) = z.1
      rw [hone, one_smul]
    · rintro ⟨⟨⟨u, θ⟩, s⟩, hs, rfl⟩
      have hs' : (s : ℝ) = 1 := hs
      refine (hfrY _).mpr ?_
      change ‖(r + (s : ℝ) * (1 - r)) • (u : EuclideanSpace ℝ (Fin 2))‖ = 1
      rw [hs', hone, one_smul]
      exact mem_sphere_zero_iff_norm.mp u.2

theorem exists_innerSolidTorus_toroidalShell_of_annulusImage
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))} {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {N : Set (EuclideanSpace ℝ (Fin 3))} {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hc : IsRevolvedTorusChain P D Dint J A S T) (hN : N = ⋃ j, S j)
    (hh : IsEmbedding (N.domRestrict h)) (j : Fin 3) :
    ∃ S₁ : Set (EuclideanSpace ℝ (Fin 3)), IsTopologicalSolidTorus S₁ ∧
      h '' A j ⊆ interior S₁ ∧ S₁ ⊆ interior (h '' S j) ∧
      IsToroidalShell (closure (h '' S j \ S₁)) (frontier S₁) (frontier (h '' S j)) := by
  have hSN : S j ⊆ N := by
    rw [hN]
    exact subset_iUnion S j
  have hemb : IsEmbedding ((S j).domRestrict h) := hh.comp (IsEmbedding.inclusion hSN)
  let e : S j ≃ₜ h '' S j :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr (range_domRestrict h (S j)))
  obtain ⟨φ₀⟩ := hc.isSolidTorus j
  have hA : IsCompact (h '' A j) := by
    have hseg : IsCompact (A j) := by
      rw [hc.annulusEq j, segment_eq_image ℝ]
      exact isCompact_revolutionOf_of_isCompact (isCompact_Icc.image (by fun_prop))
    exact hseg.image_of_continuousOn ((continuousOn_iff_continuous_domRestrict.mpr
      hemb.continuous).mono ((hc.annulusSubset j).trans interior_subset))
  have hAint : h '' A j ⊆ interior (h '' S j) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : x ∈ S j := interior_subset (hc.annulusSubset j hx)
    have hlt : ‖((φ₀ ⟨x, hxS⟩).1 : EuclideanSpace ℝ (Fin 2))‖ < 1 :=
      lt_of_le_of_ne (mem_closedBall_zero_iff.mp (φ₀ ⟨x, hxS⟩).1.2) fun heq =>
        notMem_interior_of_homeomorph_closedBall_prod_sphere φ₀ ⟨x, hxS⟩ heq
          (hc.annulusSubset j hx)
    have hmem := mem_interior_of_homeomorph_closedBall_prod_sphere (e.symm.trans φ₀)
      (φ₀ ⟨x, hxS⟩).1 (φ₀ ⟨x, hxS⟩).2 hlt
    rw [Prod.mk.eta, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
      φ₀.symm_apply_apply] at hmem
    exact hmem
  exact IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior
    ⟨e.symm.trans φ₀⟩ hA hAint

end DifferentialGeometry.Topology.PiecewiseLinear
