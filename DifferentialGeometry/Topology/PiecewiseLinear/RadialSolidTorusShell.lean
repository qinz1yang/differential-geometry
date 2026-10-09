/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.InnerSolidTorusToroidalShell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem smul_mem_closedBall_zero_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {v : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ ≤ 1) :
    t • v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg v]

theorem exists_radial_inner_torus_with_spine {Y : Set E3}
    (φ : Y ≃ₜ (Metric.closedBall (0 : Plane) 1 × Metric.sphere (0 : Plane) 1))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ S₁ : Set E3, IsTopologicalSolidTorus S₁ ∧ S₁ ⊆ interior Y ∧
      IsToroidalShell (closure (Y \ S₁)) (frontier S₁) (frontier Y) ∧
      (∀ z, (φ.symm z : E3) ∈ S₁ ↔ ‖(z.1 : Plane)‖ ≤ r) ∧
      IsSpine S₁ (Subtype.val '' (φ.symm '' {z | (z.1 : Plane) = 0})) := by
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
  have hsp : IsSpine (range f) (Subtype.val '' (φ.symm '' {z | (z.1 : Plane) = 0})) := by
    refine ⟨φ₁.symm, 0, ?_, ?_⟩
    · rw [interior_closedBall _ one_ne_zero]
      exact Metric.mem_ball_self zero_lt_one
    · rw [image_image, image_image]
      change (fun z => (φ.symm z : E3)) '' {z | (z.1 : Plane) = 0} =
        f '' {z | (z.1 : Plane) = 0}
      apply EqOn.image_eq
      intro z hz
      have hz' : (z.1 : Plane) = 0 := hz
      change (φ.symm z : E3) = Ψ _
      rw [← hΨ z]
      apply congrArg Ψ
      refine Prod.ext (Subtype.ext ?_) rfl
      change (z.1 : Plane) = r • (z.1 : Plane)
      rw [hz', smul_zero]
  refine ⟨range f, ⟨φ₁⟩, hS₁Y, ⟨ψ, ?_, ?_⟩, ?_, hsp⟩
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
  · intro z
    simpa only [hΨ z] using hmemS₁ z

end DifferentialGeometry.Topology.PiecewiseLinear
