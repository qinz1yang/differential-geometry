import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.PlanarJordan.CutPair
import DifferentialGeometry.External.Schoenflies.FaceCyclesLand

open Set
open scoped Manifold ContDiff

noncomputable section

namespace Schoenflies

theorem isArcBetween_range_of_isEmbedding {α : unitInterval → Plane}
    (hα : Topology.IsEmbedding α) : IsArcBetween (range α) (α 0) (α 1) := by
  let f : ℝ → Plane := fun t => α (projIcc 0 1 (by norm_num) t)
  refine ⟨f, (hα.continuous.comp continuous_projIcc).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := hα.injective hxy
    simpa only [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hx,
      projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hy, Subtype.mk.injEq] using h
  · apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact mem_range_self _
    · rintro z ⟨t, rfl⟩
      exact ⟨t, t.property, by dsimp [f]; rw [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) t.property]⟩
  · simp [f]
  · simp [f]

end Schoenflies

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem isSmoothEmbedding_interval_addCircle
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {a b : ℝ} (hab : a ≠ b) (hlen : |b - a| < 1) :
    Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞
      (fun t : unitInterval => γ ((a + (b - a) * (t : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  have hlin : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => a + (b - a) * t) := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
      (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    intro t
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ (fun t : ℝ => a + (b - a) * t) t)
    have hd : HasDerivAt (fun t : ℝ => a + (b - a) * t) (b - a) t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (b - a)).const_add a
    rw [hd.hasFDerivAt.fderiv]
    intro x y hxy
    change x * (b - a) = y * (b - a) at hxy
    exact mul_right_cancel₀ (sub_ne_zero.mpr hab.symm) (by simpa using hxy)
  have hq := DifferentialGeometry.Topology.Manifold.isImmersion_of_isLocalDiffeomorph
    AddCircle.isLocalDiffeomorph_coe
  have hi := hlin.comp hq (by simp)
  have hfull := hi.comp hγ.isImmersion (by simp)
  have himm := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
    (n := ∞)).isImmersion.comp_of_boundarylessManifold_middle hfull (by simp)
  refine ⟨himm, ?_⟩
  apply Topology.IsClosedEmbedding.isEmbedding
  apply himm.contMDiff.continuous.isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  have hmem (t : unitInterval) : a + (b - a) * (t : ℝ) ∈ Ico (min a b) (min a b + 1) := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]
      have hd := (abs_lt.mp hlen).2
      constructor <;> nlinarith [t.property.1, t.property.2]
    · rw [min_eq_right h]
      have hd := (abs_lt.mp hlen).1
      constructor <;> nlinarith [t.property.1, t.property.2]
  have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem x) (hmem y)).mp (hγ.isEmbedding.injective hxy)
  have hmul : (b - a) * (x : ℝ) = (b - a) * (y : ℝ) := by linarith
  exact mul_left_cancel₀ (sub_ne_zero.mpr hab.symm) hmul

private theorem range_interval_subarc (f : ℝ → Schoenflies.Plane) (a b : ℝ) :
    range (fun t : unitInterval => f (Schoenflies.reparam a b t)) = f '' uIcc a b := by
  calc
    range (fun t : unitInterval => f (Schoenflies.reparam a b t)) =
        Schoenflies.subarc f a b '' (Icc (0 : ℝ) 1) := by
      rw [← @Subtype.range_coe ℝ (Icc (0 : ℝ) 1), ← range_comp]
      rfl
    _ = f '' uIcc a b := Schoenflies.subarc_image

private theorem exists_isCutPair_isSmoothEmbedding
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (a : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ∃ α β : unitInterval → Schoenflies.Plane,
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ α ∧
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      α 0 = γ (a : AddCircle (1 : ℝ)) ∧ α 1 = γ ((a + θ : ℝ) : AddCircle (1 : ℝ)) ∧
      β 0 = γ (a : AddCircle (1 : ℝ)) ∧ β 1 = γ ((a + θ : ℝ) : AddCircle (1 : ℝ)) ∧
      Schoenflies.IsCutPair (range γ) (γ (a : AddCircle (1 : ℝ)))
        (γ ((a + θ : ℝ) : AddCircle (1 : ℝ))) (range α) (range β) := by
  let f : ℝ → Schoenflies.Plane := fun t => γ ((a + t : ℝ) : AddCircle (1 : ℝ))
  have hf : Schoenflies.IsLoop f := by
    refine ⟨?_, ?_, ?_⟩
    · exact (hγ.contMDiff.comp (AddCircle.contMDiff_coe.comp
        (contDiff_const.add contDiff_id).contMDiff)).continuous.continuousOn
    · simp [f, AddCircle.coe_period]
    · intro x hx y hy hxy
      have hh := hγ.isEmbedding.injective hxy
      have hx' : a + x ∈ Ico a (a + 1) := by constructor <;> linarith [hx.1, hx.2]
      have hy' : a + y ∈ Ico a (a + 1) := by constructor <;> linarith [hy.1, hy.2]
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hx' hy').mp hh
      linarith
  have hrange : f '' Icc (0 : ℝ) 1 = range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact mem_range_self _
    · rintro _ ⟨z, rfl⟩
      obtain ⟨t, ht, heq⟩ := AddCircle.eq_coe_Ico (z - (a : AddCircle (1 : ℝ)))
      refine ⟨t, ⟨ht.1, ht.2.le⟩, ?_⟩
      dsimp [f]
      rw [heq, add_sub_cancel]
  let α : unitInterval → Schoenflies.Plane := fun t => f (Schoenflies.reparam 0 θ t)
  let β : unitInterval → Schoenflies.Plane := fun t => f (Schoenflies.reparam 1 θ t)
  have hα : range α = f '' Icc 0 θ := by
    rw [show α = (fun t : unitInterval => f (Schoenflies.reparam 0 θ t)) from rfl,
      range_interval_subarc, uIcc_of_le hθ.1.le]
  have hβ : range β = f '' Icc θ 1 := by
    rw [show β = (fun t : unitInterval => f (Schoenflies.reparam 1 θ t)) from rfl,
      range_interval_subarc, uIcc_of_ge hθ.2.le]
  have hαsm : Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ α := by
    have h := isSmoothEmbedding_interval_addCircle hγ (a := a) (b := a + θ)
      (by linarith [hθ.1]) (by rw [add_sub_cancel_left, abs_of_pos hθ.1]; exact hθ.2)
    convert h using 1
    funext t
    apply congrArg (fun r : ℝ => γ (r : AddCircle (1 : ℝ)))
    dsimp [Schoenflies.reparam]
    ring
  have hβsm : Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β := by
    have h := isSmoothEmbedding_interval_addCircle hγ (a := a + 1) (b := a + θ)
      (by linarith [hθ.2]) (by
        rw [show a + θ - (a + 1) = θ - 1 by ring, abs_of_neg (by linarith [hθ.2])]
        linarith [hθ.1])
    convert h using 1
    funext t
    apply congrArg (fun r : ℝ => γ (r : AddCircle (1 : ℝ)))
    dsimp [Schoenflies.reparam]
    ring
  have hfront : f '' Icc 0 0 ∪ f '' Icc θ 1 = f '' Icc θ 1 := by
    rw [Icc_self, image_singleton, hf.closes]
    exact union_eq_right.mpr (singleton_subset_iff.mpr ⟨1, ⟨hθ.2.le, le_rfl⟩, rfl⟩)
  have h0 : f 0 = γ (a : AddCircle (1 : ℝ)) := by simp [f]
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  refine ⟨α, β, hαsm, hβsm, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [α] using h0
  · simp [α, f]
  · simpa [β, hf.closes.symm] using h0
  · simp [β, f]
  · rw [hα, hβ, ← hrange, ← h0]
    refine ⟨hf.middle_IsArcBetween Schoenflies.zero_mem_I hθ' hθ.2.ne hθ.1,
      ?_, ?_, ?_⟩
    · simpa only [hf.closes] using (hf.back_IsArcBetween hθ' hθ.2.ne hθ.1).reverse
    · simpa only [hfront] using (Schoenflies.IsLoop.pieces_cover (f := f) Schoenflies.zero_mem_I hθ')
    · simpa only [hfront] using (hf.pieces_meet_at_ends Schoenflies.zero_mem_I hθ'
        (by norm_num) hθ.2.ne hθ.1)

theorem exists_isSmoothEmbedding_complementary_arc
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ range γ) :
    ∃ β : unitInterval → Schoenflies.Plane,
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      β 0 = p ∧ β 1 = q ∧ Schoenflies.IsCutPair (range γ) p q A (range β) := by
  obtain ⟨z, hz⟩ := hsub hA.left_mem
  obtain ⟨w, hw⟩ := hsub hA.right_mem
  obtain ⟨a, -, ha⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨θ, hθ, hθeq⟩ := AddCircle.eq_coe_Ico (w - z)
  have hθpos : 0 < θ := by
    apply hθ.1.lt_of_ne'
    intro hzero
    have hwz : w = z := sub_eq_zero.mp (by simpa [hzero] using hθeq.symm)
    exact hA.ne (hz.symm.trans (hwz ▸ hw))
  have hp : γ (a : AddCircle (1 : ℝ)) = p := ha ▸ hz
  have hq : γ ((a + θ : ℝ) : AddCircle (1 : ℝ)) = q := by
    rw [AddCircle.coe_add, ha, hθeq, add_sub_cancel]
    exact hw
  obtain ⟨α, β, hα, hβ, hα0, hα1, hβ0, hβ1, hcut⟩ :=
    exists_isCutPair_isSmoothEmbedding hγ a ⟨hθpos, hθ.2⟩
  simp only [hp, hq] at hα0 hα1 hβ0 hβ1 hcut
  rcases hA.eq_fst_or_eq_snd_of_subset hsub hcut with h | h
  · exact ⟨β, hβ, hβ0, hβ1, by simpa only [h] using hcut⟩
  · exact ⟨α, hα, hα0, hα1, by simpa only [h] using hcut.symm⟩

theorem exists_isSmoothEmbedding_complementary_arc_of_isEmbedding
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {α : unitInterval → Schoenflies.Plane} (hα : Topology.IsEmbedding α)
    (hsub : range α ⊆ range γ) :
    ∃ β : unitInterval → Schoenflies.Plane,
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      β 0 = α 0 ∧ β 1 = α 1 ∧
      range α ∪ range β = range γ ∧ range α ∩ range β = {α 0, α 1} := by
  obtain ⟨β, hβ, h0, h1, hcut⟩ := exists_isSmoothEmbedding_complementary_arc hγ
    (Schoenflies.isArcBetween_range_of_isEmbedding hα) hsub
  exact ⟨β, hβ, h0, h1, hcut.union_eq, hcut.inter_eq⟩

end DifferentialGeometry.Topology.PlanarJordan
