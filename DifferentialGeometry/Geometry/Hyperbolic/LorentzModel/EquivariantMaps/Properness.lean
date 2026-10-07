/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.DirichletDomain
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPartCompactness
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.BoundedTorsion
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.EquivariantProperness

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicTransitive
open LatticeCompactness

variable {n : ℕ}

theorem displacement_basepoint_le (hn : 1 ≤ n) (g : PO n 1)
    {y : HUpper n} {R : ℝ} (hy : dist y basepointH ≤ R)
    (hg : dist y ((poMulAction hn).smul g y) < 1) :
    dist ((poMulAction hn).smul g basepointH) basepointH ≤ 2 * R + 1 := by
  let := poMulAction hn
  change dist y (g • y) < 1 at hg
  calc
    dist (g • basepointH) basepointH
        ≤ dist (g • basepointH) (g • y) + dist (g • y) y + dist y basepointH :=
      (dist_triangle _ _ _).trans (add_le_add_left (dist_triangle _ _ _) _)
    _ = dist y basepointH + dist y (g • y) + dist y basepointH := by
      rw [po_dist_smul hn g basepointH y, dist_comm basepointH y, dist_comm (g • y) y]
    _ ≤ 2 * R + 1 := by linarith

theorem exists_nhds_small_powers (hn : 1 ≤ n) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set (PO n 1), V ∈ 𝓝 1 ∧
      ∀ a ∈ V, ∀ i : Fin (N + 1),
        dist basepointH ((poMulAction hn).smul (a ^ (i : ℕ)) basepointH) < ε := by
  let V : Set (PO n 1) :=
    ⋂ i : Fin (N + 1), (fun a : PO n 1 => a ^ (i : ℕ)) ⁻¹' shortDisplacement hn ε
  refine ⟨V, Filter.iInter_mem.mpr (fun i => ?_), fun a ha i => mem_iInter.mp ha i⟩
  exact (continuous_pow (i : ℕ)).continuousAt.preimage_mem_nhds
    (by simpa only [one_pow] using shortDisplacement_mem_nhds hn hε)

theorem exists_nhds_thick_preimage (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (discΛ : IsDiscrete (SetLike.coe Λ)) (f : Γ ≃* Λ)
    {Φ : HUpper n → HUpper n} (hΦ : UniformContinuous Φ)
    (heq : PseudoIsometry.IsFEquivariant f hn Φ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    ∃ U : Set (PO n 1), U ∈ 𝓝 1 ∧ ∀ g : PO n 1,
      Φ ((poMulAction hn).smul g basepointH) ∈ K → g ∈ thickSet Γ U := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (basepointH : HUpper n)
  let S : Set Λ :=
    {δ | dist ((poMulAction hn).smul (δ : PO n 1) (basepointH : HUpper n))
      basepointH ≤ 2 * R + 1}
  have hS : S.Finite := DirichletDomain.finite_setOf_coe_le hn Λ discΛ (2 * R + 1)
  let : Fintype S := hS.fintype
  let N := Fintype.card S
  obtain ⟨ε, hε, huc⟩ := Metric.uniformContinuous_iff.mp hΦ 1 zero_lt_one
  obtain ⟨U₀, hU₀, htors⟩ := BoundedTorsion.exists_po_nhds_no_bounded_torsion hn N
  obtain ⟨V, hV, hsmall⟩ := exists_nhds_small_powers hn N hε
  refine ⟨U₀ ∩ V, inter_mem hU₀ hV, fun g hg γ hγ => ?_⟩
  let a : PO n 1 := g⁻¹ * (γ : PO n 1) * g
  have ha : a ∈ U₀ ∩ V := hγ
  have hconj (i : ℕ) : a ^ i = g⁻¹ * ((γ ^ i : Γ) : PO n 1) * g := by
    simpa only [MulAut.conj_apply, inv_inv, Subgroup.coe_pow] using
      (map_pow (MulAut.conj g⁻¹) (γ : PO n 1) i).symm
  have hpS (i : Fin (N + 1)) : f (γ ^ (i : ℕ)) ∈ S := by
    have hd : dist ((poMulAction hn).smul g (basepointH : HUpper n))
        ((poMulAction hn).smul ((γ ^ (i : ℕ) : Γ) : PO n 1)
          ((poMulAction hn).smul g basepointH)) < ε := by
      rw [displacement_conj hn g _ basepointH, ← hconj]
      exact hsmall a ha.2 i
    have h := huc hd
    rw [heq (γ ^ (i : ℕ)) ((poMulAction hn).smul g basepointH)] at h
    exact displacement_basepoint_le hn _ (Metric.mem_closedBall.mp (hR hg)) h
  let p : Fin (N + 1) → S := fun i => ⟨f (γ ^ (i : ℕ)), hpS i⟩
  have hnot : ¬Function.Injective p :=
    Fintype.not_injective_of_card_lt p (by simp only [Fintype.card_fin]; omega)
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnot
  have hpow : γ ^ (i : ℕ) = γ ^ (j : ℕ) :=
    f.injective (congrArg Subtype.val hij)
  have hroot (r s : Fin (N + 1)) (hrs : (r : ℕ) < s)
      (he : γ ^ (r : ℕ) = γ ^ (s : ℕ)) : γ = 1 := by
    have hγpow : γ ^ ((s : ℕ) - r) = 1 := by
      rw [pow_sub γ hrs.le, ← he, mul_inv_cancel]
    have hapow : a ^ ((s : ℕ) - r) = 1 := by
      rw [hconj, hγpow, Subgroup.coe_one]
      group
    have ha1 : a = 1 :=
      htors a ha.1 ((s : ℕ) - r) (by omega) (by have := s.isLt; omega) hapow
    apply Subtype.ext
    change (γ : PO n 1) = 1
    calc
      (γ : PO n 1) = g * a * g⁻¹ := by dsimp [a]; group
      _ = 1 := by rw [ha1]; group
  rcases lt_or_gt_of_ne (show (i : ℕ) ≠ (j : ℕ) from fun h => hne (Fin.ext h)) with h | h
  · exact hroot i j h hpow
  · exact hroot j i h hpow.symm

theorem exists_compact_preimage_representatives (hn : 1 ≤ n)
    (Γ Λ : Subgroup (PO n 1))
    (discΓ : IsDiscrete (SetLike.coe Γ)) (discΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] (hcovΓ : covolume Γ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {Φ : HUpper n → HUpper n} (hΦ : UniformContinuous Φ)
    (heq : PseudoIsometry.IsFEquivariant f hn Φ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    ∃ D : Set (HUpper n), IsCompact D ∧ ∀ x : HUpper n, Φ x ∈ K →
      ∃ γ : Γ, (poMulAction hn).smul (γ : PO n 1) x ∈ D := by
  let := poMulAction hn
  obtain ⟨U, hU, hthick⟩ := exists_nhds_thick_preimage hn Γ Λ discΛ f hΦ heq hK
  obtain ⟨C, hC, hcover⟩ := exists_compact_cover_thick_frames hn Γ discΓ hcovΓ hU
  let p : PO n 1 → HUpper n := fun g => g • basepointH
  have hp : Continuous p :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_id.prodMk continuous_const)
  refine ⟨p '' C, hC.image hp, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := exists_po_smul_basepoint hn x
  have hg' : g • (basepointH : HUpper n) = x := hg
  obtain ⟨γ, hγ⟩ := hcover g (hthick g (by rwa [hg]))
  refine ⟨γ, (γ : PO n 1) * g, hγ, ?_⟩
  change ((γ : PO n 1) * g) • basepointH = (γ : PO n 1) • x
  rw [mul_smul, hg']

theorem isCompact_preimage (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (discΓ : IsDiscrete (SetLike.coe Γ)) (discΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] (hcovΓ : covolume Γ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {Φ : HUpper n → HUpper n} (hΦ : UniformContinuous Φ)
    (heq : PseudoIsometry.IsFEquivariant f hn Φ)
    {K : Set (HUpper n)} (hK : IsCompact K) : IsCompact (Φ ⁻¹' K) := by
  classical
  let := poMulAction hn
  obtain ⟨D, hD, hcover⟩ :=
    exists_compact_preimage_representatives hn Γ Λ discΓ discΛ hcovΓ f hΦ heq hK
  let E : Set (HUpper n) := K ∪ Φ '' D
  have hE : IsCompact E := hK.union (hD.image hΦ.continuous)
  let T : Set Λ := {δ | ∃ y ∈ E, ((δ : PO n 1) • y) ∈ E}
  have hT : T.Finite := DirichletDomain.finite_exists_smul_inter hn Λ discΛ hE
  let A : Set Γ := f ⁻¹' T
  have hA : A.Finite := hT.preimage f.injective.injOn
  let : Fintype A := hA.fintype
  let B : Set (HUpper n) :=
    ⋃ γ : A, (fun y : HUpper n => ((γ : Γ) : PO n 1)⁻¹ • y) '' D
  have hB : IsCompact B := isCompact_iUnion fun γ =>
    hD.image ((ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id))
  apply hB.of_isClosed_subset (hK.isClosed.preimage hΦ.continuous)
  intro x hx
  obtain ⟨γ, hγ⟩ := hcover x hx
  have hγA : γ ∈ A := by
    refine ⟨Φ x, Or.inl hx, Or.inr ?_⟩
    exact ⟨(γ : PO n 1) • x, hγ, heq γ x⟩
  refine mem_iUnion.mpr ⟨⟨γ, hγA⟩, (γ : PO n 1) • x, hγ, ?_⟩
  exact inv_smul_smul (γ : PO n 1) x

theorem isProperMap_of_uniformContinuous_equivariant (hn : 1 ≤ n)
    (Γ Λ : Subgroup (PO n 1))
    (discΓ : IsDiscrete (SetLike.coe Γ)) (discΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] (hcovΓ : covolume Γ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {Φ : HUpper n → HUpper n} (hΦ : UniformContinuous Φ)
    (heq : PseudoIsometry.IsFEquivariant f hn Φ) : IsProperMap Φ := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hΦ.continuous, ?_⟩
  intro K hK
  exact isCompact_preimage hn Γ Λ discΓ discΛ hcovΓ f hΦ heq hK

theorem exists_preimage_dist_bound (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (discΓ : IsDiscrete (SetLike.coe Γ)) (discΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] (hcovΓ : covolume Γ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {Φ : HUpper n → HUpper n} (hΦ : UniformContinuous Φ)
    (heq : PseudoIsometry.IsFEquivariant f hn Φ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : HUpper n, Φ x ∈ K → Φ y ∈ K → dist x y ≤ B := by
  obtain ⟨R, hR⟩ :=
    (isCompact_preimage hn Γ Λ discΓ discΛ hcovΓ f hΦ heq hK).isBounded.subset_closedBall
      (basepointH : HUpper n)
  refine ⟨2 * max R 0, mul_nonneg (by norm_num) (le_max_right _ _), fun x y hx hy => ?_⟩
  have hxR := Metric.mem_closedBall.mp (hR hx)
  have hyR := Metric.mem_closedBall.mp (hR hy)
  have hd := dist_triangle x (basepointH : HUpper n) y
  rw [dist_comm basepointH y] at hd
  linarith [le_max_left R 0]

end DifferentialGeometry.EquivariantProperness
