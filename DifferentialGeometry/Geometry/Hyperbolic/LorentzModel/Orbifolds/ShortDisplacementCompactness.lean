/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Properness

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.OrbifoldCompactness

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicTransitive
open LatticeCompactness

variable {n : ℕ}

def boundedShortLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) (N : ℕ) :
    Set (HUpper n) :=
  {x | ∀ a : Fin (N + 1) → Γ,
    (∀ i, dist ((poMulAction hn).smul (a i : PO n 1) x) x < ε) →
      ¬Function.Injective a}

theorem mem_boundedShortLocus_of_finite_subgroup (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (ε : ℝ) (H : Subgroup Γ) [Finite H]
    {x : HUpper n}
    (hx : ∀ γ : Γ, dist ((poMulAction hn).smul (γ : PO n 1) x) x < ε → γ ∈ H) :
    x ∈ boundedShortLocus hn Γ ε (Nat.card H) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  intro a ha hinj
  let b : Fin (Nat.card H + 1) → H := fun i => ⟨a i, hx (a i) (ha i)⟩
  have hnot : ¬Function.Injective b :=
    Fintype.not_injective_of_card_lt b (by
      simp only [Fintype.card_fin, Nat.card_eq_fintype_card]
      omega)
  exact hnot (fun i j hij => hinj (congrArg Subtype.val hij))

theorem isClosed_boundedShortLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (N : ℕ) : IsClosed (boundedShortLocus hn Γ ε N) := by
  classical
  have he : boundedShortLocus hn Γ ε N =
      ⋂ a : Fin (N + 1) → Γ,
        {x : HUpper n |
          (∀ i, dist ((poMulAction hn).smul (a i : PO n 1) x) x < ε) →
            ¬Function.Injective a} := by
    ext x
    simp only [boundedShortLocus, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro a
  by_cases ha : Function.Injective a
  · have he' : {x : HUpper n |
          (∀ i, dist ((poMulAction hn).smul (a i : PO n 1) x) x < ε) →
            ¬Function.Injective a} =
        (⋂ i, {x : HUpper n |
          dist ((poMulAction hn).smul (a i : PO n 1) x) x < ε})ᶜ := by
      ext x
      simp only [ha, not_true_eq_false, imp_false, mem_ofPred_eq, mem_compl_iff,
        mem_iInter]
    rw [he']
    apply IsOpen.isClosed_compl
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x : HUpper n =>
        dist ((poMulAction hn).smul (a i : PO n 1) x) x) := by
      simpa only [dist_comm] using continuous_displacement hn (a i)
    exact isOpen_lt hc continuous_const
  · simp only [ha, not_false_eq_true, implies_true, ofPred_true, isClosed_univ]

theorem smul_mem_boundedShortLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (N : ℕ) {x : HUpper n} (hx : x ∈ boundedShortLocus hn Γ ε N)
    (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) x ∈ boundedShortLocus hn Γ ε N := by
  intro a ha hinj
  let b : Fin (N + 1) → Γ := fun i => δ⁻¹ * a i * δ
  have hb (i : Fin (N + 1)) :
      dist ((poMulAction hn).smul (b i : PO n 1) x) x < ε := by
    have h := ha i
    rw [dist_comm, displacement_conj, dist_comm] at h
    exact h
  apply hx b hb
  intro i j hij
  apply hinj
  apply (MulAut.conj δ⁻¹).injective
  simpa only [MulAut.conj_apply, inv_inv] using hij

theorem exists_nhds_thick_boundedShort (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ U : Set (PO n 1), U ∈ 𝓝 1 ∧ ∀ g : PO n 1,
      (poMulAction hn).smul g basepointH ∈ boundedShortLocus hn Γ ε N →
        g ∈ thickSet Γ U := by
  obtain ⟨U₀, hU₀, htors⟩ := BoundedTorsion.exists_po_nhds_no_bounded_torsion hn N
  obtain ⟨V, hV, hsmall⟩ := EquivariantProperness.exists_nhds_small_powers hn N hε
  refine ⟨U₀ ∩ V, inter_mem hU₀ hV, fun g hg γ hγ => ?_⟩
  let a : PO n 1 := g⁻¹ * (γ : PO n 1) * g
  have ha : a ∈ U₀ ∩ V := hγ
  have hconj (i : ℕ) : a ^ i = g⁻¹ * ((γ ^ i : Γ) : PO n 1) * g := by
    simpa only [MulAut.conj_apply, inv_inv, Subgroup.coe_pow] using
      (map_pow (MulAut.conj g⁻¹) (γ : PO n 1) i).symm
  have hp (i : Fin (N + 1)) :
      dist ((poMulAction hn).smul ((γ ^ (i : ℕ) : Γ) : PO n 1)
        ((poMulAction hn).smul g basepointH))
        ((poMulAction hn).smul g basepointH) < ε := by
    rw [dist_comm, displacement_conj, ← hconj]
    exact hsmall a ha.2 i
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp
    (hg (fun i : Fin (N + 1) => γ ^ (i : ℕ)) hp)
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
  · exact hroot i j h hij
  · exact hroot j i h hij.symm

theorem exists_compact_boundedShort_core (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ boundedShortLocus hn Γ ε N ∧
      ∀ x ∈ boundedShortLocus hn Γ ε N, ∃ γ : Γ,
        (poMulAction hn).smul (γ : PO n 1) x ∈ K := by
  let := poMulAction hn
  obtain ⟨U, hU, hthick⟩ := exists_nhds_thick_boundedShort hn Γ hε N
  obtain ⟨C, hC, hcover⟩ := exists_compact_cover_thick_frames hn Γ disc hcov hU
  let p : PO n 1 → HUpper n := fun g => g • basepointH
  have hp : Continuous p :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_id.prodMk continuous_const)
  refine ⟨p '' C ∩ boundedShortLocus hn Γ ε N,
    (hC.image hp).inter_right (isClosed_boundedShortLocus hn Γ ε N),
    inter_subset_right, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := exists_po_smul_basepoint hn x
  have hg' : g • (basepointH : HUpper n) = x := hg
  obtain ⟨γ, hγ⟩ := hcover g (hthick g (hg.symm ▸ hx))
  refine ⟨γ, ⟨?_, smul_mem_boundedShortLocus hn Γ ε N hx γ⟩⟩
  refine ⟨(γ : PO n 1) * g, hγ, ?_⟩
  change ((γ : PO n 1) * g) • basepointH = (γ : PO n 1) • x
  rw [mul_smul, hg']

theorem isCompact_quotient_boundedShortLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) ''
      boundedShortLocus hn Γ ε N) := by
  let := EquivariantMap.subAction hn Γ
  obtain ⟨K, hK, hKB, hcover⟩ := exists_compact_boundedShort_core hn Γ disc hcov hε N
  have he : (Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' K =
      (Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' boundedShortLocus hn Γ ε N := by
    apply Subset.antisymm (image_mono hKB)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hcover x hx
    exact ⟨(poMulAction hn).smul (γ : PO n 1) x, hγ, Quotient.sound ⟨γ, rfl⟩⟩
  rw [← he]
  exact hK.image continuous_quotient_mk'

theorem properlyDiscontinuous_subAction (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) :
    letI := EquivariantMap.subAction hn Γ
    ProperlyDiscontinuousSMul Γ (HUpper n) := by
  let := EquivariantMap.subAction hn Γ
  refine ⟨fun {K L} hK hL => ?_⟩
  apply (DirichletDomain.finite_exists_smul_inter hn Γ disc (hK.union hL)).subset
  rintro γ ⟨y, ⟨x, hx, rfl⟩, hy⟩
  exact ⟨x, Or.inl hx, Or.inr hy⟩

theorem t2Space_hyperbolic_quotient (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) :
    letI := EquivariantMap.subAction hn Γ
    T2Space (Quotient (MulAction.orbitRel Γ (HUpper n))) := by
  let := EquivariantMap.subAction hn Γ
  let := properlyDiscontinuous_subAction hn Γ disc
  let : ContinuousConstSMul Γ (HUpper n) :=
    ⟨fun γ => (ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id)⟩
  infer_instance

theorem isCompact_closure_quotient_of_compact_cover (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (disc : IsDiscrete (SetLike.coe Γ))
    {A K : Set (HUpper n)} (hK : IsCompact K)
    (hcover : ∀ x ∈ A, ∃ γ : Γ, (poMulAction hn).smul (γ : PO n 1) x ∈ K) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact (closure ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' A)) := by
  let := EquivariantMap.subAction hn Γ
  let := t2Space_hyperbolic_quotient hn Γ disc
  let q := Quotient.mk (MulAction.orbitRel Γ (HUpper n))
  have hqK : IsCompact (q '' K) := hK.image continuous_quotient_mk'
  have hsub : q '' A ⊆ q '' K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hcover x hx
    exact ⟨(poMulAction hn).smul (γ : PO n 1) x, hγ, Quotient.sound ⟨γ, rfl⟩⟩
  exact hqK.of_isClosed_subset isClosed_closure (hqK.isClosed.closure_subset_iff.mpr hsub)

end DifferentialGeometry.OrbifoldCompactness
