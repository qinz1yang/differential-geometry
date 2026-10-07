/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Strata

noncomputable section

open Set
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Pointwise

namespace DifferentialGeometry.ElementaryEnds

open Hyperbolic HyperbolicAction HyperbolicBoundary
open ElementaryGroups BoundaryFixedPoints BoundaryStabilizer BusemannCocycle
open OrbifoldStrata

variable {n : ℕ}

def HasEnds (hn : 1 ≤ n) (D : Subgroup (PO n 1)) (S : Set (BoundaryH n)) : Prop :=
  (∃ ξ : BoundaryH n, S = {ξ} ∧
    ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1) ∨
  (∃ ξ η : BoundaryH n, ξ ≠ η ∧ S = {ξ, η} ∧
    ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (g : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))

theorem HasEnds.mono {hn : 1 ≤ n} {D E : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn E S) (hle : D ≤ E) : HasEnds hn D S := by
  rcases h with ⟨ξ, hS, hξ⟩ | ⟨ξ, η, hne, hS, hpair⟩
  · exact Or.inl ⟨ξ, hS, fun g => hξ ⟨g, hle g.property⟩⟩
  · exact Or.inr ⟨ξ, η, hne, hS, fun g => hpair ⟨g, hle g.property⟩⟩

theorem HasEnds.finite {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) : S.Finite := by
  rcases h with ⟨ξ, rfl, _⟩ | ⟨ξ, η, _, rfl, _⟩
  · exact finite_singleton ξ
  · exact (finite_singleton η).insert ξ

theorem HasEnds.nonempty {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) : S.Nonempty := by
  rcases h with ⟨ξ, rfl, _⟩ | ⟨ξ, η, _, rfl, _⟩
  · exact singleton_nonempty ξ
  · exact ⟨ξ, mem_insert ξ _⟩

theorem HasEnds.ncard_le_two {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) : S.ncard ≤ 2 := by
  rcases h with ⟨ξ, rfl, _⟩ | ⟨ξ, η, hne, rfl, _⟩
  · simp
  · exact (ncard_pair hne).le

theorem HasEnds.invariant {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) (g : D) {ξ : BoundaryH n}
    (hξ : ξ ∈ S) : (poBoundaryMulAction hn).smul (g : PO n 1) ξ ∈ S := by
  rcases h with ⟨η, rfl, hη⟩ | ⟨u, v, _, rfl, hpair⟩
  · rw [mem_singleton_iff.mp hξ, (hη g).1]
    exact mem_singleton _
  · rcases hξ with rfl | hξ
    · exact (hpair g).1
    · rw [mem_singleton_iff.mp hξ]
      exact (hpair g).2

theorem exists_ends (hn : 1 ≤ n) (D : Subgroup (PO n 1)) [Infinite D]
    (hgeom : ElementaryGeometry hn D) : ∃ S : Set (BoundaryH n), HasEnds hn D S := by
  rcases hgeom with ⟨hfinite, _⟩ | ⟨ξ, η, hne, hpair⟩ | ⟨ξ, hξ⟩
  · exact hfinite.false.elim
  · exact ⟨{ξ, η}, Or.inr ⟨ξ, η, hne, rfl, hpair⟩⟩
  · exact ⟨{ξ}, Or.inl ⟨ξ, rfl, hξ⟩⟩

theorem finite_of_horospherical_two_fixed (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) {ξ η : BoundaryH n} (hne : ξ ≠ η)
    (hξ : ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1)
    (hη : ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) η = η) : Finite D :=
  (fixedLocus_nonempty_iff_finite hn D hD).mp
    ⟨boundaryPairPoint ξ η hne, fun g =>
      smul_boundaryPairPoint_of_two_fixed_scale_one hn g hne (hξ g).1 (hη g) (hξ g).2⟩

theorem finite_of_horospherical_pair (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) (ξ u v : BoundaryH n) (huv : u ≠ v)
    (hξ : ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1)
    (hp : ∀ g : D,
      (poBoundaryMulAction hn).smul (g : PO n 1) u ∈ ({u, v} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (g : PO n 1) v ∈ ({u, v} : Set (BoundaryH n))) :
    Finite D := by
  let := poBoundaryMulAction hn
  have endpoint (u v : BoundaryH n) (hne : u ≠ v)
      (hf : ∀ g : D, (g : PO n 1) • u = u ∧ poConfFactor hn g u = 1)
      (hv : ∀ g : D, (g : PO n 1) • v ∈ ({u, v} : Set (BoundaryH n))) :
      Finite D := by
    apply finite_of_horospherical_two_fixed hn D hD hne hf
    intro g
    rcases hv g with h | h
    · exact (hne ((MulAction.toPerm (g : PO n 1)).injective
        ((hf g).1.trans h.symm))).elim
    · exact h
  by_cases hξu : ξ = u
  · subst ξ
    exact endpoint u v huv hξ (fun g => (hp g).2)
  by_cases hξv : ξ = v
  · subst ξ
    apply endpoint v u huv.symm hξ
    intro g
    rcases (hp g).1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  let S : Set (BoundaryH n) := {u, v} ∪ {ξ}
  have hSpair : HasEnds hn D {u, v} := Or.inr ⟨u, v, huv, rfl, hp⟩
  have hSsingle : HasEnds hn D {ξ} := Or.inl ⟨ξ, rfl, hξ⟩
  apply finite_of_finite_invariant_boundary_set_three hn D hD
    (hSpair.finite.union hSsingle.finite)
    (fun g _ h => h.elim (fun h => Or.inl (hSpair.invariant g h))
      (fun h => Or.inr (hSsingle.invariant g h)))
    (show u ∈ S by simp [S]) (show v ∈ S by simp [S])
    (show ξ ∈ S by simp [S]) huv (Ne.symm hξu) (Ne.symm hξv)

theorem pair_eq_of_infinite (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) [Infinite D]
    {ξ η u v : BoundaryH n} (hξη : ξ ≠ η) (huv : u ≠ v)
    (hS : HasEnds hn D {ξ, η}) (hT : HasEnds hn D {u, v}) :
    ({ξ, η} : Set (BoundaryH n)) = {u, v} := by
  have subset (a b : BoundaryH n) (hne : a ≠ b) (S : Set (BoundaryH n))
      (hp : HasEnds hn D {a, b}) (hS : HasEnds hn D S) : S ⊆ {a, b} := by
    intro z hz
    by_contra hznot
    have hza : z ≠ a := fun h => hznot (h.symm ▸ mem_insert a {b})
    have hzb : z ≠ b := fun h => hznot (h.symm ▸ mem_insert_of_mem a (mem_singleton b))
    have hf := finite_of_finite_invariant_boundary_set_three hn D hD
      (hp.finite.union hS.finite)
      (fun g _ h => h.elim (fun h => Or.inl (hp.invariant g h))
        (fun h => Or.inr (hS.invariant g h)))
      (show a ∈ ({a, b} : Set (BoundaryH n)) ∪ S by simp)
      (show b ∈ ({a, b} : Set (BoundaryH n)) ∪ S by simp)
      (Or.inr hz) hne hza.symm hzb.symm
    exact hf.false
  exact Subset.antisymm (subset u v huv _ hT hS) (subset ξ η hξη _ hS hT)

theorem HasEnds.unique {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    (hD : IsDiscrete (SetLike.coe D)) [Infinite D] {S T : Set (BoundaryH n)}
    (hS : HasEnds hn D S) (hT : HasEnds hn D T) : S = T := by
  rcases hS with ⟨ξ, rfl, hξ⟩ | ⟨ξ, η, hξη, rfl, hp⟩
  · rcases hT with ⟨η, rfl, hη⟩ | ⟨u, v, huv, rfl, hq⟩
    · have he : ξ = η := by
        by_contra hne
        exact (finite_of_horospherical_two_fixed hn D hD hne hξ (fun g => (hη g).1)).false
      rw [he]
    · exact (finite_of_horospherical_pair hn D hD ξ u v huv hξ hq).false.elim
  · rcases hT with ⟨u, rfl, hu⟩ | ⟨u, v, huv, rfl, hq⟩
    · exact (finite_of_horospherical_pair hn D hD u ξ η hξη hu hp).false.elim
    · exact pair_eq_of_infinite hn D hD hξη huv
        (Or.inr ⟨ξ, η, hξη, rfl, hp⟩) (Or.inr ⟨u, v, huv, rfl, hq⟩)

theorem HasEnds.of_le {hn : 1 ≤ n} {D E : Subgroup (PO n 1)}
    (hE : IsDiscrete (SetLike.coe E)) [Infinite D] {S : Set (BoundaryH n)}
    (hD : HasEnds hn D S) (hle : D ≤ E) (hgeom : ElementaryGeometry hn E) :
    HasEnds hn E S := by
  let : Infinite E := Infinite.of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  obtain ⟨T, hT⟩ := exists_ends hn E hgeom
  have he : S = T := hD.unique (hE.mono hle) (hT.mono hle)
  rwa [he]

theorem HasEnds.horospherical {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {ξ : BoundaryH n} (h : HasEnds hn D {ξ}) :
    ∀ g : D, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1 := by
  rcases h with ⟨η, he, hη⟩ | ⟨u, v, huv, he, _⟩
  · have hξη : ξ = η := singleton_injective he
    simpa only [hξη] using hη
  · have hu : u = ξ := mem_singleton_iff.mp (he.symm ▸ mem_insert u {v})
    have hv : v = ξ := mem_singleton_iff.mp
      (he.symm ▸ mem_insert_of_mem u (mem_singleton v))
    exact (huv (hu.trans hv.symm)).elim

theorem horospherical_conj (hn : 1 ≤ n) (a g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) :
    (poBoundaryMulAction hn).smul (a * g * a⁻¹)
        ((poBoundaryMulAction hn).smul a ξ) = (poBoundaryMulAction hn).smul a ξ ∧
      poConfFactor hn (a * g * a⁻¹) ((poBoundaryMulAction hn).smul a ξ) = 1 := by
  let := poBoundaryMulAction hn
  change g • ξ = ξ at hfix
  constructor
  · change (a * g * a⁻¹) • (a • ξ) = a • ξ
    rw [mul_smul, inv_smul_smul, mul_smul, hfix]
  · have hi := poConfFactor_mul hn a⁻¹ a ξ
    rw [inv_mul_cancel, poConfFactor_one] at hi
    change poConfFactor hn (a * g * a⁻¹) (a • ξ) = 1
    rw [poConfFactor_mul, inv_smul_smul, poConfFactor_mul, hfix, hscale, one_mul]
    simpa only [mul_comm] using hi.symm

theorem HasEnds.conj {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) (a : PO n 1) :
    HasEnds hn (D.map (MulAut.conj a).toMonoidHom)
      ((fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul a ξ) '' S) := by
  let := poBoundaryMulAction hn
  rcases h with ⟨ξ, rfl, hξ⟩ | ⟨ξ, η, hne, rfl, hp⟩
  · refine Or.inl ⟨a • ξ, image_singleton, ?_⟩
    intro g
    obtain ⟨d, hd, he⟩ := g.property
    change a * d * a⁻¹ = (g : PO n 1) at he
    rw [← he]
    exact horospherical_conj hn a d ξ (hξ ⟨d, hd⟩).1 (hξ ⟨d, hd⟩).2
  · refine Or.inr ⟨a • ξ, a • η,
      fun he => hne ((MulAction.toPerm a).injective he), image_pair _ _ _, ?_⟩
    intro g
    obtain ⟨d, hd, he⟩ := g.property
    change a * d * a⁻¹ = (g : PO n 1) at he
    change (g : PO n 1) • (a • ξ) ∈ ({a • ξ, a • η} : Set (BoundaryH n)) ∧
      (g : PO n 1) • (a • η) ∈ ({a • ξ, a • η} : Set (BoundaryH n))
    rw [← he, mul_smul, inv_smul_smul, mul_smul,
      mul_smul, inv_smul_smul, mul_smul, ← image_pair]
    exact ⟨mem_image_of_mem _ (hp ⟨d, hd⟩).1, mem_image_of_mem _ (hp ⟨d, hd⟩).2⟩

def setStabilizer (hn : 1 ≤ n) (S : Set (BoundaryH n)) : Subgroup (PO n 1) :=
  letI := poBoundaryMulAction hn
  MulAction.stabilizer (PO n 1) S

theorem mem_setStabilizer (hn : 1 ≤ n) (S : Set (BoundaryH n)) (g : PO n 1) :
    g ∈ setStabilizer hn S ↔
      (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul g ξ) '' S = S := Iff.rfl

theorem HasEnds.le_setStabilizer {hn : 1 ≤ n} {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (h : HasEnds hn D S) : D ≤ setStabilizer hn S := by
  let := poBoundaryMulAction hn
  intro g hg
  rw [mem_setStabilizer]
  apply Subset.antisymm
  · rintro _ ⟨ξ, hξ, rfl⟩
    exact h.invariant ⟨g, hg⟩ hξ
  · intro ξ hξ
    exact ⟨g⁻¹ • ξ, h.invariant ⟨g⁻¹, D.inv_mem hg⟩ hξ, smul_inv_smul g ξ⟩

theorem geometry_setStabilizer (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {D : Subgroup (PO n 1)}
    {S : Set (BoundaryH n)} (hS : HasEnds hn D S) :
    ElementaryGeometry hn (Γ ⊓ setStabilizer hn S) := by
  let E := Γ ⊓ setStabilizer hn S
  obtain ⟨ξ, hξ⟩ := hS.nonempty
  have hsub : boundaryOrbit hn E ξ ⊆ S := by
    rintro _ ⟨g, rfl⟩
    have he := (mem_setStabilizer hn S (g : PO n 1)).mp g.property.2
    rw [← he]
    exact mem_image_of_mem _ hξ
  exact elementary_geometry hn E (hΓ.mono inf_le_left)
    (Or.inr ⟨ξ, hS.finite.subset hsub,
      (ncard_le_ncard hsub hS.finite).trans hS.ncard_le_two⟩)

end DifferentialGeometry.ElementaryEnds
