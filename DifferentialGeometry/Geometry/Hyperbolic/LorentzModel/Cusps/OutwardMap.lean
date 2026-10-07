import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoreBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Cusp

noncomputable section

open Set

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Busemann (horosphere)
open GC.Endpoint (Torus halfPoint halfZero)
open Geometry.Hyperbolic (CuspHalfSpace)

variable {Γ : Subgroup (PO 3 1)} {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)
  (hΓ : IsDiscrete (SetLike.coe Γ))

variable {H : Type*} [TopologicalSpace H]
  (e : (@MulAction.orbitRel.Quotient Γ (HUpper 3) _
    (EquivariantMap.subAction (Nat.le_add_left 1 2) Γ)) ≃ₜ H)
  {count : ℕ} (σ : Fin count ≃ D.centers)
  (F : ∀ ξ : D.centers, Torus ≃ₜ ((Quotient.mk
    (@MulAction.orbitRel (endStabilizer (Nat.le_add_left 1 2) Γ {Subtype.val ξ})
      (HUpper 3) _ (EquivariantMap.subAction (Nat.le_add_left 1 2)
        (endStabilizer (Nat.le_add_left 1 2) Γ {Subtype.val ξ})))) ''
          horosphere (Subtype.val ξ) (D.level ξ)))
  (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ)

def outwardCuspMap (i : Fin count) : C(CuspHalfSpace, H) where
  toFun p := e (D.horoballCylinderMap hΓ (σ i)
    (F (σ i) p.1, ⟨R (σ i) + p.2.val 0 / 2,
      add_nonneg (hR (σ i)) (div_nonneg p.2.property (by norm_num))⟩))
  continuous_toFun := by
    have hrad : Continuous (fun p : CuspHalfSpace => p.2.val 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
        (continuous_subtype_val.comp continuous_snd)
    have hdepth : Continuous (fun p : CuspHalfSpace => R (σ i) + p.2.val 0 / 2) :=
      continuous_const.add (hrad.div_const 2)
    exact e.continuous.comp ((D.horoballCylinderMap hΓ (σ i)).continuous.comp
      (((F (σ i)).continuous.comp continuous_fst).prodMk (hdepth.subtype_mk _)))

@[simp] theorem outwardCuspMap_apply (i : Fin count) (p : CuspHalfSpace) :
    D.outwardCuspMap hΓ e σ F R hR i p =
      e (D.horoballCylinderMap hΓ (σ i)
        (F (σ i) p.1, ⟨R (σ i) + p.2.val 0 / 2,
          add_nonneg (hR (σ i)) (div_nonneg p.2.property (by norm_num))⟩)) := rfl

theorem outwardCuspMap_zero (i : Fin count) (x : Torus) :
    D.outwardCuspMap hΓ e σ F R hR i (x, halfZero) =
      e (D.horoballCylinderMap hΓ (σ i) (F (σ i) x, ⟨R (σ i), hR (σ i)⟩)) := by
  apply congrArg e
  apply congrArg (D.horoballCylinderMap hΓ (σ i))
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change R (σ i) + 0 / 2 = R (σ i)
    ring

theorem range_outwardCuspMap (i : Fin count) :
    range (D.outwardCuspMap hΓ e σ F R hR i) =
      e '' ((D.horoballCylinderMap hΓ (σ i)) '' {p | R (σ i) ≤ p.2.val}) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
    change R (σ i) ≤ R (σ i) + p.2.val 0 / 2
    linarith [p.2.property]
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    change R (σ i) ≤ p.2.val at hp
    refine ⟨((F (σ i)).symm p.1,
      halfPoint (2 * (p.2.val - R (σ i)))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hp))), ?_⟩
    apply congrArg e
    apply congrArg (D.horoballCylinderMap hΓ (σ i))
    apply Prod.ext
    · exact (F (σ i)).apply_symm_apply p.1
    · apply Subtype.ext
      change R (σ i) + (2 * (p.2.val - R (σ i))) / 2 = p.2.val
      ring

theorem pairwise_disjoint_range_outwardCuspMap :
    Pairwise fun i j : Fin count => Disjoint
      (range (D.outwardCuspMap hΓ e σ F R hR i))
      (range (D.outwardCuspMap hΓ e σ F R hR j)) := by
  intro i j hij
  rw [D.range_outwardCuspMap hΓ e σ F R hR i,
    D.range_outwardCuspMap hΓ e σ F R hR j]
  apply disjoint_image_of_injective e.injective
  exact (D.pairwise_disjoint_range_horoballCylinderMap hΓ
    (fun h => hij (σ.injective h))).mono (image_subset_range _ _) (image_subset_range _ _)

theorem outwardCuspMap_mem_core_iff (i : Fin count) (p : CuspHalfSpace) :
    D.outwardCuspMap hΓ e σ F R hR i p ∈
      e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R ↔
        p.2.val 0 = 0 := by
  rw [D.outwardCuspMap_apply, e.injective.mem_set_image,
    Topology.mem_cylindricalCore_image_iff
      (fun ξ => D.horoballCylinderMap hΓ ξ)
      (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
      (D.pairwise_disjoint_range_horoballCylinderMap hΓ)]
  change R (σ i) + p.2.val 0 / 2 ≤ R (σ i) ↔ p.2.val 0 = 0
  constructor
  · intro h
    linarith [p.2.property]
  · intro h
    rw [h]
    simp

theorem core_inter_range_outwardCuspMap (i : Fin count) :
    (e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R) ∩
      range (D.outwardCuspMap hΓ e σ F R hR i) =
        range (fun x : Torus => D.outwardCuspMap hΓ e σ F R hR i (x, halfZero)) := by
  ext y
  constructor
  · rintro ⟨hy, p, rfl⟩
    have hz := (D.outwardCuspMap_mem_core_iff hΓ e σ F R hR i p).mp hy
    refine ⟨p.1, ?_⟩
    apply congrArg e
    apply congrArg (D.horoballCylinderMap hΓ (σ i))
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change R (σ i) + 0 / 2 = R (σ i) + p.2.val 0 / 2
      rw [hz]
  · rintro ⟨x, rfl⟩
    exact ⟨(D.outwardCuspMap_mem_core_iff hΓ e σ F R hR i (x, halfZero)).mpr rfl,
      ⟨(x, halfZero), rfl⟩⟩

theorem core_union_range_outwardCuspMap :
    (e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R) ∪
      (⋃ i, range (D.outwardCuspMap hΓ e σ F R hR i)) = univ := by
  classical
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ e '' Topology.cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) R
  · exact Or.inl hy
  · have hx : e.symm y ∉ Topology.cylindricalCore
        (fun ξ => D.horoballCylinderMap hΓ ξ) R := by
      intro hx
      exact hy ⟨e.symm y, hx, e.apply_symm_apply y⟩
    obtain ⟨ξ, p, hp, he⟩ := mem_iUnion.mp (not_not.mp hx)
    obtain ⟨i, rfl⟩ := σ.surjective ξ
    change R (σ i) < p.2.val at hp
    refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
    rw [D.range_outwardCuspMap hΓ e σ F R hR]
    exact ⟨_, ⟨p, hp.le, rfl⟩, (congrArg e he).trans (e.apply_symm_apply y)⟩

include hR in
theorem isConnected_image_cylindricalCore :
    IsConnected (e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R) :=
  (D.isConnected_cylindricalCore hΓ R hR).image e e.continuous.continuousOn

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
