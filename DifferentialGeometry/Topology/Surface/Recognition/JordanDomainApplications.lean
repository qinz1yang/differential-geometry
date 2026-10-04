import DifferentialGeometry.Topology.Surface.Recognition.JordanDomainDisk
import DifferentialGeometry.Topology.Connected.DiskFaceDegree
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleApplications
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Actual round Jordan domains and compact one-dimensional bases -/

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.Surface

def unitPlaneCircle (z : Circle) : Schoenflies.Plane :=
  Complex.orthonormalBasisOneI.repr z.val

private theorem unitPlaneCircle_data : Continuous unitPlaneCircle ∧ Injective unitPlaneCircle ∧
    range unitPlaneCircle = sphere (0 : Schoenflies.Plane) 1 := by
  refine ⟨Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val,
    Complex.orthonormalBasisOneI.repr.injective.comp Subtype.val_injective, ?_⟩
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact (Complex.orthonormalBasisOneI.repr.norm_map z.val).trans (Circle.norm_coe z)
  · intro hx
    let z := Complex.orthonormalBasisOneI.repr.symm x
    have hz : ‖z‖ = 1 :=
      (Complex.orthonormalBasisOneI.repr.symm.norm_map x).trans
        (mem_sphere_zero_iff_norm.mp hx)
    exact ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩,
      Complex.orthonormalBasisOneI.repr.apply_symm_apply x⟩

private theorem round_image_data {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Schoenflies.Plane → Y} (hf : Topology.IsOpenEmbedding f) :
    IsCompact (f '' closedBall 0 1) ∧ (interior (f '' closedBall 0 1)).Nonempty ∧
      frontier (f '' closedBall 0 1) = range (f ∘ unitPlaneCircle) := by
  have hk := (isCompact_closedBall (0 : Schoenflies.Plane) 1).image hf.continuous
  refine ⟨hk, ⟨f 0, ?_⟩, ?_⟩
  · exact interior_maximal (image_mono ball_subset_closedBall)
      (hf.isOpenMap _ isOpen_ball) ⟨0, mem_ball_self zero_lt_one, rfl⟩
  · rw [range_comp, unitPlaneCircle_data.2.2]
    have hp : f ⁻¹' (f '' closedBall 0 1) = closedBall 0 1 := hf.injective.preimage_image _
    have he : f ⁻¹' frontier (f '' closedBall 0 1) = sphere 0 1 := by
      rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous, hp,
        frontier_closedBall (0 : Schoenflies.Plane) one_ne_zero]
    apply Subset.antisymm
    · intro y hy
      have hm : y ∈ f '' closedBall 0 1 := hk.isClosed.closure_eq ▸ frontier_subset_closure hy
      obtain ⟨x, hx, rfl⟩ := hm
      exact ⟨x, he ▸ hy, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      change x ∈ f ⁻¹' frontier (f '' closedBall 0 1)
      exact he.symm ▸ hx

theorem round_plane_disk_recognized :
    ∃ e : Disk 2 → Schoenflies.Plane, Topology.IsClosedEmbedding e ∧
      range e = closedBall 0 1 ∧ e '' diskSphere 2 = range unitPlaneCircle := by
  have h := round_image_data (Homeomorph.refl Schoenflies.Plane).isOpenEmbedding
  simp only [Homeomorph.refl_apply, image_id, Function.id_comp] at h
  exact exists_disk_of_jordan_frontier_plane h.1 h.2.1 unitPlaneCircle_data.1
    unitPlaneCircle_data.2.1 h.2.2

private instance sphereFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def sphereRoundCap : Set SphereTwo :=
  (stereographic' 2 sphereTwoNorth).symm '' closedBall 0 1

theorem sphere_round_cap_recognized :
    ∃ e : Disk 2 → SphereTwo, Topology.IsClosedEmbedding e ∧
      range e = sphereRoundCap ∧
      e '' diskSphere 2 = range ((stereographic' 2 sphereTwoNorth).symm ∘ unitPlaneCircle) := by
  have hf := (stereographic' 2 sphereTwoNorth).symm.isOpenEmbedding
    (stereographic'_target sphereTwoNorth)
  obtain ⟨hk, hi, hfr⟩ := round_image_data hf
  exact exists_disk_of_jordan_frontier_sphereTwo hk hi
    (hf.continuous.comp unitPlaneCircle_data.1)
    (hf.injective.comp unitPlaneCircle_data.2.1) hfr

def cylinderRoundChart (x : Schoenflies.Plane) : Circle × ℝ :=
  (Circle.exp (Real.arctan (x 0)), x 1)

private theorem cylinderRoundChart_open : Topology.IsOpenEmbedding cylinderRoundChart := by
  let g : ℝ → Circle := fun x => Circle.exp (Real.arctan x)
  have hg : Topology.IsOpenEmbedding g := by
    rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
    refine ⟨Circle.exp.continuous.comp Real.continuous_arctan, ?_, ?_⟩
    · intro x y h
      apply Real.arctan_strictMono.injective
      apply Circle.exp_injOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)
        (by linarith [Real.pi_pos])
        ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩
        ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩ h
    · have ht : IsOpenMap Real.arctan :=
        isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap.comp
          Real.tanOrderIso.symm.toHomeomorph.isOpenMap
      exact isLocalHomeomorph_circleExp.isOpenMap.comp ht
  let h : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ)
  exact (hg.prodMap (Homeomorph.refl ℝ).isOpenEmbedding).comp h.isOpenEmbedding

def cylinderRoundDisk : Set (Circle × ℝ) := cylinderRoundChart '' closedBall 0 1

theorem cylinder_round_disk_recognized :
    ∃ e : Disk 2 → Circle × ℝ, Topology.IsClosedEmbedding e ∧
      range e = cylinderRoundDisk ∧
      e '' diskSphere 2 = range (cylinderRoundChart ∘ unitPlaneCircle) := by
  obtain ⟨hk, hi, hfr⟩ := round_image_data cylinderRoundChart_open
  exact exists_disk_of_jordan_frontier_cylinder hk hi
    (cylinderRoundChart_open.continuous.comp unitPlaneCircle_data.1)
    (cylinderRoundChart_open.injective.comp unitPlaneCircle_data.2.1) hfr

theorem interval_base_boundary_degree :
    ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)).ncard = 0 ∨
      ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)).ncard = 2 :=
  Manifold.OneManifold.ncard_boundary_eq_zero_or_two

theorem interval_incidence_degree :
    (Finset.univ.filter (fun i : Fin 2 => (fun _ : Fin 2 => ()) i = ())).card = 0 ∨
      (Finset.univ.filter (fun i : Fin 2 => (fun _ : Fin 2 => ()) i = ())).card = 2 := by
  let _ := Fintype.ofFinite ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1))
  let e : {i : Fin 2 // (fun _ : Fin 2 => ()) i = ()} ≃
      (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) := Fintype.equivOfCardEq (by
    have hb : Fintype.card ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)) = 2 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact Manifold.OneManifold.ncard_boundary_Icc_of_lt
    rw [hb]
    simp)
  exact hdeg_of_boundary_equiv (fun _ : Fin 2 => ()) (fun _ : Unit => Icc (0 : ℝ) 1)
    (fun _ => e) ()

theorem interval_base_components :
    Finite (ConnectedComponents (Icc (0 : ℝ) 1)) ∧ ∀ x : Icc (0 : ℝ) 1,
      Nonempty (Manifold.OneManifold.componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨
        Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ Manifold.OneManifold.componentOpens x) :=
  Manifold.OneManifold.fdc02_base_components

theorem circle_base_classified : Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :=
  Manifold.OneManifold.nonempty_diffeomorph_circle_self

end DifferentialGeometry.Topology.Surface
