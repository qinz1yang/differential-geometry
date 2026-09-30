import DifferentialGeometry.Topology.ClosedBall.UnitDisk
import DifferentialGeometry.Topology.Sphere.SphereHigherConnectivity

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology unitInterval
open scoped ContinuousMap

def diskRadialQuotient (k : ℕ) :
    C(I × sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Disk (k + 1)) where
  toFun p := ⟨(p.1 : ℝ) • p.2.1, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.2.1,
      norm_eq_of_mem_sphere p.2, mul_one]
    exact p.1.2.2⟩
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp]
theorem diskRadialQuotient_norm (k : ℕ)
    (p : I × sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ‖(diskRadialQuotient k p : EuclideanSpace ℝ (Fin (k + 1)))‖ = p.1.1 := by
  change ‖(p.1 : ℝ) • p.2.1‖ = p.1.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.2.1,
    norm_eq_of_mem_sphere p.2, mul_one]

theorem diskRadialQuotient_surjective (k : ℕ) : Function.Surjective (diskRadialQuotient k) := by
  intro x
  by_cases hx : x.1 = 0
  · obtain ⟨s⟩ : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
    refine ⟨(0, s), Subtype.ext ?_⟩
    change (0 : ℝ) • s.1 = x.1
    simp [hx]
  · let r : I := ⟨‖x.1‖, norm_nonneg _, mem_closedBall_zero_iff.mp x.2⟩
    let s : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
      ⟨radialProj x.1, radialProj_mem_sphere hx⟩
    refine ⟨(r, s), Subtype.ext ?_⟩
    change ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) _

theorem diskRadialQuotient_isQuotientMap (k : ℕ) : IsQuotientMap (diskRadialQuotient k) :=
  .of_surjective_continuous (diskRadialQuotient_surjective k) (diskRadialQuotient k).continuous

theorem diskRadialQuotient_eq_iff {k : ℕ}
    (p q : I × sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    diskRadialQuotient k p = diskRadialQuotient k q ↔
      p.1 = q.1 ∧ (p.1 = 0 ∨ p.2 = q.2) := by
  constructor
  · intro heq
    have hr : p.1 = q.1 := Subtype.ext (by
      have h := congrArg (fun x : Disk (k + 1) => ‖x.1‖) heq
      simpa only [diskRadialQuotient_norm] using h)
    refine ⟨hr, ?_⟩
    by_cases hz : p.1 = 0
    · exact Or.inl hz
    · right
      have hne : (p.1 : ℝ) ≠ 0 := fun h => hz (Subtype.ext h)
      have heq' := congrArg Subtype.val heq
      change (p.1 : ℝ) • p.2.1 = (q.1 : ℝ) • q.2.1 at heq'
      rw [← hr] at heq'
      exact Subtype.ext (smul_right_injective _ hne heq')
  · rintro ⟨hr, hz | hs⟩
    · apply Subtype.ext
      change (p.1 : ℝ) • p.2.1 = (q.1 : ℝ) • q.2.1
      rw [← hr, hz]
      simp
    · exact congrArg (diskRadialQuotient k) (Prod.ext hr hs)

variable {Y : Type*} [TopologicalSpace Y]

theorem exists_disk_extension_of_nullhomotopic {k : ℕ}
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Y))
    (hf : f.Nullhomotopic) :
    ∃ F : C(Disk (k + 1), Y),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) := by
  obtain ⟨c, ⟨H⟩⟩ := hf
  let g : C(I × sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Y) := H.symm.toContinuousMap
  have hfactor : Function.FactorsThrough g (diskRadialQuotient k) := by
    intro p q hpq
    obtain ⟨hr, hz | hs⟩ := (diskRadialQuotient_eq_iff p q).mp hpq
    · have hp : g p = c := by
        change H.symm (p.1, p.2) = c
        rw [hz]
        exact H.symm.map_zero_left p.2
      have hq : g q = c := by
        change H.symm (q.1, q.2) = c
        rw [← hr, hz]
        exact H.symm.map_zero_left q.2
      exact hp.trans hq.symm
    · exact congrArg g (Prod.ext hr hs)
  let F := (diskRadialQuotient_isQuotientMap k).lift g hfactor
  have hF : F.comp (diskRadialQuotient k) = g :=
    (diskRadialQuotient_isQuotientMap k).lift_comp g hfactor
  refine ⟨F, fun x => ?_⟩
  have hboundary : diskRadialQuotient k (1, diskSphereHomeomorph (k + 1) x) = x.1 := by
    apply Subtype.ext
    change (1 : ℝ) • (diskSphereHomeomorph (k + 1) x).1 = x.1.1
    rw [one_smul]
    rfl
  have h := congrArg (fun a => a (1, diskSphereHomeomorph (k + 1) x)) hF
  change F (diskRadialQuotient k (1, diskSphereHomeomorph (k + 1) x)) =
    H.symm (1, diskSphereHomeomorph (k + 1) x) at h
  rw [hboundary] at h
  exact h.trans (H.symm.map_one_left _)

theorem nullhomotopic_map_of_homotopyEquiv_sphere {k n : ℕ} (hkn : k + 2 ≤ n)
    (e : Y ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Y)) : f.Nullhomotopic := by
  have h := (nullhomotopic_map_sphere_of_add_two_le hkn (e.toFun.comp f)).comp_right e.invFun
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  exact ((e.left_inv.comp (.refl f)).symm).trans hc

theorem exists_disk_extension_of_homotopyEquiv_sphere {k n : ℕ} (hkn : k + 2 ≤ n)
    (e : Y ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Y)) :
    ∃ F : C(Disk (k + 1), Y),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) :=
  exists_disk_extension_of_nullhomotopic f (nullhomotopic_map_of_homotopyEquiv_sphere hkn e f)

theorem nullhomotopic_of_disk_extension {k : ℕ}
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Y))
    (F : C(Disk (k + 1), Y))
    (hF : ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x)) :
    f.Nullhomotopic := by
  let c : Y := F ⟨0, by simp⟩
  let H := F.comp (diskRadialQuotient k)
  have hzero (s : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) : H (0, s) = c := by
    change F (diskRadialQuotient k (0, s)) = F ⟨0, _⟩
    congr 1
    exact Subtype.ext (zero_smul ℝ s.1)
  have hone (s : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) : H (1, s) = f s := by
    let x := (diskSphereHomeomorph (k + 1)).symm s
    have hq : diskRadialQuotient k (1, s) = x.1 := by
      apply Subtype.ext
      change (1 : ℝ) • s.1 = x.1.1
      rw [one_smul]
      exact (congrArg Subtype.val ((diskSphereHomeomorph (k + 1)).apply_symm_apply s)).symm
    change F (diskRadialQuotient k (1, s)) = f s
    rw [hq, hF x]
    exact congrArg f ((diskSphereHomeomorph (k + 1)).apply_symm_apply s)
  have hh : (ContinuousMap.const _ c).Homotopic f :=
    ⟨{ toContinuousMap := H, map_zero_left := hzero, map_one_left := hone }⟩
  exact ⟨c, hh.symm⟩

end DifferentialGeometry.Topology
