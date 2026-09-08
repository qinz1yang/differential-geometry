import DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree
import DifferentialGeometry.Topology.ProjectiveSpace.Manifold

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open TopologicalSpace

namespace DifferentialGeometry

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩

instance puncturedRealProjectiveThreeSpaceChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 3)) PuncturedRealProjectiveThreeSpace :=
  inferInstanceAs (ChartedSpace (EuclideanSpace Real (Fin 3))
    (⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
      isOpen_compl_singleton⟩ : Opens RealProjectiveThreeSpace))

instance puncturedRealProjectiveThreeSpaceIsManifold :
    IsManifold (𝓡 3) ∞ PuncturedRealProjectiveThreeSpace :=
  inferInstanceAs (IsManifold (𝓡 3) ∞
    (⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
      isOpen_compl_singleton⟩ : Opens RealProjectiveThreeSpace))

instance threeSphereAwayFromRealProjectivePunctureChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 3))
      threeSphereAwayFromRealProjectivePuncture :=
  inferInstanceAs (ChartedSpace (EuclideanSpace Real (Fin 3))
    (⟨threeSphereAwayFromRealProjectivePuncture,
      isOpen_threeSphereAwayFromRealProjectivePuncture⟩ :
      Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)))

instance threeSphereAwayFromRealProjectivePunctureIsManifold :
    IsManifold (𝓡 3) ∞ threeSphereAwayFromRealProjectivePuncture :=
  inferInstanceAs (IsManifold (𝓡 3) ∞
    (⟨threeSphereAwayFromRealProjectivePuncture,
      isOpen_threeSphereAwayFromRealProjectivePuncture⟩ :
      Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)))

private theorem twoSphereProdRealToThreeSphere_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      (fun x => (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x).1) := by
  let split : EuclideanSpace Real (Fin 4) ≃L[Real]
      EuclideanSpace Real (Fin 3) × EuclideanSpace Real (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := Real) (n := 3) (m := 1)
  let v : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      EuclideanSpace Real (Fin 4) :=
    fun x => split.symm (x.1.1, WithLp.toLp 2 (fun _ => x.2))
  have hv : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      𝓘(Real, EuclideanSpace Real (Fin 4)) ∞ v := by
    apply split.symm.contDiff.contMDiff.comp
    apply ContMDiff.prodMk_space
    · exact contMDiff_coe_sphere.comp contMDiff_fst
    · have hline : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
          𝓘(Real, EuclideanSpace Real (Fin 1)) ∞
          (fun x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
            x.2 • (WithLp.toLp 2 (fun _ : Fin 1 => (1 : Real)))) :=
        contMDiff_snd.smul contMDiff_const
      apply hline.congr
      intro x
      ext i
      simp
  have hne (x) : v x ≠ 0 := by
    intro h
    have hf := congrArg (fun z => (split z).1) h
    simp only [v, ContinuousLinearEquiv.apply_symm_apply, map_zero] at hf
    exact ne_zero_of_mem_unit_sphere x.1 hf
  have hn : ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun x => ‖v x‖⁻¹) := by
    intro x
    exact ((contDiffAt_norm Real (hne x)).comp_contMDiffAt hv.contMDiffAt).inv₀
      (norm_ne_zero_iff.mpr (hne x))
  have hnrm : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      𝓘(Real, EuclideanSpace Real (Fin 4)) ∞ (fun x => ‖v x‖⁻¹ • v x) := hn.smul hv
  have hmem (x) : ‖v x‖⁻¹ • v x ∈ Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x))]
  have hs := hnrm.codRestrict_sphere (n := 3) hmem
  apply hs.congr
  intro x
  apply Subtype.ext
  change 1 • ‖v x‖⁻¹ • v x = ‖v x‖⁻¹ • v x
  rw [one_smul]

private theorem threeSphereAwayFromRealProjectivePunctureToTwoSphereProdReal_contMDiff :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(Real, Real)) ∞
      twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm := by
  let split : EuclideanSpace Real (Fin 4) ≃L[Real]
      EuclideanSpace Real (Fin 3) × EuclideanSpace Real (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := Real) (n := 3) (m := 1)
  let u : threeSphereAwayFromRealProjectivePuncture → EuclideanSpace Real (Fin 3) :=
    fun z => (split z.1.1).1
  let t : threeSphereAwayFromRealProjectivePuncture → Real :=
    fun z => (split z.1.1).2 0
  have hsphere : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : threeSphereAwayFromRealProjectivePuncture →
        Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :=
    contMDiff_subtype_val (U := ⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩)
  have hsplit := split.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp hsphere)
  have hu : ContMDiff (𝓡 3) 𝓘(Real, EuclideanSpace Real (Fin 3)) ∞ u :=
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3))
      (EuclideanSpace Real (Fin 1))).contDiff.contMDiff.comp hsplit
  have ht : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ t :=
    (PiLp.proj 2 (fun _ : Fin 1 => Real) 0).contDiff.contMDiff.comp
      ((ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3))
        (EuclideanSpace Real (Fin 1))).contDiff.contMDiff.comp hsplit)
  have hne (z) : u z ≠ 0 := by
    intro h
    have hnorm := norm_eq_of_mem_sphere
      (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm z).1
    change ‖1 • ‖u z‖⁻¹ • u z‖ = 1 at hnorm
    simp [h] at hnorm
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ (fun z => ‖u z‖⁻¹) := by
    intro z
    exact ((contDiffAt_norm Real (hne z)).comp_contMDiffAt hu.contMDiffAt).inv₀
      (norm_ne_zero_iff.mpr (hne z))
  have hmem (z) : ‖u z‖⁻¹ • u z ∈ Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne z))]
  have hy := (hn.smul hu).codRestrict_sphere (n := 2) hmem
  apply (hy.prodMk (ht.smul hn)).congr
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change 1 • ‖u z‖⁻¹ • u z = ‖u z‖⁻¹ • u z
    rw [one_smul]
  · change t z / ‖u z‖ = t z * ‖u z‖⁻¹
    exact div_eq_mul_inv _ _

noncomputable def twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
      (𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯ threeSphereAwayFromRealProjectivePuncture where
  toEquiv := twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.toEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff
      (⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩ :
        Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)) _).mp
      twoSphereProdRealToThreeSphere_contMDiff
  contMDiff_invFun := threeSphereAwayFromRealProjectivePunctureToTwoSphereProdReal_contMDiff

@[simp] theorem twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x =
      twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x := rfl

@[simp] theorem twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture_symm_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm z =
      twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm z := rfl

end DifferentialGeometry
