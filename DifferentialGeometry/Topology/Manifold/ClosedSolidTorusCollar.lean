import DifferentialGeometry.Topology.Manifold.ClosedCellPunctured
import DifferentialGeometry.Topology.Diffeomorph.LinearIsometrySphere
import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusBoundary
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] finrank_real_complex_fact'
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

private abbrev puncturedDisk : TopologicalSpace.Opens (ClosedCell 2) :=
  ⟨{x | x.val ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

private def circleToDiskSphere :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  LinearIsometryEquiv.sphereDiffeomorph (n := 1) Complex.orthonormalBasisOneI.repr

private def collarReorder :
    ((Circle × Circle) × EuclideanHalfSpace 1) ≃ₘ⟮((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1),
      ((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)⟯ ((Circle × EuclideanHalfSpace 1) × Circle) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)

private def diskPuncturedCoordinates :
    (Circle × EuclideanHalfSpace 1) ≃ₘ⟮(𝓡 1).prod (𝓡∂ 1), 𝓡∂ 2⟯
      puncturedDisk :=
  (circleToDiskSphere.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).trans
    (closedCellPuncturedDiffeomorph 1)

private def diskPuncturedPartial :
    PartialDiffeomorph ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2)
      (Circle × EuclideanHalfSpace 1) (ClosedCell 2) ∞ :=
  diskPuncturedCoordinates.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (puncturedDisk)
      ⟨⟨closedDiskBoundary 1, by
        intro h
        have hn := closedDiskBoundary_norm 1
        rw [h, norm_zero] at hn
        norm_num at hn⟩⟩)

private def fullRadialCollar :
    PartialDiffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡 1))
      ((Circle × Circle) × EuclideanHalfSpace 1) (ClosedCell 2 × Circle) ∞ :=
  collarReorder.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod diskPuncturedPartial
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph)

def closedSolidTorusRadialCollar :
    PartialDiffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡 1))
      ((Circle × Circle) × EuclideanHalfSpace 1) (ClosedCell 2 × Circle) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict fullRadialCollar
    {p | p.2.val 0 < 1}
    (isOpen_lt (by fun_prop) continuous_const)

theorem closedSolidTorusRadialCollar_apply (p : (Circle × Circle) × EuclideanHalfSpace 1) :
    (closedSolidTorusRadialCollar p).1.val =
      (1 + p.2.val 0)⁻¹ • (closedDiskBoundary p.1.1).val := rfl

theorem closedSolidTorusRadialCollar_apply_snd
    (p : (Circle × Circle) × EuclideanHalfSpace 1) :
    (closedSolidTorusRadialCollar p).2 = p.1.2 := rfl

theorem closedSolidTorusRadialCollar_source :
    closedSolidTorusRadialCollar.source = {p | p.2.val 0 < 1} := by
  ext p
  simp [closedSolidTorusRadialCollar, fullRadialCollar, diskPuncturedPartial,
    DifferentialGeometry.Topology.PartialDiffeomorph.restrict,
    DifferentialGeometry.Topology.PartialDiffeomorph.prod,
    DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal,
    Diffeomorph.toPartialDiffeomorph]

theorem closedSolidTorusRadialCollar_norm
    (p : (Circle × Circle) × EuclideanHalfSpace 1) :
    ‖(closedSolidTorusRadialCollar p).1.val‖ = (1 + p.2.val 0)⁻¹ := by
  rw [closedSolidTorusRadialCollar_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by linarith [p.2.property])),
    closedDiskBoundary_norm, mul_one]

private theorem fullRadialCollar_target :
    fullRadialCollar.target = {x | x.1.val ≠ 0} := by
  ext x
  simp [fullRadialCollar, diskPuncturedPartial, puncturedDisk,
    DifferentialGeometry.Topology.PartialDiffeomorph.prod,
    DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal,
    Diffeomorph.toPartialDiffeomorph]

theorem closedSolidTorusRadialCollar_target :
    closedSolidTorusRadialCollar.target = {x | 1 / 2 < ‖x.1.val‖} := by
  have himage : closedSolidTorusRadialCollar '' closedSolidTorusRadialCollar.source =
      closedSolidTorusRadialCollar.target :=
    closedSolidTorusRadialCollar.toOpenPartialHomeomorph.image_source_eq_target
  rw [← himage]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [closedSolidTorusRadialCollar_source] at hp
    change p.2.val 0 < 1 at hp
    change 1 / 2 < ‖(closedSolidTorusRadialCollar p).1.val‖
    rw [closedSolidTorusRadialCollar_norm]
    have hpos : 0 < 1 + p.2.val 0 := by linarith [p.2.property]
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt hpos (show 1 + p.2.val 0 < 2 by linarith))
  · intro hx
    change 1 / 2 < ‖x.1.val‖ at hx
    have hxt : x ∈ fullRadialCollar.target := by
      rw [fullRadialCollar_target]
      change x.1.val ≠ 0
      exact norm_pos_iff.mp (by linarith)
    let p := fullRadialCollar.symm x
    have he : closedSolidTorusRadialCollar p = x := fullRadialCollar.apply_symm_apply hxt
    have hn := closedSolidTorusRadialCollar_norm p
    rw [he] at hn
    refine ⟨p, ?_, he⟩
    rw [closedSolidTorusRadialCollar_source]
    change p.2.val 0 < 1
    have hpos : 0 < 1 + p.2.val 0 := by linarith [p.2.property]
    rw [hn] at hx
    have hlt : 1 + p.2.val 0 < 2 :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hpos).mp (by
        simpa only [one_div] using hx)
    linarith

theorem closedSolidTorusRadialCollar_zero (z : Circle × Circle)
    (h : EuclideanHalfSpace 1) (hh : h.val 0 = 0) :
    closedSolidTorusRadialCollar (z, h) = closedSolidTorusBoundary z := by
  apply Prod.ext
  · apply Subtype.ext
    rw [closedSolidTorusRadialCollar_apply, hh]
    simp [closedSolidTorusBoundary]
  · rfl

theorem closedSolidTorusRadialCollar_symm_height (x : ClosedCell 2 × Circle)
    (hx : 1 / 2 < ‖x.1.val‖) :
    (closedSolidTorusRadialCollar.symm x).2.val 0 = ‖x.1.val‖⁻¹ - 1 := by
  have hxt : x ∈ closedSolidTorusRadialCollar.target := by
    rw [closedSolidTorusRadialCollar_target]
    exact hx
  have hn := closedSolidTorusRadialCollar_norm (closedSolidTorusRadialCollar.symm x)
  rw [closedSolidTorusRadialCollar.apply_symm_apply hxt] at hn
  rw [hn, inv_inv]
  ring

theorem closedSolidTorusRadialCollar_symm_axial (x : ClosedCell 2 × Circle)
    (hx : 1 / 2 < ‖x.1.val‖) :
    (closedSolidTorusRadialCollar.symm x).1.2 = x.2 := by
  have hxt : x ∈ closedSolidTorusRadialCollar.target := by
    rw [closedSolidTorusRadialCollar_target]
    exact hx
  have he := congrArg Prod.snd (closedSolidTorusRadialCollar.apply_symm_apply hxt)
  simpa only [closedSolidTorusRadialCollar_apply_snd] using he

end DifferentialGeometry.Topology.Manifold
