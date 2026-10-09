import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Defs
import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusSmooth
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology
namespace DoubleCylinder

abbrev Cylinder := SphereTwo × Icc (0 : ℝ) 1

variable (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)

def attachingMap : Bool × SphereTwo → Cylinder
  | (false, z) => (z, ⟨0, by norm_num⟩)
  | (true, z) => (f.symm z, ⟨1, by norm_num⟩)

abbrev Space := AdjunctionSpace (SelfAttachment.boundaryInclusion (n := 3)) (attachingMap f)

def core : Cylinder → Space f := adjunctionLower (attachingMap f)
def band : Cylinder → Space f := adjunctionCell SelfAttachment.boundaryInclusion (attachingMap f)

def coreToMappingTorus (p : Cylinder) : SphereMappingTorus f :=
  Quotient.mk _ (p.1, ⟨p.2.val / 2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

def bandToMappingTorus (p : Cylinder) : SphereMappingTorus f :=
  Quotient.mk _ (f.symm p.1,
    ⟨1 - p.2.val / 2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

theorem toMappingTorus_seam (q : Bool × SphereTwo) :
    bandToMappingTorus f (SelfAttachment.boundaryInclusion q) =
      coreToMappingTorus f (attachingMap f q) := by
  rcases q with ⟨b, z⟩
  cases b
  · apply Quotient.sound
    apply Relation.EqvGen.rel
    refine ⟨by norm_num [SelfAttachment.boundaryInclusion], by norm_num [attachingMap], ?_⟩
    exact (f.apply_symm_apply z).symm
  · change Quotient.mk (sphereMappingTorusSetoid f) (f.symm z, ⟨1 - 1 / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) (f.symm z, ⟨1 / 2, _⟩)
    congr 1
    exact Prod.ext rfl (Subtype.ext (by norm_num))

def toMappingTorus : Space f → SphereMappingTorus f :=
  Quot.lift (Sum.elim (bandToMappingTorus f) (coreToMappingTorus f)) (by
    rintro _ _ ⟨q, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact toMappingTorus_seam f q
    · exact (toMappingTorus_seam f q).symm)

theorem continuous_toMappingTorus : Continuous (toMappingTorus f) := by
  apply continuous_adjunction_lift
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_quotient_mk'.comp
      ((f.symm.continuous.comp continuous_fst).prodMk
        ((continuous_const.sub ((continuous_subtype_val.comp continuous_snd).div_const 2)).subtype_mk _))
  · exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (((continuous_subtype_val.comp continuous_snd).div_const 2).subtype_mk _))

private def coreClamp (p : Cylinder) : Cylinder :=
  (p.1, ⟨min 1 (2 * p.2.val), le_min (by norm_num) (by nlinarith [p.2.property.1]), min_le_left _ _⟩)

private def bandClamp (p : Cylinder) : Cylinder :=
  (f p.1, ⟨min 1 (2 - 2 * p.2.val), le_min (by norm_num) (by nlinarith [p.2.property.2]),
    min_le_left _ _⟩)

def fromRepresentative (p : Cylinder) : Space f :=
  if p.2.val ≤ 1 / 2 then core f (coreClamp p) else band f (bandClamp f p)

private theorem fromRepresentative_of_le (p : Cylinder) (hp : p.2.val ≤ 1 / 2) :
    fromRepresentative f p = core f (p.1, ⟨2 * p.2.val,
      by constructor <;> nlinarith [p.2.property.1]⟩) := by
  simp only [fromRepresentative, ite_eq_left hp, coreClamp,
    min_eq_right (by linarith : 2 * p.2.val ≤ 1)]

private theorem fromRepresentative_of_gt (p : Cylinder) (hp : 1 / 2 < p.2.val) :
    fromRepresentative f p = band f (f p.1, ⟨2 - 2 * p.2.val,
      by constructor <;> nlinarith [p.2.property.2]⟩) := by
  simp only [fromRepresentative, ite_eq_right (not_le.mpr hp), bandClamp,
    min_eq_right (by linarith : 2 - 2 * p.2.val ≤ 1)]

theorem continuous_fromRepresentative : Continuous (fromRepresentative f) := by
  have ht : Continuous (fun p : Cylinder => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous coreClamp :=
    continuous_fst.prodMk ((continuous_const.min (continuous_const.mul ht)).subtype_mk _)
  have hb : Continuous (bandClamp f) :=
    (f.continuous.comp continuous_fst).prodMk
      ((continuous_const.min (continuous_const.sub (continuous_const.mul ht))).subtype_mk _)
  apply continuous_if_le ht continuous_const
    ((continuous_adjunctionLower _ _).comp hc).continuousOn
    ((continuous_adjunctionCell _ _).comp hb).continuousOn
  intro p hp
  have hc1 : coreClamp p = (p.1, ⟨1, by norm_num⟩) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change min 1 (2 * p.2.val) = 1
    rw [hp]
    norm_num
  have hb1 : bandClamp f p = (f p.1, ⟨1, by norm_num⟩) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change min 1 (2 - 2 * p.2.val) = 1
    rw [hp]
    norm_num
  dsimp only [comp_apply]
  rw [hc1, hb1]
  have h := (adjunction_coherence SelfAttachment.boundaryInclusion (attachingMap f) (true, f p.1)).symm
  simpa only [attachingMap, SelfAttachment.boundaryInclusion, f.symm_apply_apply] using h

theorem fromRepresentative_eq_of_rel {p q : Cylinder} (h : sphereMappingTorusRel f p q) :
    fromRepresentative f p = fromRepresentative f q := by
  obtain ⟨hp, hq, hz⟩ := h
  rw [fromRepresentative_of_gt f p (by rw [hp]; norm_num),
    fromRepresentative_of_le f q (by rw [hq]; norm_num)]
  have hpa : (f p.1, (⟨2 - 2 * p.2.val, by rw [hp]; norm_num⟩ : Icc (0 : ℝ) 1)) =
      SelfAttachment.boundaryInclusion (false, f p.1) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change 2 - 2 * p.2.val = 0
    rw [hp]
    norm_num
  have hqa : (q.1, (⟨2 * q.2.val, by rw [hq]; norm_num⟩ : Icc (0 : ℝ) 1)) = attachingMap f (false, f p.1) := by
    refine Prod.ext hz (Subtype.ext ?_)
    change 2 * q.2.val = 0
    rw [hq, mul_zero]
  rw [hpa, hqa]
  exact adjunction_coherence _ _ _

def fromMappingTorus : SphereMappingTorus f → Space f :=
  Quotient.lift (fromRepresentative f) (by
    intro p q h
    induction h with
    | rel _ _ h => exact fromRepresentative_eq_of_rel f h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem continuous_fromMappingTorus : Continuous (fromMappingTorus f) :=
  Continuous.quotient_lift (continuous_fromRepresentative f) _

theorem from_to_core (p : Cylinder) : fromMappingTorus f (toMappingTorus f (core f p)) = core f p := by
  change fromRepresentative f (p.1, ⟨p.2.val / 2, _⟩) = _
  rw [fromRepresentative_of_le f _ (by dsimp; linarith [p.2.property.2])]
  congr 1
  exact Prod.ext rfl (Subtype.ext (by dsimp; ring))

theorem from_to_band (p : Cylinder) : fromMappingTorus f (toMappingTorus f (band f p)) = band f p := by
  change fromRepresentative f (f.symm p.1, ⟨1 - p.2.val / 2, _⟩) = _
  by_cases hp : p.2.val = 1
  · rw [fromRepresentative_of_le f _ (by dsimp; rw [hp]; norm_num)]
    have hq : (f.symm p.1, (⟨2 * (1 - p.2.val / 2), by rw [hp]; norm_num⟩ : Icc (0 : ℝ) 1)) =
        attachingMap f (true, p.1) := by
      refine Prod.ext (by rfl) (Subtype.ext ?_)
      change 2 * (1 - p.2.val / 2) = 1
      rw [hp]
      norm_num
    have he : SelfAttachment.boundaryInclusion (true, p.1) = p := by
      exact Prod.ext rfl (Subtype.ext hp.symm)
    rw [hq, ← he]
    exact (adjunction_coherence _ _ _).symm
  · have hplt : p.2.val < 1 := lt_of_le_of_ne p.2.property.2 hp
    rw [fromRepresentative_of_gt f _ (by dsimp; linarith), f.apply_symm_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp; ring))

theorem from_to (q : Space f) : fromMappingTorus f (toMappingTorus f q) = q := by
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl x => exact from_to_band f x
    | inr x => exact from_to_core f x

theorem to_from (q : SphereMappingTorus f) : toMappingTorus f (fromMappingTorus f q) = q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change toMappingTorus f (fromRepresentative f p) = _
    by_cases hp : p.2.val ≤ 1 / 2
    · rw [fromRepresentative_of_le f p hp]
      change Quotient.mk (sphereMappingTorusSetoid f) (p.1, ⟨(2 * p.2.val) / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) p
      congr 1
      exact Prod.ext rfl (Subtype.ext (by ring))
    · rw [fromRepresentative_of_gt f p (not_le.mp hp)]
      change Quotient.mk (sphereMappingTorusSetoid f) (f.symm (f p.1), ⟨1 - (2 - 2 * p.2.val) / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) p
      rw [f.symm_apply_apply]
      congr 1
      exact Prod.ext rfl (Subtype.ext (by ring))

def mappingTorusHomeomorph : Space f ≃ₜ SphereMappingTorus f where
  toFun := toMappingTorus f
  invFun := fromMappingTorus f
  left_inv := from_to f
  right_inv := to_from f
  continuous_toFun := continuous_toMappingTorus f
  continuous_invFun := continuous_fromMappingTorus f


private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

def seamDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4), isOpen_univ.prod isOpen_Ioo⟩

def lowerSeam (p : seamDomain) : Space f :=
  if ht : 0 ≤ p.val.2 then
    core f (p.val.1, ⟨p.val.2, ht, by linarith [p.property.2.2]⟩)
  else band f (p.val.1, ⟨-p.val.2, by constructor <;> linarith [not_le.mp ht, p.property.2.1]⟩)

def upperSeam (p : seamDomain) : Space f :=
  if ht : 0 ≤ p.val.2 then
    band f (f p.val.1, ⟨1 - p.val.2, by constructor <;> linarith [p.property.2.2]⟩)
  else core f (p.val.1, ⟨1 + p.val.2, by constructor <;> linarith [not_le.mp ht, p.property.2.1]⟩)

private def halfSeam (p : seamDomain) : sphereMappingTorusSeamDomain :=
  ⟨(p.val.1, p.val.2 / 2), mem_univ _, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

private def middleSeam (p : seamDomain) : sphereMappingTorusInteriorDomain :=
  ⟨(p.val.1, (1 + p.val.2) / 2), mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

theorem toMappingTorus_lowerSeam (p : seamDomain) :
    toMappingTorus f (lowerSeam f p) = sphereMappingTorusSeam f (halfSeam p) := by
  unfold lowerSeam
  split_ifs with ht
  · change Quotient.mk (sphereMappingTorusSetoid f) (p.val.1, ⟨p.val.2 / 2, _⟩) = _
    rw [sphereMappingTorusSeam, dite_eq_left (by change 0 ≤ p.val.2 / 2; linarith)]
    rfl
  · change Quotient.mk (sphereMappingTorusSetoid f) (f.symm p.val.1, ⟨1 - -p.val.2 / 2, _⟩) = _
    rw [sphereMappingTorusSeam, dite_eq_right (by change ¬ 0 ≤ p.val.2 / 2; linarith)]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp [halfSeam]; ring))

theorem toMappingTorus_upperSeam (p : seamDomain) :
    toMappingTorus f (upperSeam f p) = sphereMappingTorusInterior f (middleSeam p) := by
  unfold upperSeam
  split_ifs with ht
  · change Quotient.mk (sphereMappingTorusSetoid f)
      (f.symm (f p.val.1), ⟨1 - (1 - p.val.2) / 2, _⟩) = _
    rw [f.symm_apply_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp [middleSeam]; ring))
  · rfl

private def axialAffine (c : ℝ) : Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (p.1, (c + p.2) / 2)
  invFun p := (p.1, 2 * p.2 - c)
  left_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  contMDiff_toFun := contMDiff_fst.prodMk ((contMDiff_const.add contMDiff_snd).div_const 2)
  contMDiff_invFun := contMDiff_fst.prodMk ((contMDiff_const.mul contMDiff_snd).sub contMDiff_const)

theorem lowerSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
      (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (lowerSeam D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (mappingTorusHomeomorph D.target)
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open seamDomain
    ((axialAffine 0).isLocalDiffeomorph.isLocalDiffeomorphOn seamDomain)
  have hseam := sphereMappingTorusSeam_isLocalDiffeomorph D
  have hh : IsLocalDiffeomorph IC IC ∞ (halfSeam : seamDomain → sphereMappingTorusSeamDomain) := by
    intro p
    have hx := hloc p
    have hmem : ∀ q : seamDomain, (axialAffine 0) q.val ∈ sphereMappingTorusSeamDomain := by
      intro q
      change (q.val.1, (0 + q.val.2) / 2) ∈ _
      simpa only [halfSeam, zero_add] using (halfSeam q).property
    have h := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem hx
    have heq : (fun y : seamDomain => (⟨(axialAffine 0) y.val, hmem y⟩ : sphereMappingTorusSeamDomain)) =
        halfSeam := by
      funext y
      apply Subtype.ext
      change (y.val.1, (0 + y.val.2) / 2) = (y.val.1, y.val.2 / 2)
      rw [zero_add]
    rw [heq] at h
    exact h
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp hseam hh)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusSeam D.target ∘ halfSeam) = lowerSeam D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    exact (toMappingTorus_lowerSeam D.target p).symm
  rw [heq] at h
  exact h


theorem upperSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (upperSeam D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open seamDomain
    ((axialAffine 1).isLocalDiffeomorph.isLocalDiffeomorphOn seamDomain)
  have hseam := sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
    (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi)
  have hh : IsLocalDiffeomorph IC IC ∞ (middleSeam : seamDomain → sphereMappingTorusInteriorDomain) := by
    intro p
    have hx := hloc p
    have hmem : ∀ q : seamDomain, (axialAffine 1) q.val ∈ sphereMappingTorusInteriorDomain := by
      intro q
      change q.val.1 ∈ univ ∧ (1 + q.val.2) / 2 ∈ Ioo (0 : ℝ) 1
      exact (middleSeam q).property
    have h := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem hx
    have heq : (fun y : seamDomain => (⟨(axialAffine 1) y.val, hmem y⟩ : sphereMappingTorusInteriorDomain)) =
        middleSeam := by
      funext y
      exact Subtype.ext rfl
    rw [heq] at h
    exact h
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp hseam hh)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ middleSeam) = upperSeam D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    exact (toMappingTorus_upperSeam D.target p).symm
  rw [heq] at h
  exact h

end DoubleCylinder
end DifferentialGeometry.Topology
