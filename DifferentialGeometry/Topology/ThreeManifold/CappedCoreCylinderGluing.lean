import DifferentialGeometry.Topology.ThreeManifold.CappedCoreBandGluing
import DifferentialGeometry.Topology.ThreeManifold.CapBoundaryCylinder

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S2 × unitInterval
local notation "Band" => S2 × Icc (-1 : ℝ) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def _root_.DifferentialGeometry.Topology.SphericalTubeSystem.coreCylinderBoundaryInclusion
    {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M) (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → (Σ _a : S, Cylinder) :=
  fun q => ⟨q.1, q.2.2, if q.2.1 then 1 else 0⟩

def _root_.DifferentialGeometry.Topology.SphericalTubeSystem.cylinderMap
    {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M) (a : T.Index) :
    C(Cylinder, M.Carrier) where
  toFun q := T.tube a (q.1, ⟨2 * q.2.val - 1, by
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩)
  continuous_toFun := (T.tube a).continuous.comp
    (continuous_fst.prodMk ((by fun_prop : Continuous (fun q : Cylinder => 2 * q.2.val - 1)).subtype_mk _))

theorem _root_.DifferentialGeometry.Topology.SphericalTubeSystem.contMDiff_cylinderMap
    {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M) (a : T.Index) :
    ContMDiff CI (𝓡 3) ∞ (T.cylinderMap a) := by
  let _ : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  have ht : ContMDiff CI (𝓡∂ 1) ∞ (fun q : Cylinder =>
      (⟨2 * q.2.val - 1, by constructor <;> linarith [q.2.property.1, q.2.property.2]⟩ : Icc (-2 : ℝ) 2)) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨?_, ?_⟩
    · exact (by fun_prop : Continuous (fun q : Cylinder => 2 * q.2.val - 1)).subtype_mk _
    exact (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).sub contMDiff_const
  exact (T.smooth a).contMDiff.comp (contMDiff_fst.prodMk ht)

theorem _root_.DifferentialGeometry.Topology.SphericalTubeSystem.cylinderMap_injective
    {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M) (a : T.Index) :
    Function.Injective (T.cylinderMap a) := by
  let _ : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  intro p q h
  have hh := (T.smooth a).isEmbedding.injective h
  apply Prod.ext
  · exact congrArg (fun q : S2 × Icc (-2 : ℝ) 2 => q.1) hh
  apply Subtype.ext
  have ht := congrArg (fun q : S2 × Icc (-2 : ℝ) 2 => q.2.val) hh
  change 2 * p.2.val - 1 = 2 * q.2.val - 1 at ht
  linarith

abbrev CappedCoreCylinderGluing (S : Finset T.Index) :=
  AdjunctionSpace (T.coreCylinderBoundaryInclusion S) (C.cappedCoreBandAttachingMap S)

private def cylinderBandHomeomorph : Cylinder ≃ₜ Band :=
  (Homeomorph.refl S2).prodCongr ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm)

private theorem cylinderBandHomeomorph_end (b : Bool) (z : S2) :
    cylinderBandHomeomorph (z, if b then 1 else 0) =
      (z, if b then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩) := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  cases b <;> norm_num [cylinderBandHomeomorph, Homeomorph.prodCongr,
    iccHomeoI_symm_apply_coe]

private def cylinderBandFamilyHomeomorph (S : Finset T.Index)
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder) :
    (Σ _a : S, Cylinder) ≃ₜ (Σ _a : S, Band) where
  toFun q := ⟨q.1, cylinderBandHomeomorph (Ψ q.1.val q.2)⟩
  invFun q := ⟨q.1, (Ψ q.1.val).symm (cylinderBandHomeomorph.symm q.2)⟩
  left_inv q := by cases q; simp
  right_inv q := by cases q; simp
  continuous_toFun := continuous_sigma fun a =>
    continuous_sigmaMk.comp (cylinderBandHomeomorph.continuous.comp (Ψ a.val).continuous)
  continuous_invFun := continuous_sigma fun a =>
    continuous_sigmaMk.comp ((Ψ a.val).symm.continuous.comp cylinderBandHomeomorph.symm.continuous)

private theorem cylinderBandFamilyHomeomorph_boundary (S : Finset T.Index)
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a b z, Ψ a (z, if b then 1 else 0) = (C.attaching (a, b) z, if b then 1 else 0)) :
    cylinderBandFamilyHomeomorph S Ψ ∘ T.coreCylinderBoundaryInclusion S =
      C.cappedCoreBandBoundaryInclusion S := by
  funext q
  rcases q with ⟨a, b, z⟩
  change (⟨a, cylinderBandHomeomorph (Ψ a.val (z, if b then 1 else 0))⟩ : Σ _a : S, Band) = _
  rw [hΨ, cylinderBandHomeomorph_end]
  cases b <;> rfl

private theorem coreBandMap_cylinderBandFamilyHomeomorph (S : Finset T.Index)
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder) (q : Σ _a : S, Cylinder) :
    T.coreBandMap S (cylinderBandFamilyHomeomorph S Ψ q) = T.cylinderMap q.1.val (Ψ q.1.val q.2) := by
  apply congrArg (T.tube q.1.val)
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm (Ψ q.1.val q.2).2 : Icc (-1 : ℝ) 1) : ℝ) = _
  rw [iccHomeoI_symm_apply_coe]
  ring

private def cappedCoreCylinderHomeomorphSource
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a b z, Ψ a (z, if b then 1 else 0) = (C.attaching (a, b) z, if b then 1 else 0)) :
    C.CappedCoreCylinderGluing Finset.univ ≃ₜ M.Carrier := by
  let e := cylinderBandFamilyHomeomorph Finset.univ Ψ
  let h : C.CappedCoreCylinderGluing Finset.univ ≃ₜ C.CappedCoreBandGluing Finset.univ :=
    Homeomorph.Quot.congr (e.sumCongr (Homeomorph.refl _)) (fun x y => by
      rw [← cylinderBandFamilyHomeomorph_boundary C Finset.univ Ψ hΨ]
      cases x <;> cases y <;> simp [adjunctionRel, Homeomorph.sumCongr, e.injective.eq_iff, e])
  exact h.trans C.cappedCoreBandHomeomorphSource

private theorem cappedCoreCylinderHomeomorphSource_core
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a b z, Ψ a (z, if b then 1 else 0) = (C.attaching (a, b) z, if b then 1 else 0))
    (x : T.core) :
    C.cappedCoreCylinderHomeomorphSource Ψ hΨ
      (adjunctionLower (i := T.coreCylinderBoundaryInclusion Finset.univ)
        (C.cappedCoreBandAttachingMap Finset.univ) (C.coreImageHomeomorph x)) = x.val := by
  unfold cappedCoreCylinderHomeomorphSource
  simp only [Homeomorph.trans_apply]
  exact C.cappedCoreBandHomeomorphSource_core x

private theorem cappedCoreCylinderHomeomorphSource_cylinder
    (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder)
    (hΨ : ∀ a b z, Ψ a (z, if b then 1 else 0) = (C.attaching (a, b) z, if b then 1 else 0))
    (q : Σ _a : (Finset.univ : Finset T.Index), Cylinder) :
    C.cappedCoreCylinderHomeomorphSource Ψ hΨ
      (adjunctionCell (T.coreCylinderBoundaryInclusion Finset.univ)
        (C.cappedCoreBandAttachingMap Finset.univ) q) = T.cylinderMap q.1.val (Ψ q.1.val q.2) := by
  unfold cappedCoreCylinderHomeomorphSource
  simp only [Homeomorph.trans_apply]
  exact (C.cappedCoreBandHomeomorphSource_band
    (cylinderBandFamilyHomeomorph Finset.univ Ψ q)).trans
      (coreBandMap_cylinderBandFamilyHomeomorph Finset.univ Ψ q)

theorem exists_cappedCoreCylinder_homeomorph_source :
    ∃ Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder,
      (∀ a p, (Ψ a p).2 = p.2) ∧
      (∀ a (t : unitInterval), t.val ≤ 1 / 3 → ∀ z,
        Ψ a (z, t) = (C.attaching (a, false) z, t)) ∧
      (∀ a (t : unitInterval), 2 / 3 ≤ t.val → ∀ z,
        Ψ a (z, t) = (C.attaching (a, true) z, t)) ∧
      ∃ H : C.CappedCoreCylinderGluing Finset.univ ≃ₜ M.Carrier,
        (∀ x : T.core,
          H (adjunctionLower (i := T.coreCylinderBoundaryInclusion Finset.univ)
            (C.cappedCoreBandAttachingMap Finset.univ) (C.coreImageHomeomorph x)) = x.val) ∧
        ∀ q : Σ _a : (Finset.univ : Finset T.Index), Cylinder,
          H (adjunctionCell (T.coreCylinderBoundaryInclusion Finset.univ)
            (C.cappedCoreBandAttachingMap Finset.univ) q) = T.cylinderMap q.1.val (Ψ q.1.val q.2) := by
  choose Ψ hp hlo hhi using C.exists_cylinder_diffeomorph_attaching
  have hΨ (a : T.Index) (b : Bool) (z : S2) :
      Ψ a (z, if b then 1 else 0) = (C.attaching (a, b) z, if b then 1 else 0) := by
    cases b with
    | false => exact hlo a 0 (by norm_num) z
    | true => exact hhi a 1 (by norm_num) z
  exact ⟨Ψ, hp, hlo, hhi, C.cappedCoreCylinderHomeomorphSource Ψ hΨ,
    C.cappedCoreCylinderHomeomorphSource_core Ψ hΨ,
    C.cappedCoreCylinderHomeomorphSource_cylinder Ψ hΨ⟩

theorem cappedCoreCylinderGluing_seam (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    adjunctionCell (T.coreCylinderBoundaryInclusion S) (C.cappedCoreBandAttachingMap S)
      (T.coreCylinderBoundaryInclusion S q) =
    adjunctionLower (i := T.coreCylinderBoundaryInclusion S)
      (C.cappedCoreBandAttachingMap S) (C.cappedCoreBandAttachingMap S q) :=
  adjunction_coherence _ _ q

end DifferentialGeometry.Topology.SphericalCapping
