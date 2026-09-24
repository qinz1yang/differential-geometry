import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusReversal

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.isPLAnnulusWithEnds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} {X : Set (EuclideanSpace ℝ (Fin 3))}
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hJ : IsPLSphere 1 J)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) X) :
    IsPLAnnulusWithEnds X (ρ '' (J ×ˢ {0})) (ρ '' (J ×ˢ {1})) := by
  let J₀ := ρ '' (J ×ˢ {0})
  let η := fun x : E => ρ (x, 0)
  have hη : IsPLHomeomorphOn η J J₀ :=
    (hJ.isPolyhedron.isPLHomeomorphOn_prod_const 0).trans
      (hρ.restrict (hJ.isPolyhedron.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (prod_mono_right (singleton_subset_iff.mpr (by norm_num))))
  let ψ := ρ ∘ Prod.map (Function.invFunOn η J) id
  have hψ : IsPLHomeomorphOn ψ (J₀ ×ˢ Icc (0 : ℝ) 1) X :=
    (hη.symm.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ
  refine ⟨J₀, ψ, hJ.of_isPLHomeomorphOn hη, hψ, ?_, ?_⟩
  · change J₀ = (ρ ∘ Prod.map (Function.invFunOn η J) id) '' (J₀ ×ˢ {0})
    rw [image_comp, prodMap_image_prod, hη.symm.image_eq, image_id]
  · change ρ '' (J ×ˢ {1}) = (ρ ∘ Prod.map (Function.invFunOn η J) id) '' (J₀ ×ˢ {1})
    rw [image_comp, prodMap_image_prod, hη.symm.image_eq, image_id]

theorem IsPLAnnulusWithEnds.union_two_rim_annuli
    {X Y₀ Y₁ J₀ J₁ K₀ K₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁)
    (hY₀ : IsPLAnnulusWithEnds Y₀ J₀ K₀) (hY₁ : IsPLAnnulusWithEnds Y₁ J₁ K₁)
    (hXY₀ : X ∩ Y₀ = J₀) (hXY₁ : X ∩ Y₁ = J₁) (hdis : Disjoint Y₀ Y₁) :
    IsPLAnnulusWithEnds (X ∪ (Y₀ ∪ Y₁)) K₀ K₁ := by
  have hfirst := hY₀.symm.union hX (inter_comm _ _ ▸ hXY₀)
  have hsecond : (Y₀ ∪ X) ∩ Y₁ = J₁ := by
    rw [union_inter_distrib_right, hdis.inter_eq, empty_union, hXY₁]
  have hall := hfirst.union hY₁ hsecond
  simpa only [union_assoc, union_comm Y₀ X, union_left_comm Y₀ X Y₁] using hall

theorem IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {P B : Set E}
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsCylindricalDiagram f P C)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) B) (hBP : B ⊆ P) :
    IsPLAnnulusWithEnds (f '' (B ×ˢ Icc (0 : ℝ) 1))
      (f '' ({γ 0} ×ˢ Icc (0 : ℝ) 1)) (f '' ({γ 1} ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨ρ, hρ, hzero, hone⟩ := hf.exists_annulus_chart_of_base_arc hends hγ hBP
  simpa only [hzero, hone] using hρ.isPLAnnulusWithEnds
    ⟨id, isPolyhedron_stdSimplexBoundary_two.isPLHomeomorphOn_id⟩

theorem IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {P : Set E}
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsCylindricalDiagram f P C)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {v : E} (hv : v ≠ 0)
    {d : ℝ} (hd : 0 < d) (hBP : (fun r : ℝ => r • v) '' Icc 0 d ⊆ P) :
    IsPLAnnulusWithEnds (f '' (((fun r : ℝ => r • v) '' Icc 0 d) ×ˢ Icc (0 : ℝ) 1))
      (f '' ({0} ×ˢ Icc (0 : ℝ) 1)) (f '' ({d • v} ×ˢ Icc (0 : ℝ) 1)) := by
  have hδ : IsPLHomeomorphOn (fun r : ℝ => r • v) (Icc 0 d)
      ((fun r : ℝ => r • v) '' Icc 0 d) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v).toAffineMap isHPolytope_Icc)
      (smul_left_injective ℝ hv).injOn.bijOn_image
  have hγ := (isPLHomeomorphOn_mul_add_Icc hd
    (show d * 0 + 0 = 0 by ring) (show d * 1 + 0 = d by ring)).trans hδ
  simpa only [Function.comp_apply, mul_zero, zero_add, zero_smul, mul_one, add_zero] using
    hf.isPLAnnulusWithEnds_base_arc hends hγ hBP

theorem IsPLAnnulusWithEnds.rims_subset {X J₀ J₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) : J₀ ⊆ X ∧ J₁ ⊆ X := by
  obtain ⟨J, ρ, -, hρ, rfl, rfl⟩ := hX
  exact ⟨(image_mono (prod_mono_right (singleton_subset_iff.mpr (by norm_num)))).trans
    hρ.image_eq.subset,
    (image_mono (prod_mono_right (singleton_subset_iff.mpr (by norm_num)))).trans
      hρ.image_eq.subset⟩

theorem IsPLAnnulusWithEnds.union_two_external_annuli
    {X R Y₀ Y₁ J₀ J₁ K₀ K₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) (hXR : X ⊆ R)
    (hY₀ : IsPLAnnulusWithEnds Y₀ J₀ K₀) (hY₁ : IsPLAnnulusWithEnds Y₁ J₁ K₁)
    (hY₀R : Y₀ ∩ R = J₀) (hY₁R : Y₁ ∩ R = J₁) (hdis : Disjoint Y₀ Y₁) :
    IsPLAnnulusWithEnds (X ∪ (Y₀ ∪ Y₁)) K₀ K₁ := by
  have h₀ : X ∩ Y₀ = J₀ := Subset.antisymm
    (fun _ h => hY₀R.subset ⟨h.2, hXR h.1⟩)
    (fun _ h => ⟨hX.rims_subset.1 h, (hY₀R.symm.subset h).1⟩)
  have h₁ : X ∩ Y₁ = J₁ := Subset.antisymm
    (fun _ h => hY₁R.subset ⟨h.2, hXR h.1⟩)
    (fun _ h => ⟨hX.rims_subset.2 h, (hY₁R.symm.subset h).1⟩)
  exact hX.union_two_rim_annuli hY₀ hY₁ h₀ h₁ hdis

end DifferentialGeometry.Topology.PiecewiseLinear
