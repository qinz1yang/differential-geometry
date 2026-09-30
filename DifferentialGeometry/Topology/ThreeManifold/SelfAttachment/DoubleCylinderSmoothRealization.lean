import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderRealization
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderInterior
import DifferentialGeometry.Topology.Manifold.CylinderCollar.DoubleSlabMatching

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.DoubleCylinder

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def slabMap (c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞) (p : Cylinder) : M :=
  c (p.1,p.2.val)

theorem continuous_slabMap (c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source) : Continuous (slabMap c) :=
  continuousOn_univ.mp (c.contMDiffOn_toFun.continuousOn.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun p _ => hc ⟨mem_univ _,p.2.property⟩))

theorem slabMap_injective (c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source) : Injective (slabMap c) := by
  intro p q h
  have heq := c.injOn (hc ⟨mem_univ _,p.2.property⟩) (hc ⟨mem_univ _,q.2.property⟩) h
  apply Prod.ext
  · exact congrArg (fun x : SphereTwo × ℝ => x.1) heq
  · exact Subtype.ext (congrArg (fun x : SphereTwo × ℝ => x.2) heq)

theorem range_slabMap (c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞) :
    range (slabMap c) = c '' (univ ×ˢ Icc (0 : ℝ) 1) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨(p.1,p.2.val),⟨mem_univ _,p.2.property⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(p.1,⟨p.2,hp.2⟩),rfl⟩

private theorem lowerSeam_zero (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (z : SphereTwo) :
    lowerSeam f ⟨(z,0),mem_univ _,by norm_num⟩ = core f (z,⟨0,by norm_num⟩) := by
  simp only [lowerSeam,le_refl,dite_eq_left]

private theorem upperSeam_zero (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (z : SphereTwo) :
    upperSeam f ⟨(z,0),mem_univ _,by norm_num⟩ = band f (f z,⟨1,by norm_num⟩) := by
  simp only [upperSeam,le_refl,dite_eq_left,sub_zero]

private theorem interior_zero_seam_cover
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (q : Space f) :
    (∃ p : Interior, interiorCore f p = q) ∨
      (∃ p : Interior, interiorBand f p = q) ∨
      (∃ z : SphereTwo, lowerSeam f ⟨(z,0),mem_univ _,by norm_num⟩ = q) ∨
      ∃ z : SphereTwo, upperSeam f ⟨(z,0),mem_univ _,by norm_num⟩ = q := by
  induction q using Quot.inductionOn with
  | h q =>
    cases q with
    | inl p =>
      by_cases hz : p.2.val = 0
      · right; right; left
        refine ⟨p.1,?_⟩
        rw [lowerSeam_zero]
        have hp : p = (p.1,⟨0,by norm_num⟩) := by
          apply Prod.ext
          · rfl
          · exact Subtype.ext hz
        rw [hp]
        exact (adjunction_coherence SelfAttachment.boundaryInclusion (attachingMap f) (false,p.1)).symm
      · by_cases ho : p.2.val = 1
        · right; right; right
          refine ⟨f.symm p.1,?_⟩
          rw [upperSeam_zero,f.apply_symm_apply]
          apply congrArg (band f)
          apply Prod.ext
          · rfl
          · exact Subtype.ext ho.symm
        · right; left
          exact ⟨⟨(p.1,p.2.val),mem_univ _,lt_of_le_of_ne p.2.property.1 (Ne.symm hz),
            lt_of_le_of_ne p.2.property.2 ho⟩,rfl⟩
    | inr p =>
      by_cases hz : p.2.val = 0
      · right; right; left
        refine ⟨p.1,?_⟩
        rw [lowerSeam_zero]
        apply congrArg (core f)
        apply Prod.ext
        · rfl
        · exact Subtype.ext hz.symm
      · by_cases ho : p.2.val = 1
        · right; right; right
          refine ⟨p.1,?_⟩
          rw [upperSeam_zero]
          have hh := adjunction_coherence SelfAttachment.boundaryInclusion (attachingMap f) (true,f p.1)
          change band f (f p.1,⟨1,by norm_num⟩) = core f (f.symm (f p.1),⟨1,by norm_num⟩) at hh
          rw [f.symm_apply_apply] at hh
          refine hh.trans ?_
          apply congrArg (core f)
          apply Prod.ext
          · rfl
          · exact Subtype.ext ho.symm
        · left
          exact ⟨⟨(p.1,p.2.val),mem_univ _,lt_of_le_of_ne p.2.property.1 (Ne.symm hz),
            lt_of_le_of_ne p.2.property.2 ho⟩,rfl⟩

theorem isLocalDiffeomorph_ambient_of_collar_equations
    (J : SphereMappingTorusIsotopy)
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (a c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (hlo : ∀ z : SphereTwo, (a : SphereTwo × ℝ → M) =ᶠ[𝓝 (z,0)] (fun q => c (q.1,-q.2)))
    (hhi : ∀ z : SphereTwo, (a : SphereTwo × ℝ → M) =ᶠ[𝓝 (z,1)] (fun q => c (J.target.symm q.1,2-q.2)))
    (H₀ : Space J.target ≃ₜ M)
    (hband : ∀ p : Cylinder, H₀ (band J.target p) = slabMap a p)
    (hcore : ∀ p : Cylinder, H₀ (core J.target p) = slabMap c p) :
    let _ := sphereMappingTorusChartedSpace J.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph J.target)
    IsLocalDiffeomorph IC I ∞ H₀ := by
  let _ := sphereMappingTorusChartedSpace J.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph J.target)
  have hci : IsLocalDiffeomorph IC I ∞ (H₀ ∘ interiorCore J.target) := by
    have hh : IsLocalDiffeomorph IC I ∞ (fun p : Interior => c p.val) :=
      DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior (fun p =>
        c.isLocalDiffeomorphAt _ _ ∞ (hc ⟨mem_univ _,p.property.2.1.le,p.property.2.2.le⟩))
    have heq : H₀ ∘ interiorCore J.target = (fun p : Interior => c p.val) := by
      funext p
      exact hcore _
    exact heq ▸ hh
  have hai : IsLocalDiffeomorph IC I ∞ (H₀ ∘ interiorBand J.target) := by
    have hh : IsLocalDiffeomorph IC I ∞ (fun p : Interior => a p.val) :=
      DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior (fun p =>
        a.isLocalDiffeomorphAt _ _ ∞ (ha ⟨mem_univ _,p.property.2.1.le,p.property.2.2.le⟩))
    have heq : H₀ ∘ interiorBand J.target = (fun p : Interior => a p.val) := by
      funext p
      exact hband _
    exact heq ▸ hh
  have hls (z : SphereTwo) : IsLocalDiffeomorphAt IC I ∞ (H₀ ∘ lowerSeam J.target)
      (⟨(z,0),mem_univ _,by norm_num⟩ : seamDomain) := by
    let p₀ : seamDomain := ⟨(z,0),mem_univ _,by norm_num⟩
    have hlocal : IsLocalDiffeomorphAt IC I ∞ (fun p : seamDomain => c p.val) p₀ :=
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val seamDomain p₀).comp I M
        (c.isLocalDiffeomorphAt _ _ ∞ (hc ⟨mem_univ _,by constructor <;> norm_num⟩))
    have ht : Tendsto (fun p : seamDomain => (p.val.1,-p.val.2)) (𝓝 p₀) (𝓝 (z,0)) := by
      have hh : Continuous (fun p : seamDomain => (p.val.1,-p.val.2)) :=
        (continuous_fst.comp continuous_subtype_val).prodMk (continuous_snd.comp continuous_subtype_val).neg
      simpa only [p₀,neg_zero] using hh.tendsto p₀
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hlocal
    filter_upwards [(hlo z).comp_tendsto ht] with p hp
    change H₀ (lowerSeam J.target p) = c p.val
    unfold lowerSeam
    split_ifs with h
    · exact hcore _
    · rw [hband]
      change a (p.val.1,-p.val.2) = c p.val
      change a (p.val.1,-p.val.2) = c (p.val.1,- -p.val.2) at hp
      simpa only [neg_neg,Prod.mk.eta] using hp
  have hus (z : SphereTwo) : IsLocalDiffeomorphAt IC I ∞ (H₀ ∘ upperSeam J.target)
      (⟨(z,0),mem_univ _,by norm_num⟩ : seamDomain) := by
    let p₀ : seamDomain := ⟨(z,0),mem_univ _,by norm_num⟩
    let T : (SphereTwo × ℝ) ≃ₘ⟮IC,IC⟯ (SphereTwo × ℝ) :=
      Diffeomorph.fiberwiseAffine (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
        contMDiff_const contMDiff_const (fun _ => one_ne_zero)
    have hT (q : SphereTwo × ℝ) : T q = (q.1,1+q.2) := by
      change (q.1,1+1*q.2) = _
      rw [one_mul]
    have hlocT := (DifferentialGeometry.isLocalDiffeomorph_subtype_val seamDomain p₀).comp IC (SphereTwo × ℝ)
      (T.isLocalDiffeomorph p₀.val)
    have hmem : T p₀.val ∈ c.source := by
      rw [hT]
      exact hc ⟨mem_univ _,by constructor <;> norm_num [p₀]⟩
    have hlocal := hlocT.comp I M (c.isLocalDiffeomorphAt _ _ ∞ hmem)
    have ht : Tendsto (fun p : seamDomain => (J.target p.val.1,1-p.val.2))
        (𝓝 p₀) (𝓝 (J.target z,1)) := by
      have hh : Continuous (fun p : seamDomain => (J.target p.val.1,1-p.val.2)) :=
        (J.target.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_const.sub (continuous_snd.comp continuous_subtype_val))
      simpa only [p₀,sub_zero] using hh.tendsto p₀
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hlocal
    filter_upwards [(hhi (J.target z)).comp_tendsto ht] with p hp
    change H₀ (upperSeam J.target p) = c (T p.val)
    rw [hT]
    unfold upperSeam
    split_ifs with h
    · rw [hband]
      change a (J.target p.val.1,1-p.val.2) = _
      change a (J.target p.val.1,1-p.val.2) = c (J.target.symm (J.target p.val.1),2-(1-p.val.2)) at hp
      rw [J.target.symm_apply_apply] at hp
      exact hp.trans (congrArg c (by congr 1; ring))
    · exact hcore _
  change IsLocalDiffeomorph IC I ∞ H₀
  intro q
  rcases interior_zero_seam_cover J.target q with ⟨p,rfl⟩ | ⟨p,rfl⟩ | ⟨z,rfl⟩ | ⟨z,rfl⟩
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hci p) (interiorCore_isLocalDiffeomorph J hJ hJi p)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hai p) (interiorBand_isLocalDiffeomorph J hJ hJi p)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hls z) (lowerSeam_isLocalDiffeomorph J _)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hus z) (upperSeam_isLocalDiffeomorph J hJ hJi _)

theorem exists_mappingTorus_diffeomorph_of_double_slab
    [T2Space M]
    (J : SphereMappingTorusIsotopy)
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (a c : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (hzero : ∀ z : SphereTwo, a (z,0) = c (z,0))
    (hone : ∀ z : SphereTwo, a (z,1) = c (J.target.symm z,1))
    (hmeet : a '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ c '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      c '' (univ ×ˢ ({0} : Set ℝ)) ∪ c '' (univ ×ˢ ({1} : Set ℝ)))
    (hcover : a '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ c '' (univ ×ˢ Icc (0 : ℝ) 1) = univ) :
    ∃ G : (SphereTwo × ℝ) ≃ₘ⟮IC,IC⟯ (SphereTwo × ℝ),
      G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : SphereTwo, G (z,0) = (z,0)) ∧ (∀ z : SphereTwo, G (z,1) = (z,1)) ∧
      (∀ z : SphereTwo, (fun q => a (G q)) =ᶠ[𝓝 (z,0)] (fun q => c (q.1,-q.2))) ∧
      (∀ z : SphereTwo, (fun q => a (G q)) =ᶠ[𝓝 (z,1)] (fun q => c (J.target.symm q.1,2-q.2))) ∧
      let _ := sphereMappingTorusChartedSpace J.flatten
      ∃ D : M ≃ₘ⟮I,IC⟯ SphereMappingTorus J.target,
        (∀ p : Cylinder, D (a (G (p.1,p.2.val))) = bandToMappingTorus J.target p) ∧
        ∀ p : Cylinder, D (c (p.1,p.2.val)) = coreToMappingTorus J.target p := by
  obtain ⟨G,hGb,hG0,hG1,hGlo,hGhi⟩ :=
    Manifold.exists_double_slab_collar_matching a c J.target ha hc hzero hone hmeet
  let a' := G.toPartialDiffeomorph.trans a
  have ha' : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a'.source := by
    intro q hq
    refine ⟨mem_univ _,ha ?_⟩
    change G q ∈ univ ×ˢ Icc (0 : ℝ) 1
    rw [← hGb]
    exact mem_image_of_mem G hq
  have ha'i : a' '' (univ ×ˢ Icc (0 : ℝ) 1) = a '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    calc
      _ = a '' (G '' (univ ×ˢ Icc (0 : ℝ) 1)) := by rw [image_image]; rfl
      _ = _ := by rw [hGb]
  have ha'0 (z : SphereTwo) : slabMap a' (z,⟨0,by norm_num⟩) = slabMap c (z,⟨0,by norm_num⟩) := by
    change a (G (z,0)) = c (z,0)
    rw [hG0,hzero]
  have ha'1 (z : SphereTwo) : slabMap a' (z,⟨1,by norm_num⟩) = slabMap c (J.target.symm z,⟨1,by norm_num⟩) := by
    change a (G (z,1)) = c (J.target.symm z,1)
    rw [hG1,hone]
  have hcross := band_eq_core_iff_of_boundary_eq J.target (slabMap a') (slabMap c)
    (slabMap_injective a' ha') (slabMap_injective c hc) (by
      rw [range_slabMap,range_slabMap,ha'i]
      intro y hy
      rcases hmeet hy with ⟨q,hq,hqy⟩ | ⟨q,hq,hqy⟩
      · left
        refine ⟨q.1,?_⟩
        change c (q.1,0) = y
        have he : q = (q.1,0) := Prod.ext rfl hq.2
        exact he ▸ hqy
      · right
        refine ⟨q.1,?_⟩
        change c (q.1,1) = y
        have he : q = (q.1,1) := Prod.ext rfl hq.2
        exact he ▸ hqy) ha'0 ha'1
  have hcov : range (slabMap a') ∪ range (slabMap c) = univ := by
    rw [range_slabMap,range_slabMap,ha'i,hcover]
  let H₀ := ambientHomeomorph J.target (slabMap a') (slabMap c)
    (continuous_slabMap a' ha') (continuous_slabMap c hc) (slabMap_injective a' ha')
    (slabMap_injective c hc) hcov hcross
  let _ := sphereMappingTorusChartedSpace J.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph J.target)
  have hloc : IsLocalDiffeomorph IC I ∞ H₀ := isLocalDiffeomorph_ambient_of_collar_equations
    J hJ hJi a' c ha' hc hGlo hGhi H₀ (fun _ => rfl) (fun _ => rfl)
  let A : Space J.target ≃ₘ⟮IC,I⟯ M := hloc.diffeomorphOfBijective H₀.bijective
  let B := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (mappingTorusHomeomorph J.target)
  let D := A.symm.trans B
  refine ⟨G,hGb,hG0,hG1,hGlo,hGhi,?_⟩
  change ∃ D : M ≃ₘ⟮I,IC⟯ SphereMappingTorus J.target, _
  refine ⟨D,?_,?_⟩
  · intro p
    change B (A.symm (a (G (p.1,p.2.val)))) = bandToMappingTorus J.target p
    have hA : A (band J.target p) = a (G (p.1,p.2.val)) := rfl
    rw [← hA,A.symm_apply_apply]
    rfl
  · intro p
    change B (A.symm (c (p.1,p.2.val))) = coreToMappingTorus J.target p
    have hA : A (core J.target p) = c (p.1,p.2.val) := rfl
    rw [← hA,A.symm_apply_apply]
    rfl

end DifferentialGeometry.Topology.DoubleCylinder
