import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCircle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PeriodicLateralExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.exists_end_fixed_prod_alignment {P : Set E} (hP : IsPolyhedron P)
    {Ψ : E × ℝ → E × ℝ} (hΨ : IsPLHomeomorphOn Ψ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1))
    (hΨ0 : ∀ x ∈ P, Ψ (x, 0) = (x, 0)) {ν : E → E} (hν : IsPLHomeomorphOn ν P P)
    (hΨ1 : ∀ x ∈ P, Ψ (x, 1) = (ν x, 1)) :
    ∃ φ : E × ℝ → E × ℝ, IsPLHomeomorphOn φ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1) ∧
      (∀ x ∈ P, φ (x, 0) = (x, 0)) ∧ (∀ x ∈ P, φ (x, 1) = (x, 1)) ∧
      EqOn φ Ψ (P ×ˢ Icc (0 : ℝ) (1 / 2)) := by
  let μ := Function.invFunOn ν P
  let Γ := Function.invFunOn Ψ (P ×ˢ Icc (0 : ℝ) 1)
  have hΓ : IsPLHomeomorphOn Γ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1) := hΨ.symm
  have hμ : IsPLHomeomorphOn μ P P := hν.symm
  have hΓ0 (x : E) (hx : x ∈ P) : Γ (x, 0) = (x, 0) := by
    have h := hΨ.bijOn.invOn_invFunOn.1
      (show (x, (0 : ℝ)) ∈ P ×ˢ Icc 0 1 from ⟨hx, by norm_num⟩)
    rwa [hΨ0 x hx] at h
  have hΓ1 (x : E) (hx : x ∈ P) : Γ (x, 1) = (μ x, 1) := by
    have hxμ := hμ.bijOn.mapsTo hx
    have hνμ : ν (μ x) = x := hν.bijOn.invOn_invFunOn.2 hx
    have h := hΨ.bijOn.invOn_invFunOn.1
      (show (μ x, (1 : ℝ)) ∈ P ×ˢ Icc 0 1 from ⟨hxμ, by norm_num⟩)
    rwa [hΨ1 (μ x) hxμ, hνμ] at h
  obtain ⟨Θ, hΘ, hΘlo, hΘhi, -⟩ := hP.exists_isPLHomeomorphOn_prod_Icc_of_slab
    hΓ hΓ0 hμ hΓ1 (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) le_rfl
  refine ⟨Ψ ∘ Θ, hΘ.trans hΨ, ?_, ?_, fun z hz => congrArg Ψ (hΘlo z hz)⟩
  · intro x hx
    rw [Function.comp_apply, hΘlo (x, 0) ⟨hx, by norm_num⟩, hΨ0 x hx]
  · intro x hx
    rw [Function.comp_apply, hΘhi (x, 1) ⟨hx, by norm_num⟩,
      hΨ1 (μ x) (hμ.bijOn.mapsTo hx), hν.bijOn.invOn_invFunOn.2 hx]

theorem IsPLSphere.exists_periodic_prism_lateral_level
    {K : Set ((Fin 3 → ℝ) × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ stdSimplexBoundary 2, φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ stdSimplexBoundary 2, φ (x, 1) = (x, 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) = K := by
  have hP : IsPolyhedron (stdSimplexBoundary 2) := by
    exact (show IsPLSphere 1 (stdSimplexBoundary 2) from
      by simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1)
      |>.isPolyhedron
  obtain ⟨Ψ, ν, hΨ, hν, hΨ0, hΨ1, hmid⟩ :=
    hK.exists_isPLHomeomorphOn_prism_lateral_level hKA hess
  obtain ⟨φ, hφ, hφ0, hφ1, hφΨ⟩ := hP.exists_end_fixed_prod_alignment hΨ hΨ0 hν hΨ1
  refine ⟨φ, hφ, hφ0, hφ1, ?_⟩
  have hsub : stdSimplexBoundary 2 ×ˢ ({1 / 2} : Set ℝ) ⊆
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) (1 / 2) := by
    intro z hz
    exact ⟨hz.1, by rw [show z.2 = 1 / 2 from hz.2]; norm_num⟩
  exact (hφΨ.mono hsub).image_eq.trans hmid

open Classical in
theorem IsPLSphere.exists_periodic_lateral_level
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {K : Set (E × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ (boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (Q : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        q '' stdSimplexBoundary 2 = K) :
    ∃ φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)
        ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ (boundaryComplex 2 D).space, φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ (boundaryComplex 2 D).space, φ (x, 1) = (x, 1)) ∧
      φ '' ((boundaryComplex 2 D).space ×ˢ {1 / 2}) = K := by
  obtain ⟨r, hr⟩ := hD
  have hB : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hrB : IsPLHomeomorphOn r (stdSimplexBoundary 2) (boundaryComplex 2 D).space := by
    rw [← hr.image_stdSimplexBoundary_eq_boundaryComplex D rfl]
    exact hr.restrict hB (fun _ hx => hx.1)
  let σ : (Fin 3 → ℝ) × ℝ → E × ℝ := Prod.map r id
  let A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let B := (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1
  have hσ : IsPLHomeomorphOn σ A B :=
    hrB.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  let τ := Function.invFunOn σ A
  let K' := τ '' K
  have hKB : K ⊆ B := hKA.trans (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hK' : IsPLSphere 1 K' :=
    hK.of_isPLHomeomorphOn (hσ.symm.restrict hK.isPolyhedron hKB)
  have hback : σ '' K' = K := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact (hσ.bijOn.invOn_invFunOn.2 (hKB hw)).symm ▸ hw
    · intro hy
      exact ⟨τ y, ⟨y, hy, rfl⟩, hσ.bijOn.invOn_invFunOn.2 (hKB hy)⟩
  have hK'A : K' ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro z ⟨y, hy, rfl⟩
    have hτy := hσ.symm.bijOn.mapsTo (hKB hy)
    have heq := congrArg Prod.snd (hσ.bijOn.invOn_invFunOn.2 (hKB hy))
    change (τ y).2 = y.2 at heq
    exact ⟨hτy.1, heq.symm ▸ (hKA hy).2⟩
  have hess' : ¬ ∃ (Q : Set ((Fin 3 → ℝ) × ℝ))
      (q : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧ Q ⊆ A ∧
        q '' stdSimplexBoundary 2 = K' := by
    rintro ⟨Q, q, hq, hQA, hqK⟩
    apply hess
    refine ⟨σ '' Q, σ ∘ q, hq.trans (hσ.restrict (IsPLBall.isPolyhedron ⟨q, hq⟩) hQA),
      (image_mono hQA).trans hσ.image_eq.subset, ?_⟩
    rw [image_comp, hqK, hback]
  obtain ⟨φ, hφ, hφ0, hφ1, hφmid⟩ := hK'.exists_periodic_prism_lateral_level hK'A hess'
  let ψ := σ ∘ φ ∘ τ
  have hψ : IsPLHomeomorphOn ψ B B := (hσ.symm.trans hφ).trans hσ
  have hinv (x : Fin 3 → ℝ) (hx : x ∈ stdSimplexBoundary 2) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) : τ (σ (x, t)) = (x, t) :=
    hσ.bijOn.invOn_invFunOn.1 (show (x, t) ∈ A from ⟨hx, ht⟩)
  refine ⟨ψ, hψ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hrB.bijOn.surjOn hx
    change σ (φ (τ (σ (y, 0)))) = σ (y, 0)
    rw [hinv y hy 0 (by norm_num), hφ0 y hy]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hrB.bijOn.surjOn hx
    change σ (φ (τ (σ (y, 1)))) = σ (y, 1)
    rw [hinv y hy 1 (by norm_num), hφ1 y hy]
  · have hσmid : σ '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) =
        (boundaryComplex 2 D).space ×ˢ {1 / 2} :=
      image_prod_singleton_of_map_level hrB (fun _ _ => rfl)
    have heq : EqOn (ψ ∘ σ) (σ ∘ φ) (stdSimplexBoundary 2 ×ˢ {1 / 2}) := by
      intro z hz
      change σ (φ (τ (σ z))) = σ (φ z)
      exact congrArg (σ ∘ φ) (hσ.bijOn.invOn_invFunOn.1
        (show z ∈ A from ⟨hz.1, by rw [show z.2 = 1 / 2 from hz.2]; norm_num⟩))
    rw [← hσmid, ← image_comp]
    exact heq.image_eq.trans (by rw [image_comp, hφmid, hback])

open Classical in
theorem IsCylindricalDiagram.exists_volume_meridian_alignment
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {K : Set (E × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ (boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (Q : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        q '' stdSimplexBoundary 2 = K) :
    ∃ H : F → F, IsPLHomeomorphOn H S S ∧
      EqOn H id (f '' ((boundaryComplex 2 D).space ×ˢ {0})) ∧
      H '' (f '' ((boundaryComplex 2 D).space ×ˢ {1 / 2})) = f '' K := by
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  obtain ⟨φ, hφ, hφ0, hφ1, hφmid⟩ := hK.exists_periodic_lateral_level D hD hKA hess
  obtain ⟨H, hH, hHf⟩ := hf.exists_lateral_extension_of_periodic_lift D hD hends
    (isPolyhedron_space (boundaryComplex 2 D)).isPLHomeomorphOn_id hφ hφ0 hφ1
  refine ⟨H, hH, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have hzpair : z = (z.1, 0) := Prod.ext rfl hz0
    rw [hzpair, hHf (z.1, 0) ⟨hz.1, by norm_num⟩, hφ0 z.1 hz.1]
    rfl
  · have heq : EqOn (H ∘ f) (f ∘ φ) ((boundaryComplex 2 D).space ×ˢ {1 / 2}) := by
      intro z hz
      exact hHf z ⟨hz.1, by rw [show z.2 = 1 / 2 from hz.2]; norm_num⟩
    rw [← image_comp, heq.image_eq, image_comp, hφmid]

open Classical in
theorem IsCylindricalDiagram.exists_aligned_meridian_disk
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {K : Set (E × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ (boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (Q : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        q '' stdSimplexBoundary 2 = K) :
    ∃ (H : F → F) (q : (Fin 3 → ℝ) → F), IsPLHomeomorphOn H S S ∧
      EqOn H id (f '' ((boundaryComplex 2 D).space ×ˢ {0})) ∧
      IsCylindricalDiagram (H ∘ f) D.space S ∧
      (∀ x ∈ D.space, (H ∘ f) (x, 0) = (H ∘ f) (x, 1)) ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 = f '' K ∧ ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ⊆ S := by
  obtain ⟨H, hH, hfix, hmid⟩ := hf.exists_volume_meridian_alignment D hD hends hK hKA hess
  have hg := hf.postcomp_equivalence hH
  obtain ⟨a, ha⟩ := hD
  have hbd := ha.image_stdSimplexBoundary_eq_boundaryComplex D rfl
  have hslice := hg.isPLHomeomorphOn_slice (isPolyhedron_space D)
    (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
  let q : (Fin 3 → ℝ) → F := fun x => H (f (a x, 1 / 2))
  have hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3))
      ((H ∘ f) '' (D.space ×ˢ {1 / 2})) := ha.trans hslice
  refine ⟨H, q, hH, hfix, hg, fun x hx => congrArg H (hends x hx), hq, ?_, ?_⟩
  · have hqimg : q '' stdSimplexBoundary 2 =
        H '' (f '' ((a '' stdSimplexBoundary 2) ×ˢ {1 / 2})) := by
      rw [prod_singleton, image_image, image_image, image_image]
    rw [hqimg, hbd, hmid]
  · rw [← hg.image_eq]
    exact image_mono (fun z hz => ⟨hz.1,
      by rw [show z.2 = 1 / 2 from hz.2]; norm_num⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
