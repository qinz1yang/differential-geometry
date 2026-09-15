import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage
import DifferentialGeometry.Topology.PiecewiseLinear.RadialProjection
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineMap_apply_sum_smul (A : E →ᵃ[ℝ] F) {σ : Finset E} {μ : E → ℝ}
    (hμ : ∑ v ∈ σ, μ v = 1) : A (∑ v ∈ σ, μ v • v) = ∑ v ∈ σ, μ v • A v := by
  have h1 : ∑ v ∈ σ, μ v • v = σ.affineCombination ℝ id μ :=
    (Finset.affineCombination_eq_linear_combination σ id μ hμ).symm
  have h2 : ∑ v ∈ σ, μ v • A v = σ.affineCombination ℝ (A ∘ id) μ :=
    (Finset.affineCombination_eq_linear_combination σ (A ∘ id) μ hμ).symm
  rw [h1, h2, Finset.map_affineCombination σ id μ hμ A]

theorem affineIndependent_image_of_injOn_convexHull [DecidableEq F] (A : E →ᵃ[ℝ] F)
    {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E))
    (hinj : InjOn A (convexHull ℝ (σ : Set E))) :
    AffineIndependent ℝ ((↑) : {u // u ∈ σ.image A} → F) := by
  have hinjσ : ∀ v ∈ σ, ∀ w ∈ σ, A v = A w → v = w := fun v hv w hw h =>
    hinj (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)) h
  refine affineIndependent_of_forall_eq_zero fun a ha₀ ha₁ => ?_
  rw [Finset.sum_image hinjσ] at ha₀ ha₁
  have hsplit : ∀ v, max (-a (A v)) 0 = max (a (A v)) 0 - a (A v) := fun v => by
    linarith [max_zero_sub_max_neg_zero_eq_self (a (A v))]
  have hc' : ∑ v ∈ σ, max (-a (A v)) 0 = ∑ v ∈ σ, max (a (A v)) 0 := by
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ha₀, sub_zero]
  have hc0 : 0 ≤ ∑ v ∈ σ, max (a (A v)) 0 := Finset.sum_nonneg fun v _ => le_max_right _ _
  rcases hc0.lt_or_eq with hpos | hzero
  · set c := ∑ v ∈ σ, max (a (A v)) 0 with hc
    have hμ₁ : ∑ v ∈ σ, max (a (A v)) 0 * c⁻¹ = 1 := by
      rw [← Finset.sum_mul, mul_inv_cancel₀ hpos.ne']
    have hν₁ : ∑ v ∈ σ, max (-a (A v)) 0 * c⁻¹ = 1 := by
      rw [← Finset.sum_mul, hc', mul_inv_cancel₀ hpos.ne']
    have hx₁ : ∑ v ∈ σ, (max (a (A v)) 0 * c⁻¹) • v ∈ convexHull ℝ (σ : Set E) :=
      (convex_convexHull ℝ _).sum_mem
        (fun v _ => mul_nonneg (le_max_right _ _) (inv_pos.mpr hpos).le) hμ₁
        fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hx₂ : ∑ v ∈ σ, (max (-a (A v)) 0 * c⁻¹) • v ∈ convexHull ℝ (σ : Set E) :=
      (convex_convexHull ℝ _).sum_mem
        (fun v _ => mul_nonneg (le_max_right _ _) (inv_pos.mpr hpos).le) hν₁
        fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hdiff : ∀ v, max (a (A v)) 0 * c⁻¹ - max (-a (A v)) 0 * c⁻¹ = a (A v) * c⁻¹ := fun v => by
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
    have hAeq : A (∑ v ∈ σ, (max (a (A v)) 0 * c⁻¹) • v) =
        A (∑ v ∈ σ, (max (-a (A v)) 0 * c⁻¹) • v) := by
      rw [affineMap_apply_sum_smul A hμ₁, affineMap_apply_sum_smul A hν₁, ← sub_eq_zero,
        ← Finset.sum_sub_distrib]
      simp_rw [← sub_smul, hdiff, mul_comm _ c⁻¹, mul_smul]
      rw [← Finset.smul_sum, ha₁, smul_zero]
    have hxx := hinj hx₁ hx₂ hAeq
    have h0 := eq_zero_of_sum_eq_zero_of_affineIndependent hσ
      (a := fun v => max (a (A v)) 0 * c⁻¹ - max (-a (A v)) 0 * c⁻¹)
      (by rw [Finset.sum_sub_distrib, hμ₁, hν₁, sub_self])
      (by simp_rw [sub_smul]; rw [Finset.sum_sub_distrib, hxx, sub_self])
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have h := h0 v hv
    rw [hdiff, mul_eq_zero] at h
    rcases h with h | h
    · exact h
    · exact absurd h (inv_pos.mpr hpos).ne'
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have h1 : max (a (A v)) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ => le_max_right _ _).mp hzero.symm v hv
    have h2 : max (-a (A v)) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ => le_max_right _ _).mp
        (hc'.trans hzero.symm) v hv
    have h := max_zero_sub_max_neg_zero_eq_self (a (A v))
    rw [h1, h2, sub_self] at h
    exact h.symm

theorem IsPLHomeomorphOn.congr {f g : E → F} {P : Set E} {Q : Set F} (h : IsPLHomeomorphOn f P Q)
    (hfg : EqOn g f P) : IsPLHomeomorphOn g P Q := by
  have hbij : BijOn g P Q := h.bijOn.congr hfg.symm
  refine ⟨hbij, h.isPiecewiseAffineOn.congr hfg,
    h.isPiecewiseAffineOn_invFunOn.congr fun y hy => ?_⟩
  have h1 : Function.invFunOn g P y ∈ P := hbij.surjOn.mapsTo_invFunOn hy
  have h2 : g (Function.invFunOn g P y) = y := hbij.invOn_invFunOn.2 hy
  have h3 : Function.invFunOn f P y ∈ P := h.bijOn.surjOn.mapsTo_invFunOn hy
  have h4 : f (Function.invFunOn f P y) = y := h.bijOn.invOn_invFunOn.2 hy
  exact h.bijOn.injOn h1 h3 (by rw [← hfg h1, h2, h4])

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_image (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {f : E → F} (hf : IsPiecewiseAffineOn f K.space) (hinj : InjOn f K.space) :
    ∃ L : Geometry.SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = f '' K.space ∧
      IsPLHomeomorphOn f K.space L.space := by
  classical
  obtain ⟨K', hK', hfin', hAff⟩ := hf.exists_isSubdivision_affineOn_faces K
  have : Finite K'.faces := hfin'.to_subtype
  have hspace : K'.space = K.space := hK'.space_eq
  choose A hA using hAff
  have hsm : EqOn (simplicialMap K' f) f K'.space := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := K'.mem_space_iff.mp hx
    rw [simplicialMap_eq_of_mem K' f hσ hxσ, hA _ hσ hxσ]
    conv_rhs => rw [← sum_weights_smul hxσ]
    rw [affineMap_apply_sum_smul (A _ hσ) (sum_weights hxσ)]
    exact Finset.sum_congr rfl fun v hv =>
      by rw [hA _ hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
  have hind : ∀ σ ∈ K'.faces, AffineIndependent ℝ ((↑) : {u // u ∈ σ.image f} → F) := by
    intro σ hσ
    have himg : σ.image f = σ.image (A σ hσ) :=
      Finset.image_congr fun v hv => hA σ hσ (subset_convexHull ℝ _ hv)
    rw [himg]
    refine affineIndependent_image_of_injOn_convexHull (A σ hσ) (K'.indep hσ) ?_
    intro x hx y hy hxy
    have hxK : x ∈ K.space := hspace ▸ K'.convexHull_subset_space hσ hx
    have hyK : y ∈ K.space := hspace ▸ K'.convexHull_subset_space hσ hy
    exact hinj hxK hyK (by rw [hA σ hσ hx, hA σ hσ hy, hxy])
  have hinj' : InjOn (simplicialMap K' f) K'.space := by
    intro x hx y hy hxy
    rw [hsm hx, hsm hy] at hxy
    exact hinj (hspace ▸ hx) (hspace ▸ hy) hxy
  refine ⟨simplicialImage K' f hind hinj', simplicialImage_faces_finite K' f hind hinj', ?_, ?_⟩
  · rw [simplicialImage_space, hsm.image_eq, hspace]
  · have h := isPLHomeomorphOn_simplicialImage K' f hind hinj'
    rw [hspace] at h
    exact h.congr fun x hx => (hsm (hspace ▸ hx)).symm

theorem IsPolyhedron.image_of_isPiecewiseAffineOn {P : Set E} (hP : IsPolyhedron P) {f : E → F}
    (hf : IsPiecewiseAffineOn f P) (hinj : InjOn f P) : IsPolyhedron (f '' P) := by
  classical
  obtain ⟨K, hfin, rfl⟩ := hP.exists_simplicialComplex
  have := hfin.to_subtype
  obtain ⟨L, hfinL, hL, -⟩ := exists_isPLHomeomorphOn_image K hf hinj
  rw [← hL]
  have := hfinL.to_subtype
  exact isPolyhedron_space L

theorem IsPLHomeomorphOn.restrict {f : E → F} {P : Set E} {Q : Set F} (h : IsPLHomeomorphOn f P Q)
    {P₀ : Set E} (hP₀ : IsPolyhedron P₀) (hsub : P₀ ⊆ P) : IsPLHomeomorphOn f P₀ (f '' P₀) := by
  have hpl : IsPiecewiseAffineOn f P₀ := h.isPiecewiseAffineOn.mono_of_isPolyhedron hP₀ hsub
  have hinj : InjOn f P₀ := h.bijOn.injOn.mono hsub
  have himg : IsPolyhedron (f '' P₀) := hP₀.image_of_isPiecewiseAffineOn hpl hinj
  have himgQ : f '' P₀ ⊆ Q := (image_mono hsub).trans h.image_eq.subset
  refine ⟨hinj.bijOn_image, hpl, ?_⟩
  refine (h.isPiecewiseAffineOn_invFunOn.mono_of_isPolyhedron himg himgQ).congr fun y hy => ?_
  have hbij : BijOn f P₀ (f '' P₀) := hinj.bijOn_image
  have h1 : Function.invFunOn f P₀ y ∈ P₀ := hbij.surjOn.mapsTo_invFunOn hy
  have h2 : f (Function.invFunOn f P₀ y) = y := hbij.invOn_invFunOn.2 hy
  have h3 : Function.invFunOn f P y ∈ P := h.bijOn.surjOn.mapsTo_invFunOn (himgQ hy)
  have h4 : f (Function.invFunOn f P y) = y := h.bijOn.invOn_invFunOn.2 (himgQ hy)
  exact h.bijOn.injOn (hsub h1) h3 (h2.trans h4.symm)

theorem IsPLHomeomorphOn.isPolyhedron_preimage {f : E → F} {P : Set E} {Q : Set F}
    (h : IsPLHomeomorphOn f P Q) {R : Set F} (hR : IsPolyhedron R) (hRQ : R ⊆ Q) :
    IsPolyhedron (P ∩ f ⁻¹' R) := by
  have hsymm := h.symm
  have heq : P ∩ f ⁻¹' R = Function.invFunOn f P '' R := by
    ext x
    constructor
    · rintro ⟨hxP, hxR⟩
      exact ⟨f x, hxR, h.bijOn.invOn_invFunOn.1 hxP⟩
    · rintro ⟨y, hyR, rfl⟩
      refine ⟨h.bijOn.surjOn.mapsTo_invFunOn (hRQ hyR), ?_⟩
      rw [mem_preimage, h.bijOn.invOn_invFunOn.2 (hRQ hyR)]
      exact hyR
  rw [heq]
  exact hR.image_of_isPiecewiseAffineOn
    (hsymm.isPiecewiseAffineOn.mono_of_isPolyhedron hR hRQ) (hsymm.bijOn.injOn.mono hRQ)

theorem IsPLBall.isPolyhedron {n : ℕ} {P : Set E} (hP : IsPLBall n P) : IsPolyhedron P := by
  obtain ⟨f, hf⟩ := hP
  rw [← hf.image_eq]
  exact (isHPolytope_stdSimplex _).isPolyhedron.image_of_isPiecewiseAffineOn
    hf.isPiecewiseAffineOn hf.bijOn.injOn

theorem isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn {f : E → F} {P : Set E}
    {Q : Set F} (hP : IsPolyhedron P) (hf : IsPiecewiseAffineOn f P) (hbij : BijOn f P Q) :
    IsPLHomeomorphOn f P Q := by
  obtain ⟨K, hKfin, hK⟩ := hP.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  obtain ⟨L, -, hL, h⟩ := exists_isPLHomeomorphOn_image K (hK.symm ▸ hf)
    (hK.symm ▸ hbij.injOn)
  rwa [hL, hK, hbij.image_eq] at h

end DifferentialGeometry.Topology.PiecewiseLinear
