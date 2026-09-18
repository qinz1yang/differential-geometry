import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialPairImage
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn
    [DecidableEq E] [DecidableEq F]
    (K M N : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces] [Finite N.faces]
    (hM : M.faces ⊆ K.faces) (hN : N.faces ⊆ K.faces) {p : E}
    (hpM : {p} ∈ M.faces) (hpN : {p} ∈ N.faces)
    {U : Set E} (hU : U ∈ 𝓝 p) {h : E → F}
    (hpl : IsPiecewiseAffineOn h U) (hinj : InjOn h U) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (K₁ M₁ N₁ : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ ({p} : Finset E) ∈ R.faces ∧ closedStar R p ⊆ U ∧
        K₁.faces.Finite ∧ M₁.faces.Finite ∧ N₁.faces.Finite ∧
        M₁.faces ⊆ K₁.faces ∧ N₁.faces ⊆ K₁.faces ∧
        ({h p} : Finset F) ∈ M₁.faces ∧ ({h p} : Finset F) ∈ N₁.faces ∧
        K₁.space = h '' closedStar R p ∧
        M₁.space = h '' closedStar (restrict R M.space) p ∧
        N₁.space = h '' closedStar (restrict R N.space) p ∧
        (∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink M {p}).space
          (SimplicialComplex.geometricLink M₁ {h p}).space) ∧
        (∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink N {p}).space
          (SimplicialComplex.geometricLink N₁ {h p}).space) := by
  classical
  have hpK : p ∈ K.space :=
    K.convexHull_subset_space (hM hpM) (subset_convexHull ℝ _ (by simp))
  obtain ⟨R, hRK, hRfin, hpR, hstarU⟩ :=
    exists_isSubdivision_closedStar_subset_of_mem_nhds K hpK hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hM' : IsSubdivision (restrict R M.space) M := hRK.restrict M hM
  have hN' : IsSubdivision (restrict R N.space) N := hRK.restrict N hN
  let _ : Finite (restrict R M.space).faces := (restrict_faces_finite R M.space).to_subtype
  let _ : Finite (restrict R N.space).faces := (restrict_faces_finite R N.space).to_subtype
  have hM'faces : (restrict R M.space).faces ⊆ R.faces := restrict_faces_subset R M.space
  have hN'faces : (restrict R N.space).faces ⊆ R.faces := restrict_faces_subset R N.space
  have hpM' : ({p} : Finset E) ∈ (restrict R M.space).faces := hM'.singleton_mem hpM
  have hpN' : ({p} : Finset E) ∈ (restrict R N.space).faces := hN'.singleton_mem hpN
  let _ : Finite (starComplex R p).faces := (starComplex_faces_finite R p).to_subtype
  let _ : Finite (starComplex (restrict R M.space) p).faces :=
    (starComplex_faces_finite (restrict R M.space) p).to_subtype
  let _ : Finite (starComplex (restrict R N.space) p).faces :=
    (starComplex_faces_finite (restrict R N.space) p).to_subtype
  have hKSspace : (starComplex R p).space = closedStar R p := starComplex_space R p hpR
  have hMSspace : (starComplex (restrict R M.space) p).space =
      closedStar (restrict R M.space) p := starComplex_space _ p hpM'
  have hNSspace : (starComplex (restrict R N.space) p).space =
      closedStar (restrict R N.space) p := starComplex_space _ p hpN'
  have hMSfaces : (starComplex (restrict R M.space) p).faces ⊆ (starComplex R p).faces :=
    fun _ hs => ⟨hM'faces hs.1, hM'faces hs.2⟩
  have hNSfaces : (starComplex (restrict R N.space) p).faces ⊆ (starComplex R p).faces :=
    fun _ hs => ⟨hN'faces hs.1, hN'faces hs.2⟩
  have hpMS : ({p} : Finset E) ∈ (starComplex (restrict R M.space) p).faces :=
    singleton_mem_starComplex _ p hpM'
  have hpNS : ({p} : Finset E) ∈ (starComplex (restrict R N.space) p).faces :=
    singleton_mem_starComplex _ p hpN'
  have hKSU : (starComplex R p).space ⊆ U := by
    rw [hKSspace]
    exact hstarU
  obtain ⟨K₁, M₁, N₁, hK₁fin, hM₁fin, hN₁fin, hMK₁, hNK₁, hpM₁, hpN₁, hK₁space, hM₁space,
    hN₁space, -, -, -, hlinkM, hlinkN⟩ :=
    exists_simplicialComplex_triple_image_of_isPiecewiseAffineOn (starComplex R p)
      (starComplex (restrict R M.space) p) (starComplex (restrict R N.space) p) hMSfaces hNSfaces
      hpMS hpNS (hpl.mono_of_isPolyhedron (isPolyhedron_space _) hKSU) (hinj.mono hKSU)
  refine ⟨R, K₁, M₁, N₁, hRK, hRfin, hpR, hstarU, hK₁fin, hM₁fin, hN₁fin, hMK₁, hNK₁, hpM₁,
    hpN₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK₁space, hKSspace]
  · rw [hM₁space, hMSspace]
  · rw [hN₁space, hNSspace]
  · obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hM' hpM
    obtain ⟨g₁, hg₁⟩ := hlinkM
    rw [geometricLink_starComplex] at hg₁
    exact ⟨_, hg.symm.trans hg₁⟩
  · obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hN' hpN
    obtain ⟨g₁, hg₁⟩ := hlinkN
    rw [geometricLink_starComplex] at hg₁
    exact ⟨_, hg.symm.trans hg₁⟩

theorem exists_simplicialComplex_pair_image_closedStar_of_isPiecewiseAffineOn
    [DecidableEq E] [DecidableEq F]
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    {U : Set E} (hU : U ∈ 𝓝 p) {h : E → F}
    (hpl : IsPiecewiseAffineOn h U) (hinj : InjOn h U) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (K₁ M₁ : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ ({p} : Finset E) ∈ R.faces ∧ closedStar R p ⊆ U ∧
        K₁.faces.Finite ∧ M₁.faces.Finite ∧ M₁.faces ⊆ K₁.faces ∧
          ({h p} : Finset F) ∈ M₁.faces ∧
            K₁.space = h '' closedStar R p ∧
              M₁.space = h '' closedStar (restrict R M.space) p ∧
                ∃ g : E → F, IsPLHomeomorphOn g (SimplicialComplex.geometricLink M {p}).space
                  (SimplicialComplex.geometricLink M₁ {h p}).space := by
  obtain ⟨R, K₁, M₁, -, hRK, hRfin, hpR, hstarU, hK₁fin, hM₁fin, -, hMK₁, -, hpM₁, -, hK₁space,
    hM₁space, -, hlinkM, -⟩ :=
    exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn K M M hM hM hp hp hU
      hpl hinj
  exact ⟨R, K₁, M₁, hRK, hRfin, hpR, hstarU, hK₁fin, hM₁fin, hMK₁, hpM₁, hK₁space, hM₁space,
    hlinkM⟩

omit [FiniteDimensional ℝ E] in
theorem image_closedStar_mem_nhds_of_isPLHomeomorphOn
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hK : K.space ∈ 𝓝 p)
    {U : Set E} {W : Set F} {h : E → F} (hW : IsOpen W) (hh : IsPLHomeomorphOn h U W)
    (hpU : p ∈ U) :
    h '' closedStar K p ∈ 𝓝 (h p) := by
  have hstarNhds : closedStar K p ∈ 𝓝 p := closedStar_mem_nhds K hK
  have hhpW : h p ∈ W := hh.bijOn.mapsTo hpU
  have hinvhp : Function.invFunOn h U (h p) = p := hh.bijOn.invOn_invFunOn.1 hpU
  have hcont : ContinuousAt (Function.invFunOn h U) (h p) :=
    hh.isPiecewiseAffineOn_invFunOn.continuousOn.continuousAt (hW.mem_nhds hhpW)
  have hpre : Function.invFunOn h U ⁻¹' closedStar K p ∈ 𝓝 (h p) :=
    hcont.preimage_mem_nhds (by rw [hinvhp]; exact hstarNhds)
  refine Filter.mem_of_superset (Filter.inter_mem (hW.mem_nhds hhpW) hpre) ?_
  rintro y ⟨hyW, hyS⟩
  exact ⟨Function.invFunOn h U y, hyS, hh.bijOn.invOn_invFunOn.2 hyW⟩

theorem IsPLHomeomorphOn.restrict_isOpen {f : E → F} {P : Set E} {Q : Set F}
    (h : IsPLHomeomorphOn f P Q) {P₀ : Set E} (hP₀ : IsOpen P₀) (hsub : P₀ ⊆ P)
    (hQ₀ : IsOpen (f '' P₀)) : IsPLHomeomorphOn f P₀ (f '' P₀) := by
  have hinj : InjOn f P₀ := h.bijOn.injOn.mono hsub
  have himg : f '' P₀ ⊆ Q := (image_mono hsub).trans h.image_eq.subset
  refine ⟨hinj.bijOn_image, h.isPiecewiseAffineOn.mono hP₀ hsub, ?_⟩
  refine (h.isPiecewiseAffineOn_invFunOn.mono hQ₀ himg).congr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : Function.invFunOn f P₀ (f x) = x := hinj.leftInvOn_invFunOn hx
  have h2 : Function.invFunOn f P (f x) = x := h.bijOn.injOn.leftInvOn_invFunOn (hsub hx)
  rw [h1, h2]

theorem isPiecewiseAffineOn_injOn_linearEquiv_comp {h : E → E} {U V : Set E}
    (hh : IsPLHomeomorphOn h U V) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ) :
    IsPiecewiseAffineOn (fun y => L (h y)) U ∧ InjOn (fun y => L (h y)) U := by
  refine ⟨?_, fun y hy z hz hyz => hh.bijOn.injOn hy hz (L.injective hyz)⟩
  have hL : IsPiecewiseAffineOn (fun q : E => (L q : ℝ × ℝ × ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap isOpen_univ).congr fun _ _ => rfl
  have hcomp := hL.comp (IsPLHomeomorphOn.isPiecewiseAffineOn hh)
  rw [preimage_univ, inter_univ] at hcomp
  exact hcomp.congr fun _ _ => rfl

omit [FiniteDimensional ℝ E] in
theorem IsPLHomeomorphOn.isOpen_image_of_isOpen {f : E → F} {P : Set E} {Q : Set F}
    (h : IsPLHomeomorphOn f P Q) (hQ : IsOpen Q) {P₀ : Set E} (hP₀ : IsOpen P₀)
    (hsub : P₀ ⊆ P) : IsOpen (f '' P₀) := by
  have heq : f '' P₀ = Q ∩ Function.invFunOn f P ⁻¹' P₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨h.bijOn.mapsTo (hsub hx), ?_⟩
      change Function.invFunOn f P (f x) ∈ P₀
      rw [h.bijOn.injOn.leftInvOn_invFunOn (hsub hx)]
      exact hx
    · rintro ⟨hyQ, hyP⟩
      exact ⟨Function.invFunOn f P y, hyP, h.bijOn.invOn_invFunOn.2 hyQ⟩
  rw [heq]
  exact h.isPiecewiseAffineOn_invFunOn.continuousOn.isOpen_inter_preimage hQ hP₀

theorem isPLHomeomorphOn_linearEquiv (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ) {V : Set E} (hV : IsOpen V) :
    IsPLHomeomorphOn (fun y => L y) V ((fun y => L y) '' V) := by
  have hopen : IsOpen ((fun y => L y) '' V) := by
    have h := L.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
    simpa using h
  have hinj : InjOn (fun y => L y) V := L.injective.injOn
  refine ⟨hinj.bijOn_image,
    (isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap hV).congr fun _ _ => rfl, ?_⟩
  refine (isPiecewiseAffineOn_of_affine L.symm.toLinearMap.toAffineMap hopen).congr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  change Function.invFunOn (fun y => L y) V (L x) = L.symm (L x)
  rw [hinj.leftInvOn_invFunOn hx, L.symm_apply_apply]

theorem exists_isPLHomeomorphOn_comp_two_sheets
    {U : Set E} (hU : IsOpen U) {p : E} (hpU : p ∈ U)
    {φ : E → ℝ × ℝ × ℝ} {W : Set (ℝ × ℝ × ℝ)} (hW : IsOpen W)
    (hφ : IsPLHomeomorphOn φ U W) (hφp : φ p = 0)
    {U₂ V₂ : Set (ℝ × ℝ × ℝ)} (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
    (h0 : (0 : ℝ × ℝ × ℝ) ∈ U₂)
    {h₂ : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ} (hh₂ : IsPLHomeomorphOn h₂ U₂ V₂) (hh₂0 : h₂ 0 = 0)
    (L₂ : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ)
    {A B : Set E} {S : Set (ℝ × ℝ × ℝ)}
    (hA : ∀ᶠ y in 𝓝 p, y ∈ A → (φ y).2.2 = 0)
    (hB : ∀ᶠ y in 𝓝 p, y ∈ B → φ y ∈ S)
    (hS : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ × ℝ), (z ∈ S → (L₂ (h₂ z)).2.2 = 0) ∧
      (z.2.2 = 0 → (L₂ (h₂ z)).2.1 = 0)) :
    ∃ (U₀ : Set E) (V₀ : Set (ℝ × ℝ × ℝ)), IsOpen U₀ ∧ p ∈ U₀ ∧
      IsPLHomeomorphOn (fun y => L₂ (h₂ (φ y))) U₀ V₀ ∧ L₂ (h₂ (φ p)) = 0 ∧
      ∀ᶠ y in 𝓝 p, (y ∈ A → (L₂ (h₂ (φ y))).2.1 = 0) ∧
        (y ∈ B → (L₂ (h₂ (φ y))).2.2 = 0) := by
  have hcont : ContinuousOn φ U := hφ.isPiecewiseAffineOn.continuousOn
  have hU₀ : IsOpen (U ∩ φ ⁻¹' U₂) := hcont.isOpen_inter_preimage hU hU₂
  have hpU₀ : p ∈ U ∩ φ ⁻¹' U₂ := ⟨hpU, by change φ p ∈ U₂; rw [hφp]; exact h0⟩
  have hsub : U ∩ φ ⁻¹' U₂ ⊆ U := inter_subset_left
  have himgU : IsOpen (φ '' (U ∩ φ ⁻¹' U₂)) := hφ.isOpen_image_of_isOpen hW hU₀ hsub
  have himgsub : φ '' (U ∩ φ ⁻¹' U₂) ⊆ U₂ := by
    rintro z ⟨y, hy, rfl⟩
    exact hy.2
  have hφ₀ : IsPLHomeomorphOn φ (U ∩ φ ⁻¹' U₂) (φ '' (U ∩ φ ⁻¹' U₂)) :=
    hφ.restrict_isOpen hU₀ hsub himgU
  have himg2 : IsOpen (h₂ '' (φ '' (U ∩ φ ⁻¹' U₂))) :=
    hh₂.isOpen_image_of_isOpen hV₂ himgU himgsub
  have hh₂₀ : IsPLHomeomorphOn h₂ (φ '' (U ∩ φ ⁻¹' U₂)) (h₂ '' (φ '' (U ∩ φ ⁻¹' U₂))) :=
    hh₂.restrict_isOpen himgU himgsub himg2
  have hcomp := (hφ₀.trans hh₂₀).trans (isPLHomeomorphOn_linearEquiv L₂ himg2)
  have hcontAt : ContinuousAt φ p := hcont.continuousAt (hU.mem_nhds hpU)
  have htend : Filter.Tendsto φ (𝓝 p) (𝓝 (0 : ℝ × ℝ × ℝ)) := by
    rw [← hφp]
    exact hcontAt
  refine ⟨U ∩ φ ⁻¹' U₂, _, hU₀, hpU₀, hcomp, by rw [hφp, hh₂0, map_zero], ?_⟩
  filter_upwards [hA, hB, htend.eventually hS] with y hAy hBy hSy
  exact ⟨fun hy => hSy.2 (hAy hy), fun hy => hSy.1 (hBy hy)⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] in
theorem eventually_mem_image_closedStar_of_mem_space
    (N : Geometry.SimplicialComplex ℝ E) [Finite N.faces] (p : E) (φ : E → F) :
    ∀ᶠ y in 𝓝 p, y ∈ N.space → φ y ∈ φ '' closedStar N p := by
  obtain ⟨W, hW, hWsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (closedStar_mem_nhdsWithin N p)
  filter_upwards [hW] with y hy hyN
  exact ⟨y, hWsub ⟨hy, hyN⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
