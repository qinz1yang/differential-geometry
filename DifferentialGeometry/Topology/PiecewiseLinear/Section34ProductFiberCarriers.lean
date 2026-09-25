import DifferentialGeometry.Topology.PiecewiseLinear.Section34LongitudeClass
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAnnulus

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem carriesFundamentalGroupOnto_prod_fiber_of_isPathConnected
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Z] {J : Set X} {Q : Set Y} {S : Set Z}
    (hJ : IsCompact J) (hQ : IsPathConnected Q) {f : X × Y → Z}
    (hf : ContinuousOn f (J ×ˢ Q)) (hfS : MapsTo f (J ×ˢ Q) S)
    {q₀ : Y} (hq₀ : q₀ ∈ Q) (hinj : InjOn (fun x => f (x, q₀)) J)
    (hgen : CarriesFundamentalGroupOnto (f '' (J ×ˢ {q₀})) S)
    {q : Y} (hq : q ∈ Q) : CarriesFundamentalGroupOnto (f '' (J ×ˢ {q})) S := by
  obtain ⟨γ, hγ⟩ := hQ.joinedIn q hq q₀ hq₀
  let F : X × ℝ → Z := fun p => f (p.1, γ (projIcc 0 1 zero_le_one p.2))
  have hF : ContinuousOn F (J ×ˢ Icc 0 1) := by
    apply hf.comp
      (continuous_fst.prodMk
        (γ.continuous.comp (continuous_projIcc.comp continuous_snd))).continuousOn
    exact fun p hp => ⟨hp.1, hγ _⟩
  have hFS : MapsTo F (J ×ˢ Icc 0 1) S := fun p hp => hfS ⟨hp.1, hγ _⟩
  have hzero : (fun x => F (x, (0 : ℝ))) = fun x => f (x, q) := by
    funext x
    change f (x, γ (projIcc 0 1 zero_le_one 0)) = f (x, q)
    rw [projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩]
    exact congrArg (fun y => f (x, y)) γ.source
  have hone : (fun x => F (x, (1 : ℝ))) = fun x => f (x, q₀) := by
    funext x
    change f (x, γ (projIcc 0 1 zero_le_one 1)) = f (x, q₀)
    rw [projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩]
    exact congrArg (fun y => f (x, y)) γ.target
  have h := carriesFundamentalGroupOnto_image_zero_of_image_one hJ hF hFS
    (hone.symm ▸ hinj) (by simpa only [hone, prod_singleton, image_image] using hgen)
  simpa only [hzero, prod_singleton, image_image] using h

theorem IsPLHomeomorphInto.carriesFundamentalGroupOnto_all_product_fibers
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P B J Q : Set (EuclideanSpace ℝ (Fin 3))} {S : Set M}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hBP : B ⊆ P) (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3)} (hf : IsPLHomeomorphOn f (J ×ˢ Q) B)
    (hBS : u '' B ⊆ S) {q₀ : EuclideanSpace ℝ (Fin 3)} (hq₀ : q₀ ∈ Q)
    (hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {q₀})) S)
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ∈ Q) :
    CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {q})) S := by
  apply carriesFundamentalGroupOnto_prod_fiber_of_isPathConnected hJ.isPolyhedron.isCompact
    hQ.isPathConnected_one
    (hu.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn
      fun x hx => hBP (hf.bijOn.mapsTo hx))
    (fun x hx => hBS ⟨f x, hf.bijOn.mapsTo hx, rfl⟩) hq₀ ?_ hgen hq
  intro x hx y hy hxy
  exact congrArg Prod.fst (hf.bijOn.injOn ⟨hx, hq₀⟩ ⟨hy, hq₀⟩
    (hu.injOn (hBP (hf.bijOn.mapsTo ⟨hx, hq₀⟩))
      (hBP (hf.bijOn.mapsTo ⟨hy, hq₀⟩)) hxy))

theorem IsPLHomeomorphInto.not_nullhomotopic_all_model_product_fibers
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J Q : Set (EuclideanSpace ℝ (Fin 3))} {S : Set M}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3)} (hf : IsPLHomeomorphOn f (J ×ˢ Q) (frontier C))
    (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    {q₀ : EuclideanSpace ℝ (Fin 3)} (hq₀ : q₀ ∈ Q)
    (hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {q₀})) S)
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ∈ Q) :
    IsPLSphere 1 (f '' (J ×ˢ {q})) ∧ f '' (J ×ˢ {q}) ⊆ C ∧
      ∀ hLC : f '' (J ×ˢ {q}) ⊆ C,
        ¬ (⟨inclusion hLC, continuous_inclusion hLC⟩ : C(f '' (J ×ˢ {q}), C)).Nullhomotopic := by
  have hfront : frontier C ⊆ C := hC.isPolyhedron.isClosed.frontier_subset
  have hsub : J ×ˢ {q} ⊆ J ×ˢ Q := prod_mono_right (singleton_subset_iff.mpr hq)
  have hprod : IsPLHomeomorphOn (fun x => (x, q)) J (J ×ˢ {q}) := by
    let ι := (AffineMap.id ℝ (EuclideanSpace ℝ (Fin 3))).prod
      (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 3)) q)
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      ((isPiecewiseAffineOn_of_affine ι isOpen_univ).mono_of_isPolyhedron
        hJ.isPolyhedron (subset_univ _))
    exact ⟨fun _ hx => ⟨hx, rfl⟩, fun _ _ _ _ heq => congrArg Prod.fst heq,
      fun y hy => ⟨y.1, hy.1, Prod.ext rfl hy.2.symm⟩⟩
  have hL : IsPLSphere 1 (f '' (J ×ˢ {q})) :=
    (hJ.of_isPLHomeomorphOn hprod).of_isPLHomeomorphOn
      (hf.restrict (hJ.isPolyhedron.prod (isHPolytope_singleton q).isPolyhedron) hsub)
  have hLC : f '' (J ×ˢ {q}) ⊆ C :=
    (image_mono hsub).trans (hf.image_eq ▸ hfront)
  have hcarry := hu.carriesFundamentalGroupOnto_all_product_fibers
    (hfront.trans hCP) hJ hQ hf ((image_mono hfront).trans hCS) hq₀ hgen hq
  rw [image_comp] at hcarry
  exact ⟨hL, hLC, fun hLC' =>
    hu.not_nullhomotopic_model_longitude_of_carrying_image hC hCP hL.nonempty hLC' hS hCS
      hcarry⟩

end DifferentialGeometry.Topology.PiecewiseLinear
