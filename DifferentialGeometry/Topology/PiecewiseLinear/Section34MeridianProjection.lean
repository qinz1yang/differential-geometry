import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.projection_of_singleton_product_fibers
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {P : Set E} {J : Set F} {Q : Set G} {K S : Set H} {g : E → H} {f : F × G → H}
    (hg : IsPLHomeomorphOn g P K) (hP : IsPolyhedron P)
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) S) (hKS : K ⊆ S)
    (hmark : ∀ q ∈ Q, ∃ z ∈ J, K ∩ f '' (J ×ˢ {q}) = {f (z, q)}) :
    IsPLHomeomorphOn (fun x => (Function.invFunOn f (J ×ˢ Q) (g x)).2) P Q ∧
      ∀ x ∈ P, g x ∈ f '' (J ×ˢ {(Function.invFunOn f (J ×ˢ Q) (g x)).2}) := by
  let v := Function.invFunOn f (J ×ˢ Q)
  let π : E → G := fun x => (v (g x)).2
  have hv (x : E) (hx : x ∈ P) : v (g x) ∈ J ×ˢ Q :=
    hf.symm.bijOn.mapsTo (hKS (hg.bijOn.mapsTo hx))
  have hfv (x : E) (hx : x ∈ P) : f (v (g x)) = g x :=
    hf.bijOn.invOn_invFunOn.2 (hKS (hg.bijOn.mapsTo hx))
  have hπQ : MapsTo π P Q := fun x hx => (hv x hx).2
  have hfiber (x : E) (hx : x ∈ P) : g x ∈ f '' (J ×ˢ {π x}) :=
    ⟨v (g x), ⟨(hv x hx).1, rfl⟩, hfv x hx⟩
  have hK : IsPolyhedron K := hg.image_eq ▸
    hP.image_of_isPiecewiseAffineOn hg.isPiecewiseAffineOn hg.bijOn.injOn
  have hvPL := (hg.trans (hf.symm.restrict hK hKS)).isPiecewiseAffineOn
  have hsnd : IsPiecewiseAffineOn (Prod.snd : F × G → G) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ F G).toAffineMap isOpen_univ
  have hπPL : IsPiecewiseAffineOn π P := by
    simpa only [π, v, Function.comp_def, preimage_univ, inter_univ] using hsnd.comp hvPL
  have hinj : InjOn π P := by
    intro x hx y hy hxy
    obtain ⟨z, -, hz⟩ := hmark (π x) (hπQ hx)
    have hxf : g x = f (z, π x) := hz.subset ⟨hg.bijOn.mapsTo hx, hfiber x hx⟩
    have hyf : g y = f (z, π x) :=
      hz.subset ⟨hg.bijOn.mapsTo hy, hxy.symm ▸ hfiber y hy⟩
    exact hg.bijOn.injOn hx hy (hxf.trans hyf.symm)
  have hsurj : SurjOn π P Q := by
    intro q hq
    obtain ⟨z, hz, htrace⟩ := hmark q hq
    have hzK : f (z, q) ∈ K := (htrace.symm.subset rfl).1
    obtain ⟨x, hx, hxeq⟩ := hg.bijOn.surjOn hzK
    refine ⟨x, hx, ?_⟩
    change (Function.invFunOn f (J ×ˢ Q) (g x)).2 = q
    rw [hxeq, hf.bijOn.invOn_invFunOn.1 ⟨hz, hq⟩]
  exact ⟨isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hπPL ⟨hπQ, hinj, hsurj⟩,
    hfiber⟩

end DifferentialGeometry.Topology.PiecewiseLinear
