import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Basic
import DifferentialGeometry.Topology.PiecewiseLinear.Map.Composition
import DifferentialGeometry.Topology.PiecewiseLinear.Map.EuclideanSpace
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.isPLHomeomorphOn_invFunOn_comp
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {m : ℕ} {N : Set X} (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X N)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → X}
    (hu : IsPLHomeomorphInto 3 u P) (hNP : N ⊆ u '' P) :
    IsPLHomeomorphOn (Function.invFunOn u P ∘ T.map) T.complex.space
      (Function.invFunOn u P '' N) := by
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin m) → _)
      T.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.isPolyhedron_space
      (subset_univ _)
  have hmap : IsPLOn m 3 (T.map ∘ id) T.complex.space :=
    T.isPLOn_comp hid (mapsTo_id _)
  have hmaps : MapsTo (T.map ∘ id) T.complex.space (u '' P) :=
    fun x hx => hNP (T.bijOn.mapsTo hx)
  have hpa : IsPiecewiseAffineOn (Function.invFunOn u P ∘ T.map ∘ id)
      T.complex.space :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hmap hmaps)
  have hsec : ∀ z ∈ u '' P, u (Function.invFunOn u P z) = z := fun z hz =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hinj : InjOn (Function.invFunOn u P ∘ T.map) T.complex.space := by
    intro x hx y hy hxy
    refine T.bijOn.injOn hx hy ?_
    have hx' := hsec _ (hmaps hx)
    have hy' := hsec _ (hmaps hy)
    exact hx'.symm.trans ((congrArg u hxy).trans hy')
  have himg : (Function.invFunOn u P ∘ T.map) '' T.complex.space =
      Function.invFunOn u P '' N := by rw [image_comp, T.bijOn.image_eq]
  rw [← himg]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.isPolyhedron_space hpa
    hinj.bijOn_image

end DifferentialGeometry.Topology.PiecewiseLinear
