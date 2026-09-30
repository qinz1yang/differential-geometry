import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_union
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P Q : Set E} {P' Q' : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) {f g : E → F}
    (hf : IsPLHomeomorphOn f P P') (hg : IsPLHomeomorphOn g Q Q')
    (hfg : EqOn f g (P ∩ Q)) (hinter : SurjOn f (P ∩ Q) (P' ∩ Q')) :
    ∃ h : E → F, IsPLHomeomorphOn h (P ∪ Q) (P' ∪ Q') ∧ EqOn h f P ∧ EqOn h g Q := by
  classical
  let h := P.piecewise f g
  have hPf : EqOn h f P := fun _ hx => piecewise_eq_of_mem P f g hx
  have hQg : EqOn h g Q := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · exact (hPf hxP).trans (hfg ⟨hxP, hxQ⟩)
    · exact piecewise_eq_of_notMem P f g hxP
  have hcross {x y : E} (hx : x ∈ P) (hy : y ∈ Q) (hxy : f x = g y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hinter ⟨hf.bijOn.mapsTo hx, hxy.symm ▸ hg.bijOn.mapsTo hy⟩
    have hzx' : z = x := hf.bijOn.injOn hz.1 hx hzx
    have hzy : g z = g y := (hfg hz).symm.trans (hzx.trans hxy)
    exact hzx'.symm.trans (hg.bijOn.injOn hz.2 hy hzy)
  have hinj : InjOn h (P ∪ Q) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hPf hx, hPf hy] at hxy
      exact hf.bijOn.injOn hx hy hxy
    · rw [hPf hx, hQg hy] at hxy
      exact hcross hx hy hxy
    · rw [hQg hx, hPf hy] at hxy
      exact (hcross hy hx hxy.symm).symm
    · rw [hQg hx, hQg hy] at hxy
      exact hg.bijOn.injOn hx hy hxy
  have hbij : BijOn h (P ∪ Q) (P' ∪ Q') := by
    refine ⟨?_, hinj, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · rw [hPf hx]
        exact Or.inl (hf.bijOn.mapsTo hx)
      · rw [hQg hx]
        exact Or.inr (hg.bijOn.mapsTo hx)
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn hy
        exact ⟨x, Or.inl hx, (hPf hx).trans hxy⟩
      · obtain ⟨x, hx, hxy⟩ := hg.bijOn.surjOn hy
        exact ⟨x, Or.inr hx, (hQg hx).trans hxy⟩
  have hpl : IsPiecewiseAffineOn h (P ∪ Q) :=
    (hf.isPiecewiseAffineOn.congr hPf).union_of_isClosed (hg.isPiecewiseAffineOn.congr hQg)
      hP.isCompact.isClosed hQ.isCompact.isClosed
  obtain ⟨K, hfinite, hspace⟩ := (hP.union hQ).exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  have hplK : IsPiecewiseAffineOn h K.space := by rwa [hspace]
  have hinjK : InjOn h K.space := by rwa [hspace]
  obtain ⟨L, _, hL, hh⟩ := exists_isPLHomeomorphOn_image K hplK hinjK
  rw [hspace] at hh hL
  rw [hL, hbij.image_eq] at hh
  exact ⟨h, hh, hPf, hQg⟩

theorem exists_isPLHomeomorphOn_union_of_eqOn_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) {f g : E → E}
    (hf : IsPLHomeomorphOn f P P) (hg : IsPLHomeomorphOn g Q Q)
    (hfg : EqOn f g (P ∩ Q)) (hinter : SurjOn f (P ∩ Q) (P ∩ Q)) :
    ∃ h : E → E, IsPLHomeomorphOn h (P ∪ Q) (P ∪ Q) ∧ EqOn h f P ∧ EqOn h g Q :=
  exists_isPLHomeomorphOn_union hP hQ hf hg hfg hinter

end DifferentialGeometry.Topology.PiecewiseLinear
