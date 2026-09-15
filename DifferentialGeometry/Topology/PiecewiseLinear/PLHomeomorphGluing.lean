import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_union_of_eqOn_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) {f g : E → E}
    (hf : IsPLHomeomorphOn f P P) (hg : IsPLHomeomorphOn g Q Q)
    (hfg : EqOn f g (P ∩ Q)) (hinter : SurjOn f (P ∩ Q) (P ∩ Q)) :
    ∃ h : E → E, IsPLHomeomorphOn h (P ∪ Q) (P ∪ Q) ∧ EqOn h f P ∧ EqOn h g Q := by
  classical
  let h := P.piecewise f g
  have hPf : EqOn h f P := fun _ hx => piecewise_eq_of_mem P f g hx
  have hQg : EqOn h g Q := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · exact (hPf hxP).trans (hfg ⟨hxP, hxQ⟩)
    · exact piecewise_eq_of_notMem P f g hxP
  have hgP {x : E} (hxQ : x ∈ Q) : g x ∈ P ↔ x ∈ P := by
    constructor
    · intro hxP
      obtain ⟨y, hy, hyx⟩ := hinter ⟨hxP, hg.bijOn.mapsTo hxQ⟩
      have hgy : g y = g x := (hfg hy).symm.trans hyx
      exact hg.bijOn.injOn hy.2 hxQ hgy ▸ hy.1
    · intro hxP
      rw [← hfg ⟨hxP, hxQ⟩]
      exact hf.bijOn.mapsTo hxP
  have hPiff {x : E} (hx : x ∈ P ∪ Q) : h x ∈ P ↔ x ∈ P := by
    by_cases hxP : x ∈ P
    · rw [hPf hxP]
      exact iff_of_true (hf.bijOn.mapsTo hxP) hxP
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      rw [hQg hxQ]
      exact hgP hxQ
  have hinj : InjOn h (P ∪ Q) := by
    intro x hx y hy hxy
    by_cases hxP : x ∈ P
    · have hyP : y ∈ P := (hPiff hy).mp (hxy ▸ (hPiff hx).mpr hxP)
      rw [hPf hxP, hPf hyP] at hxy
      exact hf.bijOn.injOn hxP hyP hxy
    · have hyP : y ∉ P := fun hyP => hxP ((hPiff hx).mp (hxy ▸ (hPiff hy).mpr hyP))
      have hxQ : x ∈ Q := hx.resolve_left hxP
      have hyQ : y ∈ Q := hy.resolve_left hyP
      rw [hQg hxQ, hQg hyQ] at hxy
      exact hg.bijOn.injOn hxQ hyQ hxy
  have hbij : BijOn h (P ∪ Q) (P ∪ Q) := by
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
  have : Finite K.faces := hfinite.to_subtype
  have hplK : IsPiecewiseAffineOn h K.space := by rwa [hspace]
  have hinjK : InjOn h K.space := by rwa [hspace]
  obtain ⟨L, _, hL, hh⟩ := exists_isPLHomeomorphOn_image K hplK hinjK
  rw [hspace] at hh hL
  rw [hL, hbij.image_eq] at hh
  exact ⟨h, hh, hPf, hQg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
