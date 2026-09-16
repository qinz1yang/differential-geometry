import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem PLPieceIn.isClosedEmbedding [T2Space X] {Y : Set X} (T : PLPieceIn E n X Y) :
    IsClosedEmbedding (fun x : T.complex.space => T.map x) := by
  let _ : CompactSpace T.complex.space := isCompact_iff_compactSpace.mp T.isPolyhedron_space.isCompact
  exact T.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hxy => Subtype.ext (T.bijOn.injOn x.2 y.2 hxy))

noncomputable def PLPieceIn.homeomorph [T2Space X] {Y : Set X} (T : PLPieceIn E n X Y) :
    T.complex.space ≃ₜ Y :=
  T.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (by
    change range (T.map ∘ ((↑) : T.complex.space → E)) = Y
    rw [range_comp, Subtype.range_coe, T.bijOn.image_eq]))

theorem PLPieceIn.homeomorph_apply_coe [T2Space X] {Y : Set X} (T : PLPieceIn E n X Y)
    (x : T.complex.space) : (T.homeomorph x : X) = T.map x := rfl
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def PLPieceIn.precomp {Y : Set X} (T : PLPieceIn F n X Y)
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space T.complex.space) : PLPieceIn E n X Y := by
  have hbij : BijOn (T.map ∘ f) K.space Y := T.bijOn.comp hf.bijOn
  refine ⟨K, hK, T.map ∘ f, hbij,
    T.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hf.bijOn.mapsTo, ?_, ?_⟩
  · intro e he
    have h := (T.isPiecewiseAffineOn_chart e he).comp hf.isPiecewiseAffineOn
    have heq : K.space ∩ f ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source) =
        K.space ∩ (T.map ∘ f) ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, hf.bijOn.mapsTo hx.1, hx.2⟩⟩
    rw [heq] at h
    exact h.congr fun _ _ => rfl
  · intro e he
    have h := hf.symm.isPiecewiseAffineOn.comp (T.isPiecewiseAffineOn_chart_symm e he)
    have hsub : e.target ∩ e.symm ⁻¹' Y ⊆
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' T.complex.space :=
      fun _ hy => T.bijOn.surjOn.mapsTo_invFunOn hy.2
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun y hy => ?_
    have hyT : Function.invFunOn T.map T.complex.space (e.symm y) ∈ T.complex.space :=
      T.bijOn.surjOn.mapsTo_invFunOn hy.2
    apply hbij.injOn (hbij.surjOn.mapsTo_invFunOn hy.2)
      (hf.bijOn.surjOn.mapsTo_invFunOn hyT)
    change (T.map ∘ f) (Function.invFunOn (T.map ∘ f) K.space (e.symm y)) =
      T.map (f (Function.invFunOn f K.space
        (Function.invFunOn T.map T.complex.space (e.symm y))))
    rw [hbij.invOn_invFunOn.2 hy.2, hf.bijOn.invOn_invFunOn.2 hyT,
      T.bijOn.invOn_invFunOn.2 hy.2]

theorem PLPieceIn.precomp_complex {Y : Set X} (T : PLPieceIn F n X Y)
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space T.complex.space) : (T.precomp K hK hf).complex = K := rfl

theorem PLPieceIn.precomp_map {Y : Set X} (T : PLPieceIn F n X Y)
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space T.complex.space) : (T.precomp K hK hf).map = T.map ∘ f := rfl

end DifferentialGeometry.Topology.PiecewiseLinear
