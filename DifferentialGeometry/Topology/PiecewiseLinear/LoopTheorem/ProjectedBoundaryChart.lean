/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryOpenCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem mem_maximalAtlas_of_piece_parametrization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {W : Set X} (B : PLPieceIn E 3 X W)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (φ : EuclideanSpace ℝ (Fin 3) → E) (hφ : IsPiecewiseAffineOn φ e.target)
    (hmaps : MapsTo φ e.target B.complex.space)
    (heq : ∀ z ∈ e.target, e.symm z = B.map (φ z)) :
    e ∈ (plGroupoid 3).maximalAtlas X := by
  intro e' he'
  have hdom : e.target ∩ φ ⁻¹' (B.complex.space ∩ B.map ⁻¹' e'.source) =
      (e.symm.trans e').source := by
    ext z
    change (z ∈ e.target ∧ φ z ∈ B.complex.space ∧ B.map (φ z) ∈ e'.source) ↔
      z ∈ e.target ∧ e.symm z ∈ e'.source
    constructor
    · rintro ⟨hz, -, hs⟩
      exact ⟨hz, (heq z hz).symm ▸ hs⟩
    · rintro ⟨hz, hs⟩
      exact ⟨hz, hmaps hz, heq z hz ▸ hs⟩
  have htrans : e.symm.trans e' ∈ plGroupoid 3 := by
    apply mem_plGroupoid_of_isPiecewiseAffineOn
    have h := (B.isPiecewiseAffineOn_chart e' he').comp hφ
    rw [hdom] at h
    refine h.congr fun z hz => ?_
    change e' (e.symm z) = e' (B.map (φ z))
    rw [heq z hz.1]
  exact ⟨htrans, (plGroupoid 3).symm htrans⟩

private theorem exists_boundary_chart_of_open_product_piece
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {S W : Set X} (T : PLPiece 3 X S)
    (B : PLPieceIn ((EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ) 3 X W)
    (hT : IsCombinatorialManifold 2 T.piece.complex) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : B.complex.space = T.piece.complex.space ×ˢ Icc (-1 : ℝ) 1)
    (hopen : IsOpenEmbedding
      (fun z : T.piece.complex.space × Ioo (-ε) ε => B.map (z.1, z.2)))
    (hcenter : ∀ x : T.piece.complex.space, B.map (x, 0) = T.piece.map x)
    (hzero : ∀ (x : T.piece.complex.space) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      (B.map (x, t) ∈ S ↔ t = 0)) {y : X} (hy : y ∈ S) :
    ∃ (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      e ∈ (plGroupoid 3).maximalAtlas X ∧ ℓ ≠ 0 ∧ y ∈ e.source ∧
      ∀ z ∈ e.source, z ∈ S ↔ ℓ (e z) = 0 := by
  classical
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  let _ := combinatorialChartedSpace T.piece.complex hT
  obtain ⟨u, hu, huy⟩ := T.piece.bijOn.surjOn hy
  let x : T.piece.complex.space := ⟨u, hu⟩
  let a := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hxa : x ∈ a.source := mem_chart_source _ x
  have hpa : IsPiecewiseAffineOn
      (fun z : EuclideanSpace ℝ (Fin 2) => (a.symm z : EuclideanSpace ℝ (Fin T.ambientDim)))
      a.target := by
    obtain ⟨v, hv, ha⟩ := mem_combinatorialChartedSpace_atlas T.piece.complex hT
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 2)) x)
    change IsPiecewiseAffineOn
      (fun z => ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm z :
        EuclideanSpace ℝ (Fin T.ambientDim))) _
    rw [ha]
    exact isPiecewiseAffineOn_vertexChart_symm T.piece.complex hv (hT.isPLSphere_link hv)
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {z | (L.symm z).1 ∈ a.target ∧ (L.symm z).2 ∈ Ioo (-ε) ε}
  have hU : IsOpen U :=
    (a.open_target.prod isOpen_Ioo).preimage L.toContinuousLinearEquiv.symm.continuous
  let φ : EuclideanSpace ℝ (Fin 3) → (EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ :=
    fun z => (a.symm (L.symm z).1, (L.symm z).2)
  let f : EuclideanSpace ℝ (Fin 3) → X := B.map ∘ φ
  have hLU (z : a.target × Ioo (-ε) ε) : L (z.1, z.2) ∈ U := by
    change (L.symm (L ((z.1 : EuclideanSpace ℝ (Fin 2)), (z.2 : ℝ)))).1 ∈ a.target ∧
      (L.symm (L ((z.1 : EuclideanSpace ℝ (Fin 2)), (z.2 : ℝ)))).2 ∈ Ioo (-ε) ε
    rw [L.symm_apply_apply]
    exact ⟨z.1.property, z.2.property⟩
  let j : U ≃ₜ a.target × Ioo (-ε) ε :=
    { toFun := fun z => (⟨(L.symm z).1, z.property.1⟩, ⟨(L.symm z).2, z.property.2⟩)
      invFun := fun z => ⟨L (z.1, z.2), hLU z⟩
      left_inv := fun z => Subtype.ext (L.apply_symm_apply z)
      right_inv := fun z => by
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst (L.symm_apply_apply ((z.1 : EuclideanSpace ℝ (Fin 2)), (z.2 : ℝ)))
        · exact congrArg Prod.snd (L.symm_apply_apply ((z.1 : EuclideanSpace ℝ (Fin 2)), (z.2 : ℝ)))
      continuous_toFun := by
        apply Continuous.prodMk
        · exact
            (L.toContinuousLinearEquiv.symm.continuous.comp continuous_subtype_val).fst.subtype_mk _
        · exact
            (L.toContinuousLinearEquiv.symm.continuous.comp continuous_subtype_val).snd.subtype_mk _
      continuous_invFun :=
        (L.toContinuousLinearEquiv.continuous.comp
          (continuous_fst.subtype_val.prodMk continuous_snd.subtype_val)).subtype_mk hLU }
  have hf : IsOpenEmbedding (U.domRestrict f) := by
    have h := hopen.comp
      ((a.symm.isOpenEmbedding_restrict.prodMap IsOpenEmbedding.id).comp j.isOpenEmbedding)
    exact h
  let z₀ := L (a x, 0)
  have hz₀ : z₀ ∈ U := by
    change (L.symm (L (a x, 0))).1 ∈ a.target ∧
      (L.symm (L (a x, 0))).2 ∈ Ioo (-ε) ε
    rw [L.symm_apply_apply]
    exact ⟨a.map_source hxa, neg_lt_zero.mpr hε, hε⟩
  have hfy : f z₀ = y := by
    change B.map ((a.symm (L.symm (L (a x, 0))).1 : EuclideanSpace ℝ (Fin T.ambientDim)),
      (L.symm (L (a x, 0))).2) = y
    rw [L.symm_apply_apply, a.left_inv hxa]
    exact (hcenter x).trans huy
  let _ : Nonempty U := ⟨⟨z₀, hz₀⟩⟩
  let q := hf.toOpenPartialHomeomorph (U.domRestrict f)
  let r := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    ((↑) : U → EuclideanSpace ℝ (Fin 3))
  let e := q.symm.trans r
  have htarget : e.target ⊆ U := by
    intro z hz
    have hz' : z ∈ ((↑) : U → EuclideanSpace ℝ (Fin 3)) '' univ := hz.1
    rwa [image_univ, Subtype.range_coe] at hz'
  have heq (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ e.target) : e.symm z = f z := by
    change f (r.symm z) = f z
    exact congrArg f (r.right_inv hz.1)
  have hφ : IsPiecewiseAffineOn φ U := by
    have h := (hpa.prodMap (isPiecewiseAffineOn_id (u := Ioo (-ε) ε) isOpen_Ioo)).comp
      (isPiecewiseAffineOn_of_affine L.symm.toLinearMap.toAffineMap isOpen_univ)
    have hdom : (univ : Set (EuclideanSpace ℝ (Fin 3))) ∩
        L.symm ⁻¹' (a.target ×ˢ Ioo (-ε) ε) = U := by rw [univ_inter]; rfl
    change IsPiecewiseAffineOn φ
      (univ ∩ L.symm ⁻¹' (a.target ×ˢ Ioo (-ε) ε)) at h
    rw [hdom] at h
    exact h
  have hmaps : MapsTo φ e.target B.complex.space := by
    intro z hz
    rw [hB]
    exact ⟨(a.symm (L.symm z).1).property,
      (neg_le_neg hε1).trans (htarget hz).2.1.le, (htarget hz).2.2.le.trans hε1⟩
  let ℓ := (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp L.symm.toLinearMap
  have hℓ : ℓ ≠ 0 := by
    intro h
    have hv := congrArg (fun l : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => l (L (0, 1))) h
    change (L.symm (L (0, 1))).2 = 0 at hv
    rw [L.symm_apply_apply] at hv
    norm_num at hv
  refine ⟨e, ℓ, mem_maximalAtlas_of_piece_parametrization B e φ
    (hφ.mono e.open_target htarget) hmaps heq, hℓ, ?_, ?_⟩
  · exact ⟨⟨⟨z₀, hz₀⟩, mem_univ _, hfy⟩, mem_univ _⟩
  · intro z hz
    let w : U := q.symm z
    have hw : f w = z := q.right_inv hz.1
    change z ∈ S ↔ (L.symm (w : EuclideanSpace ℝ (Fin 3))).2 = 0
    rw [← hw]
    exact hzero (a.symm (L.symm w).1) (L.symm w).2
      ⟨(neg_le_neg hε1).trans w.property.2.1.le, w.property.2.2.le.trans hε1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_boundary_chart_glued₂_space_in_double
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (p : K.space) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    ∀ y ∈ frontier C,
      ∃ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        e ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧ y ∈ e.source ∧
        ∀ z ∈ e.source, z ∈ frontier C ↔ ℓ (e z) = 0 := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  change ∀ y ∈ frontier C, _
  intro y hy
  obtain ⟨T, W, B, ε, hε, hε1, -, hT, hB, hopen, hcenter, hzero⟩ :=
    exists_open_bicollar_glued₂_space_in_double K hK p univ Filter.univ_mem
  exact exists_boundary_chart_of_open_product_piece T B hT hε hε1 hB hopen hcenter hzero hy

end DifferentialGeometry.Topology.PiecewiseLinear
