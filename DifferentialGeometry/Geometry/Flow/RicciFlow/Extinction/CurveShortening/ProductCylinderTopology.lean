import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLoopEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap

section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_productCurve_of_continuous_map
    (A : QuotientProductAtlas I M) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {P : Type*} [TopologicalSpace P]
    (c : P → ProductCurve M)
    (hc : letI := A.charts
      @Continuous P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
        (smoothCylinderTopology (A.smoothLoopEmbedding e) J) (fun p => (c p).map)) :
    @Continuous P (ProductCurve M) inferInstance (smoothProductCylinderTopology e J) c := by
  let L : (EuclideanSpace ℝ (Fin N) × ℂ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + 2)) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
  let := A.charts
  let eP := A.smoothLoopEmbedding e
  let K := ‖L.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hcoordinates (d : ProductCurve M) :
      (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2) =
        L.symm ∘ (fun q : ℝ × ℝ => eP.map (d.map.lift q.1 q.2)) := by
    funext q
    have hforward : eP.map (d.map.lift q.1 q.2) =
        L (productEmbeddedCoordinates e d q.1 q.2) := rfl
    rw [Function.comp_apply, hforward, L.symm_apply_apply]
  have hbound (d d' : ProductCurve M) (m : ℕ) (q : ℝ × ℝ)
      (hq : q ∈ univ ×ˢ J) :
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
          (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d' q.1 q.2)
          (univ ×ˢ J) q‖ ≤
        K * ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => eP.map (d.map.lift q.1 q.2))
          (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => eP.map (d'.map.lift q.1 q.2))
          (univ ×ˢ J) q‖ := by
    rw [hcoordinates d, hcoordinates d',
      L.symm.iteratedFDerivWithin_comp_left _ (uniqueDiffOn_univ.prod hJ) hq,
      L.symm.iteratedFDerivWithin_comp_left _ (uniqueDiffOn_univ.prod hJ) hq]
    have hsub (F G : (ℝ × ℝ) [×m]→L[ℝ] EuclideanSpace ℝ (Fin (N + 2))) :
        L.symm.toContinuousLinearMap.compContinuousMultilinearMap F -
          L.symm.toContinuousLinearMap.compContinuousMultilinearMap G =
        L.symm.toContinuousLinearMap.compContinuousMultilinearMap (F - G) := by
      apply ContinuousMultilinearMap.ext
      intro v
      change L.symm (F v) - L.symm (G v) = L.symm (F v - G v)
      exact (map_sub L.symm (F v) (G v)).symm
    rw [hsub]
    exact (L.symm.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _))
  let : TopologicalSpace (ProductCurve M) := smoothProductCylinderTopology e J
  let : TopologicalSpace (CurveMap (M × Surgery.Topology.Circle)) :=
    smoothCylinderTopology eP J
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcat := hc.continuousAt (x := p)
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hcat
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro U ⟨d, m, ε, hε, rfl⟩ ⟨ρ₀, hρ₀, hb₀⟩
  have hgap : 0 < (ε - ρ₀) / K := div_pos (sub_pos.mpr hρ₀) hK
  have hW := hcat _ ⟨(c p).map, m, (ε - ρ₀) / K, hgap, rfl⟩
    ⟨0, hgap, fun q _ => by simp⟩
  filter_upwards [hW] with p' hp'
  obtain ⟨ρ, hρ, hb⟩ := hp'
  have hmax : max ρ 0 < (ε - ρ₀) / K := max_lt hρ hgap
  have hmul : K * max ρ 0 < ε - ρ₀ := by
    have h := (lt_div_iff₀ hK).mp hmax
    simpa only [mul_comm] using h
  refine ⟨K * max ρ 0 + ρ₀, by linarith, ?_⟩
  intro q hq
  have htriangle := norm_add_le
    (iteratedFDerivWithin ℝ m (fun q => productEmbeddedCoordinates e (c p') q.1 q.2)
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q => productEmbeddedCoordinates e (c p) q.1 q.2)
        (univ ×ˢ J) q)
    (iteratedFDerivWithin ℝ m (fun q => productEmbeddedCoordinates e (c p) q.1 q.2)
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q => productEmbeddedCoordinates e d q.1 q.2)
        (univ ×ˢ J) q)
  rw [sub_add_sub_cancel] at htriangle
  exact htriangle.trans (add_le_add
    ((hbound (c p') (c p) m q ⟨mem_univ q.1, hq.2⟩).trans
      (mul_le_mul_of_nonneg_left ((hb q hq).trans (le_max_left _ _)) hK.le)) (hb₀ q hq))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end

section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_map_of_continuous_productCurve
    (A : QuotientProductAtlas I M) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {P : Type*} [TopologicalSpace P]
    (c : P → ProductCurve M)
    (hc : @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e J) c) :
    letI := A.charts
    @Continuous P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
      (smoothCylinderTopology (A.smoothLoopEmbedding e) J) (fun p => (c p).map) := by
  let L : (EuclideanSpace ℝ (Fin N) × ℂ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + 2)) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
  let := A.charts
  let eP := A.smoothLoopEmbedding e
  let K := ‖L.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hcoordinates (d : ProductCurve M) :
      (fun q : ℝ × ℝ => eP.map (d.map.lift q.1 q.2)) =
        L ∘ (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2) := by
    funext q
    have hforward : eP.map (d.map.lift q.1 q.2) =
        L (productEmbeddedCoordinates e d q.1 q.2) := rfl
    rw [Function.comp_apply, hforward]
  have hbound (d d' : ProductCurve M) (m : ℕ) (q : ℝ × ℝ)
      (hq : q ∈ univ ×ˢ J) :
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => eP.map (d.map.lift q.1 q.2))
          (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => eP.map (d'.map.lift q.1 q.2))
          (univ ×ˢ J) q‖ ≤
        K * ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
            (univ ×ˢ J) q -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => productEmbeddedCoordinates e d' q.1 q.2)
            (univ ×ˢ J) q‖ := by
    rw [hcoordinates d, hcoordinates d',
      L.iteratedFDerivWithin_comp_left _ (uniqueDiffOn_univ.prod hJ) hq,
      L.iteratedFDerivWithin_comp_left _ (uniqueDiffOn_univ.prod hJ) hq]
    have hsub (F G : (ℝ × ℝ) [×m]→L[ℝ] (EuclideanSpace ℝ (Fin N) × ℂ)) :
        L.toContinuousLinearMap.compContinuousMultilinearMap F -
          L.toContinuousLinearMap.compContinuousMultilinearMap G =
        L.toContinuousLinearMap.compContinuousMultilinearMap (F - G) := by
      apply ContinuousMultilinearMap.ext
      intro v
      change L (F v) - L (G v) = L (F v - G v)
      exact (map_sub L (F v) (G v)).symm
    rw [hsub]
    exact (L.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _))
  let : TopologicalSpace (ProductCurve M) := smoothProductCylinderTopology e J
  let : TopologicalSpace (CurveMap (M × Surgery.Topology.Circle)) :=
    smoothCylinderTopology eP J
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcat := hc.continuousAt (x := p)
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hcat
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro U ⟨d, m, ε, hε, rfl⟩ ⟨ρ₀, hρ₀, hb₀⟩
  have hgap : 0 < (ε - ρ₀) / K := div_pos (sub_pos.mpr hρ₀) hK
  have hW := hcat _ ⟨c p, m, (ε - ρ₀) / K, hgap, rfl⟩
    ⟨0, hgap, fun q _ => by simp⟩
  filter_upwards [hW] with p' hp'
  obtain ⟨ρ, hρ, hb⟩ := hp'
  have hmax : max ρ 0 < (ε - ρ₀) / K := max_lt hρ hgap
  have hmul : K * max ρ 0 < ε - ρ₀ := by
    have h := (lt_div_iff₀ hK).mp hmax
    simpa only [mul_comm] using h
  refine ⟨K * max ρ 0 + ρ₀, by linarith, ?_⟩
  intro q hq
  have htriangle := norm_add_le
    (iteratedFDerivWithin ℝ m (fun q => eP.map ((c p').map.lift q.1 q.2))
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q => eP.map ((c p).map.lift q.1 q.2))
        (univ ×ˢ J) q)
    (iteratedFDerivWithin ℝ m (fun q => eP.map ((c p).map.lift q.1 q.2))
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q => eP.map (d.lift q.1 q.2))
        (univ ×ˢ J) q)
  rw [sub_add_sub_cancel] at htriangle
  exact htriangle.trans (add_le_add
    ((hbound (c p') (c p) m q ⟨mem_univ q.1, hq.2⟩).trans
      (mul_le_mul_of_nonneg_left ((hb q hq).trans (le_max_left _ _)) hK.le)) (hb₀ q hq))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem smoothProductCylinderTopology_continuous_mono
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J K : Set ℝ}
    (hJK : J ⊆ K) (hJ : UniqueDiffOn ℝ J) (hK : UniqueDiffOn ℝ K)
    (c : P → ProductCurve M)
    (hc : @Continuous P (ProductCurve M) inferInstance (smoothProductCylinderTopology e K) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) K) :
    @Continuous P (ProductCurve M) inferInstance (smoothProductCylinderTopology e J) c := by
  let A : QuotientProductAtlas I M := quotientProductAtlas (I := I) (M := M)
  let := A.charts
  let := A.smoothManifold
  have hmap := continuous_map_of_continuous_productCurve A e hK c hc
  have hrestrict := smoothCylinderTopology_continuous_mono (A.smoothLoopEmbedding e)
    hJK hJ hK hmap (fun p => (c p).smoothOn_map A (hs p))
  exact continuous_productCurve_of_continuous_map A e hJ c hrestrict

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end
