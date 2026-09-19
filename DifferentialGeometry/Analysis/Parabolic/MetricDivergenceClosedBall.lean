import DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedBall
import DifferentialGeometry.Analysis.Parabolic.WeakEquationAffine

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff Matrix

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)))))
local instance : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m
local instance : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

private theorem chartModelBasis_repr_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x : E) (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr x i = toEuclidean x i := by
  rw [chartModelBasis, Module.Basis.map_repr]
  change (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.repr (toEuclidean x) i = _
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

private def closedCellCoordinateEquiv
    (e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    EuStd ≃ᴬ[ℝ] EuStd := by
  let L : EuN ≃L[ℝ] EuStd := toEuclidean
  let t : EuN ≃ᴬ[ℝ] EuN := ContinuousAffineEquiv.constVAdd ℝ EuN
    (-EuclideanSpace.single (0 : Fin (m + 1)) 1)
  exact L.symm.toContinuousAffineEquiv.trans (t.trans (e.trans L.toContinuousAffineEquiv))

private theorem closedCell_coordinate_affine_matrix
    (e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    let L : EuN ≃L[ℝ] EuStd := toEuclidean
    let s := closedCellCoordinateEquiv e
    (∀ z : EuStd, s z = L (e (closedCellShiftSucc m (-1) (L.symm z)))) ∧
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis s.toAffineEquiv.linear.toLinearMap =
      LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis EuN) e.toAffineEquiv.linear.toLinearMap := by
  intro L s
  constructor
  · intro z
    change L (e (-EuclideanSpace.single (0 : Fin (m + 1)) 1 + L.symm z)) = _
    rw [closedCellShiftSucc_eq_add]
    simp only [EuclideanSpace.basisFun_apply, neg_one_smul, add_comm]
  · ext i j
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, chartModelBasis_repr_apply, chartModelBasis_apply,
      LinearEquiv.coe_coe]
    rfl

variable {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem weak_metric_divergence_comp_closedCell_chart
    (g : ℝ → SmoothRiemannianMetric I M) (α : M) (e : EuN ≃ᴬ[ℝ] EuN)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target)
    {β : ClosedCell (m + 1)} (hβ : ‖β.val‖ < 1)
    {J : Set ℝ} {Ω : Set EuStd} :
    let L : EuN ≃L[ℝ] EuStd := toEuclidean
    let f := fun z => L (e (closedCellShiftSucc m (-1) (L.symm z)))
    let C := LinearMap.toMatrix (chartModelBasis EuN) (chartModelBasis EuN)
      e.toAffineEquiv.linear.toLinearMap
    let h : ℝ → SmoothRiemannianMetric (𝓡∂ (m + 1)) (ClosedCell (m + 1)) :=
      fun t : ℝ => (g t).pullback (I := 𝓡∂ (m + 1)) (J := I) (M := ClosedCell (m + 1)) (N := M)
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val))
      (contMDiff_extChartAt_symm_comp_affine_closedCell α e he)
      (fun x => injective_mfderiv_extChartAt_symm_comp_affine_closedCell α e (he x))
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    let A' := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (h p.1) β i j p.2
    (∀ z ∈ f ⁻¹' Ω, L.symm z ∈ (extChartAt (𝓡∂ (m + 1)) β).target) →
    ∀ (U R : ℝ × EuStd → ℝ) (K : ℝ × EuStd → Fin (Module.finrank ℝ EuN) → ℝ),
      (∀ j, LocallyIntegrableOn (fun p => ((A p).transpose *ᵥ K p) j) (J ×ˢ Ω)
        ((volume : Measure ℝ).prod (volume : Measure EuStd))) →
      (∀ φ : ℝ × EuStd → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
        (∫ p in J ×ˢ Ω, ρ p * U p * fderiv ℝ φ p (1, 0) ∂volume.prod volume) =
          (∑ j, ∫ p in J ×ˢ Ω, ((A p).transpose *ᵥ K p) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod volume) -
          ∫ p in J ×ˢ Ω, R p * φ p ∂volume.prod volume) →
      let K' := fun p : ℝ × EuStd => C.transpose *ᵥ K (p.1, f p.2)
      ∀ φ : ℝ × EuStd → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ (f ⁻¹' Ω) →
        (∫ p in J ×ˢ (f ⁻¹' Ω), densityOnEuclid (h p.1) β p.2 * U (p.1, f p.2) *
          fderiv ℝ φ p (1, 0) ∂volume.prod volume) =
          (∑ j, ∫ p in J ×ˢ (f ⁻¹' Ω), ((A' p).transpose *ᵥ K' p) j *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod volume) -
          ∫ p in J ×ˢ (f ⁻¹' Ω), |e.toAffineEquiv.linear.toLinearMap.det| *
            R (p.1, f p.2) * φ p ∂volume.prod volume := by
  intro L f C h ρ A A' hΩ U R K hV hweak K' φ hφ hφc hφs
  let s := closedCellCoordinateEquiv e
  obtain ⟨hs, hC⟩ := closedCell_coordinate_affine_matrix e
  have hsfun : (s : EuStd → EuStd) = f := funext hs
  have hdet : s.toAffineEquiv.linear.toLinearMap.det = e.toAffineEquiv.linear.toLinearMap.det := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ EuN)) ℝ).toBasis]
    rw [hC, LinearMap.det_toMatrix]
  have hw := weighted_divergence_comp_spatial_affineEquiv s (ρ := ρ) (U := U) (R := R)
    (K := K) (A := A) hV hweak φ hφ hφc (hsfun.symm ▸ hφs)
  dsimp only at hw
  rw [hC, hdet] at hw
  simp only [hsfun] at hw
  have hρ (p : ℝ × EuStd) (hp : p.2 ∈ f ⁻¹' Ω) :
      densityOnEuclid (h p.1) β p.2 =
        |e.toAffineEquiv.linear.toLinearMap.det| * ρ (p.1, f p.2) := by
    have hh := densityOnEuclid_closedCell_chart_pullback_eq_abs_det_mul
      (g p.1) α e he hβ (hΩ p.2 hp)
    simpa only [L, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hA (p : ℝ × EuStd) (hp : p.2 ∈ f ⁻¹' Ω) :
      A' p = |e.toAffineEquiv.linear.toLinearMap.det| • (C⁻¹ * A (p.1, f p.2) * C⁻¹.transpose) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hh := weightedInvGramOnEuclid_closedCell_chart_pullback_eq_congruence
      (g p.1) α e he hβ (hΩ p.2 hp) i j
    simpa only [L, C, A, A', f, Matrix.of_apply, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hz (p : ℝ × EuStd) (hp : p.2 ∉ f ⁻¹' Ω) (v : ℝ × EuStd) : fderiv ℝ φ p v = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x v)
    intro ht
    exact hp (hφs (tsupport_fderiv_apply_subset ℝ v ht)).2
  calc
    _ = ∫ p in J ×ˢ (f ⁻¹' Ω), (|e.toAffineEquiv.linear.toLinearMap.det| * ρ (p.1, f p.2)) *
        U (p.1, f p.2) * fderiv ℝ φ p (1, 0) ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only
        by_cases hp : p.2 ∈ f ⁻¹' Ω
        · rw [hρ p hp]
        · rw [hz p hp, mul_zero, mul_zero]
    _ = _ := by
      rw [hw]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only
        by_cases hp : p.2 ∈ f ⁻¹' Ω
        · rw [hA p hp]
        · rw [hz p hp, mul_zero, mul_zero]

end DifferentialGeometry.Analysis.Parabolic
