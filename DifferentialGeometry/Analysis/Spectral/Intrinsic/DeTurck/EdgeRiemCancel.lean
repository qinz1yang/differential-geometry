import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairing
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Exact Riemann cancellation at the closed edge

The closed-edge Ricci--DeTurck refold initially exposes a Riemann--Palatini
order-zero family together with its second-order formal partner.  Those two
pieces are not error terms: together they reproduce exactly the Riemann term
inserted in `edgeRicciHalf`.  This file cancels that complete block before any
estimate is taken.

The resulting producer retains only the genuine connection-difference
order-zero Ricci coefficient and the DeTurck Lie refold.  In particular, no
Riemann second-order budget remains in the boundary energy estimate.
-/

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

/-! ## Exact algebraic cancellation -/

/-- A Riemann refold identity cancels exactly against the Riemann half inserted
in `edgeRicciHalf`, leaving only the connection-difference Ricci coefficient. -/
theorem edgeRiem_cancel
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (C₀ : SmoothCcTensor g 2 2) (C₂ : SmoothCcTensor g 4 2)
    (hrefold :
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g gm) W =
        operatorFieldApply (I := I) (M := M) g 2 2 C₀ W +
          operatorFieldApply (I := I) (M := M) g 4 2 C₂
            (iteratedCovGrad (I := I) g 0 2 2 W)) :
    (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
        (edgeRicciHalf (I := I) (M := M) g gm) W +
      (operatorFieldApply (I := I) (M := M) g 2 2 C₀ W +
        operatorFieldApply (I := I) (M := M) g 4 2 C₂
          (iteratedCovGrad (I := I) g 0 2 2 W)) =
      (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
        (linearizedRicciConnDiffOrder0CoeffField
          (I := I) (M := M) g gm) W := by
  rw [← hrefold]
  simp only [edgeRicciHalf, appCc_add_left, appCc_smul_left]
  module

/-! ## Lie-only formal pairing -/

omit [BoundarylessManifold I M] in
/-- The DeTurck Lie pair field is the exact Hilbert-space formal partner of
the Lie second-order refold family. -/
theorem edgeLie_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, operatorFieldApply (I := I) (M := M) g 2 2
        (edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ
          q epsilon s) T⟫_ℝ : Real) =
      ⟪edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ q epsilon s,
        iteratedCovGrad (I := I) g 0 2 2 T⟫_ℝ := by
  rw [edgeLiePairFam, edgeLiePartner,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_add_left, appCc_smul_left,
    inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  simp_rw [edgePair_inner (I := I) (M := M) g]

/-- Green form of the Lie-only refold pairing.  Every second derivative of
the edge tensor is transferred to the explicit Lie formal partner. -/
theorem edgeLie_green
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, operatorFieldApply (I := I) (M := M) g 2 2
        (edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ
          q epsilon s) T⟫_ℝ : Real) =
      -⟪covDivergence (I := I) (M := M) g 3
          (edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ
            q epsilon s),
        iteratedCovGrad (I := I) g 0 2 1 T⟫_ℝ := by
  let P : SmoothCcTensor g 0 4 :=
    edgeLiePartner (I := I) (M := M) g T hdelta hdeltaZ q epsilon s
  let T₁ : SmoothCcTensor g 0 3 := iteratedCovGrad (I := I) g 0 2 1 T
  have hjet : iteratedCovGrad (I := I) g 0 2 2 T =
      covGrad (I := I) (M := M) g 0 3 T₁ := by
    dsimp only [T₁]
    exact (iteratedCovGrad_succ g 0 2 1 T).symm
  have hgreen :
      (⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_ℝ : Real) =
        -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_ℝ := by
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 3 T₁ P
  calc
    (⟪T, operatorFieldApply (I := I) (M := M) g 2 2
        (edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ
          q epsilon s) T⟫_ℝ : Real) =
        ⟪P, iteratedCovGrad (I := I) g 0 2 2 T⟫_ℝ := by
      exact edgeLie_inner (I := I) (M := M) g T hdelta hdeltaZ
        q epsilon s
    _ = ⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_ℝ := by
      rw [hjet, real_inner_comm]
    _ = -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_ℝ := hgreen
    _ = -⟪covDivergence (I := I) (M := M) g 3 P, T₁⟫_ℝ := by
      rw [real_inner_comm]

/-! ## Consumer-shaped Lie-only refold -/

/-- The complete closed-edge nonlinear arm has a refold in which the whole
Riemann--Palatini block has cancelled.  The only second-order piece left is
the explicit DeTurck Lie pair family, with uniformly bounded signs and a
uniformly bounded order-zero refold coefficient. -/
theorem exists_edgeLieRef
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B₀ : Real, 0 ≤ B₀ ∧
      ∃ (C₀ : Real → SmoothCcTensor g 2 2)
        (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
        (∀ i, |epsilon i| ≤ 1) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1,
          edgeQuadArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W =
            (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
                (linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s)) W +
              operatorFieldApply (I := I) (M := M) g 2 2 (C₀ s) W +
              operatorFieldApply (I := I) (M := M) g 2 2
                (edgeFold0 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
              operatorFieldApply (I := I) (M := M) g 3 2
                (edgeQuad1 (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
                (iteratedCovGrad (I := I) g 0 2 1 W) +
              operatorFieldApply (I := I) (M := M) g 2 2
                (edgeLiePairFam (I := I) (M := M) g W hdelta
                  (edgeZeroBoundAt (I := I) (M := M) g hdelta_nn)
                  q epsilon s) W) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C₀ s).toSection x) ≤ B₀ ^ 2) := by
  classical
  let a : Nat := 2 * Module.finrank Real E + 10
  let R : Real := ∑ j ∈ Finset.range (a + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j W‖
  have ha : 2 * Module.finrank Real E + 10 ≤ a := by rfl
  have hR : 0 ≤ R :=
    Finset.sum_nonneg fun j _ => norm_nonneg _
  have hball : ∀ j : Nat, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g 0 2 j W‖ ≤ R := by
    intro j hj
    exact Finset.single_le_sum
      (f := fun k => ‖iteratedCovGrad (I := I) g 0 2 k W‖)
      (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hhalf_lt : (1 / 2 : Real) < 1 := by norm_num
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half hhalf_lt
  let hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta :=
    edgeZeroBoundAt (I := I) (M := M) g hdelta_nn
  obtain ⟨LambdaD, hLambdaD, KD, hKD, q, epsilon, hepsilon, hDmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M)
      g g_bg a ha hR hhalf_lt
  obtain ⟨C0D, hjD, hidD, hsupD, henvD⟩ :=
    hDmain W hWsymm hdelta_half hdelta hdeltaZ hball
  have hnormal : ∀ s ∈ Set.Icc (0 : Real) 1,
      edgeQuadArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W =
        (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
            (linearizedRicciConnDiffOrder0CoeffField
              (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s)) W +
          operatorFieldApply (I := I) (M := M) g 2 2 (C0D s) W +
          operatorFieldApply (I := I) (M := M) g 2 2
            (edgeFold0 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
          operatorFieldApply (I := I) (M := M) g 3 2
            (edgeQuad1 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          operatorFieldApply (I := I) (M := M) g 2 2
            (edgeLiePairFam (I := I) (M := M) g W hdelta hdeltaZ
              q epsilon s) W := by
    intro s hs
    have hmetric := edgeMetric_bal (I := I) (M := M)
      g W hdelta_lt hdelta hdeltaZ hs
    have hlie := hidD s hs
    simp only [iteratedCovGrad_zero] at hlie
    have hlieApply := edgeLiePair_apply (I := I) (M := M)
      g W hdelta hdeltaZ q epsilon s
    rw [hmetric]
    simp only [edgeQuadArm, edgeLowerArm, edgeQuad0,
      deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      appCc_add_left, appCc_sub_left, appCc_smul_left]
    rw [hlie, ← hlieApply]
    simp only [edgeFold0, appCc_add_left, appCc_sub_left]
    module
  refine ⟨LambdaD, hLambdaD, C0D, q, epsilon, hepsilon, hnormal, ?_⟩
  exact hsupD

end Spectral
end Analysis
end DifferentialGeometry

end
