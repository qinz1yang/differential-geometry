import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimSpatialJets


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance bufferedMixedTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance bufferedMixedCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance bufferedMixedSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance bufferedMixedC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance bufferedMixedC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance bufferedMixedT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance bufferedMixedSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact


theorem exists_normalized_klim_mixed_jet_bound
    (hdim : Module.finrank ℝ E = 3) (kappa A : ℝ) (hA : 0 ≤ A) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ t : ℝ, t ≤ 0 → ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤ ENNReal.ofReal A →
          DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
          mixedCurvatureNorm F.S p q t y ≤ C := by
  classical
  obtain ⟨K, _, hspatial⟩ := exists_normalized_klim_spatial_jet_constants (I := I) hdim kappa
  choose P hP using fun j : ℕ => exists_mixed_curvature_jet_polynomials 3 p j
  let B : ℕ → ℝ := fun j => shiLocalUniformBound 3 j (K A) (Real.sqrt (K A)) * K A
  refine ⟨1 + curvatureJetPolynomialNormBound (P q) B, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  intro D F hK hbase t ht y hy
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hdim_y : Module.finrank ℝ (TangentSpace I y) = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (F.S.base.metric t) y hdim_y
  have hON : ∀ i j, (F.S.base.metric t).inner y (basis i) (basis j) =
      if i = j then 1 else 0 := horth
  have hactual : DifferentiableWithinAt ℝ
        (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor F.S p q t y) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues F.S (p + 2 * q) t basis) (P q slots) := by
    rcases lt_or_eq_of_le ht with htneg | rfl
    · have htr : t ∈ D.regular := by simpa only [hK.regular_eq, Set.mem_Iio] using htneg
      obtain ⟨hdiff, hcomp⟩ := hP q F.S F.isSolution t htr y basis
      exact ⟨hdiff.differentiableWithinAt, hcomp⟩
    · have hreg : Set.Ioo (-1 : ℝ) 0 ⊆ D.regular := by
        intro s hs
        simpa only [hK.regular_eq, Set.mem_Iio] using hs.2
      exact mixedCurvature_polynomial_terminal_of_regular F.S F.isSolution p
        (by norm_num : (-1 : ℝ) < 0) hK.carrier_eq hreg P y basis
        (fun j s hs => hP j F.S F.isSolution s (hreg hs) y basis) q
  refine ⟨hactual.1, ?_⟩
  have hbound := norm_le_curvatureJetPolynomialNormBound F.S t basis hON (P q)
    (mixedCurvatureTensor F.S p q t y) hactual.2 B
    (fun j _ => hspatial D F hK hbase A hA t ht j y hy)
  exact hbound.trans (le_add_of_nonneg_left zero_le_one)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
