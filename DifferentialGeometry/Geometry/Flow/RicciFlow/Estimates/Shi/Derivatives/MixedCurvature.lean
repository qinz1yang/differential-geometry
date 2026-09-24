import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomialBounds

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

theorem exists_mixedCurvatureNorm_bound_on_curvature_cylinder
    (n p q : ℕ) (hn : 2 ≤ n) {K R tau : ℝ}
    (hK : 0 < K) (hR : 0 < R) (htau : 0 < tau) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E]
        {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        [I.Boundaryless] {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → Module.finrank ℝ E = n →
        ∀ a : ℝ, Set.Icc a (a + tau) ⊆ D.regular → ∀ x : M,
        IsCompact {y : M | riemannianEDistOf (I := I) (S.base.metric a) x y ≤
          ENNReal.ofReal (R / Real.sqrt K)} →
        (∀ t ∈ Set.Icc a (a + tau), ∀ y : M,
          riemannianEDistOf (I := I) (S.base.metric a) x y ≤
            ENNReal.ofReal (R / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) →
        ∀ y : M, riemannianEDistOf (I := I) (S.base.metric a) x y ≤
          ENNReal.ofReal (R / (2 * Real.sqrt K)) →
        mixedCurvatureNorm S p q (a + tau) y ≤ C := by
  classical
  obtain ⟨P, hP⟩ := exists_mixed_curvature_jet_polynomials.{u, uE, uH} n p q
  let B : ℕ → ℝ := fun j => shiLocalUniformBound n j (K * tau) R * K /
    Real.sqrt tau ^ j
  refine ⟨1 + curvatureJetPolynomialNormBound P B,
    add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _), ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ _ D S hS hdim a hregular x hball hcurv y hy
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  have hab : a < a + tau := lt_add_of_pos_right a htau
  have hcarrier : Set.Icc a (a + tau) ⊆ D.carrier :=
    hregular.trans D.regular_subset
  have hb : a + tau ∈ D.regular := hregular ⟨hab.le, le_rfl⟩
  have hdim_y : Module.finrank ℝ (TangentSpace I y) = n := hdim
  have hbasis := exists_orthonormal_basis (I := I) (S.base.metric (a + tau)) y
  rw [hdim_y] at hbasis
  obtain ⟨basis, horth⟩ := hbasis
  have hpoly := (hP S hS (a + tau) hb y basis).2
  have hspatial : ∀ j ≤ p + 2 * q,
      curvDerivNorm (I := I) j (S.base.metric (a + tau)) y ≤ B j := by
    intro j _
    have h := shi_local_curvDerivNorm_terminal_of_solution_jets S hS
      (by simpa only [hdim] using hn) hab hK hR hcarrier
      (fun t ht => hregular ⟨ht.1, ht.2.le⟩) x hball hcurv
      j (a + tau) ⟨hab, le_rfl⟩ y hy
    simpa only [hdim, add_sub_cancel_left, B] using h
  have hbound := norm_le_curvatureJetPolynomialNormBound S (a + tau) basis horth P
    (mixedCurvatureTensor S p q (a + tau) y) hpoly B hspatial
  exact hbound.trans (le_add_of_nonneg_left zero_le_one)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
