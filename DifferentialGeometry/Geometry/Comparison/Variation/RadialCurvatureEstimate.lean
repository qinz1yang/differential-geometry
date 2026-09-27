import DifferentialGeometry.Geometry.Comparison.Variation.RadialEndpoint
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set intervalIntegral
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem RadialEndpointVariation.secondVariation_half_energy_le_inv_sub_quarter
    {g : SmoothRiemannianMetric I M} {gamma beta : ℝ → M}
    {L kappa : ℝ} (D : RadialEndpointVariation (I := I) g gamma beta L)
    (hkappa : 0 < kappa) (hL : 2 < L)
    (hcurvNonneg : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (D.variation 0 t)
        ((riemannOp (LeviCivita (I := I) g) (D.variation 0 t))
          (D.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
        (D.parallelField t))
    (hcurvLower : ∀ t ∈ Set.Icc (L - 1) L,
      kappa ≤ g.inner (D.variation 0 t)
        ((riemannOp (LeviCivita (I := I) g) (D.variation 0 t))
          (D.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
        (D.parallelField t)) :
    deriv
      (fun s : ℝ => deriv
        (fun r : ℝ => (1 / 2 : ℝ) *
          curveEnergy (I := I) g (fun t : ℝ => D.variation r t) 0 L) s) 0 ≤
      1 / L - kappa / 4 := by
  have hLpos : 0 < L := by linarith
  have hzeroLast : 0 ≤ L - 1 := by linarith
  have hlastL : L - 1 ≤ L := by linarith
  have hbaseEq : (fun t : ℝ ↦ D.variation 0 t) = D.baseCurve :=
    funext D.central
  have hfieldEq :
      (fun t : ℝ ↦ centralVariationField (I := I) D.variation t) =
        (fun t : ℝ ↦ D.radialField t) :=
    funext D.centralField
  let density : ℝ → ℝ := fun t ↦
    indexFormIntegrand (I := I) g (fun u : ℝ ↦ D.variation 0 u)
      (fun u : ℝ ↦ centralVariationField (I := I) D.variation u)
      (fun u : ℝ ↦ centralVariationField (I := I) D.variation u) t
  have hdensity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) L) :
      density t = (1 / L) ^ 2 - (t / L) ^ 2 *
        g.inner (D.variation 0 t)
          ((riemannOp (LeviCivita (I := I) g) (D.variation 0 t))
            (D.parallelField t)
            (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
          (D.parallelField t) := by
    dsimp only [density]
    apply indexFormIntegrand_eq_of_radial_data
      (I := I) g (fun u : ℝ ↦ D.variation 0 u)
        (fun u : ℝ ↦ centralVariationField (I := I) D.variation u)
        D.parallelField L t
    · exact (D.centralField t).trans (D.radialValue t ht)
    · rw [hfieldEq, hbaseEq]
      exact D.radialCovDeriv t ht
    · rw [D.central t]
      exact D.parallelUnit t ht
  have hdensityContinuous : ContinuousOn density (Set.Icc (0 : ℝ) L) := by
    dsimp only [density]
    exact centralVariation_indexFormIntegrand_continuousOn
      (I := I) (M := M) g D.variation D.smooth L
  have hdensityFirst : IntervalIntegrable density MeasureTheory.volume 0 (L - 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hzeroLast]
    exact hdensityContinuous.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans hlastL⟩)
  have hdensityLast : IntervalIntegrable density MeasureTheory.volume (L - 1) L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hlastL]
    exact hdensityContinuous.mono (by
      intro t ht
      exact ⟨hzeroLast.trans ht.1, ht.2⟩)
  have hfirst :
      (∫ t in (0 : ℝ)..(L - 1), density t) ≤
        ∫ _t in (0 : ℝ)..(L - 1), (1 / L) ^ 2 := by
    apply intervalIntegral.integral_mono_on hzeroLast hdensityFirst
      intervalIntegrable_const
    intro t ht
    have htFull : t ∈ Set.Icc (0 : ℝ) L := ⟨ht.1, ht.2.trans hlastL⟩
    rw [hdensity t htFull]
    have hnonneg := mul_nonneg (sq_nonneg (t / L)) (hcurvNonneg t htFull)
    linarith
  have hlast :
      (∫ t in (L - 1)..L, density t) ≤
        ∫ _t in (L - 1)..L, (1 / L) ^ 2 - kappa / 4 := by
    apply intervalIntegral.integral_mono_on hlastL hdensityLast
      intervalIntegrable_const
    intro t ht
    have htFull : t ∈ Set.Icc (0 : ℝ) L := ⟨hzeroLast.trans ht.1, ht.2⟩
    rw [hdensity t htFull]
    have htHalf : (1 / 2 : ℝ) ≤ t / L := by
      rw [le_div_iff₀ hLpos]
      exact (lt_of_lt_of_le (by nlinarith) ht.1).le
    have hweight : (1 / 4 : ℝ) ≤ (t / L) ^ 2 := by
      nlinarith [sq_nonneg (t / L - 1 / 2)]
    have hweighted : kappa / 4 ≤ (t / L) ^ 2 *
        g.inner (D.variation 0 t)
          ((riemannOp (LeviCivita (I := I) g) (D.variation 0 t))
            (D.parallelField t)
            (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
          (D.parallelField t) := by
      calc
        kappa / 4 = (1 / 4 : ℝ) * kappa := by ring
        _ ≤ (t / L) ^ 2 * kappa :=
          mul_le_mul_of_nonneg_right hweight hkappa.le
        _ ≤ (t / L) ^ 2 *
            g.inner (D.variation 0 t)
              ((riemannOp (LeviCivita (I := I) g) (D.variation 0 t))
                (D.parallelField t)
                (mfderiv 𝓘(ℝ, ℝ) I
                  (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I
                  (fun u : ℝ ↦ D.variation 0 u) t (1 : ℝ)))
              (D.parallelField t) :=
          mul_le_mul_of_nonneg_left (hcurvLower t ht) (sq_nonneg (t / L))
    linarith
  have hindex :
      indexForm (I := I) g (fun u : ℝ ↦ D.variation 0 u) 0 L
          (fun u : ℝ ↦ centralVariationField (I := I) D.variation u)
          (fun u : ℝ ↦ centralVariationField (I := I) D.variation u) ≤
        1 / L - kappa / 4 := by
    rw [indexForm_eq_intervalIntegral]
    change (∫ t in (0 : ℝ)..L, density t) ≤ 1 / L - kappa / 4
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hdensityFirst hdensityLast]
    calc
      (∫ t in (0 : ℝ)..(L - 1), density t) +
          ∫ t in (L - 1)..L, density t ≤
        (∫ _t in (0 : ℝ)..(L - 1), (1 / L) ^ 2) +
          ∫ _t in (L - 1)..L, (1 / L) ^ 2 - kappa / 4 :=
        add_le_add hfirst hlast
      _ = 1 / L - kappa / 4 := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        field_simp
        ring
  have hsecond :=
    secondVariation_half_curveEnergy_geodesic_fixedInitial_geodesicTerminal
      (I := I) (M := M) g D.variation L D.smooth hLpos
        D.centralGeodesic D.fixedInitial D.terminalGeodesic
  rw [hsecond.deriv]
  exact hindex

omit [T2Space M] in
theorem RadialEndpointVariation.parallel_inner_velocity_eq_terminal
    {g : SmoothRiemannianMetric I M} {gamma beta : ℝ → M}
    {L : ℝ} (D : RadialEndpointVariation (I := I) g gamma beta L)
    (hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgammaGeo : IsGeodesic (I := I) g gamma) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (gamma t) (D.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) =
        g.inner (gamma L) (D.parallelField L)
          (mfderiv 𝓘(ℝ, ℝ) I gamma L (1 : ℝ)) := by
  classical
  let V : ∀ t, TangentSpace I (gamma t) := fun t ↦ D.parallelField t
  let T : ∀ t, TangentSpace I (gamma t) := fun t ↦
    mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
  have hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t := by
    intro t ht
    have hrep := chartRep_congr_curve (I := I)
      D.parallelField V (D.agreesGerm t ht)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    exact hrep.differentiableAt_iff.mp (D.parallelDifferentiable t ht)
  have hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g gamma V t = 0 := by
    intro t ht
    have hcongr := covDerivAlong_congr_curve (I := I) g
      D.parallelField V (D.agreesGerm t ht)
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hzero := D.parallelCovDeriv t ht
    exact_mod_cast hcongr.symm.trans hzero
  have hTdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) gamma T t) t := by
    intro t _ht
    exact velocity_chartRepAt_differentiableAt (I := I) gamma hgammaSmooth t
  have hTpar : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g gamma T t = 0 := by
    intro t ht
    exact (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g gamma t hgammaSmooth).mpr
        (hgammaGeo.hasGeodesicEquationAt t)
  have hconst := parallel_transport_preserves_inner_product
    (I := I) g gamma (N := 2) le_rfl
      (hgammaSmooth.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
      V T hVdiff hTdiff hVpar hTpar
  intro t ht
  have ht0 := hconst t ht
  have hL0 := hconst L ⟨ht.1.trans ht.2, le_rfl⟩
  exact ht0.trans hL0.symm

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
