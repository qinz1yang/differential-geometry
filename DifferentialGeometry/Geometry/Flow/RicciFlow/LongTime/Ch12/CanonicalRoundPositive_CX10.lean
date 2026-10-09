import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalScalingTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalCurvaturePerturbation_CX10
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectionalNorm
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

/-!
The round alternative is excluded by curvature, using its actual C² comparison.
The scalar-one reference metric has sectional curvature 1/6 and |Rm|² = 1/3.
The refined quantitative perturbation estimate gives sec ≥ R(x)/12
when 0 < eps ≤ 1/100. The constant is independent of the spherical quotient.
-/

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M} {U : Set M}

omit [T2Space M] [SigmaCompactSpace M] in
/-- The tuple convention in `SecLower` agrees with the sectional-bound convention. -/
theorem sectionalBoundedBelowAt_of_secLower_CX10 {c : ℝ} (h : SecLower g c U)
    {y : M} (hy : y ∈ U) : SectionalBoundedBelowAt g y c := by
  intro v w
  have hv : vec4 (I := I3) v w w v = (fun i : Fin 4 => ![v, w, w, v] i) := by
    funext i
    fin_cases i <;> rfl
  simpa only [metricRm04StandardAt_apply, hv] using h y hy v w

omit [SigmaCompactSpace M] in
/-- Genuine strict sectional positivity derived from the round branch's C² error. -/
theorem spatialRound_secLower_CX10 (D : SpatialRoundComponent g eps x U)
    (heps : 0 < eps) (hsmall : eps ≤ 1 / 100) :
    SecLower g ((1 / 12 : ℝ) * metricScalarAt g x) U := by
  let _ := D.topology
  let _ := D.charted
  let _ := D.smooth
  let _ := D.t2
  let _ := D.compact
  let V : TopologicalSpace.Opens D.Z := ⊤
  have hsec : SecLower D.metric (1 / 6) (V : Set D.Z) := by
    intro y _ v w
    exact (D.constant_curvature y v w).ge
  have hrm : ∀ y ∈ (V : Set D.Z),
      normSq0S D.metric y 4 (metricRm04At D.metric y) ≤ (1 : ℝ) ^ 2 := by
    intro y _
    have hcc : ∀ v w : TangentSpace I3 y,
        metricRm04StandardAt D.metric y v w w v = (1 / 6 : ℝ) *
          (D.metric.inner y v v * D.metric.inner y w w - D.metric.inner y v w ^ 2) := by
      intro v w
      have hv : vec4 (I := I3) v w w v = (fun i : Fin 4 => ![v, w, w, v] i) := by
        funext i
        fin_cases i <;> rfl
      simpa only [metricRm04StandardAt_apply, hv] using D.constant_curvature y v w
    rw [normSq0S_metricRm04At_eq_of_constant_sectional_numerator D.metric y (1 / 6) hcc]
    norm_num [ThreeSpace]
  have horder : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have htwo : (2 : ℝ) ≤ eps⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2) heps]
      norm_num
      linarith
    exact_mod_cast htwo.trans (Nat.le_ceil _)
  let O := DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.sourceOpen D.map
  let G := D.metric.restrictOpen O
  let gs := scaleMetric (metricScalarAt g x) D.Q_pos g
  let gp := openPullbackMetric D.map O (sourceOpen_subset D.map) gs
  have hlocal : SecLower gp (1 / 12) (Subtype.val ⁻¹' (univ : Set D.Z)) := by
    intro y _ v w
    have hsmall' : ∀ a : ℕ, a ≤ 2 → metricDerivNorm a gp G G y ≤ eps := by
      intro a ha
      rw [D.comparison.openPullback_metricDerivNorm O (sourceOpen_subset D.map) (subset_univ _)]
      exact D.comparison.close a 0 (by omega) 0 (by simp) y (mem_univ _)
    have hsec' : ∀ a b : TangentSpace I3 y,
        (1 / 6 : ℝ) * (G.inner y a a * G.inner y b b - G.inner y a b ^ 2) ≤
          metricRm04StandardAt G y a b b a := by
      intro a b
      dsimp only [G]
      rw [metricRm04StandardAt_restrictOpen]
      simp only [mfderiv_subtype_val_apply]
      exact sectionalBoundedBelowAt_of_secLower_CX10 hsec (mem_univ _) a b
    have hrm' : normSq0S G y 4 (metricRm04At G y) ≤ 1 := by
      simpa only [G, rmNormSq_restrictOpen, one_pow] using hrm y (mem_univ _)
    have h := metricRm04_lower_bound_CX10 gp G y hsmall hsmall' hsec' hrm' v w
    have hv : vec4 (I := I3) v w w v = (fun i : Fin 4 => ![v, w, w, v] i) := by
      funext i
      fin_cases i <;> rfl
    simpa only [metricRm04StandardAt_apply, hv] using h
  have h := secLower_image_of_openPullbackMetric D.map
    (show (univ : Set D.Z) ⊆ D.map.source by rw [D.source_eq]) gs hlocal
  have himage : D.map '' (univ : Set D.Z) = U := by
    rw [← D.source_eq]
    exact D.map.toPartialEquiv.image_source_eq_target.trans D.target_eq
  rw [himage] at h
  exact (secLower_scaleMetric_iff D.Q_pos g U).mp h

/-- A negative plane in the component excludes a whole positive alternative. -/
theorem canonical_positive_excluded_CX10 (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hneg : ∃ y ∈ connectedComponent x, ¬ SectionalBoundedBelowAt g y 0)
    (whole : W.domain.carrier = connectedComponent x)
    (hsec : SecLower g (C2⁻¹ * metricScalarAt g x) W.domain.carrier) : False := by
  obtain ⟨y, hy, hbad⟩ := hneg
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  apply hbad
  exact sectionalBoundedBelowAt_of_secLower_CX10
    (hsec.mono (mul_nonneg (inv_nonneg.mpr hC2.le) W.Q_pos.le)) (whole.symm ▸ hy)

/-- A negative plane also excludes the approximately round alternative. -/
theorem canonical_round_excluded_CX10 (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hsmall : eps ≤ 1 / 100)
    (hneg : ∃ y ∈ connectedComponent x, ¬ SectionalBoundedBelowAt g y 0)
    (whole : W.domain.carrier = connectedComponent x)
    (D : SpatialRoundComponent g eps x W.domain.carrier) : False := by
  obtain ⟨y, hy, hbad⟩ := hneg
  apply hbad
  exact sectionalBoundedBelowAt_of_secLower_CX10
    ((spatialRound_secLower_CX10 D W.eps_pos hsmall).mono
      (mul_nonneg (by norm_num) W.Q_pos.le)) (whole.symm ▸ hy)

end GC.LongTime.Ch12
