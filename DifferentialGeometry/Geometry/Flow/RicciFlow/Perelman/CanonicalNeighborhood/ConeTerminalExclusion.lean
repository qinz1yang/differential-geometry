import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciRHS
import DifferentialGeometry.Geometry.Metric.ConeChart.Coordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci

set_option autoImplicit false
noncomputable section
open Bundle Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private theorem ricci_nonnegative_of_secLower {g : SmoothRiemannianMetric I3 M}
    {U : Set M} (hsec : SecLower g 0 U) {x : M} (hx : x ∈ U)
    (v : TangentSpace I3 x) : 0 ≤ metricRicciAt g x (vec2 v v) := by
  rw [metricRicciAt_apply_eq_ricciTensor]
  apply DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec g x
  apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff g x).mpr
  intro u w
  have hslots : (fun i => ![u, w, w, u] i) = vec4 u w w u := by
    funext i
    fin_cases i <;> rfl
  simpa only [zero_mul, metricRm04StandardAt_apply, hslots] using hsec x hx u w

omit [SigmaCompactSpace M] in
private theorem scalar_nonnegative_of_secLower {g : SmoothRiemannianMetric I3 M}
    {U : Set M} (hsec : SecLower g 0 U) {x : M} (hx : x ∈ U) :
    0 ≤ metricScalarAt g x := by
  classical
  obtain ⟨β, hβ⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g β hβ
  have htrace : metricScalarAt g x = ∑ i, metricRicciAt g x (vec2 (β i) (β i)) := by
    rw [metricScalarAt_def, metricTracePair0SAt_eq_sum_basis g β _ hinv]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [show identityInvMetric i j = 0 from
        diagonalInvMetric_eq_zero_of_ne hji.symm, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [htrace]
  exact Finset.sum_nonneg fun i _ => ricci_nonnegative_of_secLower hsec hx (β i)

local instance coneTerminalC1 : IsManifold I3 1 M :=
  IsManifold.of_le (I := I3) (M := M) (n := ∞) (by decide)

theorem solution_cone_terminal_exclusion
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (U : Set M) (cone : DifferentialGeometry.Geometry.Riemannian.ConeChart.{u, 0, 0, v} 2
      (S.base.metric b) U)
    (hsec : ∀ t ∈ Set.Icc a b, SecLower (S.base.metric t) 0 U)
    (hnonflat : ∃ x ∈ U, metricScalarAt (S.base.metric b) x ≠ 0) : False := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := by
    change NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
    rw [finrank_euclideanSpace_fin]
    infer_instance
  obtain ⟨x, hxU, hxne⟩ := hnonflat
  obtain ⟨W, hxW, _hWU, Z, hZ⟩ :=
    DifferentialGeometry.Geometry.Riemannian.ConeChart.exists_concurrent_field cone hxU
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 W.isOpen)
  let : IsManifold I3 1 W := IsManifold.of_le (I := I3) (M := W) (n := ∞) (by decide)
  let SW := solutionOnRestrictOpen S W
  have hSW : IsSolutionOn SW := isSolutionOn_restrictOpen S hS W
  let y : W := ⟨x, hxW⟩
  have hconcurrent : ∀ᶠ z in 𝓝 y, ∀ v : TangentSpace I3 z,
      metricCov (SW.base.metric b) Z z v = v := Filter.Eventually.of_forall hZ
  have hzero : SW.ricci b y (vec2 (Z y) (Z y)) = 0 :=
    metricRicci_concurrent_eq_zero (SW.base.metric b) Z hconcurrent (Z y)
  have hnonneg (t : ℝ) (ht : t ∈ Set.Icc a b) :
      0 ≤ SW.ricci t y (vec2 (Z y) (Z y)) := by
    change 0 ≤ metricRicciAt ((S.base.metric t).restrictOpen W) y (vec2 (Z y) (Z y))
    rw [← metricRicci_apply, metricRicci_restrictOpen_eval, metricRicci_apply]
    have hslots : (fun q => mfderiv I3 I3 (Subtype.val : W → M) y (vec2 (Z y) (Z y) q)) =
        vec2 (mfderiv I3 I3 (Subtype.val : W → M) y (Z y))
          (mfderiv I3 I3 (Subtype.val : W → M) y (Z y)) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]
    exact ricci_nonnegative_of_secLower (hsec t ht) hxU _
  have hnonpos := ricciPair_terminal_nonpos_of_nonnegative_of_rhsContinuous
    SW hSW hab hslab hreg y (Z y)
    (solution_ricciPairRHS_continuousWithinAt_terminal SW hSW hab hslab hreg y (Z y) (Z y))
    hnonneg hzero
  rw [ricciPairRHS_concurrent SW b Z hconcurrent] at hnonpos
  change 2 * metricScalarAt ((S.base.metric b).restrictOpen W) y ≤ 0 at hnonpos
  rw [metricScalarAt_restrictOpen] at hnonpos
  have hscalar := scalar_nonnegative_of_secLower (hsec b ⟨hab.le, le_rfl⟩) hxU
  apply hxne
  change 2 * metricScalarAt (S.base.metric b) x ≤ 0 at hnonpos
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
