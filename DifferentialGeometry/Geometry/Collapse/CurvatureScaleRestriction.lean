import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

private theorem sectionalBoundedBelowAt_restrictOpen_iff
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (p : U) (K : ℝ) :
    SectionalBoundedBelowAt (g.restrictOpen U) p K ↔
      SectionalBoundedBelowAt g p.val K := by
  have hRm (v w : TangentSpace I p) :
      metricRm04StandardAt (g.restrictOpen U) p v w w v =
        metricRm04StandardAt g p.val v w w v := by
    simpa only [mfderiv_subtype_val_apply] using
      metricRm04StandardAt_restrictOpen g U p v w w v
  have hGram (v w : TangentSpace I p) :
      K * ((g.restrictOpen U).inner p v v * (g.restrictOpen U).inner p w w -
        (g.restrictOpen U).inner p v w ^ 2) =
      K * (g.inner p.val v v * g.inner p.val w w - g.inner p.val v w ^ 2) := by
    simp only [SmoothRiemannianMetric.restrictOpen_inner]
  constructor
  · intro h v w
    exact (hGram v w).symm.trans_le ((h v w).trans_eq (hRm v w))
  · intro h v w
    exact (hGram v w).trans_le ((h v w).trans_eq (hRm v w).symm)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem mem_of_mem_ball_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (p : U) {r : ℝ} (hr : 0 < r)
    {q : M} (hq : q ∈ riemannianBallOf g p.val r) : q ∈ U := by
  have hp : p.val ∈ riemannianBallOf g p.val r := by
    change riemannianEDistOf g p.val p.val < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hcomponent :=
    (isPathConnected_riemannianBallOf g p.val hr).isConnected.isPreconnected.subset_connectedComponent hp
  exact (show IsClopen (U : Set M) from ⟨hU, U.isOpen⟩).connectedComponent_subset
    p.property (hcomponent hq)

theorem curvatureRadius_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (p : U) :
    curvatureRadius (g.restrictOpen U) p = curvatureRadius g p.val := by
  unfold curvatureRadius
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hsec => ?_
    have hambient : ∀ q ∈ riemannianBallOf g p.val r,
        SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
      intro q hq
      let qU : U := ⟨q, mem_of_mem_ball_of_isClosed g U hU p hr hq⟩
      have hqU : qU ∈ riemannianBallOf (g.restrictOpen U) p r := by
        change riemannianEDistOf (g.restrictOpen U) p qU < ENNReal.ofReal r
        rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
        exact hq
      exact (sectionalBoundedBelowAt_restrictOpen_iff g U qU _).mp (hsec qU hqU)
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hambient le_rfl))
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hsec => ?_
    have hrestricted : ∀ q ∈ riemannianBallOf (g.restrictOpen U) p r,
        SectionalBoundedBelowAt (g.restrictOpen U) q (-(r ^ 2)⁻¹) := by
      intro q hq
      have hqM : q.val ∈ riemannianBallOf g p.val r :=
        (riemannianEDistOf_le_restrictOpen g U p q).trans_lt hq
      exact (sectionalBoundedBelowAt_restrictOpen_iff g U q _).mpr (hsec q.val hqM)
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le hrestricted le_rfl))

theorem curvatureDerivativesControlled_restrictOpen_of_isClosed
    [I.Boundaryless] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (h : curvatureDerivativesControlled g K A w₀) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    curvatureDerivativesControlled (g.restrictOpen U) K A w₀ := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  intro p w r hw hc hr hρ hv k hk q hq
  have hρM : ENNReal.ofReal r < curvatureRadius g p.val := by
    rwa [curvatureRadius_restrictOpen_of_isClosed g U hU p] at hρ
  have hvolume : ballVolume (g.restrictOpen U) p r = ballVolume g p.val r := by
    exact Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed g U hU p r
  have hvM : ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p.val r := by
    rwa [hvolume] at hv
  have hqM : q.val ∈ riemannianBallOf g p.val r :=
    (riemannianEDistOf_le_restrictOpen g U p q).trans_lt hq
  rw [curvatureDerivativeNorm_restrictOpen]
  exact h p.val w r hw hc hr hρM hvM k hk q.val hqM

end DifferentialGeometry.Geometry.Collapse
