import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackgroundJetTransfer
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]

private local instance partialJetSourceC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance partialJetTargetC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace P] in
theorem tensor02CovDerivNormWith_le_of_partial_pullback_comparison
    {h : ℝ → SmoothRiemannianMetric J N} {k : ℝ → SmoothRiemannianMetric I3 P}
    (Phi : PartialDiffeomorph J I3 N P ∞)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ Phi.source)
    {times : Set ℝ} {order : ℕ} {alpha : ℝ}
    (c : MetricComparisonOn h k Phi U times order alpha)
    (halpha : 0 < alpha) (hsmall : alpha ≤ backgroundJetSmallness E order)
    {s : ℝ} (hs : s ∈ times)
    (A : Tensor0SField (I := I3) (M := P) (n := ∞) 2)
    (B : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (hB : ∀ y ∈ (U : Set N), ∀ v : Fin 2 → TangentSpace J y,
      B y v = A (Phi y) (fun q => mfderiv J I3 Phi y (v q)))
    {a : ℕ} (ha : a ≤ order) {y : N} (hy : y ∈ U) :
    tensor02CovDerivNormWith a B (h s) (h s) y ≤
      backgroundJetConstant E order * ∑ j ∈ Finset.range (a + 1),
        tensor02CovDerivNormWith j A (k s) (k s) (Phi y) := by
  let V : TopologicalSpace.Opens P := ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩
  let psi : Diffeomorph J I3 U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let href : SmoothRiemannianMetric J U := (h s).restrictOpen U
  let kref : SmoothRiemannianMetric I3 V := (k s).restrictOpen V
  let pulled : SmoothRiemannianMetric J U :=
    DifferentialGeometry.Diffeomorph.pullbackMetricCross kref psi
  let B' : Tensor0SField (I := J) (M := U) (n := ∞) 2 :=
    restrictOpen0S (I := J) 2 (V := U) B
  let A' : Tensor0SField (I := I3) (M := V) (n := ∞) 2 :=
    restrictOpen0S (I := I3) 2 (V := V) A
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen J U.isOpen)
  have hpull (z : U) (v w : TangentSpace J z) :
      pulled.inner z v w = (k s).inner (Phi z)
        (mfderiv J I3 Phi (z : N) v) (mfderiv J I3 Phi (z : N) w) := by
    rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
    change (k s).inner (Phi z) (mfderiv J I3 psi z v) (mfderiv J I3 psi z w) = _
    rw [DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU z v,
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU z w]
  have hmetric : metricTensorField (I := J) pulled - metricTensorField (I := J) href =
      restrictOpen0S (I := J) 2 (V := U) (c.jet 0 s) := by
    ext z v
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      metricTensorField_apply]
    rw [hpull]
    change _ = c.jet 0 s (z : N) v
    have hp := c.pullback_eq s (z : N) z.property
      (show Fin 2 → TangentSpace J (z : N) from v)
    have hz := c.jet_zero s (z : N) (show Fin 2 → TangentSpace J (z : N) from v)
    exact (congrArg (fun q => q - (h s).inner (z : N) (v 0) (v 1)) hp.symm).trans hz.symm
  have hequiv : ∀ z ∈ (Set.univ : Set U), ∀ v : TangentSpace J z,
      (1 - alpha) * href.inner z v v ≤ pulled.inner z v v ∧
        pulled.inner z v v ≤ (1 + alpha) * href.inner z v v := by
    intro z _hz v
    rw [hpull]
    have hh := c.equivalence s hs (z : N) z.property (show TangentSpace J (z : N) from v)
    have hp := c.pullback_eq s (z : N) z.property
      (fun _ => (show TangentSpace J (z : N) from v))
    rw [hp] at hh
    exact hh
  have hjets : ∀ j ≤ order, ∀ z ∈ (Set.univ : Set U),
      tensor02CovDerivNormWith j
        (metricTensorField (I := J) pulled - metricTensorField (I := J) href)
        href href z ≤ alpha := by
    intro j hj z _hz
    rw [hmetric]
    rw [tensor02CovDerivNormWith_restrictOpen0S U (h s) (h s) (c.jet 0 s) j z]
    exact c.close j 0 (by omega) s hs z z.property
  have hnatural (j : ℕ) (z : U) :
      tensor02CovDerivNormWith j B' pulled pulled z =
        tensor02CovDerivNormWith j A (k s) (k s) (Phi z) := by
    have hcompat : ∀ z : U, ∀ v : Fin 2 → TangentSpace J z,
        B' z v = A' (psi z) (fun q => mfderiv J I3 psi z (v q)) := by
      intro z v
      change B (z : N) v = A (Phi z) (fun q => mfderiv J I3 psi z (v q))
      refine (hB (z : N) z.property (show Fin 2 → TangentSpace J (z : N) from v)).trans ?_
      congr 1
      funext q
      exact (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
        Phi hU z (v q)).symm
    rw [tensor02CovDerivNormWith_pullbackCross kref kref psi B' A' hcompat j z]
    exact tensor02CovDerivNormWith_restrictOpen0S V (k s) (k s) A j (psi z)
  have hbound := tensor02CovDerivNormWith_le_of_metric_close order halpha hsmall
    href pulled isOpen_univ hequiv hjets B' a ha (Set.mem_univ (⟨y, hy⟩ : U))
  rw [tensor02CovDerivNormWith_restrictOpen0S U (h s) (h s) B a ⟨y, hy⟩] at hbound
  simpa only [hnatural] using hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
