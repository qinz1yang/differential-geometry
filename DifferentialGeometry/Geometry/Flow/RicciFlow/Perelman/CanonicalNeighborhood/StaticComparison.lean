import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Metric.Construction.TensorBumpExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Locality
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N M : Type*}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

private local instance staticComparisonComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance staticComparisonOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

theorem exists_static_metricComparisonOn_of_local_metric
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I3 M)
    (F : N → M) (U : TopologicalSpace.Opens N)
    (G : SmoothRiemannianMetric I U)
    (hG : ∀ x : U, ∀ v w : TangentSpace I x,
      G.inner x v w = g.inner (F x) (mfderiv I I3 F (x : N) v)
        (mfderiv I I3 F (x : N) w))
    (K : Set N) (hK : IsCompact K) (hKU : K ⊆ U)
    (order : ℕ) {eps : ℝ} (heps : 0 ≤ eps)
    (hbound : ∀ x : U, (x : N) ∈ K → ∀ a : ℕ, a ≤ order →
      metricDerivNorm a G
        (h.restrictOpen U) (h.restrictOpen U) x ≤ eps)
    (times : Set ℝ) :
    Nonempty (MetricComparisonOn (fun _ => h) (fun _ => g) F K times order eps) := by
  let H := h.restrictOpen U
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I) hK U.isOpen hKU
  obtain ⟨P, hP, _hout⟩ := exists_tensor_bump_extension U 2 (metricTensorField G)
    chi hchi hsupp
  have hPvalue (x : N) (hx : x ∈ K) (v : Fin 2 → TangentSpace I x) :
      P x v = g.inner (F x) (mfderiv I I3 F x (v 0)) (mfderiv I I3 F x (v 1)) := by
    rw [hP x (hKU hx), show chi x = 1 from subset_of_mem_nhdsSet hone hx, one_mul]
    exact hG ⟨x, hKU hx⟩ (v 0) (v 1)
  have hclose (a : ℕ) (ha : a ≤ order) (x : N) (hx : x ∈ K) :
      tensor02CovDerivNormWith a (P - metricTensorField h) h h x ≤ eps := by
    let y : U := ⟨x, hKU hx⟩
    have hlocal : ∀ᶠ z : U in 𝓝 y,
        restrictOpen0S (I := I) 2 (V := U) (P - metricTensorField h) z =
          (metricTensorField G - metricTensorField H) z := by
      have hchi_local : ∀ᶠ z : U in 𝓝 y, chi (z : N) = 1 :=
        (hone.filter_mono (nhds_le_nhdsSet hx)).comp_tendsto
          (continuous_subtype_val.tendsto y)
      filter_upwards [hchi_local] with z hz
      apply ContinuousMultilinearMap.ext
      intro v
      change P (z : N) v - h.inner (z : N) (v 0) (v 1) = _
      erw [hP (z : N) z.property, hz, one_mul]
      rfl
    have heq := tensor02CovDerivNormWith_eq_of_eventuallyEq H H
      (restrictOpen0S (I := I) 2 (V := U) (P - metricTensorField h))
      (metricTensorField G - metricTensorField H) a y hlocal
    rw [tensor02CovDerivNormWith_restrictOpen0S,
      tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm] at heq
    exact heq.trans_le (hbound y hx a ha)
  refine ⟨{
    pullback := fun _ => P
    pullback_eq := fun _ => hPvalue
    jet := fun b _ => if b = 0 then P - metricTensorField h else 0
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }⟩
  · intro s y v
    simp only [↓reduceIte, ContMDiffSection.coe_sub, Pi.sub_apply,
      Tensor0SSpace.sub_apply, metricTensorField_apply]
  · intro b s hs y hy v
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    simp
  · intro s hs y hy v
    exact quadratic_comparison_of_error_norm h P (P - metricTensorField h) y
      (fun w => by rfl) (hclose 0 (Nat.zero_le order) y hy) v
  · intro a b hab s hs y hy
    split_ifs with hb
    · subst b
      exact hclose a (by omega) y hy
    · have hz : tensor02CovDerivNormWith (I := I) a 0 h h y = 0 := by
        rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
          covDerivOfField_zero_tensor]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
          MetricFiberData.inner, map_zero, Real.sqrt_zero]
      exact hz.le.trans heps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
