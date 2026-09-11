import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardJetControl


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle CanonicalNeighborhood
open CanonicalNeighborhood DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance backwardWitnessC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem backwardNeck_normalizedMetric_inner
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℝ) (htau : 0 < tau) (q : F.M) (hQ : 0 < F.S.scalar (-tau) q)
    {epsilon : ℝ} {f : C(spatialNeckBuffer epsilon, F.M)}
    (hf : IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (s : ℝ) (x : spatialNeckBuffer epsilon)
    (v w : TangentSpace SpatialNeckCylinderModel x) :
    (strongNeckNormalizedMetric F.S q (-tau) hQ hf s).inner x v w =
      (scaleMetric (tau * F.S.scalar (-tau) q) (mul_pos htau hQ)
        (immersionInducedMetric (backwardScaledMetric F.S tau htau
          (1 - s / (tau * F.S.scalar (-tau) q))) hf.isImmersion)).inner x v w := by
  rw [strongNeckNormalizedMetric_inner, scaleMetric_inner, immersionInducedMetric_inner]
  have hmetric := congrArg (fun g : SmoothRiemannianMetric I3 F.M =>
      g.inner (f x) (mfderiv SpatialNeckCylinderModel I3 f x v)
        (mfderiv SpatialNeckCylinderModel I3 f x w))
    (backwardForwardNeck_metric_eq F.S tau (F.S.scalar (-tau) q) htau hQ s)
  simpa only [rescaledMetric, scaleMetric_inner, parabolicTime, div_eq_mul_inv, mul_comm] using hmetric


theorem backwardComparison_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (tau : ℝ) (htau : 0 < tau) (q : F.M) (yStar : SpatialNeckSphere)
    (f : C(spatialNeckBuffer epsilon, F.M))
    (hf : IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ f)
    (hmarked : f (spatialNeckCentralPoint epsilon hepsilon yStar) = q)
    (hfactor : (1 : ℝ) / 2 ≤ tau * F.S.scalar (-tau) q)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hzero : ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (backwardScaledMetric F.S tau htau theta).inner (f x)
        (mfderiv SpatialNeckCylinderModel I3 f x (v 0))
        (mfderiv SpatialNeckCylinderModel I3 f x (v 1)) -
          (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1))
    (hderiv : ∀ b theta, theta ∈ Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
      (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
      HasDerivWithinAt (fun r => J b r x v) (J (b + 1) theta x v) (Icc (1 : ℝ) 3) theta)
    (hclose : StrongNeckJetControl epsilon
      (backwardForwardErrorJet epsilon (tau * F.S.scalar (-tau) q) J)) :
    ∃ W : StrongNeckWitness F.S yStar q (-tau) epsilon, W.embedding = f := by
  have hQ : 0 < F.S.scalar (-tau) q := by
    by_contra hnonpos
    have hn := mul_nonpos_of_nonneg_of_nonpos htau.le (le_of_not_gt hnonpos)
    linarith
  let G (theta : ℝ) := immersionInducedMetric (backwardScaledMetric F.S tau htau theta)
    hf.isImmersion
  have hG : ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (G theta).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1) := by
    intro theta htheta x v
    rw [immersionInducedMetric_inner]
    exact hzero theta htheta x v
  let W : StrongNeckWitness F.S yStar q (-tau) epsilon := {
    dimension_three := by simp [ThreeSpace]
    isSolution := F.isSolution
    epsilon_pos := hepsilon
    epsilon_lt_one := hepsilon_one
    scalar_pos := hQ
    time_window := by
      intro t ht
      change t ≤ 0
      exact ht.2.trans (neg_nonpos.mpr htau.le)
    embedding := f
    smooth_embedding := hf
    marked := hmarked
    jet := backwardForwardErrorJet epsilon (tau * F.S.scalar (-tau) q) J
    jet_zero := by
      intro s hs x v
      have hjet := backwardForwardErrorJet_zero epsilon (tau * F.S.scalar (-tau) q)
        hfactor G J hG s hs x v
      have hmetric := backwardNeck_normalizedMetric_inner F tau htau q hQ hf s x (v 0) (v 1)
      exact hjet.trans (congrArg (fun r : ℝ =>
        r - (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1)) hmetric.symm)
    jet_succ := backwardForwardErrorJet_hasDerivWithinAt epsilon
      (tau * F.S.scalar (-tau) q) hfactor J hderiv
    closeness := hclose }
  exact ⟨W, rfl⟩


theorem backwardComparison_eventually_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (yStar : SpatialNeckSphere)
    (f : ℕ → C(spatialNeckBuffer epsilon, F.M))
    (J : ℕ → ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hfactor : Tendsto (fun i => tau i * F.S.scalar (-tau i) (q i)) atTop (𝓝 (1 : ℝ)))
    (hdata : ∀ᶠ i in atTop,
      IsSmoothEmbedding SpatialNeckCylinderModel I3 ∞ (f i) ∧
      f i (spatialNeckCentralPoint epsilon hepsilon yStar) = q i ∧
      (∀ theta ∈ Icc (1 : ℝ) 3, ∀ x v,
        J i 0 theta x v = (backwardScaledMetric F.S (tau i) (htau i) theta).inner (f i x)
          (mfderiv SpatialNeckCylinderModel I3 (f i) x (v 0))
          (mfderiv SpatialNeckCylinderModel I3 (f i) x (v 1)) -
            (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1)) ∧
      (∀ b theta, theta ∈ Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
        (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
        HasDerivWithinAt (fun r => J i b r x v) (J i (b + 1) theta x v)
          (Icc (1 : ℝ) 3) theta))
    (hconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
      ∀ a b : ℕ, a + 2 * b ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J i b theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤ eta) :
    ∀ᶠ i in atTop, ∃ W : StrongNeckWitness F.S yStar (q i) (-tau i) epsilon,
      W.embedding = f i := by
  have hhalf : ∀ᶠ i in atTop, (1 : ℝ) / 2 ≤ tau i * F.S.scalar (-tau i) (q i) :=
    ((tendsto_order.1 hfactor).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcontrol := backwardForwardErrorJet_eventually_control epsilon hepsilon J hfactor hconv
  filter_upwards [hdata, hhalf, hcontrol] with i hi hhalf_i hcontrol_i
  exact backwardComparison_strongNeckWitness F epsilon hepsilon hepsilon_one (tau i) (htau i)
    (q i) yStar (f i) hi.1 hi.2.1 hhalf_i (J i) hi.2.2.1 hi.2.2.2 hcontrol_i

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
