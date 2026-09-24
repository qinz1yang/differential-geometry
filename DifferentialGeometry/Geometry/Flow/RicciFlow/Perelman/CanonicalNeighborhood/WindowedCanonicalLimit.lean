import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedPositiveCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedRoundCanonicalLimit

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.eventually_image_of_windowed_models
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps alpha C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < min (neckModelTolerance (neckModelTolerance alpha / 4))
      (backgroundJetSmallness ThreeSpace ⌈(2 * alpha)⁻¹⌉₊)) :
    ∀ᶠ i in atTop, ∃ K' : CanonicalWitness (S (phi i)) (2 * alpha) (max C1 2)
        (max (sourceCurvatureBound 3 C2)
          (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2))))
        (x (phi i)) (t (phi i)),
      K'.domain.carrier =
        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding) ''
          K.domain.carrier := by
  have hcap : eps < neckModelTolerance (neckModelTolerance alpha / 4) :=
    heps.trans_le (min_le_left _ _)
  have hneck : eps < neckModelTolerance alpha := by
    have hb := neckModelTolerance_le (neckModelTolerance alpha / 4)
    have hp := neckModelTolerance_pos ha
    linarith
  have hea : eps < 2 * alpha := by
    have hb := neckModelTolerance_le alpha
    linarith
  have hround : eps ≤ backgroundJetSmallness ThreeSpace ⌈(2 * alpha)⁻¹⌉₊ :=
    heps.le.trans (min_le_right _ _)
  cases halt : K.alternative with
  | neck nk =>
    have hh := K.eventually_image_of_windowed_models_of_neck hS W hdelta hreg
      L hcomplete hphi F hcmp hscalar nk halt ha hsmall hneck
    exact hh.mono fun _ ⟨K', himage, _⟩ => ⟨K', himage⟩
  | cap cap depth =>
    have hh := K.eventually_image_of_windowed_models_of_cap hS W hdelta hreg
      L hcomplete hphi F hcmp hscalar cap ⟨depth, halt⟩ ha hsmall hcap
    exact hh.mono fun _ ⟨K', himage, _⟩ => ⟨K', himage⟩
  | positive whole data sec =>
    have hh := K.eventually_image_of_windowed_models_of_positive_component hS W hdelta hreg
      L hcomplete hphi F hcmp hscalar ⟨whole, data, sec, halt⟩
      (by positivity : 0 < 2 * alpha) (by linarith : 2 * alpha < 1)
    exact hh.mono fun _ ⟨K', himage, _⟩ => ⟨K', himage⟩
  | round whole R =>
    have hh := K.eventually_image_of_windowed_models_of_round_component hS W hdelta hreg
      L hcomplete hphi F hcmp hscalar ⟨whole, R, halt⟩
      (by positivity : 0 < 2 * alpha) (by linarith : 2 * alpha ≤ 1 / 2) hea hround
    exact hh.mono fun _ ⟨K', himage, _⟩ => ⟨K', himage⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
