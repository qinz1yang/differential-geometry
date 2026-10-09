import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmNoReturn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
  [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem WindowedModelWitness.eventually_composed_minimizingArm_prefix_capture
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i s, s ∈ Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 0 < B → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-B) 0) order eta))
    (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (riemannianClosedBallOf (L.S.base.metric 0) L.basepoint (4 * (A + 1))) ∧
      ∀ᶠ i in atTop,
        let Psi : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
        riemannianClosedBallOf (L.S.base.metric 0) L.basepoint (4 * (A + 1)) ⊆ Psi.source ∧
        Psi L.basepoint = x (phi i) ∧
        ∀ (a : MinimizingArm ((S (phi i)).base.metric (t (phi i))) (x (phi i)))
          (s : ℝ), s ∈ Icc 0 a.length →
          Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) * s ≤ A →
          ContinuousOn (fun v => Psi.symm (a.point v)) (Icc 0 s) ∧
          Psi.symm (a.point 0) = L.basepoint ∧
          ∀ v ∈ Icc 0 s,
            a.point v ∈ Psi.target ∧
            Psi.symm (a.point v) ∈
              riemannianClosedBallOf (L.S.base.metric 0) L.basepoint (4 * (A + 1)) ∧
            Psi.symm (a.point v) ∈ Psi.source ∧
            Psi (Psi.symm (a.point v)) = a.point v := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let R := 4 * (A + 1)
  have hR : 0 < R := by dsimp only [R]; linarith
  have hmetricComplete : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  have hK := RiemannianMetricComplete.closedEBall_isCompact hmetricComplete L.basepoint R
  refine ⟨hK, ?_⟩
  have hcomparisons := WindowedModelWitness.eventually_composed_comparison hS W hdelta hreg
    L hcomplete hphi F hcmp hK (show (0 : ℝ) < 1 by norm_num) 0
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hcomparisons] with i hi
  let Psi : PartialDiffeomorph I3 I3 L.M (M (phi i)) ∞ :=
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  let g := rescaledMetric (S (phi i)) (t (phi i))
    ((S (phi i)).scalar (t (phi i)) (x (phi i))) (W (phi i)).scalar_pos 0
  obtain ⟨hsource, cmp⟩ := hi
  obtain ⟨cmp⟩ := cmp
  have hbase : Psi L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    rw [hb]
    exact (W (phi i)).base_map
  have hlower : ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
      ∀ v : TangentSpace I3 y,
      (L.S.base.metric 0).inner y v v ≤
        (2 : ℝ) ^ 2 * g.inner (Psi y) (mfderiv I3 I3 Psi y v) (mfderiv I3 I3 Psi y v) := by
    intro y hy v
    have hh := (cmp.equivalence 0 (by norm_num) y hy v).1
    rw [cmp.pullback_eq 0 y hy (fun _ => v)] at hh
    change (1 - (1 / 2 : ℝ)) * (L.S.base.metric 0).inner y v v ≤
      g.inner (Psi y) (mfderiv I3 I3 Psi y v) (mfderiv I3 I3 Psi y v) at hh
    have hnonneg := inner_self_nonneg g (Psi y) (mfderiv I3 I3 Psi y v)
    nlinarith
  have hcapture : riemannianClosedBallOf g (x (phi i)) A ⊆
      Psi '' riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R := by
    have hh := closedBall_subset_image_of_metric_lower_crossModel (L.S.base.metric 0) g
      Psi L.basepoint hR (show (0 : ℝ) < 2 by norm_num)
      (show A < R / 2 by dsimp only [R]; linarith) hK hsource hlower
    simpa only [hbase] using hh
  refine ⟨hsource, hbase, ?_⟩
  intro a s hs hAs
  have hcaptured : ∀ v ∈ Icc 0 s,
      a.point v ∈ Psi.target ∧
      Psi.symm (a.point v) ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R ∧
      Psi.symm (a.point v) ∈ Psi.source ∧
      Psi (Psi.symm (a.point v)) = a.point v := by
    intro v hv
    have hvlen : v ∈ Icc 0 a.length := ⟨hv.1, hv.2.trans hs.2⟩
    have hball : a.point v ∈ riemannianClosedBallOf g (x (phi i)) A := by
      change riemannianEDistOf g (x (phi i)) (a.point v) ≤ ENNReal.ofReal A
      dsimp only [g]
      rw [edistOf_rescaledMetric_zero, a.edistOf_start hvlen,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        ((mul_le_mul_of_nonneg_left hv.2 (Real.sqrt_nonneg _)).trans hAs)
    obtain ⟨y, hy, hya⟩ := hcapture hball
    have htarget : a.point v ∈ Psi.target := hya ▸ Psi.map_source' (hsource hy)
    have hinverse : Psi.symm (a.point v) = y := by
      rw [← hya]
      exact Psi.left_inv' (hsource hy)
    exact ⟨htarget, hinverse.symm ▸ hy, Psi.map_target' htarget, Psi.right_inv' htarget⟩
  have hcont : ContinuousOn (fun v => Psi.symm (a.point v)) (Icc 0 s) :=
    Psi.symm.contMDiffOn_toFun.continuousOn.comp
      (a.continuousOn_point.mono (Icc_subset_Icc le_rfl hs.2))
      (fun v hv => (hcaptured v hv).1)
  have hp : L.basepoint ∈ Psi.source := hsource (by
    change riemannianEDistOf (L.S.base.metric 0) L.basepoint L.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le)
  have hzero : Psi.symm (a.point 0) = L.basepoint :=
    (congrArg Psi.symm (a.start.trans hbase.symm)).trans (Psi.left_inv' hp)
  exact ⟨hcont, hzero, hcaptured⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
