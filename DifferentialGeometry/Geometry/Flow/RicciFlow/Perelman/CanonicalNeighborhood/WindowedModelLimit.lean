import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Exhaustion

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I3 M)]

theorem WindowedModelWitness.exists_blowup_limit
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta : ℕ → ℝ} {kappa : ℝ} {x : ℕ → M} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa S (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hregular : interior D.carrier ⊆ D.regular) :
    Nonempty (BlowupLimit S o kappa x t) := by
  classical
  let models : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval := fun i => (W i).model
  obtain ⟨L, phi, hphi, Phi, hL, hnorm, _hKL, _hmetric, hcmp⟩ :=
    KappaSolutions.exists_ancientKappa_fixed_kappa_compactness models
      (fun i => (W i).model_ancient) (fun i => (W i).model_scalar_base)
  let _ : ConnectedSpace L.M := hL.connected
  let _ : PreconnectedSpace (L.atTime 0).M := inferInstanceAs (PreconnectedSpace L.M)
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp [ancientTimeInterval_carrier])
  let F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi := Phi.atTime (X := KappaSolutions.ancientPointedFlowSeq models) (L := L) 0
  have hreg : ∀ i s, s ∈ Ioo (-modelDepth (delta i)) 0 →
      parabolicTime (t i) (S.scalar (t i) (x i)) s ∈ D.regular := by
    intro i s hs
    exact ((W i).normalized_window (by
      simpa only [interior_Icc] using
        (interior_mono (W i).window_mem).trans hregular)).2 hs
  let Psi : ∀ i, PartialDiffeomorph I3 I3 L.M M ∞ := fun i =>
    partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding
  have hcomp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop, K ⊆ (Psi i).source ∧
        Nonempty (MetricComparisonOn L.S.base.metric
          (rescaledMetric S (t (phi i)) (S.scalar (t (phi i)) (x (phi i)))
            (W (phi i)).scalar_pos) (Psi i) K (Icc (-A) 0) order eta) := by
    intro K hK A hA order eta heta
    exact WindowedModelWitness.eventually_composed_comparison (fun _ => hS) W hdelta hreg L hcomplete hphi.tendsto_atTop F
      (fun K hK A hA order alpha halpha =>
        hcmp (-A) 0 (by linarith) le_rfl K hK order alpha halpha) hK hA order heta
  let X : PointedRiemannianSeq.{u, 0, 0} I3 := ⟨fun i => {
    M := M
    basepoint := x i
    metric := rescaledMetric S (t i) (S.scalar (t i) (x i)) (W i).scalar_pos 0 }⟩
  have hbase (i : ℕ) : Psi i L.basepoint = x (phi i) := by
    change (W (phi i)).embedding (F.map i L.basepoint) = x (phi i)
    have hb : F.map i L.basepoint = (W (phi i)).model.basepoint := F.basepoint_map i
    exact (congrArg (W (phi i)).embedding hb).trans (W (phi i)).base_map
  obtain ⟨sigma, hsigma, G, hG, _hGcompact, hGconn⟩ :=
    PointedRiemannianConvergenceMaps.exists_subsequence_of_eventually_contains_compacts
      (X := X) (P := L.atTime 0) (f := phi) Psi hbase
      (fun K hK => (hcomp K hK 1 zero_lt_one 0 1 zero_lt_one).mono fun _ hi => hi.1)
  have hGcomp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop, K ⊆ G.source i ∧
        Nonempty (MetricComparisonOn L.S.base.metric
          (rescaledMetric S (t (phi (sigma i))) (S.scalar (t (phi (sigma i))) (x (phi (sigma i))))
            (W (phi (sigma i))).scalar_pos) (G.map i) K (Icc (-A) 0) order eta) := by
    intro K hK A hA order eta heta
    obtain ⟨N, hN⟩ := G.source_exhausts.subset K hK
    filter_upwards [hsigma.tendsto_atTop.eventually (hcomp K hK A hA order eta heta),
      eventually_ge_atTop N] with i hi hNi
    refine ⟨hN i hNi, ?_⟩
    rw [hG i]
    exact hi.2
  have hcapture : MetricSourceCapture G := by
    intro r hr
    let R : ℝ := 2 * r + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hc : RiemannianMetricComplete (I := I3) (L.S.base.metric 0) :=
      ⟨MetricComplete.complete _ hcomplete⟩
    have hK := hc.closedEBall_isCompact L.basepoint R
    filter_upwards [hGcomp _ hK 1 zero_lt_one 0 (1 / 2) (by norm_num)] with i hi
    obtain ⟨hsrc, ⟨C⟩⟩ := hi
    have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
    have hlower : ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint R,
        ∀ v : TangentSpace I3 y,
          (L.S.base.metric 0).inner y v v ≤ Real.sqrt 2 ^ 2 *
            (X.obj ((phi ∘ sigma) i)).metric.inner (G.map i y)
              (mfderiv I3 I3 (G.map i) y v) (mfderiv I3 I3 (G.map i) y v) := by
      intro y hy v
      have hh := (C.equivalence 0 (by norm_num) y hy v).1
      rw [C.pullback_eq 0 y hy (fun _ => v)] at hh
      have hh' : (1 - 1 / 2) * (L.S.base.metric 0).inner y v v ≤
          (X.obj ((phi ∘ sigma) i)).metric.inner (G.map i y)
            (mfderiv I3 I3 (G.map i) y v) (mfderiv I3 I3 (G.map i) y v) := hh
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have hcap := ball_subset_image_of_metric_lower_crossModel (L.S.base.metric 0)
      (X.obj ((phi ∘ sigma) i)).metric (G.partialDiffeomorph i) L.basepoint
      hR hsqrt hK hsrc hlower
    have hr' : r ≤ R / Real.sqrt 2 := by
      rw [le_div_iff₀ hsqrt]
      have h2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      dsimp only [R]
      nlinarith
    intro y hy
    have hy' : y ∈ riemannianBallOf (X.obj ((phi ∘ sigma) i)).metric
        (G.partialDiffeomorph i L.basepoint) (R / Real.sqrt 2) := by
      have hb : G.partialDiffeomorph i L.basepoint = (X.obj ((phi ∘ sigma) i)).basepoint :=
        G.basepoint_map i
      rw [hb]
      exact riemannianBallOf_mono _ _ hr' hy
    obtain ⟨z, hz, hzy⟩ := hcap hy'
    exact ⟨z, hsrc hz, hzy⟩
  obtain ⟨tau, htau, O, hO⟩ := exists_subsequence_preserves_tangentOrientation G
    (fun i => (hGconn i).isPreconnected) (fun _ => o)
  let rho := (phi ∘ sigma) ∘ tau
  have hrho : StrictMono rho := (hphi.comp hsigma).comp htau
  have hdinv : Tendsto (fun i => (delta (rho i))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hdelta.comp hrho.tendsto_atTop, .of_forall fun i => (W (rho i)).eps_pos⟩)
  refine ⟨{
    model := L
    ancient := hL
    normalized := hnorm
    orientation := O
    subseq := rho
    strictMono := hrho
    scale_pos := fun i => (W (rho i)).scalar_pos
    map := (G.compSubseq tau htau).partialDiffeomorph
    exhaustion := (G.compSubseq tau htau).source_exhausts
    base_mem := (G.compSubseq tau htau).base_mem
    base_eq := (G.compSubseq tau htau).basepoint_map
    oriented := hO
    capture := fun r hr => htau.tendsto_atTop.eventually (hcapture r hr)
    convergence := ?_ }⟩
  intro K hK A hA order eta heta
  filter_upwards [htau.tendsto_atTop.eventually (hGcomp K hK A hA order eta heta),
    hdinv.eventually_ge_atTop A] with i hi hdepth
  refine ⟨?_, hi⟩
  apply (Icc_subset_Icc ?_ le_rfl).trans (W (rho i)).window_mem
  have hbound : A / S.scalar (t (rho i)) (x (rho i)) ≤
      (delta (rho i) * S.scalar (t (rho i)) (x (rho i)))⁻¹ := by
    simpa only [div_eq_mul_inv, mul_inv] using
      mul_le_mul_of_nonneg_right hdepth (inv_nonneg.mpr (W (rho i)).scalar_pos.le)
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
