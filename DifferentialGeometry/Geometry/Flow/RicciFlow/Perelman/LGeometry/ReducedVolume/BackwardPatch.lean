import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Connector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.PatchVolume

noncomputable section
open Set Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem volume_and_connector_action_bound_of_backward_ball
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {u s K : ℝ} (hK : 0 ≤ K) (hus : u ≤ s)
    (hcarrier : Icc u s ⊆ D.carrier) (hregular : Ioo u s ⊆ D.regular)
    (hRm : ∀ t ∈ Icc u s, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2)
    (p : M) {r κ : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric s) p r))
    (hroom : u ≤ s - r ^ 2)
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M (S.base.metric s) (riemannianBallOf (S.base.metric s) p r)) :
    let V := riemannianBallOf (S.base.metric s) p r;
    IsOpen V ∧
      ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ)^3 * K * r^2)) * κ) *
        ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolumeMeasure I M (S.base.metric (s-r^2)) V ∧
      ∀ T Emax : ℝ, s ≤ T → T-s+r^2 ≤ Emax → ∀ q ∈ V,
        ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧
          α (Real.sqrt (T-s)) = p ∧ α (Real.sqrt (T-s+r^2)) = q ∧
          MapsTo α (Icc (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)))
            (riemannianClosedBallOf (S.base.metric s) p r) ∧
          lRegularizedAction S T α (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)) ≤
            (Real.exp (2 * (Module.finrank ℝ E : ℝ)^2 * K * (s-u)) +
              2 * (Module.finrank ℝ E : ℝ)^2 * K * r^2) * Real.sqrt Emax := by
  intro V
  have hV : IsOpen V := isOpen_lt
    (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric s) p) continuous_const
  have hmetric (x : M) (v w : TangentSpace I x) :
      (S.base.metric s).inner x v w =
        (S.base.metric s).inner (id x) (mfderiv I I (@id M) x v) (mfderiv I I (@id M) x w) := by
    rw [mfderiv_id]
    rfl
  have hvol := PDE.RicciFlow.riemannianVolumeMeasure_preimage_ge_of_curvature_bound
    S hS (S.base.metric s) id (Diffeomorph.refl I M ∞).isLocalDiffeomorph Function.injective_id
    hK hcarrier hregular hRm hmetric V hV.measurableSet (by simp)
    (show s-r^2 ∈ Icc u s from ⟨hroom, sub_le_self _ (sq_nonneg r)⟩)
  simp only [preimage_id_eq, sub_sub_cancel] at hvol
  refine ⟨hV, ?_, ?_⟩
  · calc
      _ = ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ)^3 * K * r^2))) *
          (ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E) := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      _ ≤ ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ)^3 * K * r^2))) *
          riemannianVolumeMeasure I M (S.base.metric s) V := mul_le_mul' le_rfl hvolume
      _ ≤ _ := hvol
  · intro T Emax hsT hE q hq
    exact exists_lRegularizedAction_le_of_backward_ball S hS hK hus hcarrier hregular hRm p q hr
      hq hcompact hroom hsT hE

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
  {D : RealTimeInterval}

theorem exists_volume_and_connector_action_bound_of_terminal_map
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Injective f)
    {u s K : ℝ} (hK : 0 ≤ K) (hus : u ≤ s)
    (hcarrier : Icc u s ⊆ D.carrier) (hregular : Ioo u s ⊆ D.regular)
    (hRm : ∀ t ∈ Icc u s, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2)
    (hterminal : S.base.metric s = localPullMetric g f hf)
    (x : N) {R r κ : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcompact : IsCompact (riemannianClosedBallOf g x R))
    (hinside : riemannianBallOf g x R ⊆ range f)
    (hroom : u ≤ s-r^2)
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I N g (riemannianBallOf g x r)) :
    ∃ p : M, f p = x ∧
      let V := riemannianBallOf (S.base.metric s) p r;
      IsOpen V ∧ f '' V = riemannianBallOf g x r ∧
      ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ)^3 * K * r^2)) * κ) *
        ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolumeMeasure I M (S.base.metric (s-r^2)) V ∧
      ∀ T Emax : ℝ, s ≤ T → T-s+r^2 ≤ Emax → ∀ q ∈ V,
        ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧
          α (Real.sqrt (T-s)) = p ∧ α (Real.sqrt (T-s+r^2)) = q ∧
          MapsTo α (Icc (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)))
            (riemannianClosedBallOf (S.base.metric s) p r) ∧
          lRegularizedAction S T α (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)) ≤
            (Real.exp (2 * (Module.finrank ℝ E : ℝ)^2 * K * (s-u)) +
              2 * (Module.finrank ℝ E : ℝ)^2 * K * r^2) * Real.sqrt Emax := by
  obtain ⟨p, hp, hcompactp⟩ := exists_lift_isCompact_riemannianClosedBallOf_localPullMetric
    g f hf hinj x (hr.trans hrR) hcompact hinside
  have hsourcecompact : IsCompact (riemannianClosedBallOf (S.base.metric s) p r) := by
    rw [hterminal]
    exact hcompactp r hrR
  have hmid : r < (r+R)/2 := by linarith
  have hmidR : (r+R)/2 < R := by linarith
  have heq := Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric
    g f hf hinj p hr hmid (hcompactp _ hmidR)
  have himage := image_riemannianBallOf_localPullMetric g f hf hinj p hr hmid (hcompactp _ hmidR)
  rw [hp, ← hterminal] at heq himage
  have hvolS := hvolume.trans_eq heq.symm
  obtain ⟨hV,hvol,hconnect⟩ := volume_and_connector_action_bound_of_backward_ball
    S hS hK hus hcarrier hregular hRm p hr hsourcecompact hroom hvolS
  exact ⟨p,hp,hV,himage,hvol,hconnect⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
