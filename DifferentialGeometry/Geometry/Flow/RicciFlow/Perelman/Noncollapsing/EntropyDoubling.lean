import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Comparison.Volume.LocalDoubling
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalDoubling

set_option autoImplicit false
noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

theorem doublingConstant_eq_localDoublingFactor (n : ℕ) (a : ℝ) (hn : 2 ≤ n) (ha : 0 ≤ a) :
    doublingConstant n a = localDoublingFactor n a := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast this.ne'
  have hdpos : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hd : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hdpos
  have hfrac : 0 ≤ a / ((n - 1 : ℕ) : ℝ) := div_nonneg ha hd.le
  set q : ℝ := Real.sqrt (a / ((n - 1 : ℕ) : ℝ)) with hqdef
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = a / ((n - 1 : ℕ) : ℝ) := by
    rw [hqdef]
    exact Real.sq_sqrt hfrac
  have hK : -a / (n - 1 : ℕ) = -(q ^ 2) := by rw [hq2, neg_div]
  have hnum : modelVolume (-a / (n - 1 : ℕ)) n 1 =
      (n : ℝ) * euclideanUnitBallVolume n * hyperbolicRadialVolume q (n - 1) 1 := by
    rw [hK, modelVolume_neg_sq q n 1 hq]
  have hden : modelVolume (-a / (n - 1 : ℕ)) n (1 / 2) =
      (n : ℝ) * euclideanUnitBallVolume n * hyperbolicRadialVolume q (n - 1) (1 / 2) := by
    rw [hK, modelVolume_neg_sq q n (1 / 2) hq]
  have hc : (n : ℝ) * euclideanUnitBallVolume n ≠ 0 :=
    mul_ne_zero hn0 (euclideanUnitBallVolume_pos n).ne'
  rw [doublingConstant, localDoublingFactor, ← hqdef, hnum, hden]
  rw [mul_div_mul_left _ _ hc]

theorem one_le_doublingConstant (n : ℕ) (a : ℝ) (hn : 2 ≤ n) (ha : 0 ≤ a) :
    1 ≤ doublingConstant n a := by
  rw [doublingConstant_eq_localDoublingFactor n a hn ha]
  exact one_le_localDoublingFactor n a

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_volume_doubling_of_localDoubling
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (hn : 2 ≤ Module.finrank ℝ E)
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hRic : ∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
      -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) :
    (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal ≤
      localDoublingFactor (Module.finrank ℝ E) a *
        (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x (r / 2))).toReal := by
  have hballR : riemannianBallOf (I := I) g x r =
      {y : M | riemannianEDist I x y < ENNReal.ofReal r} := by
    unfold riemannianBallOf
    congr with y
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y]
  have hballS : riemannianBallOf (I := I) g x (r / 2) =
      {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)} := by
    unfold riemannianBallOf
    congr with y
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y]
  have hRicOn : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal r} (-a / r ^ 2) := by
    intro y hy v
    have hyb : y ∈ riemannianBallOf (I := I) g x r := by
      rw [hballR]
      exact hy
    have h := hRic y hyb v
    have hmetric : metricRicciAt (I := I) g y (fun _ : Fin 2 => v) =
        ricciTensor (I := I) g y v v := by
      have hv : (fun _ : Fin 2 => v) = vec2 v v := by
        funext i
        fin_cases i <;> simp [vec2]
      rw [hv]
      exact metricRicciAt_apply_eq_ricciTensor (I := I) g y v v
    have hc : -a * r⁻¹ ^ 2 = -a / r ^ 2 := by rw [inv_pow, div_eq_mul_inv]
    rw [hmetric, hc] at h
    exact h
  rw [hballR, hballS]
  have hmain := localDoubling (I := I) (M := M) g hEnorm x hn ha hr hRicOn
  have hmono : riemannianVolumeMeasure I M g
        {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)} ≤
      riemannianVolumeMeasure I M g {y : M | riemannianEDist I x y < ENNReal.ofReal r} :=
    measure_mono fun y hy => lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by linarith))
  have hdcpos : 0 ≤ doublingConstant (Module.finrank ℝ E) a :=
    (doublingConstant_pos (Module.finrank ℝ E) a hn ha).le
  calc (riemannianVolumeMeasure I M g
        {y : M | riemannianEDist I x y < ENNReal.ofReal r}).toReal
      ≤ (ENNReal.ofReal (doublingConstant (Module.finrank ℝ E) a) *
          riemannianVolumeMeasure I M g
            {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal :=
        ENNReal.toReal_mono' hmain fun hb => by
          rcases ENNReal.mul_eq_top.1 hb with ⟨h1, h2⟩ | ⟨h1, _⟩
          · exact top_unique (h2 ▸ hmono)
          · exact absurd h1 ENNReal.ofReal_ne_top
    _ = doublingConstant (Module.finrank ℝ E) a *
        (riemannianVolumeMeasure I M g
          {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal :=
        ENNReal.toReal_ofReal_mul _ _ hdcpos
    _ = localDoublingFactor (Module.finrank ℝ E) a *
        (riemannianVolumeMeasure I M g
          {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)}).toReal := by
        rw [doublingConstant_eq_localDoublingFactor (Module.finrank ℝ E) a hn ha]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature MeasureTheory
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open scoped Manifold ContDiff ENNReal

universe u uE uH

section WeakContext

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem local_entropy_volume_of_doubling [I.Boundaryless]
    (hdim : 2 ≤ Module.finrank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdoubling : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
      (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
        -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) →
      (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal ≤
        localDoublingFactor (Module.finrank ℝ E) a *
          (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x (r / 2))).toReal) :
    ∃ C : ℝ, ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
      (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
        -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) →
      (∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) →
      muSobolev g (r ^ 2) ≤
        ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
          r ^ Module.finrank ℝ E) + C : ℝ) : EReal) := by
  let _ := ha
  refine ⟨cutoffEntropyConstant (Module.finrank ℝ E)
    (localDoublingFactor (Module.finrank ℝ E) a) b, ?_⟩
  intro M _ _ _ _ _ g x r hr hRic hscalar
  exact cutoff_entropy_doubling (I := I) (M := M) g hdim x hr
    (one_le_localDoublingFactor (Module.finrank ℝ E) a) hb
    (hdoubling M g x r hr hRic) hscalar

end WeakContext

section StrongContext

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem local_entropy_volume_closed [I.Boundaryless]
    (hdim : 2 ≤ Module.finrank ℝ E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
        -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) →
      (∀ y ∈ riemannianBallOf (I := I) g x r, metricScalarAt g y ≤ b * r⁻¹ ^ 2) →
      muSobolev g (r ^ 2) ≤
        ((Real.log ((riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal /
          r ^ Module.finrank ℝ E) + C : ℝ) : EReal) := by
  refine ⟨cutoffEntropyConstant (Module.finrank ℝ E)
    (doublingConstant (Module.finrank ℝ E) a) b, ?_⟩
  intro M _ _ _ _ _ _ g x r hr hRic hscalar
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace M := (RiemannianMetricComplete.of_compact (I := I) g).complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun y v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  refine cutoff_entropy_doubling (I := I) (M := M) g hdim x hr
    (one_le_doublingConstant (Module.finrank ℝ E) a hdim ha) hb ?_ hscalar
  simpa only [doublingConstant_eq_localDoublingFactor (Module.finrank ℝ E) a hdim ha] using
    local_volume_doubling_of_localDoubling (I := I) (M := M) g hEnorm x hdim ha hr hRic

end StrongContext

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
