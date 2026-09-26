import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Count
set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open Exponential
open NormalCoordinates
open Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [local instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance tangentSpaceNormedAddCommGroup
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

local notation "F₀" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem volume_mul_pow_le_of_local_ricci_lower_bound
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (p : M) {q r R : ℝ}
    (hq : 0 ≤ q) (hr : 0 < r) (hrR : r ≤ R)
    (hcpt : IsCompact (riemannianClosedBallOf g p R))
    (hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor g y v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (2 ^ Module.finrank ℝ E *
        Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * R) *
          R ^ Module.finrank ℝ E) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  have hR : 0 < R := hr.trans_le hrR
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hcompact : IsCompact (Metric.closedEBall p (ENNReal.ofReal R)) := by
    convert hcpt using 1
    ext x
    rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I) p x]
    rfl
  have hbg := bishop_gromov_of_isCompact_closedEBall g hEnorm p hq hr hrR hcompact
    (fun y v hy => hRic y hy v)
  let n := Module.finrank ℝ E
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hlow : (r / 2) ^ n ≤ hyperbolicRadialVolume q (n - 1) r := by
    simpa only [hn] using hyperbolicRadialVolume_ge (n - 1) hq hr
  have hupp : hyperbolicRadialVolume q (n - 1) R ≤
      R ^ n * Real.exp (q * ((n - 1 : ℕ) : ℝ) * R) := by
    simpa only [hn] using hyperbolicRadialVolume_le (n - 1) hq (hr.le.trans hrR)
  have hcross : riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
      ENNReal.ofReal ((r / 2) ^ n) ≤
      ENNReal.ofReal (R ^ n * Real.exp (q * ((n - 1 : ℕ) : ℝ) * R)) *
        riemannianVolumeMeasure I M g (riemannianBallOf g p r) :=
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlow)).trans
      (hbg.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hupp) le_rfl))
  have hmul := mul_le_mul' hcross (le_refl (ENNReal.ofReal ((2 : ℝ) ^ n)))
  have hleft : ENNReal.ofReal ((r / 2) ^ n) * ENNReal.ofReal ((2 : ℝ) ^ n) =
      ENNReal.ofReal (r ^ n) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 1
    ring
  calc
    _ = (riemannianVolumeMeasure I M g (riemannianBallOf g p R) *
        ENNReal.ofReal ((r / 2) ^ n)) * ENNReal.ofReal ((2 : ℝ) ^ n) := by
          rw [mul_assoc, hleft]
    _ ≤ _ := hmul
    _ = _ := by
      rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
