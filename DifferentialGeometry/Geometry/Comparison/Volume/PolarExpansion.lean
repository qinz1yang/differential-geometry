import DifferentialGeometry.Geometry.Comparison.Volume.PolarCoordinates
import DifferentialGeometry.Analysis.Calculus.Inverse.MatrixSmoothness
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.MetricJets
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open scoped Topology Manifold ContDiff

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_apply_contDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (v w : E) :
    ContDiff ℝ ∞ (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z v w) := by
  let D := modelWithCornersSelf ℝ E
  let F : E → M := intrinsicFramedExp (I := I) g hEnorm p
  let V : E → TangentBundle I M := fun z =>
    TotalSpace.mk' E (F z) (mfderiv D I F z v)
  let W : E → TangentBundle I M := fun z =>
    TotalSpace.mk' E (F z) (mfderiv D I F z w)
  have hF : ContMDiff D I ∞ F :=
    intrinsicFrame_smooth (I := I) g hEnorm p
  have hvconst : ContMDiff D D.tangent ∞ (fun z : E =>
      (TotalSpace.mk' E z v : TangentBundle D E)) := by
    exact (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => v)).mpr
      contDiff_const
  have hwconst : ContMDiff D D.tangent ∞ (fun z : E =>
      (TotalSpace.mk' E z w : TangentBundle D E)) := by
    exact (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => w)).mpr
      contDiff_const
  have htangent : ContMDiff D.tangent I.tangent ∞ (tangentMap D I F) :=
    hF.contMDiff_tangentMap (le_refl _)
  have hV : ContMDiff D I.tangent ∞ V := by
    have hcomp := htangent.comp hvconst
    have hfun : V = (tangentMap D I F) ∘ fun z : E =>
        (TotalSpace.mk' E z v : TangentBundle D E) := rfl
    rw [hfun]
    exact hcomp
  have hW : ContMDiff D I.tangent ∞ W := by
    have hcomp := htangent.comp hwconst
    have hfun : W = (tangentMap D I F) ∘ fun z : E =>
        (TotalSpace.mk' E z w : TangentBundle D E) := rfl
    rw [hfun]
    exact hcomp
  have hscalar : ContMDiff D 𝓘(ℝ, ℝ) ∞
      (fun z : E => g.inner (F z) (mfderiv D I F z v)
        (mfderiv D I F z w)) := by
    let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let _ := rb
    have hinner := ContMDiff.inner_bundle
      (F := E) (B := M) (E := (TangentSpace I : M → Type _))
      (b := F) (v := fun z => mfderiv D I F z v)
      (w := fun z => mfderiv D I F z w) hV hW
    exact hinner.congr (fun _ => rfl)
  rw [contMDiff_iff_contDiff] at hscalar
  have hfun :
      (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z v w) =
        fun z : E => g.inner (F z) (mfderiv D I F z v)
          (mfderiv D I F z w) := by
    funext z
    exact intrinsicFrameMetric_apply (I := I) g hEnorm p z v w
  rw [hfun]
  exact hscalar

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_contDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ContDiff ℝ ∞ (intrinsicFrameMetric (I := I) g hEnorm p) := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_clm_apply_iff]
  intro w
  exact intrinsicFrameMetric_apply_contDiff (I := I) g hEnorm p v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_diag_jet
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (z a b : E) (n : ℕ) :
    iteratedFDeriv ℝ n (intrinsicFrameMetric (I := I) g hEnorm p) z
        (fun _ => a) b b =
      intrinsicMetricJet (I := I) g hEnorm p
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p z))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p a))
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p b)) n 0 := by
  exact intrinsicMetric_diag_jet (I := I) g hEnorm p z a b n
    (intrinsicFrameMetric_contDiff (I := I) g hEnorm p).contDiffAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def intrinsicFrameGram
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (z : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => intrinsicFrameMetric (I := I) g hEnorm p z
    ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
@[simp]
theorem intrinsicFrameGram_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    intrinsicFrameGram (I := I) g hEnorm p 0 = 1 := by
  ext i j
  change intrinsicFrameMetric (I := I) g hEnorm p 0
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j) =
    if i = j then 1 else 0
  have hzero := intrinsicFrameMetric_zero (I := I) g hEnorm p
  rw [hzero]
  exact OrthonormalBasis.inner_eq_ite (stdOrthonormalBasis ℝ E) i j

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_eq_sqrt_det_intrFrameGram
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (z : E) :
    normalExpJacobian (I := I) g hEnorm p z =
      Real.sqrt (intrinsicFrameGram (I := I) g hEnorm p z).det := by
  unfold normalExpJacobian curveDensity
  congr 1
  apply congrArg Matrix.det
  ext i j
  simp only [curveGram, Matrix.of_apply, intrinsicFrameGram]
  rw [intrinsic_metric_jacobi (I := I) g hEnorm p z
    ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)]
  simp only [normalFrame_basis]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
@[simp]
theorem normalExpJacobian_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    normalExpJacobian (I := I) g hEnorm p 0 = 1 := by
  rw [normalExpJacobian_eq_sqrt_det_intrFrameGram,
    intrinsicFrameGram_zero, Matrix.det_one, Real.sqrt_one]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_det_contDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ContDiff ℝ ∞ (fun z : E => (intrinsicFrameGram (I := I) g hEnorm p z).det) := by
  apply DifferentialGeometry.Analysis.contDiff_det_of_entries
  intro i j
  exact intrinsicFrameMetric_apply_contDiff (I := I) g hEnorm p
    ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_det_pos_of_mem_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (z : E)
    (hz : normalFrame (I := I) (E := E) g p z ∈
      SegmentInt (I := I) g hEnorm p) :
    0 < (intrinsicFrameGram (I := I) g hEnorm p z).det := by
  apply Real.sqrt_pos.mp
  rw [← normalExpJacobian_eq_sqrt_det_intrFrameGram
    (I := I) g hEnorm p z]
  exact normalExpJacobian_pos_of_mem_segInt (I := I) g hEnorm p z hz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_contDiffOn_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ContDiffOn ℝ ∞ (normalExpJacobian (I := I) g hEnorm p)
      {z : E | normalFrame (I := I) (E := E) g p z ∈
        SegmentInt (I := I) g hEnorm p} := by
  have hsqrt := (intrinsicFrameGram_det_contDiff (I := I) g hEnorm p).contDiffOn.sqrt
    (fun z hz => (intrinsicFrameGram_det_pos_of_mem_segInt
      (I := I) g hEnorm p z hz).ne')
  exact hsqrt.congr fun z _ =>
    normalExpJacobian_eq_sqrt_det_intrFrameGram (I := I) g hEnorm p z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem isOpen_normalPolarDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    IsOpen (normalPolarDomain (I := I) g hEnorm p) := by
  change IsOpen
    ({z : Metric.sphere (0 : E) 1 × ℝ | 0 < z.2} ∩
      {z | normalFrame (I := I) (E := E) g p (z.2 • (z.1 : E)) ∈
        SegmentInt (I := I) g hEnorm p})
  refine (isOpen_lt continuous_const continuous_snd).inter
    ((isOpen_segInt (I := I) g hEnorm p).preimage ?_)
  exact (normalFrame (I := I) (E := E) g p).continuous.comp
    (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_contMDiffOn
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ContMDiffOn
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : Metric.sphere (0 : E) 1 × ℝ =>
        normalPolarJacobian (I := I) g hEnorm p z.2 z.1)
      (normalPolarDomain (I := I) g hEnorm p) := by
  let P := (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
    (modelWithCornersSelf ℝ ℝ)
  let radial : Metric.sphere (0 : E) 1 × ℝ → E :=
    fun z => z.2 • (z.1 : E)
  have hradial : ContMDiff P (modelWithCornersSelf ℝ E) ∞ radial := by
    exact contMDiff_snd.smul
      ((contMDiff_coe_sphere (E := E) (n := n)).comp contMDiff_fst)
  have hJac : ContMDiffOn (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ ℝ) ∞
      (normalExpJacobian (I := I) g hEnorm p)
      {z : E | normalFrame (I := I) (E := E) g p z ∈
        SegmentInt (I := I) g hEnorm p} :=
    (normalExpJacobian_contDiffOn_segInt
      (I := I) g hEnorm p).contMDiffOn
  have hmaps : normalPolarDomain (I := I) g hEnorm p ⊆
      radial ⁻¹' {z : E | normalFrame (I := I) (E := E) g p z ∈
        SegmentInt (I := I) g hEnorm p} := by
    intro z hz
    exact hz.2
  have hcomp : ContMDiffOn P (modelWithCornersSelf ℝ ℝ) ∞
      ((normalExpJacobian (I := I) g hEnorm p) ∘ radial)
      (normalPolarDomain (I := I) g hEnorm p) :=
    hJac.comp hradial.contMDiffOn hmaps
  have hpow : ContMDiff P (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : Metric.sphere (0 : E) 1 × ℝ =>
        z.2 ^ (Module.finrank ℝ E - 1)) :=
    contMDiff_snd.pow _
  exact (hpow.contMDiffOn.mul hcomp).congr fun _ _ => rfl

end Poincare.Geometry.Riemannian.VolumeComparison

end
