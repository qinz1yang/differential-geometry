import DifferentialGeometry.Geometry.Comparison.Volume.PolarJacobianJets
import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicLaunchTwoJet
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

noncomputable section
open Bundle Set Function Filter Manifold
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
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
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem minSmoothness_two_le_infty : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [show minSmoothness ℝ 2 = (2 : ℕ∞ω) from by norm_num [minSmoothness]]
  exact WithTop.coe_le_coe.mpr le_top

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_apply_add_left
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a a' b c d : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        ![a + a', b] c d =
      iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![a, b] c d +
        iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![a', b] c d := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, add_apply]

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_apply_add_right
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b b' c d : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        ![a, b + b'] c d =
      iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![a, b] c d +
        iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![a, b'] c d := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, add_apply]

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_apply_symm
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b c d : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, b] c d =
      iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        ![b, a] c d := by
  have hsym : IsSymmSndFDerivAt ℝ (intrinsicFrameMetric (I := I) g hEnorm p) 0 :=
    (intrinsicFrameMetric_contDiff (I := I) g hEnorm p).contDiffAt.isSymmSndFDerivAt
      minSmoothness_two_le_infty
  rw [IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hsym)]

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_apply_swap_last
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a c d : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] c d =
      iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] d c := by
  have hG : ContDiff ℝ ∞ (intrinsicFrameMetric (I := I) g hEnorm p) :=
    intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hGc : ContDiff ℝ ∞ (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z c) :=
    hG.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => c))
  have h₁ := iteratedFDeriv_clm_apply_const_apply hGc (i := 2) (x := (0 : E))
    (u := d) (m := ![a, a]) (by norm_cast)
  have h₂ := iteratedFDeriv_clm_apply_const_apply hG (i := 2) (x := (0 : E))
    (u := c) (m := ![a, a]) (by norm_cast)
  have hcd : iteratedFDeriv ℝ 2
      (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z c d) 0 ![a, a] =
      (iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a]) c d :=
    h₁.trans (congrArg (fun A : E →L[ℝ] ℝ => A d) h₂)
  have hdc : iteratedFDeriv ℝ 2
      (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z d c) 0 ![a, a] =
      (iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a]) d c :=
    (iteratedFDeriv_clm_apply_const_apply
        (hG.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => d)))
        (i := 2) (x := (0 : E)) (u := c) (m := ![a, a]) (by norm_cast)).trans
      (congrArg (fun A : E →L[ℝ] ℝ => A c)
        (iteratedFDeriv_clm_apply_const_apply hG (i := 2) (x := (0 : E))
          (u := d) (m := ![a, a]) (by norm_cast)))
  have hfun : (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z c d) =
      (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z d c) := by
    funext z
    rw [intrinsicFrameMetric_apply (I := I) g hEnorm p z c d,
      intrinsicFrameMetric_apply (I := I) g hEnorm p z d c]
    exact g.symm _ _ _
  calc
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] c d =
        iteratedFDeriv ℝ 2
          (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z c d) 0 ![a, a] :=
      hcd.symm
    _ = iteratedFDeriv ℝ 2
          (fun z : E => intrinsicFrameMetric (I := I) g hEnorm p z d c) 0 ![a, a] := by
      rw [hfun]
    _ = iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] d c :=
      hdc

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem eq_of_diag_of_symm {b₁ b₂ : E → E → ℝ}
    (h₁a : ∀ x y z, b₁ (x + y) z = b₁ x z + b₁ y z)
    (h₁b : ∀ x y z, b₁ x (y + z) = b₁ x y + b₁ x z)
    (h₂a : ∀ x y z, b₂ (x + y) z = b₂ x z + b₂ y z)
    (h₂b : ∀ x y z, b₂ x (y + z) = b₂ x y + b₂ x z)
    (s₁ : ∀ x y, b₁ x y = b₁ y x) (s₂ : ∀ x y, b₂ x y = b₂ y x)
    (d : ∀ x, b₁ x x = b₂ x x) :
    ∀ x y, b₁ x y = b₂ x y := by
  intro x y
  have e₁ : b₁ (x + y) (x + y) = b₁ x x + 2 * b₁ x y + b₁ y y := by
    rw [h₁a x y (x + y), h₁b x x y, h₁b y x y, s₁ y x]
    ring
  have e₂ : b₂ (x + y) (x + y) = b₂ x x + 2 * b₂ x y + b₂ y y := by
    rw [h₂a x y (x + y), h₂b x x y, h₂b y x y, s₂ y x]
    ring
  have hxy := d (x + y)
  rw [e₁, e₂, d x, d y] at hxy
  linarith

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_diag
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a c : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] c c =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
          (normalFrame (I := I) g p c) (normalFrame (I := I) g p a)
          (normalFrame (I := I) g p a))
        (normalFrame (I := I) g p c) := by
  have htuple : (fun _ : Fin 2 => a) = ![a, a] := by
    funext i
    fin_cases i <;> rfl
  have hlib := intrinsicFrameMetric_diag_jet (I := I) g hEnorm p 0 a c 2
  simp only [map_zero] at hlib
  rw [htuple] at hlib
  rw [hlib]
  have hone : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0 :=
    fun a b => congrArg (fun v => (v : E))
      (intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b)
  have htwo : ∀ a b : E,
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
        -(1 / 3 : ℝ) •
          (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
            (b : E) (a : E) (a : E) : E) :=
    fun a b => congrArg (fun v => (v : E))
      (intrinsicLaunchJet_two_zero_of_residual (I := I) g hEnorm p a b)
  simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
    (intrinsicMetricJet_two_zero_of_launch_jets (I := I) g hEnorm p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p c)
      (hone _ _) (htwo _ _))

omit [T2Space (TangentBundle I M)] in
private theorem second_jet_diag_last
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a c d : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![a, a] c d =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
          (normalFrame (I := I) g p c) (normalFrame (I := I) g p a)
          (normalFrame (I := I) g p a))
        (normalFrame (I := I) g p d) := by
  refine eq_of_diag_of_symm
    (b₁ := fun x y => iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
      ![a, a] x y)
    (b₂ := fun x y => -(2 / 3 : ℝ) * g.inner p
      (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p a)
        (normalFrame (I := I) g p a))
      (normalFrame (I := I) g p y))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d
  · intro x y z
    simp only [map_add, add_apply]
  · intro x y z
    simp only [map_add]
  · intro x y z
    simp only [map_add, add_apply]
    ring
  · intro x y z
    simp only [map_add]
    ring
  · intro x y
    exact second_jet_apply_swap_last (I := I) g hEnorm p a x y
  · intro x y
    rw [riemannOp_diag_symm]
    rw [g.symm]
  · intro x
    exact second_jet_diag (I := I) g hEnorm p a x

omit [T2Space (TangentBundle I M)] in
theorem iteratedFDeriv_two_intrinsicFrameMetric_eq_riemannOp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (u v x y : E) :
    iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, v] x y =
      -(1 / 3 : ℝ) *
        (g.inner p
            (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
              (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
              (normalFrame (I := I) g p v))
            (normalFrame (I := I) g p y)
          + g.inner p
            (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
              (normalFrame (I := I) g p x) (normalFrame (I := I) g p v)
              (normalFrame (I := I) g p u))
            (normalFrame (I := I) g p y)) := by
  refine eq_of_diag_of_symm
    (b₁ := fun a b => iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
      ![a, b] x y)
    (b₂ := fun a b => -(1 / 3 : ℝ) *
      (g.inner p
          (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
            (normalFrame (I := I) g p x) (normalFrame (I := I) g p a)
            (normalFrame (I := I) g p b))
          (normalFrame (I := I) g p y)
        + g.inner p
          (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
            (normalFrame (I := I) g p x) (normalFrame (I := I) g p b)
            (normalFrame (I := I) g p a))
          (normalFrame (I := I) g p y)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ u v
  · intro a a' b
    exact second_jet_apply_add_left (I := I) g hEnorm p a a' b x y
  · intro a b b'
    exact second_jet_apply_add_right (I := I) g hEnorm p a b b' x y
  · intro a a' b
    simp only [map_add, add_apply]
    ring
  · intro a b b'
    simp only [map_add, add_apply]
    ring
  · intro a b
    exact second_jet_apply_symm (I := I) g hEnorm p a b x y
  · intro a b
    ring
  · intro a
    rw [second_jet_diag_last (I := I) g hEnorm p a x y]
    ring

omit [T2Space (TangentBundle I M)] in
theorem metricRm04StandardAt_normalFrame_add_eq_second_jet
    [BoundarylessManifold I M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (u v x y : E) :
    metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p v) (normalFrame (I := I) g p y)
      + metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p v)
        (normalFrame (I := I) g p u) (normalFrame (I := I) g p y)
      = -3 * iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![u, v] x y := by
  rw [DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp,
    DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
  simp only [g.symm p (normalFrame (I := I) g p y)]
  rw [iteratedFDeriv_two_intrinsicFrameMetric_eq_riemannOp (I := I) g hEnorm p u v x y]
  ring

omit [T2Space (TangentBundle I M)] in
theorem metricRm04StandardAt_normalFrame_self_eq_second_jet
    [BoundarylessManifold I M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (u x : E) :
    metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) (normalFrame (I := I) g p x)
      = -(3 / 2 : ℝ) * iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![u, u] x x := by
  have h := metricRm04StandardAt_normalFrame_add_eq_second_jet (I := I) g hEnorm p u u x x
  rw [show metricRm04StandardAt (I := I) g p
      (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
      (normalFrame (I := I) g p u) (normalFrame (I := I) g p x)
      + metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) (normalFrame (I := I) g p x)
      = 2 * metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) (normalFrame (I := I) g p x) from by ring] at h
  linarith

omit [T2Space (TangentBundle I M)] in
theorem abs_metricRm04StandardAt_normalFrame_self_le_of_second_jet_bound
    [BoundarylessManifold I M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (C : ℝ) (u x : E)
    (hC : ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ ≤ C) :
    |metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p x) (normalFrame (I := I) g p u)
        (normalFrame (I := I) g p u) (normalFrame (I := I) g p x)|
      ≤ (3 / 2 : ℝ) * C * ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [metricRm04StandardAt_normalFrame_self_eq_second_jet (I := I) g hEnorm p u x]
  have hm : ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, u]‖
      ≤ C * (‖u‖ * ‖u‖) := by
    calc
      ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, u]‖
          ≤ ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ *
              ∏ j : Fin 2, ‖(![u, u] : Fin 2 → E) j‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ *
            (‖u‖ * ‖u‖) := by
        rw [Fin.prod_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      _ ≤ C * (‖u‖ * ‖u‖) := mul_le_mul_of_nonneg_right hC (by positivity)
  have hx : |(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        ![u, u]) x x| ≤ (C * (‖u‖ * ‖u‖)) * ‖x‖ * ‖x‖ := by
    calc
      |(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, u]) x x|
          = ‖(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
              ![u, u]) x x‖ := Real.norm_eq_abs _
      _ ≤ ‖(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
              ![u, u]) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * (‖u‖ * ‖u‖)) * ‖x‖ * ‖x‖ := by
        gcongr
        calc
          ‖(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
                ![u, u]) x‖
              ≤ ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
                  ![u, u]‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (C * (‖u‖ * ‖u‖)) * ‖x‖ :=
            mul_le_mul_of_nonneg_right hm (norm_nonneg x)
  have hsq : ‖u‖ * ‖u‖ = ‖u‖ ^ 2 := (sq ‖u‖).symm
  calc
    |-(3 / 2 : ℝ) * (iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
        ![u, u]) x x| = (3 / 2 : ℝ) * |(iteratedFDeriv ℝ 2
            (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, u]) x x| := by
      rw [abs_mul]
      norm_num
    _ ≤ (3 / 2 : ℝ) * ((C * (‖u‖ * ‖u‖)) * ‖x‖ * ‖x‖) := by
      gcongr
    _ = (3 / 2 : ℝ) * C * ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [hsq]
      ring

omit [T2Space (TangentBundle I M)] in
theorem iteratedDeriv_two_intrinsicFrameGram_eq_riemannOp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (u : E)
    (i : Fin (Module.finrank ℝ E)) :
    iteratedDeriv 2 (fun t : ℝ =>
        intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) 0 =
      -(2 / 3 : ℝ) * g.inner p
        (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
          (normalFrame (I := I) g p u) (normalFrame (I := I) g p u))
        (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i)) := by
  let e : E := (stdOrthonormalBasis ℝ E) i
  let F : E → ℝ := fun z => intrinsicFrameMetric (I := I) g hEnorm p z e e
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hF : ContDiff ℝ ∞ F :=
    (hmetric.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => e))).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E => e))
  have htuple : (fun _ : Fin 2 => u) = ![u, u] := by
    funext j
    fin_cases j <;> rfl
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ u
  have hcomp := L.iteratedFDeriv_comp_right hF 0 (i := 2) (by norm_cast)
  have happ := congrArg (fun A => A (fun _ : Fin 2 => (1 : ℝ))) hcomp
  have hFL : F ∘ L = (fun t : ℝ =>
      intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) := by
    funext t
    simp only [Function.comp_apply, F, L, ContinuousLinearMap.toSpanSingleton_apply,
      intrinsicFrameGram, e]
  rw [hFL] at happ
  have hrhs :
      ((iteratedFDeriv ℝ 2 F (L 0)).compContinuousLinearMap (fun _ : Fin 2 => L))
          (fun _ : Fin 2 => (1 : ℝ)) =
        iteratedFDeriv ℝ 2 F 0 (fun _ : Fin 2 => u) := by
    simp only [L, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [iteratedDeriv_eq_iteratedFDeriv]
  calc
    iteratedFDeriv ℝ 2 (fun t : ℝ =>
          intrinsicFrameGram (I := I) g hEnorm p (t • u) i i) 0
        (fun _ : Fin 2 => (1 : ℝ)) =
        iteratedFDeriv ℝ 2 F 0 (fun _ : Fin 2 => u) :=
      happ.trans hrhs
    _ = iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
          ![u, u] e e := by
      rw [show iteratedFDeriv ℝ 2 F 0 (fun _ : Fin 2 => u) =
          iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
            (fun _ : Fin 2 => u) e e from ?_]
      · rw [htuple]
      · rw [iteratedFDeriv_clm_apply_const_apply
          (hmetric.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => e))) (by norm_cast),
          iteratedFDeriv_clm_apply_const_apply hmetric (by norm_cast)]
    _ = -(2 / 3 : ℝ) * g.inner p
        (riemannOp (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))
          (normalFrame (I := I) g p u) (normalFrame (I := I) g p u))
        (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i)) := by
      rw [iteratedFDeriv_two_intrinsicFrameMetric_eq_riemannOp (I := I) g hEnorm p u u e e]
      simp only [e]
      ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem firstBianchiAt_metricRm04At
    (g : SmoothRiemannianMetric I M) (p : M) :
    FirstBianchiAt (I := I) (metricRm04At (I := I) (M := M) g p) := by
  have hreal : rm04RealizesConnection (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g) :=
    rm04Section_realizes (I := I) g (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g)
  simpa only [metricRm04_apply] using
    (DifferentialGeometry.Geometry.Connection.firstBianchiAt_of_leviCivita_realizes
      (I := I) g (metricRm04 (I := I) (M := M) g) hreal (x := p))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem metricRm04StandardAt_pair_swap
    (g : SmoothRiemannianMetric I M) (p : M)
    (X Y Z W : TangentSpace I p) :
    metricRm04StandardAt (I := I) g p Z W X Y =
      metricRm04StandardAt (I := I) g p X Y Z W := by
  rw [DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp,
    DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
  exact (g.symm p Y (riemannOp (LeviCivita (I := I) g) p Z W X)).trans
    ((riemannOp_inner_pair_symm (I := I) g p Z W X Y).trans
      (g.symm p (riemannOp (LeviCivita (I := I) g) p X Y Z) W))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem metricRm04StandardAt_swap_last
    (g : SmoothRiemannianMetric I M) (p : M)
    (X Y Z W : TangentSpace I p) :
    metricRm04StandardAt (I := I) g p X Y W Z =
      -metricRm04StandardAt (I := I) g p X Y Z W := by
  have hskew := riemannOp_metric_skew (I := I) g p X Y Z W
  have hswap : g.inner p Z (riemannOp (LeviCivita (I := I) g) p X Y W) =
      g.inner p (riemannOp (LeviCivita (I := I) g) p X Y W) Z := g.symm p Z _
  have hsum : g.inner p (riemannOp (LeviCivita (I := I) g) p X Y Z) W +
      g.inner p (riemannOp (LeviCivita (I := I) g) p X Y W) Z = 0 := by
    rw [← hswap]
    exact hskew
  have hmain : g.inner p (riemannOp (LeviCivita (I := I) g) p X Y Z) W =
      -g.inner p (riemannOp (LeviCivita (I := I) g) p X Y W) Z :=
    eq_neg_of_add_eq_zero_left hsum
  rw [DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp,
    DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp,
    hswap, g.symm p W (riemannOp (LeviCivita (I := I) g) p X Y Z)]
  linarith only [hmain]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem metricRm04StandardAt_swap_first
    (g : SmoothRiemannianMetric I M) (p : M)
    (X Y Z W : TangentSpace I p) :
    metricRm04StandardAt (I := I) g p Y X Z W =
      -metricRm04StandardAt (I := I) g p X Y Z W := by
  rw [DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp,
    DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
  have h := riemannOp_swap (LeviCivita (I := I) g) p X Y Z
  rw [h]
  simp only [map_neg, neg_neg]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem inner_riemannOp_eq_metricRm04StandardAt
    (g : SmoothRiemannianMetric I M) (p : M)
    (X Y Z W : TangentSpace I p) :
    g.inner p (riemannOp (LeviCivita (I := I) g) p X Y Z) W =
      metricRm04StandardAt (I := I) g p X Y Z W := by
  rw [DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
  exact g.symm p (riemannOp (LeviCivita (I := I) g) p X Y Z) W

omit [T2Space (TangentBundle I M)] in
theorem metricRm04StandardAt_normalFrame_eq_second_jet
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a b c d : E) :
    metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
        (normalFrame (I := I) g p c) (normalFrame (I := I) g p d)
      = iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c
        - iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d := by
  have h1 := iteratedFDeriv_two_intrinsicFrameMetric_eq_riemannOp (I := I) g hEnorm p b c a d
  rw [inner_riemannOp_eq_metricRm04StandardAt, inner_riemannOp_eq_metricRm04StandardAt] at h1
  have h2 := iteratedFDeriv_two_intrinsicFrameMetric_eq_riemannOp (I := I) g hEnorm p d b a c
  rw [second_jet_apply_symm (I := I) g hEnorm p d b a c,
    inner_riemannOp_eq_metricRm04StandardAt, inner_riemannOp_eq_metricRm04StandardAt] at h2
  set A1 := metricRm04StandardAt (I := I) g p
    (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
    (normalFrame (I := I) g p c) (normalFrame (I := I) g p d) with hA1
  set A2 := metricRm04StandardAt (I := I) g p
    (normalFrame (I := I) g p a) (normalFrame (I := I) g p c)
    (normalFrame (I := I) g p d) (normalFrame (I := I) g p b) with hA2
  set A3 := metricRm04StandardAt (I := I) g p
    (normalFrame (I := I) g p a) (normalFrame (I := I) g p d)
    (normalFrame (I := I) g p b) (normalFrame (I := I) g p c) with hA3
  set H1 := iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d with hH1
  set H2 := iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c with hH2
  have hBianchi : A2 + A1 + A3 = 0 := by
    have hF := firstBianchiAt_metricRm04At (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p c)
      (normalFrame (I := I) g p d) (normalFrame (I := I) g p b)
    rw [← metricRm04StandardAt_apply, ← metricRm04StandardAt_apply,
      ← metricRm04StandardAt_apply] at hF
    rw [metricRm04StandardAt_pair_swap (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
      (normalFrame (I := I) g p c) (normalFrame (I := I) g p d)] at hF
    rw [metricRm04StandardAt_swap_first (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p d)
      (normalFrame (I := I) g p c) (normalFrame (I := I) g p b)] at hF
    rw [metricRm04StandardAt_swap_last (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p d)
      (normalFrame (I := I) g p b) (normalFrame (I := I) g p c)] at hF
    simpa only [neg_neg] using hF
  have e2 : metricRm04StandardAt (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p c)
      (normalFrame (I := I) g p b) (normalFrame (I := I) g p d) = -A2 :=
    metricRm04StandardAt_swap_last (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p c)
      (normalFrame (I := I) g p d) (normalFrame (I := I) g p b)
  have e4 : metricRm04StandardAt (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
      (normalFrame (I := I) g p d) (normalFrame (I := I) g p c) = -A1 :=
    metricRm04StandardAt_swap_last (I := I) g p
      (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
      (normalFrame (I := I) g p c) (normalFrame (I := I) g p d)
  linarith only [h1, h2, hBianchi, e2, e4]

omit [T2Space (TangentBundle I M)] in
theorem abs_metricRm04StandardAt_normalFrame_le_of_second_jet_bound
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) {C : ℝ}
    (hC : ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ ≤ C)
    (a b c d : E) :
    |metricRm04StandardAt (I := I) g p
        (normalFrame (I := I) g p a) (normalFrame (I := I) g p b)
        (normalFrame (I := I) g p c) (normalFrame (I := I) g p d)|
      ≤ 2 * C * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  rw [metricRm04StandardAt_normalFrame_eq_second_jet (I := I) g hEnorm p a b c d]
  have hb : ∀ u v x y : E,
      |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, v] x y|
        ≤ C * ‖u‖ * ‖v‖ * ‖x‖ * ‖y‖ := by
    intro u v x y
    have hm : ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, v]‖
        ≤ C * (‖u‖ * ‖v‖) := by
      calc
        ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, v]‖
            ≤ ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ *
                ∏ j : Fin 2, ‖(![u, v] : Fin 2 → E) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ *
              (‖u‖ * ‖v‖) := by
          rw [Fin.prod_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ C * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_right hC (by positivity)
    calc
      |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![u, v] x y|
          = ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
              ![u, v] x y‖ := Real.norm_eq_abs _
      _ ≤ ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
              ![u, v] x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * (‖u‖ * ‖v‖)) * ‖x‖ * ‖y‖ := by
        gcongr
        calc
          ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
                ![u, v] x‖
              ≤ ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0
                  ![u, v]‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (C * (‖u‖ * ‖v‖)) * ‖x‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg x)
      _ = C * ‖u‖ * ‖v‖ * ‖x‖ * ‖y‖ := by ring
  have hsplit : |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c
      - iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d|
      ≤ |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c|
        + |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c)
        (-(iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d)))
  calc
    |iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, d] a c
        - iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0 ![b, c] a d|
        ≤ (C * ‖b‖ * ‖d‖ * ‖a‖ * ‖c‖) +
          (C * ‖b‖ * ‖c‖ * ‖a‖ * ‖d‖) :=
      hsplit.trans (add_le_add (hb b d a c) (hb b c a d))
    _ = 2 * C * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by ring

omit [T2Space (TangentBundle I M)] in
theorem curvDerivNorm_zero_le_of_normalFrame_second_jet_bound
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) {C : ℝ}
    (hC : ‖iteratedFDeriv ℝ 2 (intrinsicFrameMetric (I := I) g hEnorm p) 0‖ ≤ C) :
    CheegerGromovCompactness.curvDerivNorm (I := I) 0 g p ≤
      2 * (Module.finrank ℝ E : ℝ) ^ 2 * C := by
  classical
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC
  let e : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := (stdOrthonormalBasis ℝ E).toBasis
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    e.map (normalFrame (I := I) g p).toLinearEquiv
  have hbasis : ∀ i, basis i = normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i) := by
    intro i
    simp only [basis, e, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
    rfl
  have horth : ∀ i j,
      g.inner p (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hbasis i, hbasis j, normalFrame_inner]
    exact OrthonormalBasis.inner_eq_ite (stdOrthonormalBasis ℝ E) i j
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g p basis
      (Tensor0SBundle.identityInvMetric (Idx := Fin (Module.finrank ℝ E))) :=
    Tensor0SBundle.metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [CheegerGromovCompactness.curvDerivNorm, CheegerGromovCompactness.curvDerivNormSq]
  refine le_trans (Tensor0SBundle.sqrt_normSq0S_le_card_of_component_bound (I := I) g p 4
    basis hinv (CheegerGromovCompactness.curvCovDeriv (I := I) (M := M) g 0 p) (2 * C)
    (by linarith) ?_) ?_
  · intro slots
    rw [Tensor0SBundle.component0S_apply]
    have hvec : (fun a : Fin 4 => basis (slots a)) =
        DifferentialGeometry.Geometry.Curvature.vec4 (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
      funext a
      fin_cases a <;> rfl
    rw [hvec, CheegerGromovCompactness.curvZero_apply]
    simp only [hbasis]
    have hconv : g.inner p
        (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 3)))
        (riemannOp (LeviCivita (I := I) g) p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 0)))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 1)))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 2)))) =
        metricRm04StandardAt (I := I) g p
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 0)))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 1)))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 2)))
          (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) (slots 3))) :=
      (g.symm p _ _).symm.trans (inner_riemannOp_eq_metricRm04StandardAt (I := I) g p _ _ _ _)
    rw [hconv]
    have h := abs_metricRm04StandardAt_normalFrame_le_of_second_jet_bound (I := I) g hEnorm p hC
      ((stdOrthonormalBasis ℝ E) (slots 0)) ((stdOrthonormalBasis ℝ E) (slots 1))
      ((stdOrthonormalBasis ℝ E) (slots 2)) ((stdOrthonormalBasis ℝ E) (slots 3))
    simpa only [OrthonormalBasis.norm_eq_one, mul_one] using h
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    have hroot : Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4) =
        (Module.finrank ℝ E : ℝ) ^ 2 := by
      rw [show (Module.finrank ℝ E : ℝ) ^ 4 =
          ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 from by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [hroot]
    exact le_of_eq (by ring)

end Curvature
end Geometry
end DifferentialGeometry
