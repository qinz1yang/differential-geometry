import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance instMeasTangent (x : M) : MeasurableSpace (TangentSpace I x) :=
  borel _
private local instance instBorelTangent (x : M) : BorelSpace (TangentSpace I x) :=
  ⟨rfl⟩

def gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v) < R}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
def SegDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v)
        = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal}

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem mem_segDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {x : M} {v : TangentSpace I x} :
    v ∈ SegDom (I := I) g hEnorm x ↔
      Real.sqrt (g.inner x v v)
        = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
  Iff.rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segDom_zero [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : (0 : TangentSpace I x) ∈ SegDom (I := I) g hEnorm x := by
  rw [mem_segDom, expMapIntrinsic_zero (I := I) g hEnorm x,
    show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 by simp,
    Real.sqrt_zero, Manifold.riemannianEDist_self, ENNReal.toReal_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segDom_smul [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} {v : TangentSpace I x} (hv : v ∈ SegDom (I := I) g hEnorm x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s • v ∈ SegDom (I := I) g hEnorm x := by
  set L : ℝ := Real.sqrt (g.inner x v v) with hL
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have h1s : 0 ≤ 1 - s := by linarith
  have hg0 : intrinsicGeodesic (I := I) g hEnorm x v 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hg1 : intrinsicGeodesic (I := I) g hEnorm x v 1
      = expMapIntrinsic (I := I) g hEnorm x v := rfl
  have hgs : intrinsicGeodesic (I := I) g hEnorm x v s
      = expMapIntrinsic (I := I) g hEnorm x (s • v) := by
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  have hvmem : L = (riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x v)).toReal := hv
  have hfin1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x _
  have hedist1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)
      = ENNReal.ofReal L := by
    rw [hvmem, ENNReal.ofReal_toReal hfin1]
  have hup : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) ≤ ENNReal.ofReal (L * s) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := 0) (t := s) hs0
    rw [← hL, sub_zero] at h
    exact h
  have hup2 : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
      (intrinsicGeodesic (I := I) g hEnorm x v 1)
      ≤ ENNReal.ofReal (L * (1 - s)) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := s) (t := 1) hs1
    rw [← hL] at h
    exact h
  have hsplit : ENNReal.ofReal L
      = ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hLnn hs0) (mul_nonneg hLnn h1s)]
    congr 1; ring
  have hlow : ENNReal.ofReal (L * s)
      ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
          (intrinsicGeodesic (I := I) g hEnorm x v s) := by
    have htri : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
        (intrinsicGeodesic (I := I) g hEnorm x v 1)
        ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) :=
      riemannianEDist_triangle
    have hchain : ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
        ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + ENNReal.ofReal (L * (1 - s)) := by
      calc ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
          = riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) := by
            rw [← hsplit, hg1, hg0, hedist1]
        _ ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
                (intrinsicGeodesic (I := I) g hEnorm x v 1) := htri
        _ ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + ENNReal.ofReal (L * (1 - s)) := add_le_add le_rfl hup2
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have heq : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) = ENNReal.ofReal (L * s) :=
    le_antisymm hup hlow
  rw [hg0] at heq
  rw [mem_segDom, sqrt_gInner_smul_self (I := I) g x hs0 v, ← hL, ← hgs, heq,
    ENNReal.toReal_ofReal (mul_nonneg hLnn hs0)]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem ball_sub_image_segDom [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      expMapIntrinsic (I := I) g hEnorm x ''
        (SegDom (I := I) g hEnorm x ∩ gBall (I := I) g x R) := by
  intro y hy
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm x y
  refine ⟨v, ⟨?_, ?_⟩, hexp⟩
  · rw [mem_segDom, hexp]; exact hlen
  · change Real.sqrt (g.inner x v v) < R
    rw [hlen]
    exact ENNReal.toReal_lt_of_lt_ofReal hy

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem isOpen_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsOpen (gBall (I := I) g x R) :=
  isOpen_lt (Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x))
    continuous_const

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem measurableSet_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    MeasurableSet (gBall (I := I) g x R) :=
  (isOpen_gBall (I := I) g x R).measurableSet

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem isClosed_segDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : IsClosed (SegDom (I := I) g hEnorm x) := by
  have hf₁ : Continuous fun v : TangentSpace I x => Real.sqrt (g.inner x v v) :=
    Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x)
  have hexp : Continuous fun v : TangentSpace I x =>
      expMapIntrinsic (I := I) g hEnorm x v :=
    expMapIntrinsic_continuous (I := I) g hEnorm x
  have hbase : Continuous fun v : TangentSpace I x =>
      riemannianEDist I (expMapIntrinsic (I := I) g hEnorm x v) x :=
    (continuous_riemannianEDist_to (I := I) x).comp hexp
  have hedist : Continuous fun v : TangentSpace I x =>
      riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) :=
    hbase.congr fun v => Manifold.riemannianEDist_comm
  have hf₂ : Continuous fun v : TangentSpace I x =>
      (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hedist
      (fun v => riemannianEDist_ne_top (I := I) x _)
  exact isClosed_eq hf₁ hf₂

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem measurableSet_segDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : MeasurableSet (SegDom (I := I) g hEnorm x) :=
  (isClosed_segDom (I := I) g hEnorm x).measurableSet

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
