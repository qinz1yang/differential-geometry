import DifferentialGeometry.Geometry.Comparison.CGTRadialPath

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrFiber
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p q : M) (r : Real) : Set E :=
  {u | u ∈ Metric.ball (0 : E) r ∧
    intrinsicFramedExp (I := I) g hEnorm p u = q}

private noncomputable def radialLoop
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    Path p p :=
  (radialFlat (I := I) g hEnorm p u).cast rfl hu.symm

private theorem radialLoop_flat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    IsFlatC1Path (I := I) (radialLoop (I := I) g hEnorm p u hu) := by
  have h := radialFlat_flat (I := I) g hEnorm p u
  refine {
    c1 := ?_
    flat_zero := ?_
    flat_one := ?_ }
  · simpa only [radialLoop, Path.extend_cast] using h.c1
  · simpa only [radialLoop, Path.extend_cast] using h.flat_zero
  · simpa only [radialLoop, Path.extend_cast, hu] using h.flat_one

private theorem radialLoop_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    pathLen (I := I) (radialLoop (I := I) g hEnorm p u hu) =
      ENNReal.ofReal ‖u‖ := by
  simpa only [pathLen, radialLoop, Path.extend_cast] using
    radialFlat_len (I := I) g hEnorm p u

private noncomputable def radialLoopLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    IntrFrameLift (I := I) g hEnorm p
      (radialLoop (I := I) g hEnorm p u hu).extend 0 1 where
  toFun := (radialFlatLift (I := I) g hEnorm p u).toFun
  contDiff := (radialFlatLift (I := I) g hEnorm p u).contDiff
  start := (radialFlatLift (I := I) g hEnorm p u).start
  lifts := by
    simpa only [radialLoop, Path.extend_cast] using
      (radialFlatLift (I := I) g hEnorm p u).lifts

private theorem radialLoopLift_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    (radialLoopLift (I := I) g hEnorm p u hu).toFun 1 = u := by
  exact radialLift_one (I := I) g hEnorm p u

theorem exists_fiber_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hqs :
      riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ∃ f :
        intrFiber (I := I) g hEnorm p p r₀ →
          intrFiber (I := I) g hEnorm p q (r₀ + s),
      Function.Injective f := by
  obtain ⟨c, hcFlat, hcLen⟩ :=
    exists_flat_path (I := I) hqs
  have hR : 0 < R := lt_trans (add_pos hr₀ hs) hfit
  let loop :
      intrFiber (I := I) g hEnorm p p r₀ → Path p p :=
    fun u => radialLoop (I := I) g hEnorm p u.1 u.2.2
  let path :
      intrFiber (I := I) g hEnorm p p r₀ → Path p q :=
    fun u => (loop u).trans c
  have hloopFlat (u : intrFiber (I := I) g hEnorm p p r₀) :
      IsFlatC1Path (I := I) (loop u) :=
    radialLoop_flat (I := I) g hEnorm p u.1 u.2.2
  have hpathFlat (u : intrFiber (I := I) g hEnorm p p r₀) :
      IsFlatC1Path (I := I) (path u) :=
    (hloopFlat u).trans hcFlat
  have huNorm (u : intrFiber (I := I) g hEnorm p p r₀) :
      ‖u.1‖ < r₀ := by
    simpa only [intrFiber, Metric.mem_ball, dist_zero_right] using u.2.1
  have hpathSmall (u : intrFiber (I := I) g hEnorm p p r₀) :
      pathLen (I := I) (path u) < ENNReal.ofReal (r₀ + s) := by
    dsimp only [path]
    rw [pathLen_trans (hloopFlat u) hcFlat,
      radialLoop_len (I := I) g hEnorm p u.1 u.2.2]
    calc
      ENNReal.ofReal ‖u.1‖ + pathLen (I := I) c
          < ENNReal.ofReal r₀ + ENNReal.ofReal s :=
        ENNReal.add_lt_add
          ((ENNReal.ofReal_lt_ofReal_iff hr₀).2 (huNorm u)) hcLen
      _ = ENNReal.ofReal (r₀ + s) :=
        (ENNReal.ofReal_add hr₀.le hs.le).symm
  have hpathR (u : intrFiber (I := I) g hEnorm p p r₀) :
      pathLen (I := I) (path u) < ENNReal.ofReal R :=
    (hpathSmall u).trans
      ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  have hex (u : intrFiber (I := I) g hEnorm p p r₀) :
      Nonempty
        (IntrFrameLift (I := I) g hEnorm p (path u).extend 0 1) :=
    exists_intr_lift (I := I) g hEnorm p zero_le_one
      (hpathFlat u).c1.contMDiffOn (by simp)
      hR (hpathR u) hloc
  let lift (u : intrFiber (I := I) g hEnorm p p r₀) :
      IntrFrameLift (I := I) g hEnorm p (path u).extend 0 1 :=
    Classical.choice (hex u)
  let f :
      intrFiber (I := I) g hEnorm p p r₀ →
        intrFiber (I := I) g hEnorm p q (r₀ + s) :=
    fun u => ⟨(lift u).toFun 1, by
      constructor
      · simpa only [Metric.mem_ball, dist_zero_right] using
          (lift u).norm_lt (add_pos hr₀ hs) (hpathSmall u)
            (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)
      · have h := (lift u).lifts
          (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)
        simpa only [path, Path.extend_one, Function.comp_apply] using h⟩
  refine ⟨f, ?_⟩
  intro u v huv
  apply Subtype.ext
  let A :
      IntrFrameLift (I := I) g hEnorm p (loop u).extend 0 1 :=
    radialLoopLift (I := I) g hEnorm p u.1 u.2.2
  let B :
      IntrFrameLift (I := I) g hEnorm p (loop v).extend 0 1 :=
    radialLoopLift (I := I) g hEnorm p v.1 v.2.2
  have huR :
      pathLen (I := I) (loop u) < ENNReal.ofReal R := by
    rw [radialLoop_len (I := I) g hEnorm p u.1 u.2.2]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2
      ((huNorm u).trans ((lt_add_of_pos_right r₀ hs).trans hfit))
  have hvR :
      pathLen (I := I) (loop v) < ENNReal.ofReal R := by
    rw [radialLoop_len (I := I) g hEnorm p v.1 v.2.2]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2
      ((huNorm v).trans ((lt_add_of_pos_right r₀ hs).trans hfit))
  have hend : (lift u).toFun 1 = (lift v).toFun 1 :=
    congrArg Subtype.val huv
  have hcancel :
      A.toFun 1 = B.toFun 1 := by
    apply A.end_eq_of_append B (lift u) (lift v)
      hR huR hvR (hpathR u) (hpathR v) hloc hend
  simpa only [A, B, radialLoopLift_one] using hcancel

theorem fiber_encard_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hqs :
      riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    (intrFiber (I := I) g hEnorm p p r₀).encard ≤
      (intrFiber (I := I) g hEnorm p q (r₀ + s)).encard := by
  obtain ⟨f, hf⟩ :=
    exists_fiber_inj (I := I) g hEnorm hr₀ hs hqs hfit hloc
  exact (Function.Embedding.mk f hf).encard_le

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
