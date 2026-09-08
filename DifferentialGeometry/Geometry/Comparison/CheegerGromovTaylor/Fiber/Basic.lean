import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.Radial

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrinsicFiber
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
    Path.IsContMDiffWithSittingInstants (I := I) 1 (radialLoop (I := I) g hEnorm p u hu) := by
  have h := radialFlat_flat (I := I) g hEnorm p u
  refine {
    contMDiff := ?_
    eventuallyEq_zero := ?_
    eventuallyEq_one := ?_ }
  · simpa only [radialLoop, Path.extend_cast] using h.contMDiff
  · simpa only [radialLoop, Path.extend_cast] using h.eventuallyEq_zero
  · simpa only [radialLoop, Path.extend_cast, hu] using h.eventuallyEq_one

private theorem radialLoop_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    Path.riemannianELength (I := I) (radialLoop (I := I) g hEnorm p u hu) =
      ENNReal.ofReal ‖u‖ := by
  simpa only [Path.riemannianELength, radialLoop, Path.extend_cast] using
    radialFlat_len (I := I) g hEnorm p u

private noncomputable def radialLoopLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hu :
      intrinsicFramedExp (I := I) g hEnorm p u = p) :
    IntrinsicFrameLift (I := I) g hEnorm p
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
        intrinsicFiber (I := I) g hEnorm p p r₀ →
          intrinsicFiber (I := I) g hEnorm p q (r₀ + s),
      Function.Injective f := by
  obtain ⟨c, hcFlat, hcLen⟩ :=
    Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt (I := I) hqs
  have hR : 0 < R := lt_trans (add_pos hr₀ hs) hfit
  let loop :
      intrinsicFiber (I := I) g hEnorm p p r₀ → Path p p :=
    fun u => radialLoop (I := I) g hEnorm p u.1 u.2.2
  let path :
      intrinsicFiber (I := I) g hEnorm p p r₀ → Path p q :=
    fun u => (loop u).trans c
  have hloopFlat (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      Path.IsContMDiffWithSittingInstants (I := I) 1 (loop u) :=
    radialLoop_flat (I := I) g hEnorm p u.1 u.2.2
  have hpathFlat (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      Path.IsContMDiffWithSittingInstants (I := I) 1 (path u) :=
    (hloopFlat u).trans hcFlat
  have huNorm (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      ‖u.1‖ < r₀ := by
    simpa only [intrinsicFiber, Metric.mem_ball, dist_zero_right] using u.2.1
  have hpathSmall (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      Path.riemannianELength (I := I) (path u) < ENNReal.ofReal (r₀ + s) := by
    dsimp only [path]
    rw [Path.riemannianELength_trans
      ((hloopFlat u).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)
      (hcFlat.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero),
      radialLoop_len (I := I) g hEnorm p u.1 u.2.2]
    calc
      ENNReal.ofReal ‖u.1‖ + Path.riemannianELength (I := I) c
          < ENNReal.ofReal r₀ + ENNReal.ofReal s :=
        ENNReal.add_lt_add
          ((ENNReal.ofReal_lt_ofReal_iff hr₀).2 (huNorm u)) hcLen
      _ = ENNReal.ofReal (r₀ + s) :=
        (ENNReal.ofReal_add hr₀.le hs.le).symm
  have hpathR (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      Path.riemannianELength (I := I) (path u) < ENNReal.ofReal R :=
    (hpathSmall u).trans
      ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  have hex (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      Nonempty
        (IntrinsicFrameLift (I := I) g hEnorm p (path u).extend 0 1) :=
    exists_intr_lift (I := I) g hEnorm p zero_le_one
      (hpathFlat u).contMDiff.contMDiffOn (by simp)
      (hpathR u) hloc
  let lift (u : intrinsicFiber (I := I) g hEnorm p p r₀) :
      IntrinsicFrameLift (I := I) g hEnorm p (path u).extend 0 1 :=
    Classical.choice (hex u)
  let f :
      intrinsicFiber (I := I) g hEnorm p p r₀ →
        intrinsicFiber (I := I) g hEnorm p q (r₀ + s) :=
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
      IntrinsicFrameLift (I := I) g hEnorm p (loop u).extend 0 1 :=
    radialLoopLift (I := I) g hEnorm p u.1 u.2.2
  let B :
      IntrinsicFrameLift (I := I) g hEnorm p (loop v).extend 0 1 :=
    radialLoopLift (I := I) g hEnorm p v.1 v.2.2
  have huR :
      Path.riemannianELength (I := I) (loop u) < ENNReal.ofReal R := by
    rw [radialLoop_len (I := I) g hEnorm p u.1 u.2.2]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2
      ((huNorm u).trans ((lt_add_of_pos_right r₀ hs).trans hfit))
  have hvR :
      Path.riemannianELength (I := I) (loop v) < ENNReal.ofReal R := by
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
    (intrinsicFiber (I := I) g hEnorm p p r₀).encard ≤
      (intrinsicFiber (I := I) g hEnorm p q (r₀ + s)).encard := by
  obtain ⟨f, hf⟩ :=
    exists_fiber_inj (I := I) g hEnorm hr₀ hs hqs hfit hloc
  exact (Function.Embedding.mk f hf).encard_le

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
