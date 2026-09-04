import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.ExponentialLift
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.Flat
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set TopologicalSpace
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

namespace ShortHomotopy

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
  {L : ENNReal} {R : Real} {x y : M} {p q : Path x y}

theorem exists_lift_family
    (F : ShortHomotopy (I := I) L p q)
    (hLR : L < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R)) :
    ∃ lift :
        (t : unitInterval) →
          IntrFrameLift (I := I) g hEnorm x
            (F.hom.eval t).extend 0 1,
      ∀ t : unitInterval,
        (lift t).toFun 1 = (lift 0).toFun 1 := by
  classical
  have hRenn : 0 < ENNReal.ofReal R :=
    lt_of_le_of_lt bot_le hLR
  have hR : 0 < R := ENNReal.ofReal_pos.mp hRenn
  have hlen (t : unitInterval) :
      Manifold.pathELength I (F.hom.eval t).extend 0 1 <
        ENNReal.ofReal R := by
    calc
      Manifold.pathELength I (F.hom.eval t).extend 0 1
          = pathLen (I := I) (F.hom.eval t) := rfl
      _ ≤ L := F.length_le t
      _ < ENNReal.ofReal R := hLR
  have hstart (t : unitInterval) :
      (F.hom.eval t).extend 0 = x := by
    simp
  have hcd (t : unitInterval) :
      ContMDiffOn 𝓘(Real, Real) I 1
        (F.hom.eval t).extend (Set.Icc 0 1) :=
    (F.flat t).c1.contMDiffOn
  have hex (t : unitInterval) :
      Nonempty
        (IntrFrameLift (I := I) g hEnorm x
          (F.hom.eval t).extend 0 1) :=
    exists_intr_lift (I := I) g hEnorm x zero_le_one
      (hcd t) (hstart t) hR (hlen t) hloc
  let lift :
      (t : unitInterval) →
        IntrFrameLift (I := I) g hEnorm x
          (F.hom.eval t).extend 0 1 :=
    fun t => Classical.choice (hex t)
  let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  let expU : U → M :=
    fun z => intrinsicFramedExp (I := I) g hEnorm x z
  have hlocU :
      IsLocalDiffeomorph 𝓘(Real, E) I ∞ expU :=
    isLocalDiffeomorph_restrict_open U hloc
  let expUC : C(U, M) :=
    ⟨expU, continuous_iff_continuousAt.mpr fun z =>
      (hlocU z).contMDiffAt.continuousAt⟩
  let liftPath (t : unitInterval) : C(unitInterval, U) :=
    { toFun := fun s =>
        ⟨(lift t).toFun s,
          (lift t).maps_ball hR (hlen t) s.property⟩
      continuous_toFun := by
        have hcont :
            Continuous (fun s : unitInterval => (lift t).toFun s) := by
          exact continuousOn_iff_continuous_domRestrict.mp
            (lift t).contDiff.continuousOn
        exact hcont.subtype_mk _ }
  have hlifts (t s : unitInterval) :
      expUC (liftPath t s) = F.hom (t, s) := by
    change
      intrinsicFramedExp (I := I) g hEnorm x ((lift t).toFun s) =
        F.hom (t, s)
    have hh := (lift t).lifts s.property
    change
      intrinsicFramedExp (I := I) g hEnorm x ((lift t).toFun s) =
        (F.hom.eval t).extend s at hh
    calc
      _ = (F.hom.eval t).extend s := hh
      _ = (F.hom.eval t) s := Path.extend_extends' _ _
      _ = F.hom (t, s) := rfl
  have hzero (t : unitInterval) :
      liftPath t 0 = liftPath 0 0 := by
    apply Subtype.ext
    change (lift t).toFun 0 = (lift 0).toFun 0
    rw [(lift t).start, (lift 0).start]
  have hsep : IsSeparatedMap expUC :=
    T2Space.isSeparatedMap expUC
  have hend (t : unitInterval) :
      liftPath t 1 = liftPath 0 1 :=
    hlocU.isLocalHomeomorph.monodromy_theorem
      hsep F.hom liftPath hlifts hzero t
  refine ⟨lift, fun t => ?_⟩
  exact congrArg Subtype.val (hend t)

theorem lift_end_eq
    (F : ShortHomotopy (I := I) L p q)
    (hLR : L < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R))
    (P :
      IntrFrameLift (I := I) g hEnorm x
        (F.hom.eval 0).extend 0 1)
    (Q :
      IntrFrameLift (I := I) g hEnorm x
        (F.hom.eval 1).extend 0 1) :
    P.toFun 1 = Q.toFun 1 := by
  obtain ⟨lift, hend⟩ := F.exists_lift_family hLR hloc
  have hR : 0 < R := by
    apply ENNReal.ofReal_pos.mp
    exact lt_of_le_of_lt bot_le hLR
  have hlen (t : unitInterval) :
      Manifold.pathELength I (F.hom.eval t).extend 0 1 <
        ENNReal.ofReal R := by
    calc
      Manifold.pathELength I (F.hom.eval t).extend 0 1
          = pathLen (I := I) (F.hom.eval t) := rfl
      _ ≤ L := F.length_le t
      _ < ENNReal.ofReal R := hLR
  have hP :
      Set.EqOn P.toFun (lift 0).toFun (Set.Icc 0 1) :=
    P.eqOn (lift 0) zero_le_one hR (hlen 0) hloc
  have hQ :
      Set.EqOn Q.toFun (lift 1).toFun (Set.Icc 0 1) :=
    Q.eqOn (lift 1) zero_le_one hR (hlen 1) hloc
  calc
    P.toFun 1 = (lift 0).toFun 1 := hP ⟨zero_le_one, le_rfl⟩
    _ = (lift 1).toFun 1 := (hend 1).symm
    _ = Q.toFun 1 := (hQ ⟨zero_le_one, le_rfl⟩).symm

end ShortHomotopy

namespace IntrFrameLift

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
  {R : Real} {x y z : M}
  {p q : Path x y} {c : Path y z}

theorem append_mid_eq
    (A :
      IntrFrameLift (I := I) g hEnorm x p.extend 0 1)
    (P :
      IntrFrameLift (I := I) g hEnorm x (p.trans c).extend 0 1)
    (hR : 0 < R)
    (hp : pathLen (I := I) p < ENNReal.ofReal R)
    (hpc : pathLen (I := I) (p.trans c) < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R)) :
    P.toFun (1 / 2) = A.toFun 1 := by
  let F : E → M :=
    intrinsicFramedExp (I := I) g hEnorm x
  let γ : Real → M := fun t => p.extend (2 * t)
  have hscale :
      Set.MapsTo (fun t : Real => 2 * t)
        (Set.Icc 0 (1 / 2)) (Set.Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hA :
      isLiftOn F γ (Metric.ball (0 : E) R) 0 0 (1 / 2)
        (fun t => A.toFun (2 * t)) := by
    refine ⟨A.contDiff.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hscale, ?_, ?_⟩
    · simpa only [mul_zero] using A.start
    · intro t ht
      have ht' : 2 * t ∈ Set.Icc (0 : Real) 1 := hscale ht
      exact ⟨A.maps_ball hR hp ht', A.lifts ht'⟩
  have hP :
      isLiftOn F γ (Metric.ball (0 : E) R) 0 0 (1 / 2) P.toFun := by
    refine ⟨P.contDiff.continuousOn.mono ?_, P.start, ?_⟩
    · intro t ht
      exact ⟨ht.1, ht.2.trans (by norm_num)⟩
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 :=
        ⟨ht.1, ht.2.trans (by norm_num)⟩
      refine ⟨P.maps_ball hR hpc ht', ?_⟩
      change
        intrinsicFramedExp (I := I) g hEnorm x (P.toFun t) =
          p.extend (2 * t)
      rw [← Path.extend_trans_of_le_half p c ht.2]
      exact P.lifts ht'
  have heq :
      Set.EqOn P.toFun (fun t => A.toFun (2 * t))
        (Set.Icc 0 (1 / 2)) :=
    hP.eqOn (by norm_num) Metric.isOpen_ball hloc hA
  convert heq ⟨by norm_num, le_rfl⟩ using 1
  norm_num

theorem cancel_right
    (P :
      IntrFrameLift (I := I) g hEnorm x (p.trans c).extend 0 1)
    (Q :
      IntrFrameLift (I := I) g hEnorm x (q.trans c).extend 0 1)
    (hR : 0 < R)
    (hpc : pathLen (I := I) (p.trans c) < ENNReal.ofReal R)
    (hqc : pathLen (I := I) (q.trans c) < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R))
    (hend : P.toFun 1 = Q.toFun 1) :
    P.toFun (1 / 2) = Q.toFun (1 / 2) := by
  let F : E → M :=
    intrinsicFramedExp (I := I) g hEnorm x
  let γ : Real → M := fun t => c.extend (2 * t - 1)
  have hsub :
      Set.Icc (1 / 2 : Real) 1 ⊆ Set.Icc (0 : Real) 1 := by
    intro t ht
    exact ⟨(by linarith [ht.1]), ht.2⟩
  have hP :
      isLiftOn F γ (Metric.ball (0 : E) R)
        (P.toFun (1 / 2)) (1 / 2) 1 P.toFun := by
    refine ⟨P.contDiff.continuousOn.mono hsub, rfl, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : Real) 1 := hsub ht
    refine ⟨P.maps_ball hR hpc ht', ?_⟩
    change
      intrinsicFramedExp (I := I) g hEnorm x (P.toFun t) =
        c.extend (2 * t - 1)
    rw [← Path.extend_trans_of_half_le p c ht.1]
    exact P.lifts ht'
  have hQ :
      isLiftOn F γ (Metric.ball (0 : E) R)
        (Q.toFun (1 / 2)) (1 / 2) 1 Q.toFun := by
    refine ⟨Q.contDiff.continuousOn.mono hsub, rfl, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : Real) 1 := hsub ht
    refine ⟨Q.maps_ball hR hqc ht', ?_⟩
    change
      intrinsicFramedExp (I := I) g hEnorm x (Q.toFun t) =
        c.extend (2 * t - 1)
    rw [← Path.extend_trans_of_half_le q c ht.1]
    exact Q.lifts ht'
  exact
    hP.eqOn_of_eq Metric.isOpen_ball hloc hQ
      ⟨by norm_num, le_rfl⟩ hend ⟨le_rfl, by norm_num⟩

theorem end_eq_of_append
    (A :
      IntrFrameLift (I := I) g hEnorm x p.extend 0 1)
    (B :
      IntrFrameLift (I := I) g hEnorm x q.extend 0 1)
    (P :
      IntrFrameLift (I := I) g hEnorm x (p.trans c).extend 0 1)
    (Q :
      IntrFrameLift (I := I) g hEnorm x (q.trans c).extend 0 1)
    (hR : 0 < R)
    (hp : pathLen (I := I) p < ENNReal.ofReal R)
    (hq : pathLen (I := I) q < ENNReal.ofReal R)
    (hpc : pathLen (I := I) (p.trans c) < ENNReal.ofReal R)
    (hqc : pathLen (I := I) (q.trans c) < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R))
    (hend : P.toFun 1 = Q.toFun 1) :
    A.toFun 1 = B.toFun 1 := by
  calc
    A.toFun 1 = P.toFun (1 / 2) :=
      (append_mid_eq A P hR hp hpc hloc).symm
    _ = Q.toFun (1 / 2) :=
      P.cancel_right Q hR hpc hqc hloc hend
    _ = B.toFun 1 :=
      append_mid_eq B Q hR hq hqc hloc

end IntrFrameLift

namespace ShortHomotopy

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
  {L : ENNReal} {R : Real} {x y : M} {p q : Path x y}

theorem lift_end_cancel
    {z : M} {c : Path y z}
    (F : ShortHomotopy (I := I) L (p.trans c) (q.trans c))
    (hLR : L < ENNReal.ofReal R)
    (hpR : pathLen (I := I) p < ENNReal.ofReal R)
    (hqR : pathLen (I := I) q < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm x)
        (Metric.ball (0 : E) R))
    (P : IntrFrameLift (I := I) g hEnorm x p.extend 0 1)
    (Q : IntrFrameLift (I := I) g hEnorm x q.extend 0 1) :
    P.toFun 1 = Q.toFun 1 := by
  obtain ⟨lift, hend⟩ := F.exists_lift_family hLR hloc
  let T :
      IntrFrameLift (I := I) g hEnorm x
        (p.trans c).extend 0 1 := {
    toFun := (lift (0 : unitInterval)).toFun
    contDiff := (lift (0 : unitInterval)).contDiff
    start := (lift (0 : unitInterval)).start
    lifts := by
      simpa using (lift (0 : unitInterval)).lifts }
  let U :
      IntrFrameLift (I := I) g hEnorm x
        (q.trans c).extend 0 1 := {
    toFun := (lift (1 : unitInterval)).toFun
    contDiff := (lift (1 : unitInterval)).contDiff
    start := (lift (1 : unitInterval)).start
    lifts := by
      simpa using (lift (1 : unitInterval)).lifts }
  have hR : 0 < R := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hLR)
  have hpc :
      pathLen (I := I) (p.trans c) < ENNReal.ofReal R := by
    have hle :
        pathLen (I := I) (p.trans c) ≤ L := by
      simpa using F.length_le (0 : unitInterval)
    exact hle.trans_lt hLR
  have hqc :
      pathLen (I := I) (q.trans c) < ENNReal.ofReal R := by
    have hle :
        pathLen (I := I) (q.trans c) ≤ L := by
      simpa using F.length_le (1 : unitInterval)
    exact hle.trans_lt hLR
  have hTU : T.toFun 1 = U.toFun 1 := by
    exact (hend (1 : unitInterval)).symm
  exact
    IntrFrameLift.end_eq_of_append P Q T U hR hpR hqR hpc hqc
      hloc hTU

end ShortHomotopy

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
