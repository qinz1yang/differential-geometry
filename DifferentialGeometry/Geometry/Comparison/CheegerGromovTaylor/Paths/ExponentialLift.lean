import DifferentialGeometry.Geometry.Exponential.Intrinsic.GaussLemma
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Lift

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

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

structure IntrinsicFrameLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (γ : Real → M) (a b : Real) where
  toFun : Real → E
  contDiff : ContDiffOn Real 1 toFun (Set.Icc a b)
  start : toFun a = 0
  lifts :
    Set.EqOn
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘ toFun)
      γ (Set.Icc a b)

namespace IntrinsicFrameLift

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
  {p : M} {γ : Real → M} {a b R : Real}

theorem norm_le_length
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hfin : Manifold.pathELength I γ a b ≠ ⊤)
    {t : Real} (ht : t ∈ Set.Icc a b) :
    ‖L.toFun t‖ ≤ (Manifold.pathELength I γ a b).toReal := by
  have hsub : Set.Icc a t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc le_rfl ht.2
  have hrad :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t :=
    intrinsicLift_norm_le (J := I) g hEnorm p ht.1 L.start
      (L.contDiff.mono hsub)
  have hlift :
      Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t =
        Manifold.pathELength I γ a t := by
    apply Manifold.pathELength_congr
    intro s hs
    exact L.lifts ⟨hs.1, hs.2.trans ht.2⟩
  have hmono :
      Manifold.pathELength I γ a t ≤
        Manifold.pathELength I γ a b :=
    Manifold.pathELength_mono le_rfl ht.2
  have hchain :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I γ a b := by
    calc
      ENNReal.ofReal ‖L.toFun t‖
          ≤ Manifold.pathELength I
              ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t := hrad
      _ = Manifold.pathELength I γ a t := hlift
      _ ≤ Manifold.pathELength I γ a b := hmono
  have hreal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hchain
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hreal

theorem norm_lt
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    {t : Real} (ht : t ∈ Set.Icc a b) :
    ‖L.toFun t‖ < R := by
  have hsub : Set.Icc a t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc le_rfl ht.2
  have hrad :
      ENNReal.ofReal ‖L.toFun t‖ ≤
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t :=
    intrinsicLift_norm_le (J := I) g hEnorm p ht.1 L.start
      (L.contDiff.mono hsub)
  have hlift :
      Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t =
        Manifold.pathELength I γ a t := by
    apply Manifold.pathELength_congr
    intro s hs
    exact L.lifts ⟨hs.1, hs.2.trans ht.2⟩
  have hmono :
      Manifold.pathELength I γ a t ≤
        Manifold.pathELength I γ a b :=
    Manifold.pathELength_mono le_rfl ht.2
  have hlt :
      ENNReal.ofReal ‖L.toFun t‖ < ENNReal.ofReal R := by
    calc
      ENNReal.ofReal ‖L.toFun t‖
          ≤ Manifold.pathELength I
              ((intrinsicFramedExp (I := I) g hEnorm p) ∘ L.toFun) a t := hrad
      _ = Manifold.pathELength I γ a t := hlift
      _ ≤ Manifold.pathELength I γ a b := hmono
      _ < ENNReal.ofReal R := hlen
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mp hlt

theorem maps_ball
    (L : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R) :
    Set.MapsTo L.toFun (Set.Icc a b) (Metric.ball (0 : E) R) := by
  intro t ht
  simpa only [Metric.mem_ball, dist_zero_right] using L.norm_lt hR hlen ht

theorem eqOn
    (L L' : IntrinsicFrameLift (I := I) g hEnorm p γ a b)
    (hab : a ≤ b) (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    Set.EqOn L.toFun L'.toFun (Set.Icc a b) := by
  let hL :
      isLiftOn
        (intrinsicFramedExp (I := I) g hEnorm p)
        γ (Metric.ball (0 : E) R) 0 a b L.toFun :=
    ⟨L.contDiff.continuousOn, L.start,
      fun t ht ↦ ⟨L.maps_ball hR hlen ht, L.lifts ht⟩⟩
  let hL' :
      isLiftOn
        (intrinsicFramedExp (I := I) g hEnorm p)
        γ (Metric.ball (0 : E) R) 0 a b L'.toFun :=
    ⟨L'.contDiff.continuousOn, L'.start,
      fun t ht ↦ ⟨L'.maps_ball hR hlen ht, L'.lifts ht⟩⟩
  exact hL.eqOn hab Metric.isOpen_ball hloc hL'

end IntrinsicFrameLift

theorem exists_intr_lift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {γ : Real → M} {a b R : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hγa : γ a = p)
    (hR : 0 < R)
    (hlen :
      Manifold.pathELength I γ a b < ENNReal.ofReal R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    Nonempty (IntrinsicFrameLift (I := I) g hEnorm p γ a b) := by
  let ell : Real := (Manifold.pathELength I γ a b).toReal
  have hfin : Manifold.pathELength I γ a b ≠ ⊤ := hlen.ne_top
  have hellR : ell < R := by
    exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hlen
  have hK : IsCompact (Metric.closedBall (0 : E) ell) :=
    isCompact_closedBall _ _
  have hKU :
      Metric.closedBall (0 : E) ell ⊆ Metric.ball (0 : E) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hellR
  have hzero : (0 : E) ∈ Metric.ball (0 : E) R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  have hstart :
      intrinsicFramedExp (I := I) g hEnorm p 0 = γ a := by
    rw [intrinsicFrame_zero, hγa]
  have hfence :
      ∀ {t : Real}, t ∈ Set.Icc a b →
        ∀ {η : Real → E},
          isLiftOn
            (intrinsicFramedExp (I := I) g hEnorm p)
            γ (Metric.ball (0 : E) R) 0 a t η →
          η t ∈ Metric.closedBall (0 : E) ell := by
    intro t ht η hη
    have hsub : Set.Icc a t ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc le_rfl ht.2
    have hηcd : ContDiffOn Real 1 η (Set.Icc a t) :=
      hη.contDiffOn hloc (hγ.mono hsub)
    have hrad :
        ENNReal.ofReal ‖η t‖ ≤
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) a t :=
      intrinsicLift_norm_le (J := I) g hEnorm p ht.1 hη.2.1 hηcd
    have hlift :
        Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) a t =
          Manifold.pathELength I γ a t := by
      apply Manifold.pathELength_congr
      intro s hs
      exact (hη.2.2 s hs).2
    have hmono :
        Manifold.pathELength I γ a t ≤
          Manifold.pathELength I γ a b :=
      Manifold.pathELength_mono le_rfl ht.2
    have hchain :
        ENNReal.ofReal ‖η t‖ ≤
          Manifold.pathELength I γ a b := by
      calc
        ENNReal.ofReal ‖η t‖
            ≤ Manifold.pathELength I
                ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) a t := hrad
        _ = Manifold.pathELength I γ a t := hlift
        _ ≤ Manifold.pathELength I γ a b := hmono
    have hreal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hchain
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa only [ell, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal
  obtain ⟨η, hη⟩ :=
    isLiftOn.exists_of_compact hab (Metric.isOpen_ball)
      hloc hγ.continuousOn hzero hstart hK hKU hfence
  refine ⟨{
    toFun := η
    contDiff := hη.contDiffOn hloc hγ
    start := hη.2.1
    lifts := fun t ht ↦ (hη.2.2 t ht).2 }⟩

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
