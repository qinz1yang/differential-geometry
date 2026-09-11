import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.Selection.Scale
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

private noncomputable local instance supportSelectionModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance supportSelectionModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance supportSelectionModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance supportSelectionModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem binfMemClosed {U V' : Set E} {B : Nat -> E -> E} {Binf : E -> E}
    (hB : MapCInfConvergenceOnCompacts U B Binf) {v : E} (hv : v ∈ U)
    (hV'closed : IsClosed V') (hmem : ∀ᶠ a in Filter.atTop, B a v ∈ V') :
    Binf v ∈ V' :=
  hV'closed.mem_of_tendsto (tendsto_of_cInf hB hv) hmem

theorem HasAtomWeightLim.binf_of_live
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (gamma : LiveSlot L inp.pack r)
    (Binf : E -> E)
    (hB : MapCInfConvergenceOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)))
      Binf)
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma.1 ≠ 0) :
    Binf z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
  have hweightTail := hphi.tendsto_atTop.eventually
    (hlim.weight_ne_tail hz hweight)
  have hrad : ExponentialBallRadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (exponentialBallRadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radius_scale_tail inp.divisor_pos
      (exponential_ball_radius_factor_pos inp.decay inp.D) hradRatio
      P inp.realizes L inp.pack r
  have hradTail := hphi.tendsto_atTop.eventually hrad
  have hgpTail := hphi.tendsto_atTop.eventually hgp
  have hcenterTail := hphi.tendsto_atTop.eventually
    (seqCenterD_live inp.decay P L (gamma.1 : Nat) gamma.2)
  have hmem : ∀ᶠ k in Filter.atTop,
      normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
    filter_upwards [hweightTail, hradTail, hgpTail, hcenterTail]
      with k hweightK hradK hgpK hcenterK
    let : TopologicalSpace (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).topology
    let : ChartedSpace H (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).charted
    let : IsManifold I ∞ (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).smooth
    let : T2Space (TangentBundle I (X.obj (L.φ (phi k))).M) :=
      (X.obj (L.φ (phi k))).t2TangentBundle
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.divisor_pos 0).le]))
    have hfactor : (8 : Real) ≤ exponentialBallRadiusFactor inp.decay inp.D := by
      rw [exponentialBallRadiusFactor]
      nlinarith
    have hC2 : 8 * L.lamInf (gamma.1 : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ (phi k))).metric
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) :=
      (mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma.1 : Nat))).le).trans
          (hradK gamma.1
            (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) hcenterK).2
    exact Metric.ball_subset_closedBall
      (inp.weight_trans_small P L r (phi k) hgpK
        (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
        (baseIndex inp.decay inp.realizes inp.pack hr) gamma.1 hC2 z hweightK)
  exact binfMemClosed hB hz Metric.isClosed_closedBall hmem

theorem HasAtomWeightLim.binf_of_slot
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (target : InterSlot L inp.pack r alpha)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : MapCInfConvergenceOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Binf target))
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z target.1.1 ≠ 0) :
    Binf target z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
  exact hlim.binf_of_live inp hradRatio P L r hr hgp alpha U aInf
    phi hphi target.1 (Binf target) hB hz hweight

theorem HasAtomWeightLim.binf_of_weight
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : forall target : InterSlot L inp.pack r alpha,
      MapCInfConvergenceOnCompacts U
        (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
        (Binf target))
    {z : E} (hz : z ∈ U) (gamma : Fin (inp.pack.A r))
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0) :
    ∃ target : InterSlot L inp.pack r alpha,
      target.1.1 = gamma ∧
        Binf target z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  have hdata := hlim
  dsimp only [HasAtomWeightLim] at hdata
  have hgammaLive : L.alive (gamma : Nat) = true := by
    cases hgamma : L.alive (gamma : Nat) with
    | false =>
        have haZero : aInf gamma = 0 := hdata.1 gamma hgamma
        have hnum : aInf gamma z ≠ 0 :=
          num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
        exact False.elim (hnum (by rw [haZero]; rfl))
    | true => rfl
  have hinter : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf
        (alpha.1 : Nat) (gamma : Nat) (L.φ k) :=
    hlim.binter_of_weight alpha.1 gamma hz hsource hweight
  let target : InterSlot L inp.pack r alpha :=
    ⟨⟨gamma, hgammaLive⟩, hinter⟩
  refine ⟨target, rfl, ?_⟩
  simpa only [target] using
    (hlim.binf_of_slot inp hradRatio P L r hr hgp alpha U aInf
      phi hphi target Binf (hB target) hz (by simpa only [target] using hweight))

theorem MetricCompactnessAssumptions.exists_support_trans
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (hUsub : U ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧
      ∃ Jinf : InterSlot L inp.pack r alpha -> E -> E,
      ∃ Jbarinf : InterSlot L inp.pack r alpha -> E -> E,
        (forall target : InterSlot L inp.pack r alpha,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvergenceOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf target) ∧
          MapCInfConvergenceOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf target) ∧
          (forall z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
            Jinf target z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
              Jbarinf target (Jinf target z) = z) ∧
          (forall w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
            Jbarinf target w ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
              Jinf target (Jbarinf target w) = w)) ∧
        forall z : E, z ∈ U -> forall gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
              (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0 ->
            ∃ target : InterSlot L inp.pack r alpha,
              target.1.1 = gamma ∧
                Jinf target z ∈
                  Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    inp.exists_pair_trans hradRatio P L r
      (fun _ : InterSlot L inp.pack r alpha => alpha)
      (fun target : InterSlot L inp.pack r alpha => target.1)
      (fun target : InterSlot L inp.pack r alpha => target.2)
  refine ⟨phi, hphi, Jinf, Jbarinf, hspec, ?_⟩
  intro z hz gamma hweight
  exact hlim.binf_of_weight inp hradRatio P L r hr hgp alpha U aInf
    hsource phi hphi Jinf (fun target K hK hKU p =>
      (hspec target).2.2.2.2.1 K hK (hKU.trans hUsub) p)
    hz gamma hweight

theorem MetricCompactnessAssumptions.exists_support_fin
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (U : LiveSlot L inp.pack r → Set E)
    (hUsub : ∀ alpha, U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (hlim : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P L inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat))
        (U alpha) (aInf alpha))
    (hsource : ∀ alpha, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        (U alpha) (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
      ∃ Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
        (∀ alpha target,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvergenceOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf alpha target) ∧
          MapCInfConvergenceOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf alpha target) ∧
          (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target z ∈
                Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
              Jbarinf alpha target (Jinf alpha target z) = z) ∧
          (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target w ∈
                Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
              Jinf alpha target (Jbarinf alpha target w) = w)) ∧
        ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma ≠ 0 →
          ∃ target : InterSlot L inp.pack r alpha,
            target.1.1 = gamma ∧
              Jinf alpha target z ∈
                Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r, InterSlot L inp.pack r alpha
  let (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  let : Finite PairSlot := inferInstance
  obtain ⟨phi, hphi, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradRatio P L r
      (fun pair : PairSlot => pair.1)
      (fun pair : PairSlot => pair.2.1)
      (fun pair : PairSlot => pair.2.2)
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  refine ⟨phi, hphi, Jinf, Jbarinf, ?_, ?_⟩
  · intro alpha target
    exact hspec ⟨alpha, target⟩
  · intro alpha z hz gamma hweight
    exact (hlim alpha).binf_of_weight inp hradRatio P L r hr hgp
      alpha (U alpha) (aInf alpha) (hsource alpha) phi hphi (Jinf alpha)
      (fun target K hK hKU p =>
        (hspec ⟨alpha, target⟩).2.2.2.2.1 K hK
          (hKU.trans (hUsub alpha)) p)
      hz gamma hweight

noncomputable def interSlot?
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) (gamma : Fin (pb.A r)) :
    Option (InterSlot L pb r alpha) := by
  classical
  exact
    if h : ∃ target : InterSlot L pb r alpha, target.1.1 = gamma then
      some (Classical.choose h)
    else
      none

noncomputable def totalPoints
    {M : Type u}
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (pairPoints : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) : M :=
  match interSlot? alpha gamma with
  | some target => pairPoints alpha target a b x
  | none => x

omit [CompleteSpace E] in
@[simp] theorem activeFill_totalPoints_zero
    {M : Type u}
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPoints : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) (hzero : mu x gamma = 0) :
    centerAverage.activeFill mu (totalPoints pairPoints alpha a b)
        (fun y => y) x gamma = x := by
  simp [centerAverage.activeFill, hzero]

omit [CompleteSpace E] in
theorem activeFill_totalPoints_of_ne
    {M : Type u}
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPoints : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r))
    (hslot : mu x gamma ≠ 0 →
      ∃ target : InterSlot L pb r alpha, target.1.1 = gamma)
    (hne : mu x gamma ≠ 0) :
    ∃ target : InterSlot L pb r alpha,
      target.1.1 = gamma ∧
        centerAverage.activeFill mu (totalPoints pairPoints alpha a b)
            (fun y => y) x gamma = pairPoints alpha target a b x := by
  classical
  obtain ⟨target, htarget⟩ := hslot hne
  have hexists :
      ∃ target' : InterSlot L pb r alpha, target'.1.1 = gamma :=
    ⟨target, htarget⟩
  have hlookup : interSlot? alpha gamma = some target := by
    unfold interSlot?
    split
    next h =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec h).trans htarget.symm
    next h =>
      exact (h hexists).elim
  refine ⟨target, htarget, ?_⟩
  simp [centerAverage.activeFill, hne, totalPoints, hlookup]

theorem MetricCompactnessAssumptions.exists_atom_support_fin
    (inp : MetricCompactnessAssumptions (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.metricCoerciveRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      (∀ alpha, IsOpen (U alpha)) ∧
      (∀ alpha, U alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      (∀ alpha, IsCompact (C0 alpha)) ∧
      (∀ alpha, IsCompact (C1 alpha)) ∧
      (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
      (∀ alpha, C1 alpha ⊆ U alpha) ∧
      (∀ alpha, Convex Real (C0 alpha)) ∧
      (∀ alpha, (0 : E) ∈ C0 alpha) ∧
      (∃ eta : LiveSlot L inp.pack r → Real,
        (∀ alpha, 0 < eta alpha) ∧
        ∀ k,
          let Y := X.obj (Lphi.φ k)
          letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space Y.M := Y.t2
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
          ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
            ∃ (alpha : LiveSlot L inp.pack r) (z : E),
              expMapDiffeo (I := I) Y.metric
                  (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z = y ∧
                Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
                interior (C0 alpha)) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (Lphi.φ k)
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
            (U alpha)
            (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) '' U alpha) ∧
      (∀ alpha,
        HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P Lphi inp.realizes
          inp.pack r hr
          (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (U alpha) (aInf alpha)) ∧
      (∀ alpha target,
        ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        ContinuousOn (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContinuousOn (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        MapCInfConvergenceOnCompacts
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) ∧
        MapCInfConvergenceOnCompacts
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
          (Jbarinf alpha target) ∧
        (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
          Jinf alpha target z ∈
              Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target (Jinf alpha target z) = z) ∧
        (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
          Jbarinf alpha target w ∈
              Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target (Jbarinf alpha target w) = w)) ∧
      (∀ (alpha : LiveSlot L inp.pack r)
          (target : InterSlot L inp.pack r alpha) (k : Nat),
        ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))) ∧
      ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma ≠ 0 →
        ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma ∧
            Jinf alpha target z ∈
              Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r,
    InterSlot L inp.pack r alpha
  let (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  let : Finite PairSlot := inferInstance
  obtain ⟨psi, hpsi, gInf, U, C0, C1, hginf, hg, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hC0convex, hC0zero, eta, heta, hcore⟩ :=
    inp.exists_live_cores h8 hradRatio P L r
  have hcover : ∀ᶠ k in Filter.atTop,
      let Y := X.obj (L.φ (psi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
      (∀ alpha : LiveSlot L inp.pack r,
        U alpha ⊆ Metric.ball 0
            (inp.normalBounds.radius (L.φ (psi k))
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        U alpha ⊆ Metric.ball 0
            (expMapC2Radius (I := I) Y.metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
          (U alpha)
          (L.hatBall inp.decay inp.D P inp.pack r (psi k) alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              L.innerBall inp.decay inp.D P inp.pack r (psi k) gamma)) ∧
      L.hatSourceBall inp.decay P r (psi k) ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z) '' U alpha := by
    filter_upwards [hcore] with k hk
    refine ⟨hk.1, ?_⟩
    intro y hy
    obtain ⟨alpha, v, hv, rfl⟩ := mem_iUnion.mp (hk.2.1 hy)
    refine mem_iUnion.mpr ⟨alpha, v, ?_, rfl⟩
    exact hC1U alpha (interior_subset (hC01 alpha (interior_subset hv)))
  let L0 := L.subseq hpsi
  let live0 : LiveSlot L inp.pack r → LiveSlot L0 inp.pack r := fun alpha =>
    ⟨alpha.1, by simpa only [L0, NetLimitData.subseq] using alpha.2⟩
  have hinter0 (pair : PairSlot) : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L0.lamInf
        ((live0 pair.1).1 : Nat) ((live0 pair.2.1).1 : Nat) (L0.φ k) := by
    simpa only [L0, live0, NetLimitData.subseq_phi, NetLimitData.subseq_lamInf,
      Function.comp_apply] using
        hpsi.tendsto_atTop.eventually pair.2.2
  obtain ⟨tau, htau, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradRatio P L0 r
      (fun pair : PairSlot => live0 pair.1)
      (fun pair : PairSlot => live0 pair.2.1)
      hinter0
  have hpair : ∀ᶠ k in Filter.atTop, ∀ pair : PairSlot,
      let x := seqCenterD inp.decay P L0 k ((live0 pair.1).1 : Nat)
      let y := seqCenterD inp.decay P L0 k ((live0 pair.2.1).1 : Nat)
      let Y := X.obj (L0.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L0.φ k)).ms
      ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) Y x y)
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
        NormalOverlapOn (I := I) Y x y
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) :=
    Filter.eventually_all.mpr fun pair =>
      (inp.pair_overlap_tail hradRatio P L0 r
        (live0 pair.1) (live0 pair.2.1) (hinter0 pair)).mono fun _ hk =>
          ⟨hk.2.2.2.2.1, hk.2.2.2.2.2.1⟩
  obtain ⟨hgp, _hrad⟩ := inp.exponential_scale_tails h8 hradRatio P L r
  have hgp0 : ExponentialRadiusScaleTail (I := I)
      inp.decay inp.D P L0 inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hpsi
  have hall : ∀ᶠ k in Filter.atTop,
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (L.φ (psi (tau k)))
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z)
            (U alpha)
            (L.hatBall inp.decay inp.D P inp.pack r (psi (tau k)) alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r (psi (tau k)) gamma)) ∧
        L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) '' U alpha) ∧
      ExponentialRadiusScaleAt (I := I) inp.decay inp.D P L0 inp.pack r (tau k) ∧
      (∀ pair : PairSlot,
        let x := seqCenterD inp.decay P L0 (tau k) ((live0 pair.1).1 : Nat)
        let y := seqCenterD inp.decay P L0 (tau k) ((live0 pair.2.1).1 : Nat)
        let Y := X.obj (L0.φ (tau k))
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (L0.φ (tau k))).ms
        ContDiffOn Real (⊤ : ℕ∞)
            (normalTransition (I := I) Y x y)
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
          NormalOverlapOn (I := I) Y x y
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat)))) ∧
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       (L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
         ⋃ alpha : LiveSlot L inp.pack r,
           (fun z => expMapDiffeo (I := I) Y.metric
             (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) ''
              interior (C0 alpha)) ∧
       ∀ y ∈ L.hatSourceBall inp.decay P r (psi (tau k)),
         ∃ (alpha : LiveSlot L inp.pack r) (z : E),
           expMapDiffeo (I := I) Y.metric
               (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z = y ∧
             Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) := by
    filter_upwards [htau.tendsto_atTop.eventually hcover,
      htau.tendsto_atTop.eventually hcore,
      htau.tendsto_atTop.eventually hgp0,
      htau.tendsto_atTop.eventually hpair]
      with k hcoverK hcoreK hgpK hpairK
    exact ⟨hcoverK, hgpK, hpairK, hcoreK.2⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  let shift : Nat → Nat := fun k => k + N
  have hshift : StrictMono shift := by
    intro k l hkl
    exact Nat.add_lt_add_right hkl N
  let phi : Nat → Nat := psi ∘ tau ∘ shift
  have hphi : StrictMono phi := hpsi.comp (htau.comp hshift)
  let Lphi := L.subseq hphi
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  let aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real := fun alpha gamma =>
    if htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma then
      let target := Classical.choose htarget
      fun z => gluingBump (L.lamInf (gamma : Nat))
        (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat)))
        (gInf z target.1 (Jinf alpha target z) (Jinf alpha target z))
    else fun _ => 0
  have hlimAll : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P Lphi inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (U alpha) (aInf alpha) := by
    intro alpha
    let beta : ∀ k : Nat, (X.obj (Lphi.φ k)).M := fun k =>
      seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    have hgpPhi (k : Nat) : ExponentialRadiusScaleAt (I := I)
        inp.decay inp.D P Lphi inp.pack r k := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [ExponentialRadiusScaleAt, Lphi, phi, L0, Function.comp_apply,
        NetLimitData.subseq_phi, NetLimitData.subseq_lamInf] using hk.2.1
    have hUexpPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        U alpha ⊆ Metric.ball 0
          (expMapC2Radius (I := I) (X.obj (Lphi.φ k)).metric (beta k)) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [beta, Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using (hk.1.1 alpha).2.1
    have hsourcePhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha) (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) := by
      let : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
      let : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
      let : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
      let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
        (X.obj (Lphi.φ k)).t2TangentBundle
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hout := ((hk.1.1 alpha).2.2 hz).1
      simp only [← c2_radius_normal_ball_chart_apply (I := I)] at hout ⊢
      convert hout using 1
      all_goals
        simp only [beta, Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
          seqCenterD_subseq, NetLimitData.hatBall_subseq]
      all_goals rfl
    have hcoverPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma) := by
      let : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
      let : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
      let : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
      let : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
        (X.obj (Lphi.φ k)).t2TangentBundle
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hmem := (hk.1.1 alpha).2.2 hz
      simp only [← c2_radius_normal_ball_chart_apply (I := I)] at hmem ⊢
      convert hmem.2 using 1
      all_goals
        simp only [beta, Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
          seqCenterD_subseq, NetLimitData.innerBall_subseq]
      all_goals rfl
    have hgPhi : MapCInfConvergenceOnCompacts Set.univ
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      simpa only [Lphi, phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using hg.comp_subseq (htau.comp hshift)
    have hgU : MapCInfConvergenceOnCompacts (U alpha)
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      intro K hK hKU p
      exact hgPhi K hK (hKU.trans (Set.subset_univ (U alpha))) p
    have hginfU : ContDiffOn Real (∞ : WithTop ℕ∞) gInf (U alpha) :=
      hginf.mono (Set.subset_univ (U alpha))
    have hJInf (target : InterSlot L inp.pack r alpha) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf alpha target) (U alpha) :=
      (hspec (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
    have hJConvergence (target : InterSlot L inp.pack r alpha) :
        MapCInfConvergenceOnCompacts (U alpha)
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, beta, Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hconv
    have hJStage (target : InterSlot L inp.pack r alpha) (k : Nat) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hsmooth := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
      simpa only [beta, Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hsmooth
    have hOverlap (target : InterSlot L inp.pack r alpha) (k : Nat) :
        NormalOverlapOn (I := I) (X.obj (Lphi.φ k))
          (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hover := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).2
      change NormalOverlapOn (I := I) (X.obj (L.φ (psi (tau (shift k)))))
        (seqCenterD inp.decay P L (psi (tau (shift k))) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (psi (tau (shift k))) (target.1.1 : Nat))
        (U alpha)
      intro z hz
      exact hover z (hU8 alpha hz)
    have hatom (gamma : Fin (inp.pack.A r)) :
        MapCInfConvergenceOnCompacts (U alpha)
          (fun k => seqAtomChart (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r
            beta gamma k) (aInf alpha gamma) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hslot : target.1.1 = gamma := Classical.choose_spec htarget
        have hgamma : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        have hraw := quadPiBump_convergence (hUopen alpha) hgU (hJConvergence target)
          (fun _ => contDiffOn_const) hginfU (hJStage target) (hJInf target)
          target.1 (gluingBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat))))
          (gluingBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat)))).contDiff
        have hstep : MapCInfConvergenceOnCompacts (U alpha)
            (fun k => gluingAtomChart (I := I) (X.obj (Lphi.φ k)) (beta k)
              (seqCenterD inp.decay P Lphi k (gamma : Nat))
              (L.lamInf (gamma : Nat))
              (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat))))
            (aInf alpha gamma) := by
          refine hraw.congr (hUopen alpha) (fun k z hz => ?_) (fun z _hz => ?_)
          · simpa only [gluingAtomChart, gluingAtomOn, c2_radius_normal_ball_chart_apply, hslot] using
              (gluingAtom_expMapDiffeo_apply (I := I) (X.obj (Lphi.φ k)) (beta k)
                (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
                (L.lamInf (gamma : Nat))
                (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat)))
                ((hOverlap target k) z hz).2)
          · simp only [aInf, dif_pos htarget, target]
        exact seqAtom_live_convergence (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r
          hgpPhi beta gamma (hUopen alpha) hgamma (by
            simpa only [Lphi, NetLimitData.subseq_lamInf] using hstep)
      · cases hgamma : L.alive (gamma : Nat) with
        | false =>
            have hgammaPhi : Lphi.alive (gamma : Nat) = false := by
              simpa only [Lphi, NetLimitData.subseq] using hgamma
            simpa only [aInf, dif_neg htarget] using
              (seqAtom_dead_convergence (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r
                beta gamma (hUopen alpha) hgammaPhi)
        | true =>
            rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
            · exact (htarget
                ⟨⟨⟨gamma, hgamma⟩, hinter⟩, rfl⟩).elim
            · have hdisjointPhi : ∀ᶠ k in Filter.atTop,
                  ¬ BInter inp.decay inp.D P Lphi.lamInf
                    (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
                simpa only [Lphi, NetLimitData.subseq_phi, Function.comp_apply,
                  NetLimitData.subseq_lamInf] using
                    hphi.tendsto_atTop.eventually hdisjoint
              have hsourceTail : ∀ᶠ k in Filter.atTop,
                  letI : TopologicalSpace (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).topology
                  letI : ChartedSpace H (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).charted
                  letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).smooth
                  letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
                    (X.obj (Lphi.φ k)).t2TangentBundle
                  Set.MapsTo
                    (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric
                      (beta k) z)
                    (U alpha)
                    (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) :=
                Filter.Eventually.of_forall hsourcePhi
              simpa only [aInf, dif_neg htarget] using
                (atom_disjoint_convergence (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r
                  beta alpha.1 gamma (hUopen alpha) hsourceTail
                  hdisjointPhi)
    have hdead (gamma : Fin (inp.pack.A r))
        (hgamma : Lphi.alive (gamma : Nat) = false) :
        aInf alpha gamma = 0 := by
      have hnone : ¬ ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma := by
        rintro ⟨target, hslot⟩
        have htrue : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        rw [hgamma] at htrue
        contradiction
      simp only [aInf, dif_neg hnone]
      rfl
    have hatomSmooth (k : Nat) (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (seqAtomChart (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r
            beta gamma k) (U alpha) :=
      seqAtomChart_smooth (I := I) inp.decay inp.divisor_pos P Lphi inp.pack r k
        (hgpPhi k) beta gamma (hUexpPhi k)
    have hatomInfSmooth (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (aInf alpha gamma) (U alpha) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hquad : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun z => gInf z target.1 (Jinf alpha target z)
              (Jinf alpha target z)) (U alpha) :=
          ((contDiffOn_pi.mp hginfU target.1).clm_apply (hJInf target)).clm_apply
            (hJInf target)
        refine ContDiffOn.congr
          ((gluingBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.divisor_pos (L.rInf (gamma : Nat)))).contDiff.comp_contDiffOn
              hquad) ?_
        intro z hz
        simp only [aInf, dif_pos htarget, target, Function.comp_apply]
      · simpa only [aInf, dif_neg htarget] using
          (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun _ : E => (0 : Real)) (U alpha))
    exact HasAtomWeightLim.of_atoms (I := I) inp.divisor_pos P Lphi inp.realizes inp.pack
      r hr beta (U alpha) (hUopen alpha) hcoverPhi (aInf alpha)
      hdead hatom hatomSmooth hatomInfSmooth
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨hUopen, hU8, hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
    ?_, ?_, ?_, hlimAll, ?_, ?_, ?_⟩
  · refine ⟨eta, heta, ?_⟩
    intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    have hbuf := hk.2.2.2.2
    simp only [← c2_radius_normal_ball_chart_apply (I := I)] at hbuf ⊢
    convert hbuf using 1
    all_goals
      simp only [phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    have hcoreK := hk.2.2.2.1
    simp only [← c2_radius_normal_ball_chart_apply (I := I)] at hcoreK ⊢
    convert hcoreK using 1
    all_goals
      simp only [phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    have hgeom := hk.1
    simp only [← c2_radius_normal_ball_chart_apply (I := I), ← c2_radius_normal_ball_chart_radius (I := I)]
      at hgeom ⊢
    convert hgeom using 1
    all_goals
      simp only [phi, NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.hatBall_subseq,
        NetLimitData.innerBall_subseq, NetLimitData.hatSourceBall_subseq]
    all_goals rfl
  · intro alpha target
    have hs := hspec (⟨alpha, target⟩ : PairSlot)
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_,
      hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
    · simpa only [Jinf, Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.1.comp_subseq hshift
    · simpa only [Jbarinf, Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.2.1.comp_subseq hshift
  · intro alpha target k
    let revTarget : InterSlot L inp.pack r target.1 :=
      ⟨alpha, target.2.mono fun _ hk =>
        BInter.symm inp.decay inp.D P L.lamInf hk⟩
    have hk := hN (shift k) (by
      simpa only [shift] using Nat.le_add_left N k)
    have hf := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).1
    have hr := (hk.2.2.1 (⟨target.1, revTarget⟩ : PairSlot)).1
    constructor
    · simpa only [Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hf
    · simpa only [revTarget, Lphi, phi, L0, live0, NetLimitData.subseq_phi,
        Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hr
  · intro alpha z hz gamma hweight
    have hnum : aInf alpha gamma z ≠ 0 :=
      num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
    have htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma := by
      by_contra hnone
      apply hnum
      simp only [aInf, dif_neg hnone]
    let target := Classical.choose htarget
    have hslot : target.1.1 = gamma := Classical.choose_spec htarget
    let alphaPhi : LiveSlot Lphi inp.pack r :=
      ⟨alpha.1, by simpa only [Lphi, NetLimitData.subseq] using alpha.2⟩
    let gammaPhi : LiveSlot Lphi inp.pack r :=
      ⟨target.1.1, by simpa only [Lphi, NetLimitData.subseq] using target.1.2⟩
    have hgpPhi : ExponentialRadiusScaleTail (I := I)
        inp.decay inp.D P Lphi inp.pack r :=
      Filter.Eventually.of_forall fun k => by
        have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
        simpa only [ExponentialRadiusScaleAt, Lphi, phi, L0, Function.comp_apply,
          NetLimitData.subseq_phi, NetLimitData.subseq_lamInf] using hk.2.1
    have hlimPhi : HasAtomWeightLim (I := I) inp.decay inp.divisor_pos P Lphi
        inp.realizes inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
        (U alpha) (aInf alpha) := by
      simpa only [alphaPhi] using hlimAll alpha
    have hB : MapCInfConvergenceOnCompacts (U alpha)
        (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
          (seqCenterD inp.decay P Lphi k (gammaPhi.1 : Nat)))
        (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, alphaPhi, gammaPhi, Lphi, phi, L0, live0,
        NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hconv
    refine ⟨target, hslot, ?_⟩
    have hmem := hlimPhi.binf_of_live inp hradRatio P Lphi r hr
      hgpPhi alphaPhi (U alpha) (aInf alpha) (fun k : Nat => k)
      strictMono_id gammaPhi (Jinf alpha target) (by
        simpa only [Function.id_def] using hB) hz (by
          simpa only [gammaPhi, hslot] using hweight)
    simpa only [Jinf, gammaPhi, hslot, Lphi, NetLimitData.subseq_lamInf] using hmem


end CheegerGromovCompactness
end DifferentialGeometry
