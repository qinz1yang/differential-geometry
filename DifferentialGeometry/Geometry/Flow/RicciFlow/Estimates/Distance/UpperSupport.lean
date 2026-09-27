import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.CalabiSupport
import DifferentialGeometry.Geometry.Comparison.Variation.RicciIntegral
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength
import Mathlib.Topology.Separation.Connected

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff Topology Bundle ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem backPath_deriv_le
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b T tau A : Real}
    (hab : a ≤ b)
    (ht : T - tau ∈ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hvel : ∀ u ∈ Icc a b,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0)
    (hRic : ∀ u ∈ Icc a b,
      ricciTensor (I := I) (S.base.metric (T - tau)) (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) ≤
        A * (S.base.metric (T - tau)).inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) :
    ∃ d : Real,
      HasDerivAt
        (fun s ↦ Variation.arcLength
          (I := I) (S.base.metric (T - s)) gamma a b) d tau ∧
      d ≤ A * Variation.arcLength
        (I := I) (S.base.metric (T - tau)) gamma a b := by
  classical
  let t : Real := T - tau
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let G : Real → Real :=
    fun u ↦ (S.base.metric t).inner (gamma u) (v u) (v u)
  let Ric : Real → Real :=
    fun u ↦ ricciTensor (I := I) (S.base.metric t) (gamma u) (v u) (v u)
  let Q : Real → Real := fun u ↦ -Ric u / Real.sqrt (G u)
  have hvLift : Continuous (fun u : Real ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hGcont : ContinuousOn G (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hbase : Continuous (fun u : ↥(Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥(Icc a b))
        (τ := fun _u ↦ t)
        (b := fun u ↦ gamma (u : Real))
        continuous_const
        (fun _u ↦ D.regular_subset (by simpa only [t] using ht))
        hbase
        (v := fun _i u ↦ v (u : Real))
        hvec
    refine heval.congr (fun u ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtCont :
      ContinuousOn
        (fun u ↦ S.ricciAt t (gamma u) (vec2 (I := I) (v u) (v u)))
        (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hbase : Continuous (fun u : ↥(Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval :=
      hS.ricciCont.eval_continuous
        (P := ↥(Icc a b))
        (τ := fun _u ↦ t)
        (b := fun u ↦ gamma (u : Real))
        continuous_const
        (fun _u ↦ D.regular_subset (by simpa only [t] using ht))
        hbase
        (v := fun _i u ↦ v (u : Real))
        hvec
    refine heval.congr (fun u ↦ ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (fun _i : Fin 2 ↦ v (u : Real)) =
        metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (vec2 (I := I) (v (u : Real)) (v (u : Real)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicCont : ContinuousOn Ric (Icc a b) := by
    refine hRicAtCont.congr (fun u _hu ↦ ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric t) (gamma u) (v u) (v u)).symm
  have hspeedCont : ContinuousOn (fun u ↦ Real.sqrt (G u)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hGcont
  have hQcont : ContinuousOn Q (Icc a b) := by
    change ContinuousOn (fun u ↦ -Ric u / Real.sqrt (G u)) (Icc a b)
    apply ContinuousOn.div hRicCont.neg hspeedCont
    intro u hu
    exact ne_of_gt (Real.sqrt_pos.2
      ((S.base.metric t).pos (gamma u) (v u) (hvel u hu)))
  have hleftInt : IntervalIntegrable
      (fun u ↦ -A * Real.sqrt (G u)) volume a b :=
    (continuousOn_const.mul hspeedCont).intervalIntegrable_of_Icc hab
  have hrightInt : IntervalIntegrable Q volume a b :=
    hQcont.intervalIntegrable_of_Icc hab
  have hpoint : ∀ u ∈ Icc a b, -A * Real.sqrt (G u) ≤ Q u := by
    intro u hu
    have hGpos : 0 < G u :=
      (S.base.metric t).pos (gamma u) (v u) (hvel u hu)
    have hRicLe : Ric u ≤ A * G u := by
      simpa only [Ric, G, v, t] using hRic u hu
    dsimp only [Q]
    rw [le_div_iff₀ (Real.sqrt_pos.2 hGpos)]
    rw [mul_assoc, Real.mul_self_sqrt hGpos.le]
    linarith
  have hmono :
      (∫ u in a..b, -A * Real.sqrt (G u)) ≤ ∫ u in a..b, Q u :=
    intervalIntegral.integral_mono_on hab hleftInt hrightInt hpoint
  have hforward :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS hab (by simpa only [t] using ht) gamma hgamma hvel
  have hforwardQ :
      HasDerivAt
        (fun s ↦ Variation.arcLength (I := I) (S.base.metric s) gamma a b)
        (∫ u in a..b, Q u) t := by
    simpa only [Q, Ric, G, v, t] using hforward
  have hsub : HasDerivAt (fun s : Real ↦ T - s) (-1) tau := by
    exact (hasDerivAt_id tau).const_sub T
  let d : Real := (∫ u in a..b, Q u) * (-1)
  refine ⟨d, ?_, ?_⟩
  · convert! hforwardQ.comp tau hsub using 1
  · have hforwardLower :
        -A * Variation.arcLength
            (I := I) (S.base.metric t) gamma a b ≤
          ∫ u in a..b, Q u := by
      rw [Variation.arcLength, ← intervalIntegral.integral_const_mul]
      exact hmono
    dsimp only [d]
    dsimp only [t] at hforwardLower ⊢
    linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_upper_support_riemannianEDistOf_of_lt_two_mul
    [PreconnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hK : 0 ≤ K) (hr : 0 < r)
    (x y : M)
    (hshort :
      (riemannianEDistOf
        (I := I) (S.base.metric (T - tau)) x y).toReal < 2 * r)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x z < ENNReal.ofReal r ∨
        riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) y z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∃ phi : Real → Real, ∃ d : Real,
      phi tau =
          (riemannianEDistOf
            (I := I) (S.base.metric (T - tau)) x y).toReal ∧
      (fun s ↦
          (riemannianEDistOf
            (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi ∧
      HasDerivAt phi d tau ∧
      d ≤ 2 * ((Module.finrank Real E : Real) - 1) * K * r := by
  classical
  let : Nonempty M := ⟨x⟩
  let : ConnectedSpace M := ⟨inferInstance⟩
  have hnNat : 1 ≤ Module.finrank Real E :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hn : 0 ≤ (Module.finrank Real E : Real) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hnNat)
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ ↦ 0, 0, ?_, ?_, hasDerivAt_const tau 0, ?_⟩
    · simp only [riemannianEDistOf_self, ENNReal.toReal_zero]
    · exact Filter.Eventually.of_forall (fun _ ↦ by
        simp only [riemannianEDistOf_self, ENNReal.toReal_zero, le_refl])
    · positivity
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : M ↦ TangentSpace I z) :=
    ⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := by
    simpa only [g] using hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro z w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hdist : riemannianEDistOf (I := I) g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y
  let ell : Real := (riemannianEDist I x y).toReal
  have hell_short : ell < 2 * r := by
    simpa only [g, hdist, ell] using hshort
  let v : TangentSpace I x := minimizingVec (I := I) g hEnorm x y
  let gamma : Real → M := intrinsicGeodesic (I := I) g hEnorm x v
  have hv : v ≠ 0 := by
    intro hv0
    have hexp := minimizingVec_exp (I := I) g hEnorm x y
    dsimp only [v] at hv0
    rw [hv0, expMapIntrinsic_zero] at hexp
    exact hxy hexp
  have hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma :=
    contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x v)
  have hvel : ∀ u ∈ Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0 := by
    intro u _hu
    exact Exponential.intrinsicGeo_velocity_ne (I := I) g hEnorm x v hv u
  have hgamma0 : gamma 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hgamma1 : gamma 1 = y := by
    simpa only [gamma, v, expMapIntrinsic_def] using
      minimizingVec_exp (I := I) g hEnorm x y
  have hcover : ∀ u ∈ Icc (0 : Real) 1,
      riemannianEDistOf (I := I) g x (gamma u) < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) g y (gamma u) < ENNReal.ofReal r := by
    intro u hu
    by_cases hleft : ell * u < r
    · left
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      have hseg := minJoin_edist_le (I := I) g hEnorm x y hu.1
      have hseg' :
          riemannianEDist I x (gamma u) ≤ ENNReal.ofReal (ell * u) := by
        simpa only [gamma, v, minJoin, ell] using hseg
      exact hseg'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hleft)
    · right
      have hright : ell * (1 - u) < r := by
        have hleft' : r ≤ ell * u := le_of_not_gt hleft
        have heq : ell * (1 - u) = ell - ell * u := by ring
        rw [heq]
        linarith
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      have hseg := intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm x v (s := u) (t := 1) hu.2
      have hseg' :
          riemannianEDist I (gamma u) (gamma 1) ≤
            ENNReal.ofReal (ell * (1 - u)) := by
        simpa only [gamma, v, ell, minimizingVec_len] using hseg
      have hseg'' :
          riemannianEDist I y (gamma u) ≤
            ENNReal.ofReal (ell * (1 - u)) := by
        rw [riemannianEDist_comm, ← hgamma1]
        exact hseg'
      exact hseg''.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hright)
  let A : Real := ((Module.finrank Real E : Real) - 1) * K
  have hA : 0 ≤ A := mul_nonneg hn hK
  have hRicGamma : ∀ u ∈ Icc (0 : Real) 1,
      ricciTensor (I := I) g (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) ≤
        A * g.inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) := by
    intro u hu
    simpa only [g, A] using
      hRic (gamma u) (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
        (by simpa only [g] using hcover u hu)
  let phi : Real → Real := fun s ↦
    Variation.arcLength (I := I) (S.base.metric (T - s)) gamma 0 1
  have hpath : Variation.arcLength (I := I) g gamma 0 1 = ell := by
    have hgammaMin : gamma = minJoin (I := I) g hEnorm x y := by
      funext u
      rfl
    rw [hgammaMin, minJoin_arcLength (I := I) g hEnorm x y]
  have hcontact : phi tau = ell := by
    simpa only [phi, g] using hpath
  have hupper :
      (fun s ↦
          (riemannianEDistOf
            (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi := by
    exact Filter.Eventually.of_forall (fun s ↦ by
      have hedist := riemannianEDistOf_le_arcLength
        (I := I) (S.base.metric (T - s)) zero_le_one hgamma.contMDiffOn
      rw [hgamma0, hgamma1] at hedist
      have hphi_nonneg : 0 ≤ phi s := by
        dsimp only [phi, Variation.arcLength]
        exact intervalIntegral.integral_nonneg zero_le_one
          (fun _ _ ↦ Real.sqrt_nonneg _)
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hedist
      rw [ENNReal.toReal_ofReal hphi_nonneg] at hreal
      exact hreal)
  obtain ⟨d, hphiDeriv, hd⟩ :=
    backPath_deriv_le
      (I := I) S hS zero_le_one ht gamma hgamma hvel
        (A := A) (by simpa only [g] using hRicGamma)
  refine ⟨phi, d, ?_, hupper, ?_, ?_⟩
  · calc
      phi tau = ell := hcontact
      _ = (riemannianEDist I x y).toReal := rfl
      _ = (riemannianEDistOf (I := I) g x y).toReal :=
        congrArg ENNReal.toReal hdist.symm
      _ = (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x y).toReal := rfl
  · simpa only [phi] using hphiDeriv
  · calc
      d ≤ A * Variation.arcLength (I := I) g gamma 0 1 := by
        simpa only [g] using hd
      _ = A * ell := by rw [hpath]
      _ ≤ A * (2 * r) := mul_le_mul_of_nonneg_left hell_short.le hA
      _ = 2 * ((Module.finrank Real E : Real) - 1) * K * r := by
        simp only [A]
        ring

omit [NeZero (Module.finrank Real E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_upper_support_riemannianEDistOf_of_two_mul_le
    [PreconnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hr : 0 < r)
    (x y : M)
    (hlong :
      2 * r ≤
        (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x y).toReal)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x z < ENNReal.ofReal r ∨
        riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) y z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∃ phi : Real → Real, ∃ d : Real,
      phi tau =
          (riemannianEDistOf
            (I := I) (S.base.metric (T - tau)) x y).toReal ∧
      (fun s ↦
          (riemannianEDistOf
            (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi ∧
      HasDerivAt phi d tau ∧
      d ≤ 2 * ((Module.finrank Real E : Real) - 1) *
        ((2 / 3 : Real) * K * r + 1 / r) := by
  classical
  let : Nonempty M := ⟨x⟩
  let : ConnectedSpace M := ⟨inferInstance⟩
  let : NeZero (Module.finrank Real E) := ⟨by
    intro hdim
    let : Subsingleton E := (Module.finrank_zero_iff (R := Real)).mp hdim
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := PreconnectedSpace.trivial_of_discrete
    have hzero := hlong
    rw [Subsingleton.elim x y, riemannianEDistOf_self, ENNReal.toReal_zero] at hzero
    linarith⟩
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : M ↦ TangentSpace I z) :=
    ⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := by
    simpa only [g] using hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro z w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hdist :
      riemannianEDistOf (I := I) g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y
  let ell : Real := (riemannianEDist I x y).toReal
  have hell_long : 2 * r ≤ ell := by
    simpa only [g, hdist, ell] using hlong
  have hell_pos : 0 < ell := by
    exact (show 0 < 2 * r by linarith).trans_le hell_long
  have hell0 : ell ≠ 0 := ne_of_gt hell_pos
  have hdist_real : riemannianEDist I x y = ENNReal.ofReal ell := by
    have hfin : riemannianEDist I x y ≠ ⊤ :=
      riemannianEDist_ne_top (I := I) x y
    simpa only [ell] using (ENNReal.ofReal_toReal hfin).symm
  let v : TangentSpace I x := minimizingVec (I := I) g hEnorm x y
  let w : TangentSpace I x := ell⁻¹ • v
  let gamma : Real → M := intrinsicGeodesic (I := I) g hEnorm x w
  have hv_len : Real.sqrt (g.inner x v v) = ell := by
    simpa only [v, ell] using minimizingVec_len (I := I) g hEnorm x y
  have hinner_v : g.inner x v v = ell ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g x v), hv_len]
  have hinner_w : g.inner x w w = 1 := by
    dsimp only [w]
    rw [gInner_smul_self (I := I) g x ell⁻¹ v, hinner_v,
      ← mul_pow, inv_mul_cancel₀ hell0, one_pow]
  have hell_smul : ell • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hell0, one_smul]
  have hgamma0 : gamma 0 = x := by
    exact intrinsicGeodesic_zero (I := I) g hEnorm x w
  have hgammaL : gamma ell = y := by
    calc
      gamma ell = intrinsicGeodesic (I := I) g hEnorm x (ell • w) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x w ell).symm
      _ = intrinsicGeodesic (I := I) g hEnorm x v 1 := by
        rw [hell_smul]
      _ = y := by
        rw [← expMapIntrinsic_def]
        simpa only [v] using minimizingVec_exp (I := I) g hEnorm x y
  have hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma := by
    simpa only [gamma] using
      isGeodesic_contMDiff
        (I := I) g
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x w)
        (intrinsicGeodesic_continuous (I := I) g hEnorm x w)
  have hgammaOne : ContMDiff 𝓘(Real, Real) I 1 gamma :=
    hgamma.of_le
      (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hgeo : IsGeodesicOn (I := I) g gamma (Icc 0 ell) := by
    simpa only [gamma] using
      (intrinsicGeodesic_isGeodesic
        (I := I) g hEnorm x w).isGeodesicOn (Icc 0 ell)
  have hunitAll : ∀ t : Real,
      g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) = 1 := by
    intro t
    change
      g.inner (intrinsicGeodesic (I := I) g hEnorm x w t)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm x w) t 1)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm x w) t 1) = 1
    exact (intrinsicGeodesic_speedSq_eq
      (I := I) g hEnorm x w t).trans hinner_w
  have hunit : ∀ t ∈ Icc (0 : Real) ell,
      g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) = 1 :=
    fun t _ ↦ hunitAll t
  have hvel : ∀ t ∈ Icc (0 : Real) ell,
      mfderiv 𝓘(Real, Real) I gamma t 1 ≠ 0 := by
    intro t _ht hzero
    have hone := hunitAll t
    rw [hzero] at hone
    have h01 : (0 : Real) = 1 := by
      simpa only [map_zero] using hone
    exact zero_ne_one h01
  have hpath : Variation.arcLength (I := I) g gamma 0 ell = ell := by
    unfold Variation.arcLength
    calc
      _ = ∫ _t in (0 : Real)..ell, (1 : Real) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change Real.sqrt (g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1)) = 1
        rw [hunitAll t, Real.sqrt_one]
      _ = ell := by simp
  have hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Icc 0 ell) →
      eta 0 = gamma 0 → eta ell = gamma ell →
      Variation.arcLength (I := I) g gamma 0 ell ≤
        Variation.arcLength (I := I) g eta 0 ell := by
    intro eta heta heta0 hetaL
    have heta_nonneg : 0 ≤ Variation.arcLength (I := I) g eta 0 ell := by
      unfold Variation.arcLength
      exact intervalIntegral.integral_nonneg hell_pos.le
        (fun _ _ ↦ Real.sqrt_nonneg _)
    have hed :
        riemannianEDist I (eta 0) (eta ell) ≤
          ENNReal.ofReal (Variation.arcLength (I := I) g eta 0 ell) :=
      Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
        (I := I) g hell_pos.le heta (fun t _ht ↦ hEnorm (eta t) _)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hell_le : ell ≤ Variation.arcLength (I := I) g eta 0 ell := by
      rw [heta0, hetaL, hgamma0, hgammaL, hdist_real,
        ENNReal.toReal_ofReal hell_pos.le,
        ENNReal.toReal_ofReal heta_nonneg] at hreal
      exact hreal
    rw [hpath]
    exact hell_le
  let A : Real := ((Module.finrank Real E : Real) - 1) * K
  have hRicGamma : ∀ t ∈ Icc (0 : Real) ell,
      t < r ∨ ell - r < t →
      ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) ≤ A := by
    intro t ht hend
    have hball :
        riemannianEDistOf (I := I) g x (gamma t) < ENNReal.ofReal r ∨
          riemannianEDistOf (I := I) g y (gamma t) < ENNReal.ofReal r := by
      rcases hend with hleft | hright
      · left
        rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
        have hseg :
            riemannianEDist I (gamma 0) (gamma t) ≤
              ENNReal.ofReal (Real.sqrt (g.inner x w w) * (t - 0)) := by
          simpa only [gamma] using
            intrinsicGeodesic_riemannianEDist_le
              (I := I) g hEnorm x w (s := 0) (t := t) ht.1
        rw [hgamma0, hinner_w, Real.sqrt_one, sub_zero, one_mul] at hseg
        exact hseg.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hleft)
      · right
        have htail : ell - t < r := by linarith
        rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
        have hseg :
            riemannianEDist I (gamma t) (gamma ell) ≤
              ENNReal.ofReal (Real.sqrt (g.inner x w w) * (ell - t)) := by
          simpa only [gamma] using
            intrinsicGeodesic_riemannianEDist_le
              (I := I) g hEnorm x w (s := t) (t := ell) ht.2
        rw [hinner_w, Real.sqrt_one, one_mul] at hseg
        rw [riemannianEDist_comm, ← hgammaL]
        exact hseg.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 htail)
    have hraw :=
      hRic (gamma t) (mfderiv 𝓘(Real, Real) I gamma t 1)
        (by simpa only [g] using hball)
    have hu := hunitAll t
    simpa only [g, A, hu, mul_one] using hraw
  let R : Real → Real := fun t ↦
    ricciTensor (I := I) g (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t 1)
      (mfderiv 𝓘(Real, Real) I gamma t 1)
  have hRicInt :
      (∫ t in (0 : Real)..ell, R t) ≤
        (Module.finrank Real E - 1 : Real) * (2 / r) +
          A * (4 * r / 3) := by
    simpa only [R] using
      Variation.integral_ricciTensor_le_of_endpoint_bound
        (I := I) g gamma
        (L := ell) (r := r) (A := A)
        hr hell_long hgamma hgeo hunit hmin hRicGamma
  let phi : Real → Real := fun s ↦
    Variation.arcLength
      (I := I) (S.base.metric (T - s)) gamma 0 ell
  have hcontact : phi tau = ell := by
    simpa only [phi, g] using hpath
  have hupper :
      (fun s ↦
        (riemannianEDistOf
          (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi := by
    exact Filter.Eventually.of_forall (fun s ↦ by
      have hed := riemannianEDistOf_le_arcLength
        (I := I) (S.base.metric (T - s))
        hell_pos.le hgammaOne.contMDiffOn
      rw [hgamma0, hgammaL] at hed
      have hphi_nonneg : 0 ≤ phi s := by
        dsimp only [phi, Variation.arcLength]
        exact intervalIntegral.integral_nonneg hell_pos.le
          (fun _ _ ↦ Real.sqrt_nonneg _)
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
      rw [ENNReal.toReal_ofReal hphi_nonneg] at hreal
      exact hreal)
  have hforward :
      HasDerivAt
        (fun s ↦ Variation.arcLength
          (I := I) (S.base.metric s) gamma 0 ell)
        (-(∫ t in (0 : Real)..ell, R t)) (T - tau) := by
    have h := pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS hell_pos.le ht gamma hgammaOne hvel
    have hint :
        (∫ u in (0 : Real)..ell,
          -ricciTensor (I := I) (S.base.metric (T - tau)) (gamma u)
              (mfderiv 𝓘(Real, Real) I gamma u 1)
              (mfderiv 𝓘(Real, Real) I gamma u 1) /
            Real.sqrt ((S.base.metric (T - tau)).inner (gamma u)
              (mfderiv 𝓘(Real, Real) I gamma u 1)
              (mfderiv 𝓘(Real, Real) I gamma u 1))) =
          -(∫ u in (0 : Real)..ell, R u) := by
      calc
        _ = ∫ u in (0 : Real)..ell, -R u := by
          apply intervalIntegral.integral_congr
          intro u _hu
          change
            -ricciTensor (I := I) (S.base.metric (T - tau)) (gamma u)
                (mfderiv 𝓘(Real, Real) I gamma u 1)
                (mfderiv 𝓘(Real, Real) I gamma u 1) /
              Real.sqrt ((S.base.metric (T - tau)).inner (gamma u)
                (mfderiv 𝓘(Real, Real) I gamma u 1)
                (mfderiv 𝓘(Real, Real) I gamma u 1)) =
              -R u
          have hu := hunitAll u
          rw [show
            (S.base.metric (T - tau)).inner (gamma u)
                (mfderiv 𝓘(Real, Real) I gamma u 1)
                (mfderiv 𝓘(Real, Real) I gamma u 1) = 1 by
              simpa only [g] using hu,
            Real.sqrt_one, div_one]
        _ = -(∫ u in (0 : Real)..ell, R u) := by
          rw [intervalIntegral.integral_neg]
    rw [← hint]
    exact h
  have hsub : HasDerivAt (fun s : Real ↦ T - s) (-1) tau := by
    exact (hasDerivAt_id tau).const_sub T
  let d : Real := (-(∫ t in (0 : Real)..ell, R t)) * (-1)
  have hphiDeriv : HasDerivAt phi d tau := by
    convert! hforward.comp tau hsub using 1
  have hd : d = ∫ t in (0 : Real)..ell, R t := by
    dsimp only [d]
    ring
  refine ⟨phi, d, ?_, hupper, hphiDeriv, ?_⟩
  · calc
      phi tau = ell := hcontact
      _ = (riemannianEDist I x y).toReal := rfl
      _ = (riemannianEDistOf (I := I) g x y).toReal :=
        congrArg ENNReal.toReal hdist.symm
      _ = (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x y).toReal := rfl
  · calc
      d = ∫ t in (0 : Real)..ell, R t := hd
      _ ≤ (Module.finrank Real E - 1 : Real) * (2 / r) +
          A * (4 * r / 3) := hRicInt
      _ = 2 * ((Module.finrank Real E : Real) - 1) *
          ((2 / 3 : Real) * K * r + 1 / r) := by
        simp only [A]
        ring

end DifferentialGeometry.PDE.RicciFlow
