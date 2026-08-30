import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.InnerExpansion
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.BonnetMyers
open Riemannian.CovariantDerivativeAlong
open Riemannian.Exponential
open Riemannian.Geodesic
open Riemannian.Variation
open Riemannian.Volume
open Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

def isWeightedDistanceUpperSupport
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (σ : Real) (O x : M) (r C : Real) (rho : M → Real) : Prop :=
  ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
    rho x = r ∧
    (∀ᶠ y in 𝓝 x, (riemannianEDistOf (I := I) g O y).toReal ≤ rho y) ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g rho y) x ∧
    g.inner x (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x) = 1 ∧
    laplacian (I := I) (LeviCivita (I := I) g) g rho x -
        g.inner x (gradFun (I := I) g f x)
          (gradientFun (I := I) g rho x) ≤ C - σ / 2 * r

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_local_soliton_control
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (hcomplete : RiemannianMetricComplete (I := I) g) (O : M) :
    ∃ q B : Real, 0 ≤ q ∧ 0 ≤ B ∧
      (0 < Module.finrank Real E - 1 →
        ∀ y : M,
          riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4 →
            ∀ v : TangentSpace I y,
              -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
                  g.inner y v v ≤ ricciTensor (I := I) g y v v) ∧
      (∀ y : M,
        riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4 →
          Real.sqrt (normGradSqFun (I := I) g f y) ≤ B) := by
  classical
  let K : Set M := {y : M |
    riemannianEDistOf (I := I) g O y ≤ ENNReal.ofReal 4}
  let A : M → Real := fun y =>
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04 (I := I) (M := M) g y))
  let G : M → Real := fun y =>
    Real.sqrt (normGradSqFun (I := I) g f y)
  have hK : IsCompact K :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete O 4
  have hOK : O ∈ K := by
    dsimp only [K]
    change riemannianEDistOf (I := I) g O O ≤ ENNReal.ofReal 4
    rw [riemannianEDistOf_self]
    exact bot_le
  have hA : Continuous A := by
    exact Real.continuous_sqrt.comp
      (Tensor0SBundle.normSq0S_cont (I := I) g
        (metricRm04 (I := I) (M := M) g))
  have hG : Continuous G := by
    exact Real.continuous_sqrt.comp
      (normGradSqFun_continuous (I := I) g f.contMDiff)
  obtain ⟨a, haK, ha⟩ := hK.exists_isMaxOn ⟨O, hOK⟩ hA.continuousOn
  obtain ⟨b, hbK, hb⟩ := hK.exists_isMaxOn ⟨O, hOK⟩ hG.continuousOn
  let Rm : Real := A a
  let B : Real := G b
  let q : Real := (Module.finrank Real E : Real) ^ 2 * Rm + 1
  have hRm : 0 ≤ Rm := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  refine ⟨q, B, hq, hB, ?_, ?_⟩
  · intro hd y hy v
    have hyK : y ∈ K := hy
    have hAy : A y ≤ Rm := ha hyK
    have hlocal := ricciLowerAt_of_rm (I := I) g hAy v
    have hdR : (1 : Real) ≤ ((Module.finrank Real E - 1 : Nat) : Real) := by
      exact_mod_cast hd
    have hnRm : 0 ≤ (Module.finrank Real E : Real) ^ 2 * Rm :=
      mul_nonneg (sq_nonneg _) hRm
    have hcoef :
        (Module.finrank Real E : Real) ^ 2 * Rm ≤
          ((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 := by
      dsimp only [q]
      nlinarith
    have hinner := gInner_self_nonneg (I := I) g y v
    have hmul := mul_le_mul_of_nonneg_right hcoef hinner
    apply le_trans _ hlocal
    calc
      -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) * g.inner y v v =
          -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 *
            g.inner y v v) := by ring
      _ ≤ -((Module.finrank Real E : Real) ^ 2 * Rm * g.inner y v v) :=
        neg_le_neg hmul
      _ = -((Module.finrank Real E : Real) ^ 2 * Rm) * g.inner y v v := by ring
  · intro y hy
    exact hb hy

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem gradientRicciSoliton_weightedMean_antitone
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (f : C^∞⟮I, M; Real⟯) (σ : Real)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    {O x : M} {r : Real}
    (tail : CalabiTailData (I := I) g hEnorm O x r)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I tail.p)
    (hv : LinearIndependent Real v)
    (hperp : ∀ i, g.inner tail.p tail.u (v i) = 0)
    {s : Real} (hs : 0 < s) :
    let γ : Real → M :=
      intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
    let V := fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)
    let ell := Real.sqrt (g.inner tail.p tail.u tail.u)
    AntitoneOn
      (fun t => curveMean (I := I) g γ V t - deriv (f ∘ γ) t +
        σ / 2 * ell ^ 2 * t) (Set.Icc s 1) := by
  classical
  dsimp only
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
  let V : Fin (Module.finrank Real E - 1) → ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)
  let ell : Real := Real.sqrt (g.inner tail.p tail.u tail.u)
  let z : Real → Real := fun t =>
    curveMean (I := I) g γ V t - deriv (f ∘ γ) t +
      σ / 2 * ell ^ 2 * t
  have hell : 0 < ell := by
    dsimp only [ell]
    rw [tail.u_norm]
    exact tail.ell_pos
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm tail.p tail.u
  have hfγM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ (f ∘ γ) :=
    f.contMDiff.comp hγInf
  have hfγ : ContDiff Real ∞ (f ∘ γ) :=
    contMDiff_iff_contDiff.mp hfγM
  have hspeed : ∀ t : Real,
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = ell ^ 2 := by
    intro t
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) =
          g.inner tail.p tail.u tail.u := by
        exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm tail.p tail.u t
      _ = ell ^ 2 := (Real.sq_sqrt
        (gInner_self_nonneg (I := I) g tail.p tail.u)).symm
  have hderiv : ∀ t ∈ Set.Ioo (0 : Real) tail.b,
      HasDerivAt z
          (-Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)) t ∧
        0 ≤ Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) := by
    intro t ht
    have hγt : ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t :=
      hγInf.contMDiffAt.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hVdiff : ∀ i,
        DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
      intro i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) t).1
    have hDVdiff : ∀ i,
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun a => covDerivAlong (I := I) g γ (V i) a) t) t := by
      intro i
      simpa only [γ, V] using
        (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) t).2
    have hVperp : ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
      intro i
      simpa only [γ, V] using
        Riemannian.VolumeComparison.intrJacobi_perp_ne
          (I := I) g hEnorm tail.p tail.u (v i)
          ht.1.ne' (hperp i)
    have hDVperp : ∀ i,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (covDerivAlong (I := I) g γ (V i) t) = 0 := by
      intro i
      simpa only [γ, V] using
        intrJacobi_dperp
          (I := I) g hEnorm tail.p tail.u (v i)
          ht.1.ne' (hperp i)
    have hLI : LinearIndependent Real fun i => V i t := by
      simpa only [γ, V] using
        intrinsicJacobi_linearIndependent_of_noConjVec
          (I := I) g hEnorm tail.p tail.u v hv ht.1.ne'
            (tail.no_conj t ht)
    have hW : ∀ i j, jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
      intro i j
      exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
        g γ (V i) (V j)
        (hγInf.of_le
          (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) a).1)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v j) a).1)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v i) a).2)
        (fun a _ => by simpa only [γ, V] using
          (intrJacobi_diff (I := I) g hEnorm tail.p tail.u (v j) a).2)
        (fun a _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm tail.p tail.u)
            (intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v i)) a
          exact intrinsic_jacobi
            (I := I) g hEnorm tail.p (tail.u : E) (v i : E) a)
        (fun a _ => by
          change IsJacobiAt (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm tail.p tail.u)
            (intrinsicJacobi (I := I) g hEnorm tail.p tail.u (v j)) a
          exact intrinsic_jacobi
            (I := I) g hEnorm tail.p (tail.u : E) (v j : E) a)
        (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
    have hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t := by
      intro i
      exact intrinsic_jacobi
        (I := I) g hEnorm tail.p (tail.u : E) (v i : E) t
    have hspeedPos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
      rw [hspeed]
      positivity
    obtain ⟨e, heON, heperp⟩ :=
      exists_perp_pos (I := I) g (γ t) (curveVelocity (I := I) γ t) hspeedPos
    have hmean := hasDerivAt_mean_perp (I := I) (n := (2 : WithTop ℕ∞))
      (by norm_num) g γ V t (curveVelocity (I := I) γ t) (by simp)
      hspeedPos hVperp hDVperp hγt hVdiff hDVdiff hLI hW hJ
    have hcurv := curvTrace_eq_ricci (I := I) g γ V t
      (curveVelocity (I := I) γ t) rfl (by simp) hspeedPos hVperp hLI
      e heON heperp
    have hshape := mean_sq_le_shape (I := I) g γ V t
      (curveVelocity (I := I) γ t) (by simp) hspeedPos hVperp hDVperp hLI hW
      e heON heperp
    have hshapeNonneg :
        0 ≤ Matrix.trace ((curveShape (I := I) g γ V t) ^ 2) := by
      by_cases hd0 : Module.finrank Real E - 1 = 0
      · let _ : IsEmpty (Fin (Module.finrank Real E - 1)) := by
          rw [hd0]
          exact Fin.isEmpty
        simp only [Matrix.trace, Finset.sum_of_isEmpty]
        exact le_rfl
      · have hd : 0 < Module.finrank Real E - 1 := Nat.pos_of_ne_zero hd0
        have hdR : (0 : Real) < ((Module.finrank Real E - 1 : Nat) : Real) := by
          exact_mod_cast hd
        nlinarith [sq_nonneg (curveMean (I := I) g γ V t)]
    have hpotSecond := deriv2_comp_geo (I := I) g f.contMDiff hγInf
      (intrinsicGeodesic_isGeodesic (I := I) g hEnorm tail.p tail.u) t
    change (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) at hpotSecond
    have hpotDeriv : HasDerivAt (deriv (f ∘ γ))
        ((deriv^[2] (f ∘ γ)) t) t := by
      have hfγ2 : ContDiff Real 2 (f ∘ γ) := hfγ.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
      exact (hfγ2.differentiable_deriv_two t).hasDerivAt
    have hlin : HasDerivAt (fun a : Real => σ / 2 * ell ^ 2 * a)
        (σ / 2 * ell ^ 2) t := by
      exact hasDerivAt_const_mul (x := t) (σ / 2 * ell ^ 2)
    have hz := (hmean.sub hpotDeriv).add hlin
    refine ⟨hz.congr_deriv ?_, hshapeNonneg⟩
    · rw [hcurv, hpotSecond]
      have hsolt := hsol (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)
      rw [hspeed] at hsolt
      linarith
  have hderivIcc : ∀ t ∈ Set.Icc s 1,
      HasDerivAt z (-Matrix.trace ((curveShape (I := I) g γ V t) ^ 2)) t := by
    intro t ht
    exact (hderiv t ⟨hs.trans_le ht.1, ht.2.trans_lt tail.one_lt⟩).1
  have hcont : ContinuousOn z (Set.Icc s 1) := by
    intro t ht
    exact (hderivIcc t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn Real z (interior (Set.Icc s 1)) := by
    intro t ht
    exact (hderivIcc t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc s 1) hcont hdiff
    (fun t ht => by
      rw [(hderivIcc t (interior_subset ht)).deriv]
      exact neg_nonpos.mpr
        (hderiv t ⟨hs.trans_le (interior_subset ht).1,
          (interior_subset ht).2.trans_lt tail.one_lt⟩).2)
  simpa only [z] using hanti

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gradientRicciSoliton_exists_weightedDistanceUpperSupport
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (σ : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (O : M) :
    ∃ C : Real, ∀ x : M,
      3 ≤ (riemannianEDistOf (I := I) g O x).toReal →
        ∃ rho : M → Real,
          isWeightedDistanceUpperSupport (I := I) g f σ O x
            (riemannianEDistOf (I := I) g O x).toReal C rho := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  obtain ⟨q, B, hq, hB, hRic, hGrad⟩ :=
    exists_local_soliton_control (I := I) g f hcomplete O
  let d : Real := ((Module.finrank Real E - 1 : Nat) : Real)
  let C : Real := d + d * q + B + σ
  refine ⟨C, ?_⟩
  intro x hx
  let r : Real := (riemannianEDistOf (I := I) g O x).toReal
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) :=
    riemannianEDist_ne_top (I := I) O x
  obtain ⟨u, hexp, hlen⟩ :=
    minExp_of_ne_top (I := I) g hEnorm O x hfin
  have hr_eq : (riemannianEDist I O x).toReal = r := by
    rfl
  have hlen' : Real.sqrt (g.inner O u u) = r := hlen.trans hr_eq
  have hs₀ : 1 / r ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · positivity
    · apply (div_lt_one hr).2
      linarith
  have hs₀half : 1 / r ≤ (1 : Real) / 2 := by
    apply (div_le_div_iff₀ hr (by norm_num : (0 : Real) < 2)).2
    linarith
  obtain ⟨tail, hleft, hell⟩ :=
    exists_calabiTail_of_split (I := I) g hEnorm u hexp hlen' hr hr_eq.symm
      (1 / r) hs₀ hs₀half
  have hleft_one : tail.left = 1 := by
    rw [hleft]
    field_simp [hr.ne']
  have hell_sub : tail.ell = r - 1 := by
    rw [hell]
    field_simp [hr.ne']
  have hell_two : 2 ≤ tail.ell := by
    rw [hell_sub]
    linarith
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm tail.p tail.u
  let s : Real := 1 / tail.ell
  let b : Real := 2 / tail.ell
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hsb : s < b := by
    dsimp only [s, b]
    exact (div_lt_div_iff_of_pos_right tail.ell_pos).2 (by norm_num)
  have hb_one : b ≤ 1 := by
    dsimp only [b]
    apply (div_le_iff₀ tail.ell_pos).2
    simpa only [one_mul] using hell_two
  have hs_one : s ≤ 1 := by
    exact hsb.le.trans hb_one
  have hb_tail : b < tail.b := hb_one.trans_lt tail.one_lt
  have hball : ∀ t ∈ Set.Icc (0 : Real) b,
      riemannianEDistOf (I := I) g O (γ t) ≤ ENNReal.ofReal 4 := by
    intro t ht
    have hellt : 0 ≤ tail.ell * t :=
      mul_nonneg tail.ell_pos.le ht.1
    have hdist :=
      intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm tail.p tail.u
          (s := (0 : Real)) (t := t) ht.1
    have hseg :
        riemannianEDist I tail.p (γ t) ≤
          ENNReal.ofReal (tail.ell * t) := by
      rw [intrinsicGeodesic_zero (I := I) g hEnorm tail.p tail.u] at hdist
      simpa only [γ, tail.u_norm, sub_zero] using hdist
    have hellb : tail.ell * b = 2 := by
      dsimp only [b]
      field_simp [tail.ell_pos.ne']
    have hmul : tail.ell * t ≤ 2 := by
      calc
        tail.ell * t ≤ tail.ell * b :=
          mul_le_mul_of_nonneg_left ht.2 tail.ell_pos.le
        _ = 2 := hellb
    have hreal : tail.left + tail.ell * t ≤ 4 := by
      rw [hleft_one]
      linarith
    change riemannianEDist I O (γ t) ≤ ENNReal.ofReal 4
    calc
      riemannianEDist I O (γ t) ≤
          riemannianEDist I O tail.p + riemannianEDist I tail.p (γ t) :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal tail.left + ENNReal.ofReal (tail.ell * t) :=
        add_le_add tail.left_edist.le hseg
      _ = ENNReal.ofReal (tail.left + tail.ell * t) :=
        (ENNReal.ofReal_add tail.left_nonneg hellt).symm
      _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal hreal
  have hu_pos : 0 < g.inner tail.p tail.u tail.u := by
    apply Real.sqrt_pos.mp
    rw [tail.u_norm]
    exact tail.ell_pos
  have hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm tail.p
        ((t • tail.u : TangentSpace I tail.p) : E) := by
    intro t ht
    exact tail.no_conj t ⟨ht.1, ht.2.trans hb_tail⟩
  have hRicSeed : 0 < Module.finrank Real E - 1 →
      ∀ t ∈ Set.Ioo (0 : Real) b,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) := by
    intro hd t ht
    exact hRic hd (γ t) (hball t ⟨ht.1.le, ht.2.le⟩)
      (curveVelocity (I := I) γ t)
  obtain ⟨w, hwLI, hwperp, hmean⟩ :=
    exists_intrMean_at_on (I := I) g hEnorm tail.p tail.u q s b
      hq hs hsb hu_pos hno hRicSeed
  dsimp only at hmean
  rw [tail.u_norm] at hmean
  have hsell : s * tail.ell = 1 := by
    dsimp only [s]
    field_simp [tail.ell_pos.ne']
  have hmean' :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s /
          tail.ell ≤ d + d * q := by
    dsimp only [d]
    rw [hsell, div_one] at hmean
    exact hmean
  have hmeanRaw :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s ≤
        (d + d * q) * tail.ell :=
    (div_le_iff₀ tail.ell_pos).1 hmean'
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm tail.p tail.u
  have hderivSeed :=
    deriv_comp_eq_inner_grad_velocity (I := I) g f.contMDiff hγInf s
  change deriv (f ∘ γ) s =
    g.inner (γ s) (gradFun (I := I) g f (γ s))
      (curveVelocity (I := I) γ s) at hderivSeed
  have hspeedSeed :
      Real.sqrt (g.inner (γ s) (curveVelocity (I := I) γ s)
        (curveVelocity (I := I) γ s)) = tail.ell := by
    have hspeed :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm tail.p tail.u s
    change g.inner (γ s) (curveVelocity (I := I) γ s)
      (curveVelocity (I := I) γ s) = g.inner tail.p tail.u tail.u at hspeed
    rw [hspeed, tail.u_norm]
  have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g (γ s)
    (gradFun (I := I) g f (γ s)) (curveVelocity (I := I) γ s)
  change |g.inner (γ s) (gradFun (I := I) g f (γ s))
      (curveVelocity (I := I) γ s)| ≤
    Real.sqrt (normGradSqFun (I := I) g f (γ s)) *
      Real.sqrt (g.inner (γ s) (curveVelocity (I := I) γ s)
        (curveVelocity (I := I) γ s)) at hcs
  rw [← hderivSeed, hspeedSeed] at hcs
  have hgradSeed : Real.sqrt (normGradSqFun (I := I) g f (γ s)) ≤ B :=
    hGrad (γ s) (hball s ⟨hs.le, hsb.le⟩)
  have hderivAbs : |deriv (f ∘ γ) s| ≤ B * tail.ell :=
    hcs.trans (mul_le_mul_of_nonneg_right hgradSeed tail.ell_pos.le)
  have hpotRaw : -deriv (f ∘ γ) s ≤ B * tail.ell :=
    (neg_le_abs _).trans hderivAbs
  have hanti :=
    gradientRicciSoliton_weightedMean_antitone
      (I := I) g hEnorm f σ hsol tail w hwLI hwperp hs
  dsimp only at hanti
  rw [tail.u_norm] at hanti
  have htransport := hanti ⟨le_rfl, hs_one⟩ ⟨hs_one, le_rfl⟩ hs_one
  have hseedSigma : σ / 2 * tail.ell ^ 2 * s = σ / 2 * tail.ell := by
    calc
      σ / 2 * tail.ell ^ 2 * s =
          σ / 2 * tail.ell * (s * tail.ell) := by ring
      _ = σ / 2 * tail.ell := by rw [hsell, mul_one]
  dsimp only at htransport
  rw [mul_one, hseedSigma] at htransport
  change curveMean (I := I) g γ
      (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
        deriv (f ∘ γ) 1 + σ / 2 * tail.ell ^ 2 ≤
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) s -
        deriv (f ∘ γ) s + σ / 2 * tail.ell at htransport
  have hendpointEll :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
          deriv (f ∘ γ) 1 ≤
        (d + d * q + B + σ / 2 - σ / 2 * tail.ell) * tail.ell := by
    nlinarith
  have hendpointRaw :
      curveMean (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.p tail.u (w i)) 1 -
          deriv (f ∘ γ) 1 ≤
        C * tail.ell - σ / 2 * r * tail.ell := by
    calc
      _ ≤ (d + d * q + B + σ / 2 - σ / 2 * tail.ell) * tail.ell :=
        hendpointEll
      _ = C * tail.ell - σ / 2 * r * tail.ell := by
        dsimp only [C]
        rw [hell_sub]
        ring
  obtain ⟨hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
      hgrad_norm, hlap_eq⟩ :=
    calabiData_of_tail_of_frame (I := I) g hEnorm tail w hwLI hwperp
  let rho : M → Real := fun y =>
    tail.left + branchRadius (I := I) g tail.branch y
  have hinner_eq := tail.inner_grad_support_eq_deriv f
  have hweighted :
      laplacian (I := I) (LeviCivita (I := I) g) g rho x -
          g.inner x (gradFun (I := I) g f x)
            (gradientFun (I := I) g rho x) ≤ C - σ / 2 * r := by
    rw [hlap_eq, hinner_eq]
    rw [← sub_div]
    apply (div_le_iff₀ tail.ell_pos).2
    calc
      _ ≤ C * tail.ell - σ / 2 * r * tail.ell := hendpointRaw
      _ = (C - σ / 2 * r) * tail.ell := by ring
  refine ⟨rho, hrho_inf, ?_, ?_, hrho_ev, hrho_grad,
    hgrad_norm, ?_⟩
  · simpa only [r] using hrho_x
  · simpa only [riemannianEDistOf] using hupper
  · simpa only [r] using hweighted

end DifferentialGeometry.Geometry
