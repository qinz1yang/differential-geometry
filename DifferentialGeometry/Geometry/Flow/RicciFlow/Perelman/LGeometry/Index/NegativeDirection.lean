import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Uniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ConjugatePoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Comparison.Variation.VelocityLocal
import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExtGlobal

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private theorem exists_neg_scale {k Q : Real} (hk : 0 < k) :
    ∃ s : Real, 2 * s * k + s ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let s : Real := -k / (|Q| + 1)
  have hsneg : s < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hk) hden
  have hsQ : |s * Q| < k := by
    simp only [s]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hk, abs_of_pos hden,
      div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 0 < 2 * k + s * Q := by
    linarith [(abs_lt.mp hsQ).1]
  refine ⟨s, ?_⟩
  calc
    2 * s * k + s ^ 2 * Q = s * (2 * k + s * Q) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hsneg hsum

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_lSplit_neg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a c b : Real)
    (hY : ∀ s ∈ Set.uIcc a c,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : ∀ s ∈ Set.uIcc a c,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hYYint : IntervalIntegrable (lRegIndexIntegrand S T alpha Y Y)
      MeasureTheory.volume a c)
    (hYWint : IntervalIntegrable (lRegIndexIntegrand S T alpha Y W)
      MeasureTheory.volume a c)
    (hWWac : IntervalIntegrable (lRegIndexIntegrand S T alpha W W)
      MeasureTheory.volume a c)
    (hWWcb : IntervalIntegrable (lRegIndexIntegrand S T alpha W W)
      MeasureTheory.volume c b)
    (hYY : lRegIndex S T alpha Y Y a c = 0)
    (hYW : 0 < lRegIndex S T alpha Y W a c) :
    ∃ k : Real,
      lRegIndex S T alpha (fun s ↦ Y s + k • W s)
          (fun s ↦ Y s + k • W s) a c +
        lRegIndex S T alpha (fun s ↦ k • W s)
          (fun s ↦ k • W s) c b < 0 := by
  let Q := lRegIndex S T alpha W W a b
  obtain ⟨k, hk⟩ := exists_neg_scale hYW (Q := Q)
  refine ⟨k, ?_⟩
  have hprefix := lRegIndex_add_smul_self (I := I) S T k alpha Y W a c hY hW
    hYYint hYWint hWWac
  have htail : lRegIndex S T alpha (fun s ↦ k • W s)
      (fun s ↦ k • W s) c b =
      k ^ 2 * lRegIndex S T alpha W W c b := by
    rw [lRegIndex_smul (I := I) S T k alpha W
        (fun s ↦ k • W s) c b,
      lRegIndex_smul_right (I := I) S T k alpha W W c b]
    ring
  have hjoin := lRegIndex_add_adjacent (I := I) S T alpha W W a c b hWWac hWWcb
  rw [hprefix, htail, hYY, zero_add]
  dsimp only [Q] at hk
  rw [← hjoin] at hk
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegJacobi_d_ne
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) {c : Real}
    (hcpos : 0 < c) (hc : c ∈ lRegDomain S T x Z)
    (hV : V ≠ 0)
    (hzero : lRegJacobiField S T x Z V c = 0) :
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
        (lRegCurve S T x Z) (lRegJacobiField S T x Z V) c ≠ 0 := by
  intro hDc
  let alpha : Real → M := lRegCurve S T x Z
  let Y : ∀ s, TangentSpace I (alpha s) :=
    lRegJacobiField S T x Z V
  let J : Set Real := lRegDomain S T x Z
  have hJopen : IsOpen J := lRegDomain_isOpen S T x Z
  have hJconn : IsPreconnected J := lRegDomain_preconn S T x Z
  have hcJ : c ∈ J := hc
  have h0J : (0 : Real) ∈ J := by
    exact lRegDomain_seg S T x Z hc le_rfl hcpos.le
  have hreg : ∀ s ∈ J, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegDomain_reg S T x Z hs
  let z : E := Z
  have hvel : ∀ s ∈ J, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    have hpair : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun r : Real ↦ (z, r)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hcurve : ContMDiffAt 𝓘(Real, Real) I ∞
        (lRegCurve S T x Z) s := by
      with_unfolding_all exact (lRegCurve_smooth S hS T x hs).comp s hpair
    simpa only [alpha, lVelocity] using
      velocity_rep_diffAt (I := I) (lRegCurve S T x Z) s
        hcurve
  have hY : IsLRegJacobi S T alpha Y J := by
    exact lRegCurve_jacobi S hS T x Z V J (fun _ hs ↦ hs)
  have hYsub : IsLRegJacobi S T alpha (fun r ↦ Y r - Y r) J :=
    hY.sub hJopen hY
  let g := S.base.metric (T - c ^ 2)
  have hYdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Y c) c :=
    (hY c hcJ).2.1
  have hnegdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ (-1 : Real) • Y r) c) c := by
    rw [chartRepAt_smul]
    exact hYdiff.const_smul (-1 : Real)
  have hDsub : covDerivAlong (I := I) g alpha
      (fun r ↦ Y r - Y r) c = 0 := by
    rw [show (fun r ↦ Y r - Y r) =
      (fun r ↦ Y r + (-1 : Real) • Y r) by
        funext r
        module]
    rw [covDerivAlong_add (I := I) g alpha Y
      (fun r ↦ (-1 : Real) • Y r) c hYdiff hnegdiff,
      covDerivAlong_smul]
    module
  have hfieldc : Y c = Y c - Y c := by
    dsimp only [Y]
    rw [hzero]
    simp
  have hDc' : covDerivAlong (I := I) g alpha Y c = 0 := by
    simpa only [g, alpha, Y] using hDc
  have heq : Set.EqOn Y (fun r ↦ Y r - Y r) J :=
    lRegJacobi_unique S hS T hJopen hJconn hcJ hreg hvel hY hYsub
      hfieldc (hDc'.trans hDsub.symm)
  have hzeroOn : ∀ s ∈ J, Y s = 0 := by
    intro s hs
    have hsEq := heq hs
    rw [hsEq]
    exact sub_self _
  have hEv : Y =ᶠ[𝓝 (0 : Real)]
      fun r ↦ (0 : TangentSpace I (alpha r)) := by
    filter_upwards [hJopen.mem_nhds h0J] with s hs
    exact hzeroOn s hs
  let g0 := S.base.metric T
  have hDEq : covDerivAlong (I := I) g0 alpha Y 0 =
      covDerivAlong (I := I) g0 alpha
        (fun r ↦ (0 : TangentSpace I (alpha r))) 0 :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g0 alpha hEv
  have hDzero : covDerivAlong (I := I) g0 alpha
      (fun r ↦ (0 : TangentSpace I (alpha r))) 0 = 0 := by
    rw [show (fun r ↦ (0 : TangentSpace I (alpha r))) =
      (fun r ↦ (0 : Real) • Y r) by
        funext r
        simp]
    rw [covDerivAlong_smul]
    simp
  have hDY0 : covDerivAlong (I := I) g0 alpha Y 0 = 0 :=
    hDEq.trans hDzero
  have hT : T ∈ D.regular := by
    simpa using hreg 0 h0J
  have hinit := lRegJacobi_d0 S hS T x Z V hT
  have hDY0' : covDerivAlong (I := I) (S.base.metric T)
      (lRegCurve S T x Z) (lRegJacobiField S T x Z V) 0 = 0 := by
    simpa only [g0, alpha, Y] using hDY0
  have htwo : (2 : Real) • V = 0 := hinit.symm.trans hDY0'
  have htwo_ne : (2 : Real) ≠ 0 := by norm_num
  exact hV ((smul_eq_zero.mp htwo).resolve_left htwo_ne)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_cross_pos
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (c b : Real) (hc0 : 0 < c) (hcb : c < b)
    (ht : ∀ s ∈ Set.uIcc (0 : Real) c, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc (0 : Real) c, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc (0 : Real) c, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegJacobi S T alpha Y (Set.uIcc (0 : Real) c))
    (hW : ∀ s ∈ Set.uIcc (0 : Real) c, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegIndexIntegrand S T alpha Y W)
      MeasureTheory.volume 0 c)
    (hW0 : W 0 = 0)
    (hWc : W c = (c * (b - c)) •
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c)
    (hDne : covDerivAlong (I := I)
      (S.base.metric (T - c ^ 2)) alpha Y c ≠ 0) :
    0 < lRegIndex S T alpha Y W 0 c := by
  let P : TangentSpace I (alpha c) :=
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c
  have hPc : 0 < (S.base.metric (T - c ^ 2)).inner (alpha c) P P :=
    (S.base.metric (T - c ^ 2)).pos (alpha c) P (by
      simpa only [P] using hDne)
  have hscale : 0 < c * (b - c) := mul_pos hc0 (sub_pos.mpr hcb)
  have hgreen := lRegIndex_eq_half_boundary_of_isLRegJacobi (I := I) S hS T alpha Y W 0 c ht
    halpha hA hjac hW hIint
  rw [hgreen, hW0, hWc]
  simp only [map_zero, sub_zero]
  change 0 < (1 / 2 : Real) *
    ((S.base.metric (T - c ^ 2)).inner (alpha c) P
      ((c * (b - c)) • P))
  rw [((S.base.metric (T - c ^ 2)).inner (alpha c) P).map_smul]
  positivity

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lIndex_neg_conj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {sigma tau : Real}
    (htau : (Z, tau) ∈ lExpPosDom S T x)
    (hlt : sigma < tau) (hconj : IsLConj S T x Z sigma) :
    ∃ gamma : Real → M, ∃ Y0 Y1 : Real → E,
      Set.EqOn gamma (lRegCurve S T x Z)
        (Set.Icc 0 (Real.sqrt tau)) ∧
      IsLRegCurveOn S T gamma
        (Set.uIcc 0 (Real.sqrt tau)) x Z ∧
      ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (gamma s) (Y0 s) : TangentBundle I M)) ∧
      ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (gamma s) (Y1 s) : TangentBundle I M)) ∧
      Y0 0 = 0 ∧ Y1 (Real.sqrt tau) = 0 ∧
      Y0 (Real.sqrt sigma) = Y1 (Real.sqrt sigma) ∧
      lRegIndex S T gamma Y0 Y0 0 (Real.sqrt sigma) +
        lRegIndex S T gamma Y1 Y1
          (Real.sqrt sigma) (Real.sqrt tau) < 0 := by
  let alpha : Real → M := lRegCurve S T x Z
  let c : Real := Real.sqrt sigma
  let b : Real := Real.sqrt tau
  obtain ⟨hsdom, V, hVne, hJc⟩ :=
    (isLConj_iff_jac (I := I) S T x Z sigma).1 hconj
  have hspos : 0 < sigma :=
    ((mem_lExpPosDom (I := I) S T x Z sigma).1 hsdom).1
  have htpos : 0 < tau :=
    ((mem_lExpPosDom (I := I) S T x Z tau).1 htau).1
  have hc0 : 0 < c := by
    simpa only [c] using Real.sqrt_pos.2 hspos
  have hb0 : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htpos
  have hcb : c < b := by
    simpa only [c, b] using Real.sqrt_lt_sqrt hspos.le hlt
  have hcdom : c ∈ lRegDomain S T x Z := by
    simpa only [c] using
      ((mem_lExpPosDom (I := I) S T x Z sigma).1 hsdom).2.2
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using
      ((mem_lExpPosDom (I := I) S T x Z tau).1 htau).2.2
  let J : (s : Real) → TangentSpace I (alpha s) :=
    lRegJacobiField S T x Z V
  let P : TangentSpace I (alpha c) :=
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha J c
  have hPne : P ≠ 0 := by
    simpa only [P, alpha, J] using
      lRegJacobi_d_ne (I := I) S hS T x Z V hc0 hcdom hVne
        (by simpa only [c] using hJc)
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrhoEq, _hrhoDeriv,
      _hrhoRange, hJgSmooth, _hpairEq⟩ :=
    exists_lRay_germ (I := I) S hS T x Z V hb0 hbdom
  let gamma : Real → M := fun s ↦ alpha (rho s)
  let Jg : (s : Real) → TangentSpace I (gamma s) := fun s ↦ J (rho s)
  have hseg : Set.Icc (0 : Real) b ⊆ Set.Ioo a d := by
    intro s hs
    exact ⟨ha0.trans_le hs.1, hs.2.trans_lt hbd⟩
  have hrhoGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      rho =ᶠ[nhds s] id := by
    intro s hs
    have hsad := hseg hs
    filter_upwards [Ioo_mem_nhds hsad.1 hsad.2] with r hr
    exact hrhoEq ⟨hr.1.le, hr.2.le⟩
  have hgammaGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      gamma =ᶠ[nhds s] alpha := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    simp only [gamma, id_eq, hr]
  have hJgGerm : ∀ s ∈ Set.Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Jg r : E) = (J r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (J (rho r) : E) = (J r : E)
    exact congrArg (fun q : Real ↦ (J q : E)) (by
      simpa only [id_eq] using hr)
  have hgammaEq : Set.EqOn gamma alpha (Set.Icc (0 : Real) b) := by
    intro s hs
    exact (hgammaGerm s hs).self_of_nhds
  have hJgSmooth' : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (Jg s) : TangentBundle I M)) := by
    simpa only [gamma, Jg, alpha, J] using hJgSmooth
  have hgammaSmooth : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    intro s
    exact (Bundle.contMDiffAt_totalSpace.mp hJgSmooth'.contMDiffAt).1
  have hgeoRaw := lRegCurve_isReg (I := I) S hS T x Z hb0 hbdom
  have hgeo : IsLRegCurveOn S T gamma (Set.uIcc (0 : Real) b) x Z := by
    have h0Icc : (0 : Real) ∈ Set.Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
    have h0germ := hgammaGerm 0 h0Icc
    refine ⟨?_, ?_, ?_⟩
    · exact (h0germ.self_of_nhds).trans hgeoRaw.1
    · have hvel : lVelocity (I := I) gamma 0 =
          lVelocity (I := I) alpha 0 := by
        unfold lVelocity
        rw [h0germ.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
        rfl
      exact hvel.trans hgeoRaw.2.1
    · intro s hs
      have hsIcc : s ∈ Set.Icc (0 : Real) b := by
        simpa only [Set.uIcc_of_le hb0.le] using hs
      exact lRegData_congr S T s (hgammaGerm s hsIcc)
        (hgeoRaw.2.2 s hs)
  obtain ⟨W, hWsmooth, hW0, hWb, hWc⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_contMDiff_vectorFieldAlong_zero_endpoints
      (I := I) gamma hgammaSmooth 0 c b P
  have hreg0c : ∀ s ∈ Set.uIcc (0 : Real) c,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) c := by
      simpa only [Set.uIcc_of_le hc0.le] using hs
    have hsBig : s ∈ Set.uIcc (0 : Real) b := by
      rw [Set.uIcc_of_le hb0.le]
      exact ⟨hs'.1, hs'.2.trans hcb.le⟩
    exact (hgeo.2.2 s hsBig).1
  have hregcb : ∀ s ∈ Set.uIcc c b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs' : s ∈ Set.Icc c b := by
      simpa only [Set.uIcc_of_le hcb.le] using hs
    have hsBig : s ∈ Set.uIcc (0 : Real) b := by
      rw [Set.uIcc_of_le hb0.le]
      exact ⟨hc0.le.trans hs'.1, hs'.2⟩
    exact (hgeo.2.2 s hsBig).1
  have hJ2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (Jg s) : TangentBundle I M)) :=
    hJgSmooth'.of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hW2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (W s) : TangentBundle I M)) :=
    hWsmooth.of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hJJgInt := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 c gamma Jg Jg
    hJ2 hJ2 hreg0c
  have hJWgInt := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 c gamma Jg W
    hJ2 hW2 hreg0c
  have hWW0c := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T 0 c gamma W W
    hW2 hW2 hreg0c
  have hWWcb := intervalIntegrable_lRegIndexIntegrand_of_contMDiff (I := I) S hS T c b gamma W W
    hW2 hW2 hregcb
  have hprefixIcc : Set.Icc (0 : Real) c ⊆ Set.Icc (0 : Real) b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hcb.le⟩
  have hAlphaGerm : ∀ s ∈ Set.Ioo (0 : Real) c,
      alpha =ᶠ[nhds s] gamma := by
    intro s hs
    exact (hgammaGerm s (hprefixIcc ⟨hs.1.le, hs.2.le⟩)).symm
  have hJGerm : ∀ s ∈ Set.Ioo (0 : Real) c,
      ∀ᶠ r in nhds s, (J r : E) = (Jg r : E) := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hJgGerm s (hprefixIcc ⟨hs.1.le, hs.2.le⟩))
  have hWGerm : ∀ s ∈ Set.Ioo (0 : Real) c,
      ∀ᶠ r in nhds s, (W r : E) = (W r : E) :=
    fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl
  have hJJInt : IntervalIntegrable (lRegIndexIntegrand S T alpha J J)
      MeasureTheory.volume 0 c :=
    (intervalIntegrable_lRegIndexIntegrand_congr_of_eventuallyEq (I := I) S T J J Jg Jg 0 c hc0.le
      hAlphaGerm hJGerm hJGerm).2 hJJgInt
  have hJWInt : IntervalIntegrable (lRegIndexIntegrand S T alpha J W)
      MeasureTheory.volume 0 c :=
    (intervalIntegrable_lRegIndexIntegrand_congr_of_eventuallyEq (I := I) S T J W Jg W 0 c hc0.le
      hAlphaGerm hJGerm hWGerm).2 hJWgInt
  have hAlphaMdiff : ∀ s ∈ Set.uIcc (0 : Real) c,
      ∀ᶠ r in nhds s,
        MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : Real) c := by
      simpa only [Set.uIcc_of_le hc0.le] using hs
    have hsdom : s ∈ lRegDomain S T x Z :=
      lRegDomain_seg S T x Z hcdom hsIcc.1 hsIcc.2
    filter_upwards [(lRegDomain_isOpen S T x Z).mem_nhds hsdom] with r hr
    let z : E := Z
    have hpair : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun q : Real ↦ (z, q)) r :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hcurve : ContMDiffAt 𝓘(Real, Real) I ∞ alpha r := by
      with_unfolding_all exact
        (lRegCurve_smooth S hS T x hr).comp r hpair
    exact hcurve.mdifferentiableAt (by simp)
  have hA : ∀ s ∈ Set.uIcc (0 : Real) c, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) c := by
      simpa only [Set.uIcc_of_le hc0.le] using hs
    have hsBig : s ∈ Set.uIcc (0 : Real) b := by
      rw [Set.uIcc_of_le hb0.le]
      exact ⟨hs'.1, hs'.2.trans hcb.le⟩
    simpa only [alpha] using (hgeoRaw.2.2 s hsBig).2.2.1
  have hJac : IsLRegJacobi S T alpha J (Set.uIcc (0 : Real) c) := by
    simpa only [alpha, J] using lRegCurve_jacobi S hS T x Z V
      (Set.uIcc (0 : Real) c) (fun s hs ↦ by
        have hs' : s ∈ Set.Icc (0 : Real) c := by
          simpa only [Set.uIcc_of_le hc0.le] using hs
        exact lRegDomain_seg S T x Z hcdom hs'.1 hs'.2)
  have hJdiff : ∀ s ∈ Set.uIcc (0 : Real) c,
      DifferentiableAt Real (chartRepAt (I := I) alpha J s) s := by
    intro s hs
    exact (hJac s hs).2.1
  have hWdiff : ∀ s ∈ Set.uIcc (0 : Real) c,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) c := by
      simpa only [Set.uIcc_of_le hc0.le] using hs
    have hrep :=
      DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
        (I := I) W W (hgammaGerm s (hprefixIcc hs')).symm
          (Eventually.of_forall fun _ ↦ rfl)
    exact hrep.differentiableAt_iff.mpr
      (chartRep_diff (I := I) gamma W hWsmooth s)
  have hYY : lRegIndex S T alpha J J 0 c = 0 := by
    have hgreen := lRegIndex_eq_half_boundary_of_isLRegJacobi (I := I) S hS T alpha J J 0 c
      hreg0c hAlphaMdiff hA hJac hJdiff hJJInt
    rw [hgreen]
    have hJ0 : J 0 = 0 := by
      simpa only [J, alpha] using lRegJacobi_zero S T x Z V
    have hJc' : J c = 0 := by
      simpa only [J, c] using hJc
    rw [hJ0, hJc']
    simp
  have hWc' : W c = (c * (b - c)) • P := by
    rw [sub_zero] at hWc
    with_unfolding_all exact hWc
  have hYW : 0 < lRegIndex S T alpha J W 0 c :=
    lIndex_cross_pos (I := I) S hS T alpha J W c b hc0 hcb
      hreg0c hAlphaMdiff hA hJac hWdiff hJWInt hW0
      (by with_unfolding_all exact hWc') hPne
  have hYYeq : lRegIndex S T alpha J J 0 c =
      lRegIndex S T gamma Jg Jg 0 c := by
    apply lRegIndex_congr_of_eventuallyEq (I := I) S T J J Jg Jg
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) c := by
        simpa only [Set.uIoo_of_le hc0.le] using hs
      exact hAlphaGerm s hs'
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) c := by
        simpa only [Set.uIoo_of_le hc0.le] using hs
      exact hJGerm s hs'
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) c := by
        simpa only [Set.uIoo_of_le hc0.le] using hs
      exact hJGerm s hs'
  have hYWeq : lRegIndex S T alpha J W 0 c =
      lRegIndex S T gamma Jg W 0 c := by
    apply lRegIndex_congr_of_eventuallyEq (I := I) S T J W Jg W
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) c := by
        simpa only [Set.uIoo_of_le hc0.le] using hs
      exact hAlphaGerm s hs'
    · intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) c := by
        simpa only [Set.uIoo_of_le hc0.le] using hs
      exact hJGerm s hs'
    · intro s hs
      exact Eventually.of_forall fun _ ↦ rfl
  have hJgdiff : ∀ s ∈ Set.uIcc (0 : Real) c,
      DifferentiableAt Real (chartRepAt (I := I) gamma Jg s) s :=
    fun s _ ↦ chartRep_diff (I := I) gamma Jg hJgSmooth' s
  have hWgdiff : ∀ s ∈ Set.uIcc (0 : Real) c,
      DifferentiableAt Real (chartRepAt (I := I) gamma W s) s :=
    fun s _ ↦ chartRep_diff (I := I) gamma W hWsmooth s
  obtain ⟨k, hk⟩ := exists_lSplit_neg (I := I) S T gamma Jg W 0 c b
    hJgdiff hWgdiff hJJgInt hJWgInt hWW0c hWWcb
    (hYYeq ▸ hYY) (hYWeq ▸ hYW)
  let JgE : Real → E := fun s ↦ Jg s
  let Y0 : Real → E := fun s ↦ JgE s + k • W s
  let Y1 : Real → E := fun s ↦ k • W s
  have hkW : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (Y1 s) : TangentBundle I M)) := by
    with_unfolding_all exact
      (contMDiff_const (c := k)).smul_bundle hWsmooth
  have hY0smooth : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (Y0 s) : TangentBundle I M)) := by
    with_unfolding_all exact hJgSmooth'.add_bundle hkW
  have hJg0 : Jg 0 = 0 := by
    have h0 : (0 : Real) ∈ Set.Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
    rw [(hJgGerm 0 h0).self_of_nhds]
    exact lRegJacobi_zero S T x Z V
  have hJgc : Jg c = 0 := by
    rw [(hJgGerm c (hprefixIcc ⟨hc0.le, le_rfl⟩)).self_of_nhds]
    with_unfolding_all exact hJc
  have hJgE0 : JgE 0 = 0 := hJg0
  have hJgEc : JgE c = 0 := hJgc
  refine ⟨gamma, Y0, Y1, ?_, hgeo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [alpha, b] using hgammaEq
  · exact hY0smooth.of_le (by decide :
      (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  · exact hkW.of_le (by decide :
      (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  · change JgE 0 + k • W 0 = 0
    rw [hJgE0, hW0, smul_zero, add_zero]
  · change k • W b = 0
    rw [hWb, smul_zero]
  · change JgE c + k • W c = k • W c
    rw [hJgEc, zero_add]
  · with_unfolding_all exact hk

end DifferentialGeometry.PDE.RicciFlow.Perelman
