import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Uniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ConjugatePoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.JacobiCrossTerm
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.LocalVelocity
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

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem exists_lRegIndex_split_lt_zero_of_isLConj
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
      covDerivAlong_lRegJacobiField_ne_zero (I := I) S hS T x Z V hc0 hcdom hVne
        (by simpa only [c] using hJc)
  obtain ⟨rho, a, d, ha0, hbd, hrho, hrhoEq, _hrhoDeriv,
      _hrhoRange, hJgSmooth, _hpairEq⟩ :=
    exists_lRegJacobiField_smoothGerm (I := I) S hS T x Z V hb0 hbdom
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
  have hgeoRaw := lRegCurve_isLRegCurveOn (I := I) S hS T x Z hb0 hbdom
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
    lRegIndex_cross_pos_of_isLRegJacobi (I := I) S hS T alpha J W c b hc0 hcb
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
  obtain ⟨k, hk⟩ := exists_lRegIndex_split_lt_zero_of_cross_pos
    (I := I) S T gamma Jg W 0 c b
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
