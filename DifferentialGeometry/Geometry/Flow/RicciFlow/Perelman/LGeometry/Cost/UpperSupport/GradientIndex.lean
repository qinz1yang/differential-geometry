import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.EndpointGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.Hessian


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe uM uEM uHM

variable {EM : Type uEM} [NormedAddCommGroup EM]
  [InnerProductSpace Real EM] [FiniteDimensional Real EM]
  [NeZero (Module.finrank Real EM)]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {IM : ModelWithCorners Real EM HM} [IM.Boundaryless]
variable {MM : Type uM} [PseudoMetricSpace MM] [ChartedSpace HM MM]
  [IsManifold IM ∞ MM] [T2Space MM] [SigmaCompactSpace MM]
variable {DM : RealTimeInterval}

omit [NeZero (Module.finrank ℝ EM)] [SigmaCompactSpace MM] in
theorem exists_contMDiffOn_lCost_upper_support_gradient_hess_le_index
    (S : SolutionOn (I := IM) (M := MM) DM)
    (hS : IsSolutionOn (I := IM) S) (K T : Real) (x : MM)
    {Z : TangentSpace IM x} {tau s0 : Real}
    (hmin : (Z, tau) ∈ lMinDomain (E := EM) (I := IM) S T x)
    (hreg : Icc (T - tau) T ⊆ DM.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : MM,
      normSq0S (I := IM) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (hs00 : 0 < s0) (hs0b : s0 < Real.sqrt tau) :
    ∃ U : Set MM, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ∃ F : MM → Real,
        ContMDiffOn IM 𝓘(Real, Real) ∞ F U ∧
          F (lExp S T x Z tau) =
            lCost S T x (lExp S T x Z tau) tau ∧
          (∀ y ∈ U, lCost S T x y tau ≤ F y) ∧
          gradientFun (I := IM) (S.base.metric (T - tau)) F
            (lExp S T x Z tau) =
              lVelocity (I := IM) (lRegularizedCurve S T x Z) (Real.sqrt tau) ∧
          ∀ (W : ∀ s, TangentSpace IM (lRegularizedCurve S T x Z s))
            (Omega : Set Real), IsOpen Omega →
            Icc (0 : Real) (Real.sqrt tau) ⊆ Omega →
            ContMDiffOn 𝓘(Real, Real) IM.tangent (8 : Nat)
              (fun s : Real ↦
                (TotalSpace.mk' EM (E := (TangentSpace IM : MM → Type _))
                  (lRegularizedCurve S T x Z s) (W s) :
                    TangentBundle IM MM)) Omega →
            W s0 = 0 →
            hessFun (I := IM) (S.base.metric (T - tau)) F
                (lExp S T x Z tau) (W (Real.sqrt tau)) (W (Real.sqrt tau)) ≤
              2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
                s0 (Real.sqrt tau) := by
  let gamma : Real → MM := lRegularizedCurve S T x Z
  let b : Real := Real.sqrt tau
  let x0 : MM := gamma s0
  let A0 : TangentSpace IM x0 := lVelocity (I := IM) gamma s0
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb0 : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hs0b' : s0 < b := by simpa only [b] using hs0b
  obtain ⟨V, hVopen, hA0V, Ktime, hKopen, hKconn, h0K, hs0K,
      hbK, alpha, halpha, hcurves, hinj⟩ :=
    exists_lRegularizedGeodesicFamily_with_injective_endpoint_mfderiv
      (E := EM) (I := IM) S hS K T x hmin hreg hRm
      hs00 hs0b
  have hbdom : b ∈ lRegularizedDomain S T x Z := by
    have hpos : (Z, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z tau).1 hmin).1
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hpos).2.2
  let J : Set Real := lRegularizedDomain S T x Z
  have hJopen : IsOpen J := by
    simpa only [J] using lRegularizedDomain_isOpen S T x Z
  have hJconn : IsPreconnected J := by
    simpa only [J] using lRegularizedDomain_preconn S T x Z
  have h0J : 0 ∈ J := by
    simpa only [J] using lRegularizedDomain_segment S T x Z hbdom le_rfl hb0.le
  have hs0J : s0 ∈ J := by
    simpa only [J] using
      lRegularizedDomain_segment S T x Z hbdom hs00.le hs0b'.le
  have hbJ : b ∈ J := by simpa only [J] using hbdom
  have hgamma : IsLRegularizedGeodesicOn S T gamma J := by
    intro r hr
    have hrdom : r ∈ lRegularizedDomain S T x Z := by simpa only [J] using hr
    obtain ⟨L, hLopen, hLconn, h0L, hrL, hchosen⟩ :=
      lRegularizedChosen_spec S T x Z hrdom
    have heqOn : Set.EqOn gamma (lRegularizedChosen S T x Z hrdom) L := by
      simpa only [gamma] using
        lRegularizedCurve_eqOn S hS T hLopen hLconn h0L hchosen
    have heq : gamma =ᶠ[nhds r] lRegularizedChosen S T x Z hrdom :=
      heqOn.eventuallyEq_of_mem (hLopen.mem_nhds hrL)
    exact lRegularizedData_congr S T r heq (hchosen.2.2 r hrL)
  have hcenterEq : Set.EqOn (fun r ↦ alpha (A0, r)) gamma
      (Ktime ∩ J) :=
    lRegularizedSolution_eqOn S hS T hKopen hKconn hs0K hJopen hJconn hs0J
      (hcurves A0 hA0V).2.2 hgamma
      (by simpa only [x0] using (hcurves A0 hA0V).1)
      (by simpa only [A0] using (hcurves A0 hA0V).2.1)
  have hsegK : Icc (0 : Real) b ⊆ Ktime :=
    hKconn.ordConnected.out h0K hbK
  have hsegJ : Icc (0 : Real) b ⊆ J :=
    hJconn.ordConnected.out h0J hbJ
  have hcenterEnd : alpha (A0, b) = lExp S T x Z tau := by
    calc
      alpha (A0, b) = gamma b := hcenterEq ⟨hbK, hbJ⟩
      _ = lExp S T x Z tau := by simp only [gamma, b, lExp]
  let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
    hVopen hA0V hbK halpha hinj
  have hregFamily : ∀ q ∈ V ×ˢ Ktime, T - q.2 ^ 2 ∈ DM.regular := by
    intro q hq
    exact ((hcurves q.1 hq.1).2.2 q.2 hq.2).1
  obtain ⟨U0, hU0open, hzU0, F0, hF0smooth, hF0eq⟩ :=
    exists_contMDiffOn_lRegularizedAction_endpointBranch
      S hS T s0 b hs0b' hVopen hA0V hKopen
      hKconn hs0K hbK halpha hregFamily hinj
  rw [hcenterEnd] at hzU0
  let U : Set MM := U0 ∩
    (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V)
  have hbranchOpen : IsOpen
      (hloc.localInverse.source ∩ hloc.localInverse ⁻¹' V) :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hVopen
  have hUopen : IsOpen U := hU0open.inter hbranchOpen
  have hzSource : lExp S T x Z tau ∈ hloc.localInverse.source := by
    rw [← hcenterEnd]
    exact hloc.localInverse_mem_source
  have hinv0 : hloc.localInverse (lExp S T x Z tau) = A0 := by
    rw [← hcenterEnd]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hzU : lExp S T x Z tau ∈ U := by
    refine ⟨hzU0, hzSource, ?_⟩
    change hloc.localInverse (lExp S T x Z tau) ∈ V
    rw [hinv0]
    exact hA0V
  let F : MM → Real := fun y ↦ lRegularizedAction S T gamma 0 s0 + F0 y
  have hFsmooth : ContMDiffOn IM 𝓘(Real, Real) ∞ F U := by
    exact contMDiffOn_const.add
      (hF0smooth.mono fun _ hy ↦ hy.1)
  have hregSq : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ DM.regular := by
    intro s hs
    apply hreg
    rw [← hb2]
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  have hRmSq : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : MM,
      normSq0S (I := IM) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hb2] using hRm
  have hgammaC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc (0 : Real) b) := by
    simpa only [gamma] using lRegularizedCurve_c1On S hS T x Z hbdom
  have hheadC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc (0 : Real) s0) :=
    hgammaC1.mono fun s hs ↦ ⟨hs.1, hs.2.trans hs0b'.le⟩
  have htailC1 : ContMDiffOn 𝓘(Real, Real) IM 1 gamma
      (Icc s0 b) :=
    hgammaC1.mono fun s hs ↦ ⟨hs00.le.trans hs.1, hs.2⟩
  have hheadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
    (I := IM) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T 0 s0 hs00.le gamma hheadC1
    (fun s hs ↦ hregSq s ⟨hs.1, hs.2.trans hs0b'.le⟩)
  have htailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
    (I := IM) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T s0 b hs0b'.le gamma htailC1
    (fun s hs ↦ hregSq s ⟨hs00.le.trans hs.1, hs.2⟩)
  have hactionAdd := lRegularizedAction_add (I := IM) S T gamma 0 s0 b
    hheadInt htailInt
  have htailEq : lRegularizedAction S T (fun r ↦ alpha (A0, r)) s0 b =
      lRegularizedAction S T gamma s0 b := by
    apply lRegularizedAction_congr (I := IM) S T
    intro s hs
    have hs' : s ∈ Ioo s0 b := by
      simpa only [uIoo_of_le hs0b'.le] using hs
    have hsI : s ∈ Icc (0 : Real) b :=
      ⟨hs00.le.trans hs'.1.le, hs'.2.le⟩
    exact hcenterEq ⟨hsegK hsI, hsegJ hsI⟩
  have hfullCost : lRegularizedAction S T gamma 0 b =
      lCost S T x (lExp S T x Z tau) tau := by
    have hvec := (mem_lMinDomain S T x Z tau).1 hmin
    calc
      lRegularizedAction S T gamma 0 b =
          lLength S T (squareRootReparametrization gamma) 0 tau := by
        simpa only [gamma, b] using
          (lLength_squareRootReparametrization_eq_lRegularizedAction
            (I := IM) S T gamma tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := by
        change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau =
          lCost S T x (lRegularizedCurve S T x Z (Real.sqrt tau)) tau
        exact hvec.2
  have hF0center := hF0eq (lExp S T x Z tau) hzU0
  have hFcenter : F (lExp S T x Z tau) =
      lCost S T x (lExp S T x Z tau) tau := by
    rw [show F (lExp S T x Z tau) =
      lRegularizedAction S T gamma 0 s0 + F0 (lExp S T x Z tau) by rfl,
      hF0center]
    simp only [hinv0]
    rw [htailEq, hactionAdd, hfullCost]
  have hstart : ∀ A ∈ V, alpha (A, s0) = alpha (A0, s0) := by
    intro A hA
    exact (hcurves A hA).1.trans (hcurves A0 hA0V).1.symm
  obtain ⟨G, _, hcenterG, _, _, _, hbranchGrad⟩ :=
    exists_gradient_lRegularizedAction_endpointBranch
      (I := IM) S hS T s0 b hs0b' hVopen hA0V hKopen hKconn hs0K hbK
      hstart halpha hregFamily
      (fun A hA s hs ↦ (hcurves A hA).2.2 s (hsegK ⟨hs00.le.trans hs.1, hs.2⟩)
        |>.2.2.2) hinj
  have hgrad0 := hbranchGrad (alpha (A0, b)) hcenterG
  change gradientFun (I := IM) (S.base.metric (T - b ^ 2))
    (fun y ↦ lRegularizedAction S T (fun s ↦ alpha (hloc.localInverse y, s)) s0 b)
    (alpha (A0, b)) = lVelocity (I := IM)
      (fun s ↦ alpha (hloc.localInverse (alpha (A0, b)), s)) b at hgrad0
  rw [hloc.localInverse_left_inv hloc.localInverse_mem_target] at hgrad0
  rw [hb2, hcenterEnd] at hgrad0
  have hcenterGerm : (fun s ↦ alpha (A0, s)) =ᶠ[nhds b] gamma :=
    hcenterEq.eventuallyEq_of_mem ((hKopen.inter hJopen).mem_nhds ⟨hbK, hbJ⟩)
  have hvelocity : lVelocity (I := IM) (fun s ↦ alpha (A0, s)) b =
      lVelocity (I := IM) gamma b := by
    unfold lVelocity
    rw [hcenterGerm.mfderiv_eq (I := 𝓘(Real, Real)) (I' := IM)]
    rfl
  have hF0germ : F0 =ᶠ[nhds (lExp S T x Z tau)]
      (fun y ↦ lRegularizedAction S T
        (fun s ↦ alpha (hloc.localInverse y, s)) s0 b) := by
    filter_upwards [hU0open.mem_nhds hzU0] with y hy
    exact hF0eq y hy
  have hgradF0 : gradientFun (I := IM) (S.base.metric (T - tau)) F0
      (lExp S T x Z tau) = gradientFun (I := IM) (S.base.metric (T - tau))
        (fun y ↦ lRegularizedAction S T
          (fun s ↦ alpha (hloc.localInverse y, s)) s0 b) (lExp S T x Z tau) := by
    have hmv : (mvfderiv (I := IM) F0 (lExp S T x Z tau)).toLinearMap =
        (mvfderiv (I := IM) (fun y ↦ lRegularizedAction S T
          (fun s ↦ alpha (hloc.localInverse y, s)) s0 b) (lExp S T x Z tau)).toLinearMap := by
      apply LinearMap.ext
      intro Y
      change mvfderiv (I := IM) F0 (lExp S T x Z tau) Y =
        mvfderiv (I := IM) (fun y ↦ lRegularizedAction S T
          (fun s ↦ alpha (hloc.localInverse y, s)) s0 b) (lExp S T x Z tau) Y
      rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv,
        DifferentialGeometry.mvfderiv_real_eq_mfderiv,
        hF0germ.mfderiv_eq (I := IM) (I' := 𝓘(Real, Real))]
      rw [hF0germ.self_of_nhds]
      simp [tangentSpaceCast]
    exact congrArg (metricSharp (I := IM) (S.base.metric (T - tau))
      (lExp S T x Z tau)) hmv
  have hF0diff : MDifferentiableAt IM 𝓘(Real, Real) F0 (lExp S T x Z tau) :=
    (hF0smooth (lExp S T x Z tau) hzU0).contMDiffAt (hU0open.mem_nhds hzU0)
      |>.mdifferentiableAt (by simp)
  have hgradF : gradientFun (I := IM) (S.base.metric (T - tau)) F
      (lExp S T x Z tau) = lVelocity (I := IM) gamma b := by
    change gradientFun (I := IM) (S.base.metric (T - tau))
      (fun y ↦ lRegularizedAction S T gamma 0 s0 + F0 y) (lExp S T x Z tau) = _
    rw [gradientFun_add _ mdifferentiableAt_const hF0diff,
      gradientFun_const, zero_add, hgradF0]
    exact hgrad0.trans hvelocity
  refine ⟨U, hUopen, hzU, F, hFsmooth, hFcenter, ?_, hgradF, ?_⟩
  · intro y hy
    have hy0 : y ∈ U0 := hy.1
    have hySource : y ∈ hloc.localInverse.source := hy.2.1
    have hyV : hloc.localInverse y ∈ V := hy.2.2
    let A : EM := hloc.localInverse y
    let beta : Real → MM := fun s ↦ alpha (A, s)
    have hbetaInf : ContMDiffOn 𝓘(Real, Real) IM ∞ beta
        (Icc s0 b) := by
      have hpair : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, EM).prod 𝓘(Real, Real)) ∞
          (fun s : Real ↦ (A, s)) := contMDiff_const.prodMk contMDiff_id
      apply halpha.comp hpair.contMDiffOn
      intro s hs
      exact ⟨by simpa only [A] using hyV,
        hsegK ⟨hs00.le.trans hs.1, hs.2⟩⟩
    have hbeta : ContMDiffOn 𝓘(Real, Real) IM 1 beta
        (Icc s0 b) := hbetaInf.of_le (by norm_num)
    have hnode : gamma s0 = beta s0 := by
      simpa only [beta, A, x0] using
        ((hcurves (hloc.localInverse y) hyV).1).symm
    have hend : beta b = y := by
      simpa only [beta, A, hloc] using
        hloc.localInverse_right_inv hySource
    have hbdd := lRegularizedCosts_bdd_rm (I := IM) S hS K T 0 b
      (by norm_num) hb0.le (by simpa only [hb2] using hreg) hRmSq x y
    have hle := lCost_le_join_bdd (I := IM) S hS T b hb0 x y
      hs00 hs0b' hbdd hregSq gamma beta hheadC1 hbeta hnode
      (by simpa only [gamma] using lRegularizedCurve_zero S T x Z) hend
    have hF0y := hF0eq y hy0
    change lCost S T x y tau ≤
      lRegularizedAction S T gamma 0 s0 + F0 y
    rw [hF0y]
    simpa only [hloc, A, beta, hb2] using hle
  · intro W Omega hOmega hOmegaSegment hW hWa
    let beta : Real → MM := fun s ↦ alpha (A0, s)
    let Wb : ∀ s, TangentSpace IM (beta s) := fun s ↦ (W s : EM)
    let Omega' : Set Real := (Ktime ∩ J) ∩ Omega
    have hOmega' : IsOpen Omega' := (hKopen.inter hJopen).inter hOmega
    have hOmega'Segment : Icc (0 : Real) b ⊆ Omega' := by
      intro s hs
      exact ⟨⟨hsegK hs, hsegJ hs⟩, hOmegaSegment hs⟩
    have hWb : ContMDiffOn 𝓘(Real, Real) IM.tangent (8 : Nat)
        (fun s : Real ↦
          (TotalSpace.mk' EM (E := (TangentSpace IM : MM → Type _))
            (beta s) (Wb s) : TangentBundle IM MM)) Omega' := by
      apply (hW.mono (fun s hs ↦ hs.2)).congr
      intro s hs
      have heq : beta s = gamma s := hcenterEq hs.1
      change (TotalSpace.mk' EM (beta s) (Wb s) : TangentBundle IM MM) =
        TotalSpace.mk' EM (gamma s) (W s)
      dsimp only [Wb]
      rw [heq]
    have hcenter : ∀ s ∈ Icc (0 : Real) b, beta =ᶠ[nhds s] gamma := by
      intro s hs
      exact hcenterEq.eventuallyEq_of_mem
        ((hKopen.inter hJopen).mem_nhds ⟨hsegK hs, hsegJ hs⟩)
    have hgeo : IsLRegularizedCurveOn S T gamma (uIcc (0 : Real) b) x Z := by
      simpa only [gamma] using
        lRegularizedCurve_isLRegularizedCurveOn (I := IM) S hS T x Z hb0 hbdom
    have hminGamma : ∀ delta : Real → MM,
        ContMDiff 𝓘(Real, Real) IM 1 delta →
        delta 0 = gamma 0 → delta b = gamma b →
        lRegularizedAction S T gamma 0 b ≤ lRegularizedAction S T delta 0 b := by
      intro delta hdelta hd0 hdb
      simpa only [gamma, b] using
        lMinimizingVector_min_rm (I := IM) S hS K T x hmin hreg hRm
          delta hdelta hd0 hdb
    have hWba : Wb s0 = 0 := hWa
    have hhess := hessFun_lRegularizedAction_endpointBranch_le_index
      (I := IM) S hS T s0 b hs00 hs0b' hgeo hminGamma
      hVopen hA0V hKopen hKconn h0K hbK hstart halpha hregFamily
      (fun A hA s hs ↦ (hcurves A hA).2.2 s hs |>.2.2.2)
      hcenter hinj (Wb b) Wb hOmega' hOmega'Segment hWb hWba rfl
    have hindex : lRegularizedIndex S T beta Wb Wb s0 b =
        lRegularizedIndex S T gamma W W s0 b := by
      apply lRegularizedIndex_congr_of_eventuallyEq (I := IM) S T Wb Wb W W s0 b
      · intro s hs
        have hs' : s ∈ Ioo s0 b := by
          simpa only [uIoo_of_le hs0b'.le] using hs
        exact hcenter s ⟨hs00.le.trans hs'.1.le, hs'.2.le⟩
      · exact fun _ _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
      · exact fun _ _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
    have hFhess : hessFun (I := IM) (S.base.metric (T - tau)) F
        (lExp S T x Z tau) =
        hessFun (I := IM) (S.base.metric (T - tau))
          (fun y ↦ lRegularizedAction S T
            (fun s ↦ alpha (hloc.localInverse y, s)) s0 b)
          (lExp S T x Z tau) := by
      exact (DifferentialGeometry.Geometry.Connection.hessFun_add_const
        (I := IM) (S.base.metric (T - tau))
        (lRegularizedAction S T gamma 0 s0) hU0open hF0smooth hzU0).trans
          (hessFun_congr (I := IM) (S.base.metric (T - tau)) hF0germ)
    rw [hFhess]
    change hessFun (I := IM) (S.base.metric (T - tau))
      (fun y ↦ lRegularizedAction S T
        (fun s ↦ alpha (hloc.localInverse y, s)) s0 b)
        (lExp S T x Z tau) (W b) (W b) ≤
      2 * lRegularizedIndex S T gamma W W s0 b
    rw [← hindex]
    change hessFun (I := IM) (S.base.metric (T - b ^ 2))
      (fun y ↦ lRegularizedAction S T
        (fun s ↦ alpha (hloc.localInverse y, s)) s0 b)
        (alpha (A0, b)) (W b) (W b) ≤
      2 * lRegularizedIndex S T beta Wb Wb s0 b at hhess
    rw [hb2, hcenterEnd] at hhess
    exact hhess

omit [NeZero (Module.finrank ℝ EM)] [SigmaCompactSpace MM] in
theorem exists_contMDiffOn_lCost_upper_support_hess_le_index
    (S : SolutionOn (I := IM) (M := MM) DM)
    (hS : IsSolutionOn (I := IM) S) (K T : Real) (x : MM)
    {Z : TangentSpace IM x} {tau s0 : Real}
    (hmin : (Z, tau) ∈ lMinDomain (E := EM) (I := IM) S T x)
    (hreg : Icc (T - tau) T ⊆ DM.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : MM,
      normSq0S (I := IM) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (hs00 : 0 < s0) (hs0b : s0 < Real.sqrt tau) :
    ∃ U : Set MM, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
      ∃ F : MM → Real,
        ContMDiffOn IM 𝓘(Real, Real) ∞ F U ∧
          F (lExp S T x Z tau) =
            lCost S T x (lExp S T x Z tau) tau ∧
          (∀ y ∈ U, lCost S T x y tau ≤ F y) ∧
          ∀ (W : ∀ s, TangentSpace IM (lRegularizedCurve S T x Z s))
            (Omega : Set Real), IsOpen Omega →
            Icc (0 : Real) (Real.sqrt tau) ⊆ Omega →
            ContMDiffOn 𝓘(Real, Real) IM.tangent (8 : Nat)
              (fun s : Real ↦
                (TotalSpace.mk' EM (E := (TangentSpace IM : MM → Type _))
                  (lRegularizedCurve S T x Z s) (W s) :
                    TangentBundle IM MM)) Omega →
            W s0 = 0 →
            hessFun (I := IM) (S.base.metric (T - tau)) F
                (lExp S T x Z tau) (W (Real.sqrt tau)) (W (Real.sqrt tau)) ≤
              2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
                s0 (Real.sqrt tau) := by
  obtain ⟨U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, hindex⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_le_index
      S hS K T x hmin hreg hRm hs00 hs0b
  exact ⟨U, hUopen, hyU, F, hFsm, hcontact, hupper, hindex⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
