import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Tail.Variation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailFamily_ext_of
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {gamma : Real → M} {J : Set Real} {x : M}
    {A0 : TangentSpace I x} {s0 b : Real}
    {alpha0 : E × Real → M} {V0 : Set E} {K0 : Set Real}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (hs0J : s0 ∈ J) (hbJ : b ∈ J)
    (hstart : gamma s0 = x)
    (hvel : lVelocity (I := I) gamma s0 = A0)
    (hgamma : ∀ r ∈ J,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I gamma r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r =
          lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r))
    (hV0open : IsOpen V0) (hA0V0 : A0 ∈ V0)
    (hK0open : IsOpen K0) (hK0conn : IsPreconnected K0)
    (hs0K0 : s0 ∈ K0)
    (halpha0 : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha0 (V0 ×ˢ K0))
    (hcurves0 : ∀ A ∈ V0,
      alpha0 (A, s0) = x ∧
        lVelocity (I := I) (fun r ↦ alpha0 (A, r)) s0 = A ∧
        ∀ r ∈ K0,
          T - r ^ 2 ∈ D.regular ∧
            MDifferentiableAt 𝓘(Real, Real) I
              (fun q ↦ alpha0 (A, q)) r ∧
            DifferentiableAt Real
              (chartRepAt (I := I) (fun q ↦ alpha0 (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha0 (A, z)) q) r) r ∧
            covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                (fun q ↦ alpha0 (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha0 (A, z)) q) r =
              lRegAccel S T r (alpha0 (A, r))
                (lVelocity (I := I) (fun q ↦ alpha0 (A, q)) r)) :
    ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
      ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧ K0 ⊆ K ∧
        s0 ∈ K ∧ b ∈ K ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ K) ∧
            ∀ A ∈ V,
              alpha (A, s0) = x ∧
                lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
                ∀ r ∈ K,
                  T - r ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun q ↦ alpha (A, q)) r ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
                    covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                        (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
                      lRegAccel S T r (alpha (A, r))
                        (lVelocity (I := I) (fun q ↦ alpha (A, q)) r) := by
  classical
  let Good : Set Real := {r | ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
    ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧ K0 ⊆ K ∧
      s0 ∈ K ∧ r ∈ K ∧
      ∃ alpha : E × Real → M,
        ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
            (V ×ˢ K) ∧
          ∀ A ∈ V,
            alpha (A, s0) = x ∧
              lVelocity (I := I) (fun q ↦ alpha (A, q)) s0 = A ∧
              ∀ q ∈ K,
                T - q ^ 2 ∈ D.regular ∧
                  MDifferentiableAt 𝓘(Real, Real) I
                    (fun z ↦ alpha (A, z)) q ∧
                  DifferentiableAt Real
                    (chartRepAt (I := I) (fun z ↦ alpha (A, z))
                      (fun z : Real ↦
                        lVelocity (I := I) (fun w ↦ alpha (A, w)) z) q) q ∧
                  covDerivAlong (I := I) (S.base.metric (T - q ^ 2))
                      (fun z ↦ alpha (A, z))
                      (fun z : Real ↦
                        lVelocity (I := I) (fun w ↦ alpha (A, w)) z) q =
                    lRegAccel S T q (alpha (A, q))
                      (lVelocity (I := I) (fun z ↦ alpha (A, z)) q)}
  have hGood0 : s0 ∈ Good := by
    exact ⟨V0, hV0open, hA0V0, K0, hK0open, hK0conn, Subset.rfl,
      hs0K0, hs0K0, alpha0, halpha0, hcurves0⟩
  have hGoodOpen : IsOpen Good := by
    rw [isOpen_iff_mem_nhds]
    intro r hr
    obtain ⟨V, hVopen, hA0V, K, hKopen, hKconn, hK0K, hs0K, hrK,
      alpha, halpha, hcurves⟩ := hr
    obtain ⟨epsilon, hepsilon, W, hWopen, hA0W, _hWV,
      beta, hbeta, hcurves'⟩ :=
      lTailFamily_step S hS T x hVopen hA0V hKopen hKconn hs0K hrK
        halpha hcurves
    have hrI : r ∈ Ioo (r - epsilon) (r + epsilon) :=
      ⟨by linarith, by linarith⟩
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hrI)
    intro q hq
    have hUnionOpen : IsOpen (K ∪ Ioo (r - epsilon) (r + epsilon)) :=
      hKopen.union isOpen_Ioo
    have hUnionConn : IsPreconnected
        (K ∪ Ioo (r - epsilon) (r + epsilon)) :=
      hKconn.union r hrK hrI isPreconnected_Ioo
    exact ⟨W, hWopen, hA0W, K ∪ Ioo (r - epsilon) (r + epsilon),
      hUnionOpen, hUnionConn, hK0K.trans subset_union_left,
      Or.inl hs0K, Or.inr hq, beta, hbeta, hcurves'⟩
  have hseg : uIcc s0 b ⊆ J :=
    hJconn.ordConnected.uIcc_subset hs0J hbJ
  have hclosed : closure Good ∩ uIcc s0 b ⊆ Good := by
    rintro s ⟨hscl, hsseg⟩
    have hsJ : s ∈ J := hseg hsseg
    let x0 : M := gamma s
    have hgammaCont : ContinuousOn gamma J := by
      intro r hr
      exact (hgamma r hr).2.1.continuousAt.continuousWithinAt
    have hgammaAt : ContinuousAt gamma s :=
      (hgammaCont s hsJ).continuousAt (hJopen.mem_nhds hsJ)
    have hsrcNhds : gamma ⁻¹' (chartAt H x0).source ∈ nhds s := by
      apply hgammaAt.preimage_mem_nhds
      apply (chartAt H x0).open_source.mem_nhds
      simpa only [x0] using mem_chart_source H (gamma s)
    have hlocalNhds : J ∩ gamma ⁻¹' (chartAt H x0).source ∈ nhds s :=
      inter_mem (hJopen.mem_nhds hsJ) hsrcNhds
    obtain ⟨a, c, hsQ, hQnhds, hQsub⟩ :=
      exists_Icc_mem_subset_of_mem_nhds hlocalNhds
    let Q : Set Real := Icc a c
    let X : ∀ r, TangentSpace I (gamma r) :=
      fun r ↦ lVelocity (I := I) gamma r
    let zref : Real → E × E := fun r ↦
      (chartCurve (I := I) x0 gamma r,
        chartRepAtBase (I := I) x0 gamma X r)
    have hzrefCont : ContinuousOn zref Q := by
      intro r hr
      have hrlocal : r ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub hr
      have hrdata := hgamma r hrlocal.1
      have hphase := lRegCurve_phase S T x0 gamma r hrdata.2.1
        hrlocal.2 hrdata.2.2.1 hrdata.2.2.2
      simpa only [zref, X] using hphase.continuousAt.continuousWithinAt
    let C : Set (Real × (E × E)) := (fun r ↦ (r, zref r)) '' Q
    have hC : IsCompact C :=
      isCompact_Icc.image_of_continuousOn
        (continuousOn_id.prodMk hzrefCont)
    have hCreg : C ⊆ {p : Real × (E × E) |
        T - p.1 ^ 2 ∈ D.regular ∧
          p.2.1 ∈ interior (extChartAt I x0).target} := by
      rintro p ⟨r, hrQ, rfl⟩
      have hrlocal : r ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub hrQ
      refine ⟨(hgamma r hrlocal.1).1, ?_⟩
      change extChartAt I x0 (gamma r) ∈ interior (extChartAt I x0).target
      rw [(isOpen_extChartAt_target (I := I) x0).interior_eq]
      apply (extChartAt I x0).map_source
      rw [extChartAt_source]
      exact hrlocal.2
    obtain ⟨epsilon, hepsilon, hphaseLocal⟩ :=
      exists_lPhaseComp S hS T x0 hC hCreg
    have hball : Ioo (s - epsilon) (s + epsilon) ∈ nhds s :=
      Ioo_mem_nhds (sub_lt_self _ hepsilon) (lt_add_of_pos_right _ hepsilon)
    have hnear : Q ∩ Ioo (s - epsilon) (s + epsilon) ∈ nhds s :=
      inter_mem (by simpa only [Q] using hQnhds) hball
    obtain ⟨t, ⟨htQ, htball⟩, htGood⟩ :=
      mem_closure_iff_nhds.mp hscl _ hnear
    obtain ⟨V, hVopen, hA0V, K, hKopen, hKconn, hK0K, hs0K, htK,
      alpha, halpha, hcurves⟩ := htGood
    have htlocal : t ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub htQ
    have hEq : Set.EqOn (fun r ↦ alpha (A0, r)) gamma (K ∩ J) :=
      lRegSol_eqOn S hS T hKopen hKconn hs0K hJopen hJconn hs0J
        (hcurves A0 hA0V).2.2 hgamma
        (by rw [(hcurves A0 hA0V).1, hstart])
        (by rw [(hcurves A0 hA0V).2.1, hvel])
    have hpos : alpha (A0, t) = gamma t := hEq ⟨htK, htlocal.1⟩
    have heqGerm : (fun r ↦ alpha (A0, r)) =ᶠ[nhds t] gamma :=
      hEq.eventuallyEq_of_mem
        ((hKopen.inter hJopen).mem_nhds ⟨htK, htlocal.1⟩)
    have hvelEq : lVelocity (I := I) (fun r ↦ alpha (A0, r)) t =
        lVelocity (I := I) gamma t := by
      with_unfolding_all exact
        (congrArg (fun L ↦ L (1 : Real))
          (heqGerm.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)))
    have hptC : (t, zref t) ∈ C := ⟨t, htQ, rfl⟩
    obtain ⟨U, hUopen, hzrefU, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
      hphaseLocal (t, zref t) hptC
    have halphaSrc : alpha (A0, t) ∈ (chartAt H x0).source := by
      rw [hpos]
      exact htlocal.2
    have hseedEq :
        (extChartAt I x0 (alpha (A0, t)),
          fderiv Real
            (fun r : Real ↦ extChartAt I x0 (alpha (A0, r))) t
            (1 : Real)) = zref t := by
      apply Prod.ext
      · simp only [zref, chartCurve]
        rw [hpos]
      · have hseedVel := lPhaseSeed_vel (I := I) x0
          ((hcurves A0 hA0V).2.2 t htK).2.1 halphaSrc
        calc
          fderiv Real
              (fun r : Real ↦ extChartAt I x0 (alpha (A0, r))) t
              (1 : Real) =
            trivToE (I := I) x0 (alpha (A0, t))
              (lVelocity (I := I) (fun r ↦ alpha (A0, r)) t) := hseedVel
          _ = trivToE (I := I) x0 (gamma t)
              (lVelocity (I := I) gamma t) := by rw [hpos, hvelEq]
          _ = (zref t).2 := by rfl
    obtain ⟨W, hWopen, hA0W, _hWV, beta, hbeta, hcurves'⟩ :=
      lTailFamily_step_of S hS T x x0 hVopen hA0V hKopen hKconn
        hs0K htK halpha hcurves halphaSrc epsilon hepsilon hUopen
        (by rw [hseedEq]; exact hzrefU) Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
    have hsNew : s ∈ K ∪ Ioo (t - epsilon) (t + epsilon) := by
      right
      exact ⟨by linarith [htball.2], by linarith [htball.1]⟩
    have htI : t ∈ Ioo (t - epsilon) (t + epsilon) :=
      ⟨by linarith, by linarith⟩
    exact ⟨W, hWopen, hA0W, K ∪ Ioo (t - epsilon) (t + epsilon),
      hKopen.union isOpen_Ioo,
      hKconn.union t htK htI isPreconnected_Ioo,
      hK0K.trans subset_union_left, Or.inl hs0K, hsNew,
      beta, hbeta, hcurves'⟩
  have hall : uIcc s0 b ⊆ Good :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hGoodOpen
      ⟨s0, Set.left_mem_uIcc, hGood0⟩ hclosed
  exact hall Set.right_mem_uIcc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailFamily_span
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {gamma : Real → M} {J : Set Real} {x : M}
    {A0 : TangentSpace I x} {s0 b : Real}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (h0J : 0 ∈ J) (hs0J : s0 ∈ J) (hbJ : b ∈ J)
    (hstart : gamma s0 = x)
    (hvel : lVelocity (I := I) gamma s0 = A0)
    (hgamma : ∀ r ∈ J,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I gamma r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r =
          lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r)) :
    ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
      ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
        0 ∈ K ∧ s0 ∈ K ∧ b ∈ K ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ K) ∧
            ∀ A ∈ V,
              alpha (A, s0) = x ∧
                lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
                ∀ r ∈ K,
                  T - r ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun q ↦ alpha (A, q)) r ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
                    covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                        (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
                      lRegAccel S T r (alpha (A, r))
                        (lVelocity (I := I) (fun q ↦ alpha (A, q)) r) := by
  obtain ⟨V0, hV0open, hA0V0, K0, hK0open, hK0conn, hs0K0, h0K0,
      alpha0, halpha0, hcurves0⟩ :=
    lTailFamily_extend S hS T hJopen hJconn hs0J h0J hstart hvel hgamma
  obtain ⟨V, hVopen, hA0V, K, hKopen, hKconn, hK0K, hs0K, hbK,
      alpha, halpha, hcurves⟩ :=
    lTailFamily_ext_of S hS T hJopen hJconn hs0J hbJ hstart hvel hgamma
      hV0open hA0V0 hK0open hK0conn hs0K0 halpha0 hcurves0
  exact ⟨V, hVopen, hA0V, K, hKopen, hKconn, hK0K h0K0, hs0K, hbK,
    alpha, halpha, hcurves⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
