import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
 {D : RealTimeInterval}

private theorem exists_lRegularizedGeodesicFamily_of_phase_coordinates
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T s0 : ℝ) (x : M) (z0 : E × E)
    (hT : T - s0 ^ 2 ∈ D.regular)
    (hz0pos : z0.1 ∈ interior (extChartAt I x).target) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ V : Set (E × E), IsOpen V ∧ z0 ∈ V ∧
        ∃ alpha : (E × E) × ℝ → M,
          ContMDiffOn (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) I ∞ alpha
            (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) ∧
          ∀ A ∈ V,
            alpha (A, s0) = (extChartAt I x).symm A.1 ∧
            lVelocity (I := I) (fun s ↦ alpha (A, s)) s0 =
              trivFromE (I := I) x ((extChartAt I x).symm A.1) A.2 ∧
            IsLRegularizedGeodesicOn S T (fun s ↦ alpha (A, s))
              (Ioo (s0 - epsilon) (s0 + epsilon)) := by
  obtain ⟨epsilon, hepsilon, V, hVopen, hz0V, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
    exists_lPhaseAt S hS T x s0 z0 hT hz0pos
  let phase := Phi
  let alpha : (E × E) × ℝ → M := fun p ↦ (extChartAt I x).symm (phase p).1
  have hphase := hPhiSmooth
  have hphaseMap : MapsTo (fun p : (E × E) × ℝ ↦ (phase p).1)
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) (extChartAt I x).target := by
    intro p hp
    exact interior_subset (hPhiMap hp).2
  have halpha : ContMDiffOn
      (𝓘(Real, E × E).prod 𝓘(Real, Real)) I ∞ alpha
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, (E × E) × Real) 𝓘(Real, E) ∞
        (fun p ↦ (phase p).1)
        (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) :=
      hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
      hphaseMD hphaseMap
  refine ⟨epsilon, hepsilon, V, hVopen, hz0V, alpha, halpha, ?_⟩
  intro A hA
  let z : Real → E × E := fun s ↦ phase (A, s)
  let gamma : Real → M := lPhaseCurve (I := I) x z
  let W : ∀ s, TangentSpace I (gamma s) := lPhaseVelocity (I := I) x z
  have hAV : A ∈ V := by
    exact hA
  have hsol : ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
      HasDerivAt z (lPhaseField S T x s (z s)) s := by
    intro s hs
    simpa only [z, phase] using hPhiDeriv (A) hAV s hs
  have hdata : ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
      T - s ^ 2 ∈ D.regular ∧
        (z s).1 ∈ interior (extChartAt I x).target := by
    intro s hs
    have hmem : ((A, s) : (E × E) × Real) ∈
        V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon) := ⟨hAV, hs⟩
    have hmap := hPhiMap hmem
    change T - s ^ 2 ∈ D.regular ∧
      (Phi (A, s)).1 ∈ interior (extChartAt I x).target at hmap
    exact hmap
  have hzs0 : z s0 = A := by
    simpa only [z, phase] using hPhi0 (A) hAV
  have hvel : Set.EqOn (fun s ↦ lVelocity (I := I) gamma s) W
      (Ioo (s0 - epsilon) (s0 + epsilon)) := by
    intro s hs
    have hzs := hsol s hs
    have hq : HasDerivAt (fun r : Real ↦ (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    with_unfolding_all exact
      (lPhase_velocity (I := I) x z s hq (hdata s hs).2)
  have hs0 : s0 ∈ Ioo (s0 - epsilon) (s0 + epsilon) := by
    constructor <;> linarith
  have hgamma0 : gamma s0 = (extChartAt I x).symm A.1 := by
    simp only [gamma, lPhaseCurve, hzs0]
  have hvel0 : lVelocity (I := I) gamma s0 =
      trivFromE (I := I) x ((extChartAt I x).symm A.1) A.2 := by
    have hv := hvel hs0
    change lVelocity (I := I) gamma s0 =
      trivFromE (I := I) x (gamma s0) (z s0).2 at hv
    rw [hgamma0, hzs0] at hv
    exact hv
  have halpha_eq : (fun s ↦ alpha (A, s)) = gamma := by
    funext s
    rfl
  rw [halpha_eq]
  refine ⟨hgamma0, hvel0, ?_⟩
  intro s hs
  have hzs := hsol s hs
  have hsdata := hdata s hs
  have hq : HasDerivAt (fun r : Real ↦ (z r).1) (z s).2 s := by
    have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
    simpa [lPhaseField, Function.comp_def] using h
  have hv : HasDerivAt (fun r : Real ↦ (z r).2)
      (lPhaseField S T x s (z s)).2 s := by
    have h := hasFDerivAt_snd.comp_hasDerivAt s hzs
    simpa [Function.comp_def] using h
  have hfield : (fun r ↦ lVelocity (I := I) gamma r) =ᶠ[nhds s] W :=
    hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
    simpa only [gamma] using
      lPhaseCurve_mdiff (I := I) x z s hq.differentiableAt hsdata.2
  have hWdiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma W s) s := by
    simpa only [gamma, W] using lPhaseVelocity_diff (I := I) x z s
      hq.differentiableAt hv.differentiableAt hsdata.2
  have hveldiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real ↦ lVelocity (I := I) gamma r) s) s :=
    hWdiff.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) gamma hfield)
  refine ⟨hsdata.1, hgamma, hveldiff, ?_⟩
  calc
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun r : Real ↦ lVelocity (I := I) gamma r) s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma W s :=
        covDerivAlong_congr_of_eventuallyEq
          (I := I) (S.base.metric (T - s ^ 2)) gamma hfield
    _ = lRegularizedAccel S T s (gamma s) (W s) := by
      simpa only [gamma, W] using
        lPhase_accel S T x z s hzs hsdata.2
    _ = lRegularizedAccel S T s (gamma s)
        (lVelocity (I := I) gamma s) := by
      rw [hfield.eq_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end


noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open scoped Manifold ContDiff Topology
variable {A E H M : Type*}
 [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
 {D : RealTimeInterval}

theorem exists_lRegularizedGeodesicFamily_of_smooth_phase
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T s0 : ℝ)
    {V : Set A} (hV : IsOpen V) {a0 : A} (ha0 : a0 ∈ V)
    (ζ : A → TangentBundle I M) (hζ : ContMDiffOn 𝓘(ℝ, A) I.tangent ∞ ζ V)
    (hT : T - s0 ^ 2 ∈ D.regular) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ α : A × ℝ → M,
        ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (U ×ˢ Ioo (s0 - ε) (s0 + ε)) ∧
        ∀ a ∈ U, α (a, s0) = (ζ a).proj ∧
          lVelocity (I := I) (fun r => α (a, r)) s0 = (ζ a).2 ∧
          IsLRegularizedGeodesicOn S T (fun r => α (a, r)) (Ioo (s0 - ε) (s0 + ε)) := by
  let x0 := (ζ a0).proj
  let e := trivializationAt E (TangentSpace I) x0
  let V₀ := (V ∩ ζ ⁻¹' e.source) ∩ (V ∩ (fun a => (ζ a).proj) ⁻¹' (extChartAt I x0).source)
  have hζcont : ContinuousOn ζ V := hζ.continuousOn
  have hbase : ContMDiffOn 𝓘(ℝ, A) I ∞ (fun a => (ζ a).proj) V :=
    (Bundle.contMDiff_proj (TangentSpace I)).comp_contMDiffOn hζ
  have hV₀ : IsOpen V₀ :=
    ((hζcont.isOpen_inter_preimage hV e.open_source).inter
      ((hbase.continuousOn.isOpen_inter_preimage hV (isOpen_extChartAt_source (I := I) x0))))
  have ha0V₀ : a0 ∈ V₀ := by
    refine ⟨⟨ha0, ?_⟩, ha0, mem_extChartAt_source x0⟩
    exact FiberBundle.mem_trivializationAt_proj_source (x := ζ a0)
  let seed : A → E × E := fun a => (extChartAt I x0 (ζ a).proj, (e (ζ a)).2)
  have hseed : ContDiffOn ℝ ∞ seed V₀ := by
    have hp : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (fun a => extChartAt I x0 (ζ a).proj) V₀ :=
      (contMDiffOn_extChartAt (I := I) (x := x0) (n := ∞)).comp (hbase.mono (fun _ h => h.1.1))
        (fun a ha => by simpa only [extChartAt_source] using ha.2.2)
    have hv : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (fun a => (e (ζ a)).2) V₀ :=
      ((e.contMDiffOn_iff (fun a ha => ha.1.2)).mp (hζ.mono (fun _ h => h.1.1))).2
    exact hp.contDiffOn.prodMk hv.contDiffOn
  have hz0 : (seed a0).1 ∈ interior (extChartAt I x0).target := by
    apply mem_interior_iff_mem_nhds.mpr
    exact extChartAt_target_mem_nhds x0
  obtain ⟨ε, hε, W, hW, hzW, β, hβ, hcurves⟩ :=
    exists_lRegularizedGeodesicFamily_of_phase_coordinates S hS T s0 x0 (seed a0) hT hz0
  let U := V₀ ∩ seed ⁻¹' W
  have hU : IsOpen U := hseed.continuousOn.isOpen_inter_preimage hV₀ hW
  have ha0U : a0 ∈ U := ⟨ha0V₀, hzW⟩
  let α : A × ℝ → M := fun p => β (seed p.1, p.2)
  have hinput : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, ℝ)) ∞ (fun p : A × ℝ => (seed p.1, p.2))
      (U ×ˢ Ioo (s0 - ε) (s0 + ε)) :=
    ((hseed.contMDiffOn.mono (fun _ h => h.1)).comp contMDiffOn_fst (fun p hp => hp.1)).prodMk contMDiffOn_snd
  refine ⟨ε, hε, U, hU, ha0U, (fun _ h => h.1.1.1), α,
    hβ.comp hinput (fun p hp => ⟨hp.1.2, hp.2⟩), ?_⟩
  intro a ha
  obtain ⟨hpos, hvel, hgeo⟩ := hcurves (seed a) ha.2
  have hpoint : (extChartAt I x0).symm (seed a).1 = (ζ a).proj :=
    (extChartAt I x0).left_inv ha.1.2.2
  refine ⟨hpos.trans hpoint, ?_, hgeo⟩
  rw [hvel, hpoint]
  change (e.symmL ℝ (ζ a).proj) (e (ζ a)).2 = (ζ a).2
  have hmem : (ζ a).proj ∈ e.baseSet := e.mem_source.mp ha.1.1.2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hmem]
  exact e.symmL_continuousLinearMapAt hmem (ζ a).2

end DifferentialGeometry.PDE.RicciFlow.Perelman

end



noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {F E H M : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [FiniteDimensional Real E] in
private theorem contDiffAt_time_fderiv_family
    {f : F × Real → E} {A0 : F} {s0 : Real}
    (hF : ContDiffAt Real ∞ f (A0, s0)) :
    ContDiffAt Real ∞
      (fun A : F ↦
        fderiv Real (fun s : Real ↦ f (A, s)) s0 (1 : Real)) A0 := by
  have hF' : ContMDiffAt
      (𝓘(Real, F).prod 𝓘(Real, Real)) 𝓘(Real, E) ∞
      (Function.uncurry (fun A : F ↦ fun s : Real ↦ f (A, s)))
      (A0, s0) := by
    have h := hF.contMDiffAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    have hfun : Function.uncurry (fun A : F ↦ fun s : Real ↦ f (A, s)) = f := by
      funext p
      rfl
    rw [hfun]
    exact h
  have htime : ContMDiffAt 𝓘(Real, F) 𝓘(Real, Real) ∞
      (fun _ : F ↦ s0) A0 := contMDiffAt_const
  have hparam : ContMDiffAt 𝓘(Real, F) 𝓘(Real, F) ∞
      (id : F → F) A0 := contMDiffAt_id
  have hone : ContMDiffAt 𝓘(Real, F) 𝓘(Real, Real) ∞
      (fun _ : F ↦ (1 : Real)) A0 := contMDiffAt_const
  have h := ContMDiffAt.mfderiv_apply
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E))
    (f := fun A : F ↦ fun s : Real ↦ f (A, s))
    (g := fun _ : F ↦ s0) (g₁ := id)
    (g₂ := fun _ : F ↦ (1 : Real))
    (x₀ := A0) (m := ∞) (n := ∞)
    hF' htime hparam hone le_rfl
  apply contMDiffAt_iff_contDiffAt.mp
  convert h using 1
  funext A
  simp only [inTangentCoordinates, mfderiv_eq_fderiv]
  dsimp only [ContinuousLinearMap.inCoordinates]
  simp only [TangentBundle.continuousLinearMapAt_model_space,
    TangentBundle.symmL_model_space]
  change fderiv Real (fun s : Real => f (A, s)) s0 1 =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (A, s0)))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (A, s0))).symm
        (fderiv Real (fun s : Real => f (A, s)) s0
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) s0)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) s0).symm 1))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M] in
private theorem contDiffAt_lRegularizedGeodesicFamily_seed
    {alpha : F × Real → M} {A0 : F} {s0 : Real} (x0 : M)
    (hsrc : alpha (A0, s0) ∈ (chartAt H x0).source)
    (halpha : ContMDiffAt
      (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha (A0, s0)) :
    ContDiffAt Real ∞
      (fun A : F ↦
        (extChartAt I x0 (alpha (A, s0)),
          fderiv Real
            (fun s : Real ↦ extChartAt I x0 (alpha (A, s))) s0
            (1 : Real))) A0 := by
  let f : F × Real → E := fun p ↦ extChartAt I x0 (alpha p)
  have hchart : ContMDiffAt
      (𝓘(Real, F).prod 𝓘(Real, Real)) 𝓘(Real, E) ∞ f (A0, s0) := by
    exact (contMDiffAt_extChartAt' (I := I) hsrc).comp (A0, s0) halpha
  have hF : ContDiffAt Real ∞ f (A0, s0) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hchart
  have hincl : ContDiffAt Real ∞ (fun A : F ↦ (A, s0)) A0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hpos : ContDiffAt Real ∞ (fun A : F ↦ f (A, s0)) A0 := by
    have hcomp := hF.comp A0 hincl
    have hfun : f ∘ (fun A : F ↦ (A, s0)) = fun A : F ↦ f (A, s0) := by
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hvel : ContDiffAt Real ∞
      (fun A : F ↦
        fderiv Real (fun s : Real ↦ f (A, s)) s0 (1 : Real)) A0 :=
    contDiffAt_time_fderiv_family hF
  simpa only [f] using hpos.prodMk hvel

private theorem extend_lRegularizedGeodesicFamily_of_phaseFlow_eqOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : F × Real → M} {V : Set F} {J : Set Real}
    {A0 : F} {t : Real} (x0 : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (htJ : t ∈ J)
    (halpha : ContMDiffOn
      (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ J))
    (hcurves : ∀ A ∈ V,
      IsLRegularizedGeodesicOn S T (fun r ↦ alpha (A, r)) J)
    (hsrc : alpha (A0, t) ∈ (chartAt H x0).source)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    {U : Set (E × E)} (hUopen : IsOpen U)
    (hseedU :
      (extChartAt I x0 (alpha (A0, t)),
        fderiv Real
          (fun r : Real ↦ extChartAt I x0 (alpha (A0, r))) t
          (1 : Real)) ∈ U)
    (Phi : (E × E) × Real → E × E)
    (hPhi0 : ∀ z ∈ U, Phi (z, t) = z)
    (hPhiSmooth : ContDiffOn Real ∞ Phi
      (U ×ˢ Ioo (t - epsilon) (t + epsilon)))
    (hPhiDeriv : ∀ z ∈ U, ∀ r ∈ Ioo (t - epsilon) (t + epsilon),
      HasDerivAt (fun q ↦ Phi (z, q))
        (lPhaseField S T x0 r (Phi (z, r))) r)
    (hPhiMap : MapsTo (fun q : (E × E) × Real ↦ (q.2, Phi q))
      (U ×ˢ Ioo (t - epsilon) (t + epsilon))
      {p : Real × (E × E) |
        T - p.1 ^ 2 ∈ D.regular ∧
          p.2.1 ∈ interior (extChartAt I x0).target}) :
    ∃ W : Set F, IsOpen W ∧ A0 ∈ W ∧ W ⊆ V ∧
      ∃ beta : F × Real → M,
          ContMDiffOn (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ beta
              (W ×ˢ (J ∪ Ioo (t - epsilon) (t + epsilon))) ∧
            Set.EqOn beta alpha (W ×ˢ J) ∧
            ∀ A ∈ W,
              IsLRegularizedGeodesicOn S T (fun r ↦ beta (A, r))
                  (J ∪ Ioo (t - epsilon) (t + epsilon)) := by
  classical
  let pos : F → M := fun A ↦ alpha (A, t)
  have hprodOpen : IsOpen (V ×ˢ J) := hVopen.prod hJopen
  have hposCont : ContinuousOn pos V := by
    intro A hA
    have halphaAt : ContMDiffAt
        (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha (A, t) :=
      (halpha (A, t) ⟨hA, htJ⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hA, htJ⟩)
    have hincl : ContMDiffAt 𝓘(Real, F)
        (𝓘(Real, F).prod 𝓘(Real, Real)) ∞
        (fun B : F ↦ (B, t)) A :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (halphaAt.comp A hincl).continuousAt.continuousWithinAt
  let V0 : Set F := V ∩ pos ⁻¹' (chartAt H x0).source
  have hV0open : IsOpen V0 :=
    hposCont.isOpen_inter_preimage hVopen (chartAt H x0).open_source
  have hA0V0 : A0 ∈ V0 := ⟨hA0V, hsrc⟩
  let seed : F → E × E := fun A ↦
    (extChartAt I x0 (alpha (A, t)),
      fderiv Real (fun r : Real ↦ extChartAt I x0 (alpha (A, r))) t
        (1 : Real))
  have hseed : ContDiffOn Real ∞ seed V0 := by
    intro A hA
    have halphaAt : ContMDiffAt
        (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha (A, t) :=
      (halpha (A, t) ⟨hA.1, htJ⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hA.1, htJ⟩)
    exact (contDiffAt_lRegularizedGeodesicFamily_seed (I := I) x0 hA.2 halphaAt).contDiffWithinAt
  let W : Set F := V0 ∩ seed ⁻¹' U
  have hWopen : IsOpen W :=
    hseed.continuousOn.isOpen_inter_preimage hV0open hUopen
  have hA0W : A0 ∈ W := by
    refine ⟨hA0V0, ?_⟩
    change seed A0 ∈ U
    exact hseedU
  have hWV : W ⊆ V := fun _ h ↦ h.1.1
  let K : Set Real := Ioo (t - epsilon) (t + epsilon)
  have htK : t ∈ K := ⟨by linarith, by linarith⟩
  let input : F × Real → (E × E) × Real := fun p ↦ (seed p.1, p.2)
  let phase : F × Real → E × E := fun p ↦ Phi (input p)
  let eta : F × Real → M := fun p ↦
    (extChartAt I x0).symm (phase p).1
  have hinput : ContDiffOn Real ∞ input (W ×ˢ K) := by
    have hseedW : ContDiffOn Real ∞ seed W := hseed.mono (fun _ h ↦ h.1)
    exact (hseedW.comp contDiffOn_fst (fun p hp ↦ hp.1)).prodMk contDiffOn_snd
  have hinputMap : MapsTo input (W ×ˢ K) (U ×ˢ K) := by
    rintro ⟨A, r⟩ ⟨hA, hr⟩
    exact ⟨hA.2, hr⟩
  have hphase : ContDiffOn Real ∞ phase (W ×ˢ K) := by
    have hraw := hPhiSmooth.comp hinput hinputMap
    have hfun : Phi ∘ input = phase := by
      rfl
    rw [hfun] at hraw
    exact hraw
  have hphaseMap : MapsTo (fun p : F × Real ↦ (phase p).1)
      (W ×ˢ K) (extChartAt I x0).target := by
    intro p hp
    exact interior_subset (hPhiMap (hinputMap hp)).2
  have hetaSmooth : ContMDiffOn
      (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ eta (W ×ˢ K) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, F × Real) 𝓘(Real, E) ∞
        (fun p ↦ (phase p).1) (W ×ˢ K) := hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x0).comp
      hphaseMD hphaseMap
  have hetaRegularity : ∀ A ∈ W, ∀ r ∈ K,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I (fun q ↦ eta (A, q)) r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) (fun q ↦ eta (A, q))
            (fun q : Real ↦ lVelocity (I := I) (fun z ↦ eta (A, z)) q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
            (fun q ↦ eta (A, q))
            (fun q : Real ↦ lVelocity (I := I) (fun z ↦ eta (A, z)) q) r =
          lRegularizedAccel S T r (eta (A, r))
            (lVelocity (I := I) (fun q ↦ eta (A, q)) r) := by
    intro A hA
    let z : Real → E × E := fun r ↦ phase (A, r)
    let gamma : Real → M := lPhaseCurve (I := I) x0 z
    let B : ∀ r, TangentSpace I (gamma r) := lPhaseVelocity (I := I) x0 z
    have hzU : seed A ∈ U := hA.2
    have hsol : ∀ r ∈ K,
        HasDerivAt z (lPhaseField S T x0 r (z r)) r := by
      intro r hr
      simpa only [z, phase, input] using hPhiDeriv (seed A) hzU r hr
    have hdata : ∀ r ∈ K,
        T - r ^ 2 ∈ D.regular ∧
          (z r).1 ∈ interior (extChartAt I x0).target := by
      intro r hr
      have hmem : ((seed A, r) : (E × E) × Real) ∈ U ×ˢ K := ⟨hzU, hr⟩
      have hmap := hPhiMap hmem
      change T - r ^ 2 ∈ D.regular ∧
        (Phi (seed A, r)).1 ∈ interior (extChartAt I x0).target at hmap
      exact hmap
    have hvel : Set.EqOn (fun r ↦ lVelocity (I := I) gamma r) B K := by
      intro r hr
      have hzr := hsol r hr
      have hq : HasDerivAt (fun w : Real ↦ (z w).1) (z r).2 r := by
        have h := hasFDerivAt_fst.comp_hasDerivAt r hzr
        simpa [lPhaseField, Function.comp_def] using h
      with_unfolding_all exact
        (lPhase_velocity (I := I) x0 z r hq (hdata r hr).2)
    intro r hr
    have hzr := hsol r hr
    have hrdata := hdata r hr
    have hq : HasDerivAt (fun w : Real ↦ (z w).1) (z r).2 r := by
      have h := hasFDerivAt_fst.comp_hasDerivAt r hzr
      simpa [lPhaseField, Function.comp_def] using h
    have hv : HasDerivAt (fun w : Real ↦ (z w).2)
        (lPhaseField S T x0 r (z r)).2 r := by
      have h := hasFDerivAt_snd.comp_hasDerivAt r hzr
      simpa [Function.comp_def] using h
    have hfield : (fun w ↦ lVelocity (I := I) gamma w) =ᶠ[nhds r] B :=
      hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr)
    have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma r := by
      simpa only [gamma] using
        lPhaseCurve_mdiff (I := I) x0 z r hq.differentiableAt hrdata.2
    have hBdiff : DifferentiableAt Real (chartRepAt (I := I) gamma B r) r := by
      simpa only [gamma, B] using lPhaseVelocity_diff (I := I) x0 z r
        hq.differentiableAt hv.differentiableAt hrdata.2
    have hveldiff : DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun w : Real ↦ lVelocity (I := I) gamma w) r) r :=
      hBdiff.congr_of_eventuallyEq
        (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) gamma hfield)
    have hacc : covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
          (fun w : Real ↦ lVelocity (I := I) gamma w) r =
        lRegularizedAccel S T r (gamma r) (lVelocity (I := I) gamma r) := by
      calc
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun w : Real ↦ lVelocity (I := I) gamma w) r =
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma B r :=
            covDerivAlong_congr_of_eventuallyEq
              (I := I) (S.base.metric (T - r ^ 2)) gamma hfield
        _ = lRegularizedAccel S T r (gamma r) (B r) := by
          simpa only [gamma, B] using lPhase_accel S T x0 z r hzr hrdata.2
        _ = lRegularizedAccel S T r (gamma r)
            (lVelocity (I := I) gamma r) := by rw [hfield.eq_of_nhds]
    simpa only [eta, gamma, lPhaseCurve, z] using
      ⟨hrdata.1, hgamma, hveldiff, hacc⟩
  have heta0 : ∀ A ∈ W, eta (A, t) = alpha (A, t) := by
    intro A hA
    have hz : phase (A, t) = seed A := by
      simpa only [phase, input] using hPhi0 (seed A) hA.2
    change (extChartAt I x0).symm (phase (A, t)).1 = alpha (A, t)
    rw [hz]
    apply (extChartAt I x0).left_inv
    rw [extChartAt_source]
    exact hA.1.2
  have hetaVelocity : ∀ A ∈ W,
      lVelocity (I := I) (fun r ↦ eta (A, r)) t =
        lVelocity (I := I) (fun r ↦ alpha (A, r)) t := by
    intro A hA
    let z : Real → E × E := fun r ↦ phase (A, r)
    let gamma : Real → M := lPhaseCurve (I := I) x0 z
    have hzt : z t = seed A := by
      simpa only [z, phase, input] using hPhi0 (seed A) hA.2
    have hsol := hPhiDeriv (seed A) hA.2 t htK
    have hq : HasDerivAt (fun r : Real ↦ (z r).1) (z t).2 t := by
      have h := hasFDerivAt_fst.comp_hasDerivAt t hsol
      simpa [z, phase, input, lPhaseField, Function.comp_def] using h
    have hphaseVelocity := lPhase_velocity (I := I) x0 z t hq
      (hPhiMap (show ((seed A, t) : (E × E) × Real) ∈ U ×ˢ K from
        ⟨hA.2, htK⟩)).2
    have hsrcA : alpha (A, t) ∈ (chartAt H x0).source := hA.1.2
    have hbase : alpha (A, t) ∈
        (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrcA
    have hseedVelocity : (seed A).2 =
        trivToE (I := I) x0 (alpha (A, t))
          (lVelocity (I := I) (fun r ↦ alpha (A, r)) t) :=
      lPhaseSeed_velocity (I := I) x0 ((hcurves A (hWV hA)) t htJ).2.1 hsrcA
    have hetaGamma : (fun r ↦ eta (A, r)) = gamma := by rfl
    have hgamma0 : gamma t = alpha (A, t) := by
      rw [← hetaGamma]
      exact heta0 A hA
    rw [hetaGamma]
    change lVelocity (I := I) gamma t =
      trivFromE (I := I) x0 (gamma t) (z t).2 at hphaseVelocity
    rw [hgamma0, hzt] at hphaseVelocity
    exact hphaseVelocity.trans (by
      rw [hseedVelocity]
      exact trivFromE_trivToE (I := I) x0 hbase _)
  have hmatch : ∀ A ∈ W,
      Set.EqOn (fun r ↦ alpha (A, r)) (fun r ↦ eta (A, r)) (J ∩ K) := by
    intro A hA
    exact lRegularizedSolution_eqOn S hS T hJopen hJconn htJ isOpen_Ioo
      isPreconnected_Ioo htK (hcurves A (hWV hA)) (hetaRegularity A hA)
      (heta0 A hA).symm (hetaVelocity A hA).symm
  let beta : F × Real → M := fun p ↦ if p.2 ∈ J then alpha p else eta p
  have hbetaSmooth : ContMDiffOn
      (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ beta (W ×ˢ (J ∪ K)) := by
    intro p hp
    by_cases hpJ : p.2 ∈ J
    · have halphaAt : ContMDiffAt
          (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha p :=
        (halpha p ⟨hWV hp.1, hpJ⟩).contMDiffAt
          (hprodOpen.mem_nhds ⟨hWV hp.1, hpJ⟩)
      have heq : beta =ᶠ[nhds p] alpha := by
        filter_upwards [(hJopen.preimage continuous_snd).mem_nhds hpJ] with q hq
        change q.2 ∈ J at hq
        simp only [beta]
        rw [ite_eq_left hq]
      exact (halphaAt.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have hpK : p.2 ∈ K := hp.2.resolve_left hpJ
      have hWKopen : IsOpen (W ×ˢ K) := hWopen.prod isOpen_Ioo
      have hetaAt : ContMDiffAt
          (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ eta p :=
        (hetaSmooth p ⟨hp.1, hpK⟩).contMDiffAt
          (hWKopen.mem_nhds ⟨hp.1, hpK⟩)
      have heq : beta =ᶠ[nhds p] eta := by
        filter_upwards [(hWopen.preimage continuous_fst).mem_nhds hp.1,
          (isOpen_Ioo.preimage continuous_snd).mem_nhds hpK] with q hqW hqK
        simp only [beta]
        by_cases hqJ : q.2 ∈ J
        · rw [ite_eq_left hqJ]
          exact hmatch q.1 hqW ⟨hqJ, hqK⟩
        · rw [ite_eq_right hqJ]
      exact (hetaAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  refine ⟨W, hWopen, hA0W, hWV, beta, hbetaSmooth, ?_, ?_⟩
  · intro p hp
    exact ite_eq_left hp.2
  intro A hA
  have hbetaAlpha : ∀ r ∈ J,
      (fun q ↦ beta (A, q)) =ᶠ[nhds r] (fun q ↦ alpha (A, q)) := by
    intro r hr
    filter_upwards [hJopen.mem_nhds hr] with q hq
    simp only [beta]
    rw [ite_eq_left hq]
  have hbetaEta : ∀ r ∈ K,
      (fun q ↦ beta (A, q)) =ᶠ[nhds r] (fun q ↦ eta (A, q)) := by
    intro r hr
    filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
    simp only [beta]
    by_cases hqJ : q ∈ J
    · rw [ite_eq_left hqJ]
      exact hmatch A hA ⟨hqJ, hq⟩
    · rw [ite_eq_right hqJ]
  intro r hr
  rcases hr with hrJ | hrK
  · exact lRegularizedData_congr S T r (hbetaAlpha r hrJ)
      ((hcurves A (hWV hA)) r hrJ)
  · exact lRegularizedData_congr S T r (hbetaEta r hrK) (hetaRegularity A hA r hrK)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology
variable {A E H M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
 {D : RealTimeInterval}

theorem exists_lRegularizedGeodesicFamily_to_time_of_smooth_phase
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {V : Set A} (hV : IsOpen V) {a0 : A} (ha0 : a0 ∈ V)
    (ζ : A → TangentBundle I M) (hζ : ContMDiffOn 𝓘(ℝ, A) I.tangent ∞ ζ V)
    {γ : ℝ → M} {J : Set ℝ} {s0 b : ℝ}
    (hJ : IsOpen J) (hconn : IsPreconnected J) (hs0 : s0 ∈ J) (hb : b ∈ J)
    (hstart : γ s0 = (ζ a0).proj) (hvel : lVelocity (I := I) γ s0 = (ζ a0).2)
    (hγ : IsLRegularizedGeodesicOn S T γ J) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ s0 ∈ K ∧ b ∈ K ∧
        ∃ α : A × ℝ → M,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (U ×ˢ K) ∧
          (∀ a ∈ U, α (a, s0) = (ζ a).proj ∧
            lVelocity (I := I) (fun s => α (a, s)) s0 = (ζ a).2 ∧
            IsLRegularizedGeodesicOn S T (fun s => α (a, s)) K) ∧
          EqOn (fun s => α (a0, s)) γ (K ∩ J) := by
  classical
  let Good : Set ℝ := {r | ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
    ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ s0 ∈ K ∧ r ∈ K ∧
      ∃ α : A × ℝ → M,
        ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (U ×ˢ K) ∧
        ∀ a ∈ U, α (a, s0) = (ζ a).proj ∧
          lVelocity (I := I) (fun s => α (a, s)) s0 = (ζ a).2 ∧
          IsLRegularizedGeodesicOn S T (fun s => α (a, s)) K}
  have hGood0 : s0 ∈ Good := by
    obtain ⟨ε, hε, U, hU, haU, hUV, α, hα, hcurves⟩ :=
      exists_lRegularizedGeodesicFamily_of_smooth_phase S hS T s0 hV ha0 ζ hζ (hγ s0 hs0).1
    have hs : s0 ∈ Ioo (s0 - ε) (s0 + ε) := ⟨by linarith, by linarith⟩
    exact ⟨U, hU, haU, hUV, Ioo (s0 - ε) (s0 + ε), isOpen_Ioo, isPreconnected_Ioo,
      hs, hs, α, hα, hcurves⟩
  have hGoodOpen : IsOpen Good := by
    rw [isOpen_iff_mem_nhds]
    intro r hr
    obtain ⟨U, hU, haU, hUV, K, hK, hKconn, hsK, hrK, α, hα, hcurves⟩ := hr
    apply Filter.mem_of_superset (hK.mem_nhds hrK)
    intro q hq
    exact ⟨U, hU, haU, hUV, K, hK, hKconn, hsK, hq, α, hα, hcurves⟩
  have hseg : uIcc s0 b ⊆ J := hconn.ordConnected.uIcc_subset hs0 hb
  have hclosed : closure Good ∩ uIcc s0 b ⊆ Good := by
    rintro s ⟨hscl, hsseg⟩
    have hsJ : s ∈ J := hseg hsseg
    let x0 : M := γ s
    have hγCont : ContinuousOn γ J := by
      intro r hr
      exact (hγ r hr).2.1.continuousAt.continuousWithinAt
    have hγAt : ContinuousAt γ s :=
      (hγCont s hsJ).continuousAt (hJ.mem_nhds hsJ)
    have hsrcNhds : γ ⁻¹' (chartAt H x0).source ∈ nhds s := by
      apply hγAt.preimage_mem_nhds
      apply (chartAt H x0).open_source.mem_nhds
      simpa only [x0] using mem_chart_source H (γ s)
    have hlocalNhds : J ∩ γ ⁻¹' (chartAt H x0).source ∈ nhds s :=
      inter_mem (hJ.mem_nhds hsJ) hsrcNhds
    obtain ⟨a, c, hsQ, hQnhds, hQsub⟩ :=
      exists_Icc_mem_subset_of_mem_nhds hlocalNhds
    let Q : Set Real := Icc a c
    let X : ∀ r, TangentSpace I (γ r) :=
      fun r ↦ lVelocity (I := I) γ r
    let zref : Real → E × E := fun r ↦
      (chartCurve (I := I) x0 γ r,
        chartRepAtBase (I := I) x0 γ X r)
    have hzrefCont : ContinuousOn zref Q := by
      intro r hr
      have hrlocal : r ∈ J ∩ γ ⁻¹' (chartAt H x0).source := hQsub hr
      have hrdata := hγ r hrlocal.1
      have hphase := lRegularizedCurve_phase S T x0 γ r hrdata.2.1
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
      have hrlocal : r ∈ J ∩ γ ⁻¹' (chartAt H x0).source := hQsub hrQ
      refine ⟨(hγ r hrlocal.1).1, ?_⟩
      change extChartAt I x0 (γ r) ∈ interior (extChartAt I x0).target
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
    obtain ⟨V1, hV1open, ha0V1, hV1V, K, hKopen, hKconn, hs0K, htK,
      alpha, halpha, hcurves⟩ := htGood
    have htlocal : t ∈ J ∩ γ ⁻¹' (chartAt H x0).source := hQsub htQ
    have hEq : Set.EqOn (fun r ↦ alpha (a0, r)) γ (K ∩ J) :=
      lRegularizedSolution_eqOn S hS T hKopen hKconn hs0K hJ hconn hs0
        (hcurves a0 ha0V1).2.2 hγ
        (by rw [(hcurves a0 ha0V1).1, hstart])
        (by rw [(hcurves a0 ha0V1).2.1, hvel])
    have hpos : alpha (a0, t) = γ t := hEq ⟨htK, htlocal.1⟩
    have heqGerm : (fun r ↦ alpha (a0, r)) =ᶠ[nhds t] γ :=
      hEq.eventuallyEq_of_mem
        ((hKopen.inter hJ).mem_nhds ⟨htK, htlocal.1⟩)
    have hvelEq : lVelocity (I := I) (fun r ↦ alpha (a0, r)) t =
        lVelocity (I := I) γ t := by
      with_unfolding_all exact
        (congrArg (fun L ↦ L (1 : Real))
          (heqGerm.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)))
    have hptC : (t, zref t) ∈ C := ⟨t, htQ, rfl⟩
    obtain ⟨U, hUopen, hzrefU, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
      hphaseLocal (t, zref t) hptC
    have halphaSource : alpha (a0, t) ∈ (chartAt H x0).source := by
      rw [hpos]
      exact htlocal.2
    have hseedEq :
        (extChartAt I x0 (alpha (a0, t)),
          fderiv Real
            (fun r : Real ↦ extChartAt I x0 (alpha (a0, r))) t
            (1 : Real)) = zref t := by
      apply Prod.ext
      · simp only [zref, chartCurve]
        rw [hpos]
      · have hseedVelocity := lPhaseSeed_velocity (I := I) x0
          ((hcurves a0 ha0V1).2.2 t htK).2.1 halphaSource
        calc
          fderiv Real
              (fun r : Real ↦ extChartAt I x0 (alpha (a0, r))) t
              (1 : Real) =
            trivToE (I := I) x0 (alpha (a0, t))
              (lVelocity (I := I) (fun r ↦ alpha (a0, r)) t) := hseedVelocity
          _ = trivToE (I := I) x0 (γ t)
              (lVelocity (I := I) γ t) := by rw [hpos, hvelEq]
          _ = (zref t).2 := by rfl
    obtain ⟨W, hWopen, ha0W, hWV, beta, hbeta, heqOld, hgeodesic⟩ :=
      extend_lRegularizedGeodesicFamily_of_phaseFlow_eqOn S hS T x0 hV1open ha0V1 hKopen hKconn
        htK halpha (fun a ha => (hcurves a ha).2.2) halphaSource epsilon hepsilon hUopen
        (by rw [hseedEq]; exact hzrefU) Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
    have hsNew : s ∈ K ∪ Ioo (t - epsilon) (t + epsilon) := by
      right
      exact ⟨by linarith [htball.2], by linarith [htball.1]⟩
    have htI : t ∈ Ioo (t - epsilon) (t + epsilon) :=
      ⟨by linarith, by linarith⟩
    have hcurves' : ∀ a ∈ W,
        beta (a, s0) = (ζ a).proj ∧
          lVelocity (I := I) (fun r => beta (a, r)) s0 = (ζ a).2 ∧
          IsLRegularizedGeodesicOn S T (fun r => beta (a, r))
            (K ∪ Ioo (t - epsilon) (t + epsilon)) := by
      intro a ha
      have hgerm : (fun r => beta (a, r)) =ᶠ[𝓝 s0] (fun r => alpha (a, r)) := by
        filter_upwards [hKopen.mem_nhds hs0K] with r hr
        exact heqOld ⟨ha, hr⟩
      refine ⟨(heqOld ⟨ha, hs0K⟩).trans (hcurves a (hWV ha)).1, ?_, hgeodesic a ha⟩
      unfold lVelocity
      rw [hgerm.mfderiv_eq]
      exact (hcurves a (hWV ha)).2.1
    exact ⟨W, hWopen, ha0W, hWV.trans hV1V, K ∪ Ioo (t - epsilon) (t + epsilon),
      hKopen.union isOpen_Ioo,
      hKconn.union t htK htI isPreconnected_Ioo,
      Or.inl hs0K, hsNew, beta, hbeta, hcurves'⟩
  have hall : uIcc s0 b ⊆ Good :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hGoodOpen
      ⟨s0, Set.left_mem_uIcc, hGood0⟩ hclosed
  obtain ⟨U, hU, haU, hUV, K, hK, hKconn, hsK, hbK, alpha, halpha, hcurves⟩ := hall Set.right_mem_uIcc
  refine ⟨U, hU, haU, hUV, K, hK, hKconn, hsK, hbK, alpha, halpha, hcurves, ?_⟩
  exact lRegularizedSolution_eqOn S hS T hK hKconn hsK hJ hconn hs0
    (hcurves a0 haU).2.2 hγ ((hcurves a0 haU).1.trans hstart.symm)
    ((hcurves a0 haU).2.1.trans hvel.symm)

end DifferentialGeometry.PDE.RicciFlow.Perelman
