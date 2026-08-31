import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Regularized

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
theorem exists_lTailFamily
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T s0 : Real) (x : M) (A0 : TangentSpace I x)
    (hT : T - s0 ^ 2 ∈ D.regular) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) ∧
            ∀ A ∈ V,
              alpha (A, s0) = x ∧
                lVelocity (I := I) (fun s ↦ alpha (A, s)) s0 = A ∧
                ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
                  T - s ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun r ↦ alpha (A, r)) s ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun r ↦ alpha (A, r))
                        (fun r : Real ↦
                          lVelocity (I := I) (fun q ↦ alpha (A, q)) r) s) s ∧
                    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
                        (fun r ↦ alpha (A, r))
                        (fun r : Real ↦
                          lVelocity (I := I) (fun q ↦ alpha (A, q)) r) s =
                      lRegAccel S T s (alpha (A, s))
                        (lVelocity (I := I) (fun q ↦ alpha (A, q)) s) := by
  let seed : E → E × E := fun A ↦
    (extChartAt I x x, A)
  let z0 : E × E := seed A0
  have hz0pos : z0.1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0, seed] using extChartAt_target_mem_nhds (I := I) x
  obtain ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
    exists_lPhaseAt S hS T x s0 z0 hT hz0pos
  let V : Set E := seed ⁻¹' U
  have hseed : ContDiff Real ∞ seed :=
    contDiff_const.prodMk contDiff_id
  have hVopen : IsOpen V := hUopen.preimage hseed.continuous
  have hA0V : A0 ∈ V := by
    change seed A0 ∈ U
    exact hz0U
  let input : E × Real → (E × E) × Real := fun p ↦ (seed p.1, p.2)
  let phase : E × Real → E × E := fun p ↦ Phi (input p)
  let alpha : E × Real → M := fun p ↦
    (extChartAt I x).symm (phase p).1
  have hinput : ContDiff Real ∞ input :=
    (hseed.comp contDiff_fst).prodMk contDiff_snd
  have hinputMap : MapsTo input
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon))
      (U ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) := by
    rintro ⟨A, s⟩ ⟨hA, hs⟩
    exact ⟨hA, hs⟩
  have hphase : ContDiffOn Real ∞ phase
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) := by
    have hraw := hPhiSmooth.comp hinput.contDiffOn hinputMap
    have hfun : Phi ∘ input = phase := by
      rfl
    rw [hfun] at hraw
    exact hraw
  have hphaseMap : MapsTo (fun p : E × Real ↦ (phase p).1)
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon))
      (extChartAt I x).target := by
    intro p hp
    exact interior_subset (hPhiMap (hinputMap hp)).2
  have halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
      (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, E × Real) 𝓘(Real, E) ∞
        (fun p ↦ (phase p).1)
        (V ×ˢ Ioo (s0 - epsilon) (s0 + epsilon)) :=
      hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
      hphaseMD hphaseMap
  refine ⟨epsilon, hepsilon, V, hVopen, hA0V, alpha, halpha, ?_⟩
  intro A hA
  let z : Real → E × E := fun s ↦ phase (A, s)
  let gamma : Real → M := lPhaseCurve (I := I) x z
  let W : ∀ s, TangentSpace I (gamma s) := lPhaseVel (I := I) x z
  have hzU : seed A ∈ U := by
    exact hA
  have hsol : ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
      HasDerivAt z (lPhaseField S T x s (z s)) s := by
    intro s hs
    simpa only [z, phase, input] using hPhiDeriv (seed A) hzU s hs
  have hdata : ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
      T - s ^ 2 ∈ D.regular ∧
        (z s).1 ∈ interior (extChartAt I x).target := by
    intro s hs
    have hmem : ((seed A, s) : (E × E) × Real) ∈
        U ×ˢ Ioo (s0 - epsilon) (s0 + epsilon) := ⟨hzU, hs⟩
    have hmap := hPhiMap hmem
    change T - s ^ 2 ∈ D.regular ∧
      (Phi (seed A, s)).1 ∈ interior (extChartAt I x).target at hmap
    exact hmap
  have hzs0 : z s0 = seed A := by
    simpa only [z, phase, input] using hPhi0 (seed A) hzU
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
  have hgamma0 : gamma s0 = x := by
    simp only [gamma, lPhaseCurve, hzs0, seed]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hvel0 : lVelocity (I := I) gamma s0 = A := by
    have hv := hvel hs0
    change lVelocity (I := I) gamma s0 =
      trivFromE (I := I) x (gamma s0) (z s0).2 at hv
    rw [hgamma0, hzs0] at hv
    exact hv.trans (by
      change trivFromE (I := I) x x A = A
      rw [trivFromE_self_apply]
      exact DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply (I := I) x A)
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
    simpa only [gamma, W] using lPhaseVel_diff (I := I) x z s
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
    _ = lRegAccel S T s (gamma s) (W s) := by
      simpa only [gamma, W] using
        lPhase_accel S T x z s hzs hsdata.2
    _ = lRegAccel S T s (gamma s)
        (lVelocity (I := I) gamma s) := by
      rw [hfield.eq_of_nhds]

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem tailTimeVel_smooth
    {F : E × Real → E} {A0 : E} {s0 : Real}
    (hF : ContDiffAt Real ∞ F (A0, s0)) :
    ContDiffAt Real ∞
      (fun A : E ↦
        fderiv Real (fun s : Real ↦ F (A, s)) s0 (1 : Real)) A0 := by
  have hF' : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, E) ∞
      (Function.uncurry (fun A : E ↦ fun s : Real ↦ F (A, s)))
      (A0, s0) := by
    have h := hF.contMDiffAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    have hfun : Function.uncurry (fun A : E ↦ fun s : Real ↦ F (A, s)) = F := by
      funext p
      rfl
    rw [hfun]
    exact h
  have htime : ContMDiffAt 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun _ : E ↦ s0) A0 := contMDiffAt_const
  have hparam : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (id : E → E) A0 := contMDiffAt_id
  have hone : ContMDiffAt 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun _ : E ↦ (1 : Real)) A0 := contMDiffAt_const
  have h := ContMDiffAt.mfderiv_apply
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E))
    (f := fun A : E ↦ fun s : Real ↦ F (A, s))
    (g := fun _ : E ↦ s0) (g₁ := id)
    (g₂ := fun _ : E ↦ (1 : Real))
    (x₀ := A0) (m := ∞) (n := ∞)
    hF' htime hparam hone le_rfl
  apply contMDiffAt_iff_contDiffAt.mp
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv, id_eq] using h

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M] in
private theorem tailSeed_smooth
    {alpha : E × Real → M} {A0 : E} {s0 : Real} (x0 : M)
    (hsrc : alpha (A0, s0) ∈ (chartAt H x0).source)
    (halpha : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s0)) :
    ContDiffAt Real ∞
      (fun A : E ↦
        (extChartAt I x0 (alpha (A, s0)),
          fderiv Real
            (fun s : Real ↦ extChartAt I x0 (alpha (A, s))) s0
            (1 : Real))) A0 := by
  let F : E × Real → E := fun p ↦ extChartAt I x0 (alpha p)
  have hchart : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, E) ∞ F (A0, s0) := by
    exact (contMDiffAt_extChartAt' (I := I) hsrc).comp (A0, s0) halpha
  have hF : ContDiffAt Real ∞ F (A0, s0) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hchart
  have hincl : ContDiffAt Real ∞ (fun A : E ↦ (A, s0)) A0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hpos : ContDiffAt Real ∞ (fun A : E ↦ F (A, s0)) A0 := by
    have hcomp := hF.comp A0 hincl
    have hfun : F ∘ (fun A : E ↦ (A, s0)) = fun A : E ↦ F (A, s0) := by
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hvel : ContDiffAt Real ∞
      (fun A : E ↦
        fderiv Real (fun s : Real ↦ F (A, s)) s0 (1 : Real)) A0 :=
    tailTimeVel_smooth hF
  simpa only [F] using hpos.prodMk hvel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailFamily_step_of
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : E × Real → M} {V : Set E} {J : Set Real}
    {A0 : E} {s0 t : Real} (x x0 : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (hs0J : s0 ∈ J) (htJ : t ∈ J)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ J))
    (hcurves : ∀ A ∈ V,
      alpha (A, s0) = x ∧
        lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
        ∀ r ∈ J,
          T - r ^ 2 ∈ D.regular ∧
            MDifferentiableAt 𝓘(Real, Real) I (fun q ↦ alpha (A, q)) r ∧
            DifferentiableAt Real
              (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
            covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
              lRegAccel S T r (alpha (A, r))
                (lVelocity (I := I) (fun q ↦ alpha (A, q)) r))
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
    ∃ W : Set E, IsOpen W ∧ A0 ∈ W ∧ W ⊆ V ∧
      ∃ beta : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta
              (W ×ˢ (J ∪ Ioo (t - epsilon) (t + epsilon))) ∧
            ∀ A ∈ W,
              beta (A, s0) = x ∧
                lVelocity (I := I) (fun r ↦ beta (A, r)) s0 = A ∧
                ∀ r ∈ J ∪ Ioo (t - epsilon) (t + epsilon),
                  T - r ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun q ↦ beta (A, q)) r ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun q ↦ beta (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ beta (A, z)) q) r) r ∧
                    covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                        (fun q ↦ beta (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ beta (A, z)) q) r =
                      lRegAccel S T r (beta (A, r))
                        (lVelocity (I := I) (fun q ↦ beta (A, q)) r) := by
  classical
  let pos : E → M := fun A ↦ alpha (A, t)
  have hprodOpen : IsOpen (V ×ˢ J) := hVopen.prod hJopen
  have hposCont : ContinuousOn pos V := by
    intro A hA
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A, t) :=
      (halpha (A, t) ⟨hA, htJ⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hA, htJ⟩)
    have hincl : ContMDiffAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun B : E ↦ (B, t)) A :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (halphaAt.comp A hincl).continuousAt.continuousWithinAt
  let V0 : Set E := V ∩ pos ⁻¹' (chartAt H x0).source
  have hV0open : IsOpen V0 :=
    hposCont.isOpen_inter_preimage hVopen (chartAt H x0).open_source
  have hA0V0 : A0 ∈ V0 := ⟨hA0V, hsrc⟩
  let seed : E → E × E := fun A ↦
    (extChartAt I x0 (alpha (A, t)),
      fderiv Real (fun r : Real ↦ extChartAt I x0 (alpha (A, r))) t
        (1 : Real))
  have hseed : ContDiffOn Real ∞ seed V0 := by
    intro A hA
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A, t) :=
      (halpha (A, t) ⟨hA.1, htJ⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hA.1, htJ⟩)
    exact (tailSeed_smooth (I := I) x0 hA.2 halphaAt).contDiffWithinAt
  let W : Set E := V0 ∩ seed ⁻¹' U
  have hWopen : IsOpen W :=
    hseed.continuousOn.isOpen_inter_preimage hV0open hUopen
  have hA0W : A0 ∈ W := by
    refine ⟨hA0V0, ?_⟩
    change seed A0 ∈ U
    exact hseedU
  have hWV : W ⊆ V := fun _ h ↦ h.1.1
  let K : Set Real := Ioo (t - epsilon) (t + epsilon)
  have htK : t ∈ K := ⟨by linarith, by linarith⟩
  let input : E × Real → (E × E) × Real := fun p ↦ (seed p.1, p.2)
  let phase : E × Real → E × E := fun p ↦ Phi (input p)
  let eta : E × Real → M := fun p ↦
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
  have hphaseMap : MapsTo (fun p : E × Real ↦ (phase p).1)
      (W ×ˢ K) (extChartAt I x0).target := by
    intro p hp
    exact interior_subset (hPhiMap (hinputMap hp)).2
  have hetaSmooth : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ eta (W ×ˢ K) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, E × Real) 𝓘(Real, E) ∞
        (fun p ↦ (phase p).1) (W ×ˢ K) := hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x0).comp
      hphaseMD hphaseMap
  have hetaReg : ∀ A ∈ W, ∀ r ∈ K,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I (fun q ↦ eta (A, q)) r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) (fun q ↦ eta (A, q))
            (fun q : Real ↦ lVelocity (I := I) (fun z ↦ eta (A, z)) q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
            (fun q ↦ eta (A, q))
            (fun q : Real ↦ lVelocity (I := I) (fun z ↦ eta (A, z)) q) r =
          lRegAccel S T r (eta (A, r))
            (lVelocity (I := I) (fun q ↦ eta (A, q)) r) := by
    intro A hA
    let z : Real → E × E := fun r ↦ phase (A, r)
    let gamma : Real → M := lPhaseCurve (I := I) x0 z
    let B : ∀ r, TangentSpace I (gamma r) := lPhaseVel (I := I) x0 z
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
      simpa only [gamma, B] using lPhaseVel_diff (I := I) x0 z r
        hq.differentiableAt hv.differentiableAt hrdata.2
    have hveldiff : DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun w : Real ↦ lVelocity (I := I) gamma w) r) r :=
      hBdiff.congr_of_eventuallyEq
        (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) gamma hfield)
    have hacc : covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
          (fun w : Real ↦ lVelocity (I := I) gamma w) r =
        lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r) := by
      calc
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun w : Real ↦ lVelocity (I := I) gamma w) r =
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma B r :=
            covDerivAlong_congr_of_eventuallyEq
              (I := I) (S.base.metric (T - r ^ 2)) gamma hfield
        _ = lRegAccel S T r (gamma r) (B r) := by
          simpa only [gamma, B] using lPhase_accel S T x0 z r hzr hrdata.2
        _ = lRegAccel S T r (gamma r)
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
  have hetaVel : ∀ A ∈ W,
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
    have hphaseVel := lPhase_velocity (I := I) x0 z t hq
      (hPhiMap (show ((seed A, t) : (E × E) × Real) ∈ U ×ˢ K from
        ⟨hA.2, htK⟩)).2
    have hsrcA : alpha (A, t) ∈ (chartAt H x0).source := hA.1.2
    have hbase : alpha (A, t) ∈
        (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrcA
    have hseedVel : (seed A).2 =
        trivToE (I := I) x0 (alpha (A, t))
          (lVelocity (I := I) (fun r ↦ alpha (A, r)) t) :=
      lPhaseSeed_vel (I := I) x0 ((hcurves A (hWV hA)).2.2 t htJ).2.1 hsrcA
    have hetaGamma : (fun r ↦ eta (A, r)) = gamma := by rfl
    have hgamma0 : gamma t = alpha (A, t) := by
      rw [← hetaGamma]
      exact heta0 A hA
    rw [hetaGamma]
    change lVelocity (I := I) gamma t =
      trivFromE (I := I) x0 (gamma t) (z t).2 at hphaseVel
    rw [hgamma0, hzt] at hphaseVel
    exact hphaseVel.trans (by
      rw [hseedVel]
      exact trivFromE_trivToE (I := I) x0 hbase _)
  have hmatch : ∀ A ∈ W,
      Set.EqOn (fun r ↦ alpha (A, r)) (fun r ↦ eta (A, r)) (J ∩ K) := by
    intro A hA
    exact lRegSol_eqOn S hS T hJopen hJconn htJ isOpen_Ioo
      isPreconnected_Ioo htK (hcurves A (hWV hA)).2.2 (hetaReg A hA)
      (heta0 A hA).symm (hetaVel A hA).symm
  let beta : E × Real → M := fun p ↦ if p.2 ∈ J then alpha p else eta p
  have hbetaSmooth : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta (W ×ˢ (J ∪ K)) := by
    intro p hp
    by_cases hpJ : p.2 ∈ J
    · have halphaAt : ContMDiffAt
          (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha p :=
        (halpha p ⟨hWV hp.1, hpJ⟩).contMDiffAt
          (hprodOpen.mem_nhds ⟨hWV hp.1, hpJ⟩)
      have heq : beta =ᶠ[nhds p] alpha := by
        filter_upwards [(hJopen.preimage continuous_snd).mem_nhds hpJ] with q hq
        change q.2 ∈ J at hq
        simp only [beta]
        rw [if_pos hq]
      exact (halphaAt.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have hpK : p.2 ∈ K := hp.2.resolve_left hpJ
      have hWKopen : IsOpen (W ×ˢ K) := hWopen.prod isOpen_Ioo
      have hetaAt : ContMDiffAt
          (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ eta p :=
        (hetaSmooth p ⟨hp.1, hpK⟩).contMDiffAt
          (hWKopen.mem_nhds ⟨hp.1, hpK⟩)
      have heq : beta =ᶠ[nhds p] eta := by
        filter_upwards [(hWopen.preimage continuous_fst).mem_nhds hp.1,
          (isOpen_Ioo.preimage continuous_snd).mem_nhds hpK] with q hqW hqK
        simp only [beta]
        by_cases hqJ : q.2 ∈ J
        · rw [if_pos hqJ]
          exact hmatch q.1 hqW ⟨hqJ, hqK⟩
        · rw [if_neg hqJ]
      exact (hetaAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  refine ⟨W, hWopen, hA0W, hWV, beta, hbetaSmooth, ?_⟩
  intro A hA
  have hbetaAlpha : ∀ r ∈ J,
      (fun q ↦ beta (A, q)) =ᶠ[nhds r] (fun q ↦ alpha (A, q)) := by
    intro r hr
    filter_upwards [hJopen.mem_nhds hr] with q hq
    simp only [beta]
    rw [if_pos hq]
  have hbetaEta : ∀ r ∈ K,
      (fun q ↦ beta (A, q)) =ᶠ[nhds r] (fun q ↦ eta (A, q)) := by
    intro r hr
    filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
    simp only [beta]
    by_cases hqJ : q ∈ J
    · rw [if_pos hqJ]
      exact hmatch A hA ⟨hqJ, hq⟩
    · rw [if_neg hqJ]
  have hbeta0 : beta (A, s0) = x := by
    simpa only [beta, if_pos hs0J] using (hcurves A (hWV hA)).1
  have hbetaVel : lVelocity (I := I) (fun r ↦ beta (A, r)) s0 = A := by
    have heq := hbetaAlpha s0 hs0J
    have hvel := congrArg (fun L ↦ L (1 : Real))
      (heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I))
    simpa only [lVelocity] using hvel.trans (hcurves A (hWV hA)).2.1
  refine ⟨hbeta0, hbetaVel, ?_⟩
  intro r hr
  rcases hr with hrJ | hrK
  · exact lRegData_congr S T r (hbetaAlpha r hrJ)
      ((hcurves A (hWV hA)).2.2 r hrJ)
  · exact lRegData_congr S T r (hbetaEta r hrK) (hetaReg A hA r hrK)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailFamily_step
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : E × Real → M} {V : Set E} {J : Set Real}
    {A0 : E} {s0 t : Real} (x : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (hs0J : s0 ∈ J) (htJ : t ∈ J)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ J))
    (hcurves : ∀ A ∈ V,
      alpha (A, s0) = x ∧
        lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
        ∀ r ∈ J,
          T - r ^ 2 ∈ D.regular ∧
            MDifferentiableAt 𝓘(Real, Real) I (fun q ↦ alpha (A, q)) r ∧
            DifferentiableAt Real
              (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
            covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
              lRegAccel S T r (alpha (A, r))
                (lVelocity (I := I) (fun q ↦ alpha (A, q)) r)) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ W : Set E, IsOpen W ∧ A0 ∈ W ∧ W ⊆ V ∧
        ∃ beta : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta
              (W ×ˢ (J ∪ Ioo (t - epsilon) (t + epsilon))) ∧
            ∀ A ∈ W,
              beta (A, s0) = x ∧
                lVelocity (I := I) (fun r ↦ beta (A, r)) s0 = A ∧
                ∀ r ∈ J ∪ Ioo (t - epsilon) (t + epsilon),
                  T - r ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun q ↦ beta (A, q)) r ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun q ↦ beta (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ beta (A, z)) q) r) r ∧
                    covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                        (fun q ↦ beta (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ beta (A, z)) q) r =
                      lRegAccel S T r (beta (A, r))
                        (lVelocity (I := I) (fun q ↦ beta (A, q)) r) := by
  let x0 : M := alpha (A0, t)
  let z0 : E × E :=
    (extChartAt I x0 (alpha (A0, t)),
      fderiv Real (fun r : Real ↦ extChartAt I x0 (alpha (A0, r))) t
        (1 : Real))
  have hsrc : alpha (A0, t) ∈ (chartAt H x0).source := by
    simpa only [x0] using mem_chart_source H (alpha (A0, t))
  have hreg : T - t ^ 2 ∈ D.regular :=
    ((hcurves A0 hA0V).2.2 t htJ).1
  have hz0 : z0.1 ∈ interior (extChartAt I x0).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0, x0] using
      extChartAt_target_mem_nhds (I := I) (alpha (A0, t))
  obtain ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
    exists_lPhaseAt S hS T x0 t z0 hreg hz0
  obtain ⟨W, hWopen, hA0W, hWV, beta, hbeta, hcurves'⟩ :=
    lTailFamily_step_of S hS T x x0 hVopen hA0V hJopen hJconn
      hs0J htJ halpha hcurves hsrc epsilon hepsilon hUopen
      (by simpa only [z0] using hz0U) Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
  exact ⟨epsilon, hepsilon, W, hWopen, hA0W, hWV, beta, hbeta, hcurves'⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailFamily_extend
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {gamma : Real → M} {J : Set Real} {x : M}
    {A0 : TangentSpace I x} {s0 b : Real}
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
          lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r)) :
    ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
      ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
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
    ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
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
    obtain ⟨epsilon, hepsilon, V, hVopen, hA0V, alpha, halpha, hcurves⟩ :=
      exists_lTailFamily S hS T s0 x A0 (hgamma s0 hs0J).1
    have hs0I : s0 ∈ Ioo (s0 - epsilon) (s0 + epsilon) :=
      ⟨by linarith, by linarith⟩
    exact ⟨V, hVopen, hA0V, Ioo (s0 - epsilon) (s0 + epsilon),
      isOpen_Ioo, isPreconnected_Ioo, hs0I, hs0I, alpha, halpha, hcurves⟩
  have hGoodOpen : IsOpen Good := by
    rw [isOpen_iff_mem_nhds]
    intro r hr
    obtain ⟨V, hVopen, hA0V, K, hKopen, hKconn, hs0K, hrK,
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
      hUnionOpen, hUnionConn, Or.inl hs0K, Or.inr hq,
      beta, hbeta, hcurves'⟩
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
    obtain ⟨V, hVopen, hA0V, K, hKopen, hKconn, hs0K, htK,
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
      Or.inl hs0K, hsNew, beta, hbeta, hcurves'⟩
  have hall : uIcc s0 b ⊆ Good :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hGoodOpen
      ⟨s0, Set.left_mem_uIcc, hGood0⟩ hclosed
  exact hall Set.right_mem_uIcc

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [IsManifold I ∞ M] in
theorem lTailLine_deriv
    {alpha : E × Real → M} (A B : E) (s : Real)
    (halpha : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A, s)) :
    lVelocity (I := I) (fun u : Real ↦ alpha (A + u • B, s)) 0 =
      mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, s)) A B := by
  let line : Real → E := fun u ↦ A + u • B
  let phi : E → M := fun W ↦ alpha (W, s)
  have hfoot : line 0 = A := by
    simp only [line, zero_smul, add_zero]
  have hincl : ContMDiffAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun W : E ↦ (W, s)) A :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hslice : ContMDiffAt 𝓘(Real, E) I ∞ phi A := by
    have hcomp := halpha.comp A hincl
    have hfun : alpha ∘ (fun W : E ↦ (W, s)) = phi := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have hphi : MDifferentiableAt 𝓘(Real, E) I phi A :=
    hslice.mdifferentiableAt (by simp)
  have hphi' : MDifferentiableAt 𝓘(Real, E) I phi (line 0) := by
    rw [hfoot]
    exact hphi
  have hline : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) line 0 := by
    have hlineCD : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
      have hraw := (contMDiff_const.add
        (contMDiff_id.smul contMDiff_const) :
          ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
            ((fun _ : Real ↦ A) + fun u : Real ↦ u • B))
      have hfun : ((fun _ : Real ↦ A) + fun u : Real ↦ u • B) = line := by
        funext u
        rfl
      rw [hfun] at hraw
      exact hraw
    exact hlineCD.contMDiffAt.mdifferentiableAt (by simp)
  have hline_apply :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) line 0 (1 : Real) = B := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt line
        (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) B) 0 := by
      have hraw : HasFDerivAt (fun x : Real ↦ A + id x • B)
          (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) B) 0 :=
        ((hasFDerivAt_id (0 : Real)).smul_const B).const_add A
      have hfun : (fun x : Real ↦ A + id x • B) = line := by
        funext u
        rfl
      rw [hfun] at hraw
      exact hraw
    rw [hfd.fderiv]
    change (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) B)
      (1 : Real) = B
    rw [ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
  have hcomp := mfderiv_comp_apply (f := line) (g := phi) (x := (0 : Real))
    hphi' hline (1 : Real)
  unfold lVelocity
  change mfderiv 𝓘(Real, Real) I (phi ∘ line) 0 (1 : Real) =
    mfderiv 𝓘(Real, E) I phi A B
  rw [hcomp, hline_apply, hfoot]

omit [InnerProductSpace Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M] in
theorem lTailLine_dstart
    (g : SmoothRiemannianMetric I M)
    {alpha : E × Real → M} {V : Set E} {A0 B : E} {s0 : Real} (x : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (halpha : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s0))
    (hfixed : ∀ A ∈ V, alpha (A, s0) = x)
    (hlaunch : ∀ A ∈ V,
      lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A) :
    covDerivAlong (I := I) g (fun r ↦ alpha (A0, r))
        (fun r ↦ lVelocity (I := I)
          (fun u : Real ↦ alpha (A0 + u • B, r)) 0) s0 = B := by
  let line : Real → E := fun u ↦ A0 + u • B
  let F : Real → Real → M := fun u r ↦ alpha (line u, r)
  have hline : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
    have hraw := (contMDiff_const.add
      (contMDiff_id.smul contMDiff_const) :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
          ((fun _ : Real ↦ A0) + fun u : Real ↦ u • B))
    have hfun : ((fun _ : Real ↦ A0) + fun u : Real ↦ u • B) = line := by
      funext u
      rfl
    rw [hfun] at hraw
    exact hraw
  have hline0 : line 0 = A0 := by
    simp only [line, zero_smul, add_zero]
  have hline0V : line 0 ∈ V := by
    rw [hline0]
    exact hA0V
  have hnear : ∀ᶠ u in nhds (0 : Real), line u ∈ V := by
    have hpre := hline.continuous.continuousAt.preimage_mem_nhds
      (hVopen.mem_nhds hline0V)
    exact hpre
  have hparam : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun q : Real × Real ↦ (line q.1, q.2)) (0, s0) := by
    exact ((contMDiff_const.add
      (contMDiff_fst.smul contMDiff_const)).prodMk
        contMDiff_snd).contMDiffAt
  have halphaAt : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (line 0, s0) := by
    simpa only [hline0] using halpha
  have hFInf : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
      (fun q : Real × Real ↦ F q.1 q.2) (0, s0) := by
    have hcomp := halphaAt.comp (0, s0) hparam
    have hfun : alpha ∘ (fun q : Real × Real ↦ (line q.1, q.2)) =
        (fun q : Real × Real ↦ F q.1 q.2) := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have hF2 : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2
      (fun q : Real × Real ↦ F q.1 q.2) (0, s0) :=
    hFInf.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hfev : ∀ᶠ q in nhds ((0 : Real), s0),
      ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, Real)) I 2
        (fun p : Real × Real ↦ F p.1 p.2) q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hF2
  have hlineU : Tendsto (fun u : Real ↦ (u, s0)) (nhds 0) (nhds (0, s0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hlineR : Tendsto (fun r : Real ↦ ((0 : Real), r))
      (nhds s0) (nhds (0, s0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hslice_u : ∀ᶠ u in nhds (0 : Real),
      ContMDiffAt 𝓘(Real, Real) I 2 (fun r : Real ↦ F u r) s0 := by
    filter_upwards [hlineU.eventually hfev] with u hu
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun r : Real ↦ (u, r)) s0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact hu.comp s0 hincl
  have hslice_v : ∀ᶠ r in nhds s0,
      ContMDiffAt 𝓘(Real, Real) I 2 (fun u : Real ↦ F u r) 0 := by
    filter_upwards [hlineR.eventually hfev] with r hr
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun u : Real ↦ (u, r)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    have hcomp : ContMDiffAt 𝓘(Real, Real) I 2
        ((fun p : Real × Real ↦ F p.1 p.2) ∘
          fun u : Real ↦ (u, r)) 0 :=
      hr.comp 0 hincl
    have hfun : ((fun p : Real × Real ↦ F p.1 p.2) ∘
        fun u : Real ↦ (u, r)) = (fun u : Real ↦ F u r) := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have htrans : ContinuousAt (fun u : Real ↦ F u s0) 0 := by
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun u : Real ↦ (u, s0)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact (hF2.comp 0 hincl).continuousAt
  have hcentral : ContinuousAt (fun r : Real ↦ F 0 r) s0 := by
    have hincl : ContMDiffAt 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 2
        (fun r : Real ↦ ((0 : Real), r)) s0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hF2.comp s0 hincl).continuousAt
  have hsrc : F 0 s0 ∈ (chartAt H (F 0 s0)).source :=
    mem_chart_source H (F 0 s0)
  have hext : ContMDiffAt I 𝓘(Real, E) 2
      (extChartAt I (F 0 s0)) (F 0 s0) :=
    contMDiffAt_extChartAt' (I := I) (n := 2) (x := F 0 s0) hsrc
  have hpull : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, E) 2
      (fun q : Real × Real ↦ extChartAt I (F 0 s0) (F q.1 q.2))
      (0, s0) := by
    exact hext.comp (0, s0) hF2
  have hcoord : ContDiffAt Real 2
      (fun q : Real × Real ↦ extChartAt I (F 0 s0) (F q.1 q.2))
      (0, s0) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hpull
  have hcomm :=
    covDerivAlong_commute_transverse_longitudinal_of_variation
      (I := I) g F s0 hcoord hslice_u hslice_v htrans hcentral
  have hfixedEv : (fun u : Real ↦ F u s0) =ᶠ[nhds 0]
      (fun _ ↦ x) := by
    filter_upwards [hnear] with u hu
    exact hfixed (line u) hu
  have hlaunchEv : (fun u : Real ↦ lVelocity (I := I) (F u) s0) =ᶠ[nhds 0]
      line := by
    filter_upwards [hnear] with u hu
    exact hlaunch (line u) hu
  have hlineDeriv : HasDerivAt line B 0 := by
    simpa only [line, id_eq, one_smul] using
      ((hasDerivAt_id (0 : Real)).smul_const B).const_add A0
  have hLHS := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := I) g (fun u ↦ lVelocity (I := I) (F u) s0) line
      hfixedEv hlaunchEv
  have hconst := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_const
    (I := I) g x line 0 hlineDeriv.differentiableAt
  have hleft : covDerivAlong (I := I) g (fun u : Real ↦ F u s0)
      (fun u ↦ lVelocity (I := I) (F u) s0) 0 = B :=
    hLHS.trans (hconst.trans hlineDeriv.deriv)
  have hright := hcomm.symm.trans hleft
  have hcurve : (fun r : Real ↦ alpha (A0, r)) = F 0 := by
    funext r
    simp only [F, line, zero_smul, add_zero]
  rw [hcurve]
  change covDerivAlong (I := I) g (F 0)
      (fun r ↦ mfderiv 𝓘(Real, Real) I (fun u ↦ F u r) 0 (1 : Real)) s0 = B
  exact hright

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M] in
theorem exists_lTail_germ
    {alpha : Real → M} {Y : ∀ s, TangentSpace I (alpha s)}
    {K : Set Real} {s0 b : Real}
    (hKopen : IsOpen K) (hsb : s0 < b) (hseg : Icc s0 b ⊆ K)
    (hfield : ContMDiffOn 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) K) :
    ∃ rho : Real → Real, ∃ a d : Real,
      a < s0 ∧ b < d ∧ ContDiff Real ∞ rho ∧
      Set.EqOn rho id (Icc a d) ∧
      (∀ s ∈ Icc a d, HasDerivAt rho 1 s) ∧
      (∀ s : Real, rho s ∈ K) ∧
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha (rho s)) (Y (rho s)) : TangentBundle I M)) ∧
      Set.EqOn
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha (rho s)) (Y (rho s)) : TangentBundle I M))
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (Y s) : TangentBundle I M))
        (Icc a d) := by
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hKopen hseg
  let a : Real := s0 - margin / 2
  let d : Real := b + margin / 2
  let eps : Real := margin / 4
  have has0 : a < s0 := by
    dsimp only [a]
    linarith
  have hbd : b < d := by
    dsimp only [d]
    linarith
  have had : a < d := has0.trans (hsb.trans hbd)
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  have hrange : ∀ s : Real, rho s ∈ K := by
    intro s
    apply hbuffer
    by_cases hs0 : rho s ≤ s0
    · refine Metric.mem_cthickening_of_dist_le (rho s) s0 margin
          (Icc s0 b) ⟨le_rfl, hsb.le⟩ ?_
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs0)]
      have hlo := (hrho_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsb' : rho s ≤ b
      · refine Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
            (Icc s0 b) ⟨(not_le.mp hs0).le, hsb'⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (rho s) b margin
            (Icc s0 b) ⟨hsb.le, le_rfl⟩ ?_
        rw [Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb').le)]
        have hhi := (hrho_range s).2
        dsimp only [d, eps] at hhi
        linarith
  have hrhoMD : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hsmooth : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (rho s)) (Y (rho s)) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    exact hfield.comp hrhoMD.contMDiffOn (fun s _hs ↦ hrange s)
  refine ⟨rho, a, d, has0, hbd, hrho, ?_, hrho_deriv, hrange,
    hsmooth, ?_⟩
  · intro s hs
    simpa only [id_eq] using hrho_id s hs
  · intro s hs
    change TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (alpha (rho s)) (Y (rho s)) =
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (alpha s) (Y s)
    rw [hrho_id s hs]

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lTailLine_jacobi
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 B : E} {s0 : Real} (x : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hfixed : ∀ A ∈ V, alpha (A, s0) = x)
    (hgeo : ∀ A ∈ V, ∀ s ∈ K,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun q ↦ alpha (A, q)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r ↦ alpha (A, r)) s)) :
    IsLRegJacobi S T (fun s ↦ alpha (A0, s))
        (fun s ↦ lVelocity (I := I)
          (fun u : Real ↦ alpha (A0 + u • B, s)) 0) K ∧
      lVelocity (I := I)
        (fun u : Real ↦ alpha (A0 + u • B, s0)) 0 = 0 := by
  let line : Real → E := fun u ↦ A0 + u • B
  let f : Real → Real → M := fun u s ↦ alpha (line u, s)
  have hline : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
    have hraw := (contMDiff_const.add
      (contMDiff_id.smul contMDiff_const) :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
          ((fun _ : Real ↦ A0) + fun u : Real ↦ u • B))
    have hfun : ((fun _ : Real ↦ A0) + fun u : Real ↦ u • B) = line := by
      funext u
      rfl
    rw [hfun] at hraw
    exact hraw
  have hline0 : line 0 = A0 := by
    simp only [line, zero_smul, add_zero]
  have hline0V : line 0 ∈ V := by
    rw [hline0]
    exact hA0V
  have hnear : ∀ᶠ u in nhds (0 : Real), line u ∈ V := by
    have hpre := hline.continuous.continuousAt.preimage_mem_nhds
      (hVopen.mem_nhds hline0V)
    exact hpre
  constructor
  · intro s hs
    have hparam : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real))
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun q : Real × Real ↦ (line q.1, q.2)) (0, s) := by
      exact ((contMDiff_const.add
        (contMDiff_fst.smul contMDiff_const)).prodMk
          contMDiff_snd).contMDiffAt
    have hp : (A0, s) ∈ V ×ˢ K := ⟨hA0V, hs⟩
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s) :=
      (halpha (A0, s) hp).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds hp)
    have halphaAt' : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (line 0, s) := by
      simpa only [hline0] using halphaAt
    have hfInf : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
        (fun q : Real × Real ↦ f q.1 q.2) (0, s) := by
      have hcomp := halphaAt'.comp (0, s) hparam
      have hfun : alpha ∘ (fun q : Real × Real ↦ (line q.1, q.2)) =
          (fun q : Real × Real ↦ f q.1 q.2) := by rfl
      rw [hfun] at hcomp
      exact hcomp
    have hf : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
        (fun q : Real × Real ↦ f q.1 q.2) (0, s) :=
      hfInf.of_le (by
        change (↑(3 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)
    have hgeoNear : ∀ᶠ u in nhds (0 : Real),
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f u)
            (fun r ↦ lVelocity (I := I) (f u) r) s =
          lRegAccel S T s (f u s) (lVelocity (I := I) (f u) s) := by
      filter_upwards [hnear] with u hu
      simpa only [f] using hgeo (line u) hu s hs
    have hraw := lRegVar_jacobiAt (I := I) S T f s hf hgeoNear
    have hcurve : (fun r ↦ f 0 r) = (fun r ↦ alpha (A0, r)) := by
      funext r
      simp only [f, line, zero_smul, add_zero]
    have hfield : (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) =
        (fun r ↦ lVelocity (I := I)
          (fun u : Real ↦ alpha (A0 + u • B, r)) 0) := by
      funext r
      apply congrArg (fun c : Real → M ↦ lVelocity (I := I) c 0)
      funext u
      rfl
    rw [hcurve, hfield] at hraw
    exact hraw
  · have heq : (fun u : Real ↦ alpha (line u, s0)) =ᶠ[nhds 0]
        (fun _ ↦ x) := by
      filter_upwards [hnear] with u hu
      exact hfixed (line u) hu
    unfold lVelocity
    rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
    rw [mfderiv_const]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
