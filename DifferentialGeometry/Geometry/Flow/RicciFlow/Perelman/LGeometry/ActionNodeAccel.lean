import DifferentialGeometry.Analysis.Calculus.PuncturedDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionFiniteC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionStrictC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionPieceAccel

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lFinNode_reg
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 3) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last (m + 2)) = b)
    (p : Fin (m + 2) → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin (m + 2)) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    ∀ q : Fin (m + 1),
      let c := t q.succ.castSucc
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma c ∧
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r ↦ lVelocity (I := I) gamma r) c) c ∧
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) gamma
          (fun r ↦ lVelocity (I := I) gamma r) c =
        lRegAccel S T c (gamma c) (lVelocity (I := I) gamma c) := by
  classical
  intro q
  dsimp only
  let i : Fin (m + 2) := q.castSucc
  let j : Fin (m + 2) := q.succ
  let c : Real := t q.succ.castSucc
  let x : M := gamma c
  let X : ∀ r, TangentSpace I (gamma r) :=
    fun r ↦ lVelocity (I := I) gamma r
  let z : Real → E × E := fun r ↦
    (chartCurve (I := I) x gamma r,
      chartRepAtBase (I := I) x gamma X r)
  have hic : t i.castSucc < c := by
    change t q.castSucc.castSucc < t q.succ.castSucc
    exact ht Fin.castSucc_lt_succ
  have hcj : c < t j.succ := by
    change t q.succ.castSucc < t q.succ.succ
    exact ht Fin.castSucc_lt_succ
  have hac : a < c := by
    rw [← ht0]
    exact (ht.monotone (Fin.zero_le i.castSucc)).trans_lt hic
  have hcb : c < b := by
    rw [← htlast]
    exact hcj.trans_le (ht.monotone (Fin.le_last j.succ))
  have hcurve1 := lFinCurve_c1 (I := I) S hS T a b (m := m + 2)
    (by omega) t ht0 htlast p gamma hgamma u
    (fun k ↦ ht Fin.castSucc_lt_succ) hsrc hrep hreg hmin
  have hIcc : Icc a b ∈ 𝓝 c :=
    mem_of_superset (Ioo_mem_nhds hac hcb) Ioo_subset_Icc_self
  have hgamma1 : ContMDiffAt (modelWithCornersSelf Real Real) I 1 gamma c :=
    hcurve1.contMDiffAt hIcc
  have hmdiff : MDifferentiableAt
      (modelWithCornersSelf Real Real) I gamma c :=
    hgamma1.mdifferentiableAt (by norm_num)
  have hxsrc : gamma c ∈ (chartAt H x).source := by
    simpa only [x] using mem_chart_source H (gamma c)
  have hchart1 : ContDiffAt Real 1 (chartCurve (I := I) x gamma) c := by
    exact contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt (I := I) (x := x)).comp c hgamma1)
  let v : Real → E := fun r ↦
    (fderiv Real (chartCurve (I := I) x gamma) r) (1 : Real)
  have hvcont : ContinuousAt v c := by
    exact (hchart1.continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const
  have hgamma1' : ∀ᶠ r in 𝓝 c,
      ContMDiffAt (modelWithCornersSelf Real Real) I 1 gamma r :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by decide)).mp hgamma1
  have hxsrc' : ∀ᶠ r in 𝓝 c, gamma r ∈ (chartAt H x).source :=
    hgamma1.continuousAt.preimage_mem_nhds
      ((chartAt H x).open_source.mem_nhds hxsrc)
  have hrepv : (fun r ↦ chartRepAtBase (I := I) x gamma X r)
      =ᶠ[𝓝 c] v := by
    filter_upwards [hgamma1', hxsrc'] with r hr1 hrsrc
    have hbridge :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (hr1.mdifferentiableAt (by norm_num)) x hrsrc
    change
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real
          (gamma r) ((mfderiv (modelWithCornersSelf Real Real) I gamma r) 1) =
        (fderiv Real ((extChartAt I x) ∘ gamma) r) 1
    exact hbridge
  have hzcont : ContinuousAt z c := by
    apply hchart1.continuousAt.prodMk
    exact hvcont.congr_of_eventuallyEq hrepv
  have hzc : (z c).1 ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact (extChartAt I x).map_source (by
      simpa only [extChartAt_source] using hxsrc)
  have htreg : T - c ^ 2 ∈ D.regular := hreg c ⟨hac.le, hcb.le⟩
  have hgcont : ContinuousAt
      (fun r ↦ lPhaseField S T x r (z r)) c := by
    exact (lPhaseField_smoothAt S hS T x htreg hzc).continuousAt.comp_of_eq
      (continuousAt_id.prodMk hzcont) rfl
  have hpunc : ∀ᶠ r in 𝓝[≠] c,
      HasDerivAt z (lPhaseField S T x r (z r)) r := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioo_mem_nhds hic hcj),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hxsrc']
      with r hrc hrwin hrsrc
    have hrne : r ≠ c := by simpa only [mem_compl_iff, mem_singleton_iff] using hrc
    rcases lt_or_gt_of_ne hrne with hrc' | hcr'
    · have hri : r ∈ Ioo (t i.castSucc) (t i.succ) := by
        simpa only [i, c] using ⟨hrwin.1, hrc'⟩
      have hr2 := lStrict_piece_c2_at (I := I) S hS T a b t ht ht0 htlast
        p gamma hgamma u hsrc hrep hreg hmin i r hri
      have hvel :=
        DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) gamma r hr2
      have hacc := lStrict_piece_accel (I := I) S hS T a b t ht ht0
        htlast p gamma hgamma u hsrc hrep hreg hmin i r hri
      simpa only [z, X] using
        lRegCurve_phase (I := I) S T x gamma r
          (hr2.mdifferentiableAt (by norm_num)) hrsrc hvel hacc
    · have hrj : r ∈ Ioo (t j.castSucc) (t j.succ) := by
        simpa only [j, c] using ⟨hcr', hrwin.2⟩
      have hr2 := lStrict_piece_c2_at (I := I) S hS T a b t ht ht0 htlast
        p gamma hgamma u hsrc hrep hreg hmin j r hrj
      have hvel :=
        DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) gamma r hr2
      have hacc := lStrict_piece_accel (I := I) S hS T a b t ht ht0
        htlast p gamma hgamma u hsrc hrep hreg hmin j r hrj
      simpa only [z, X] using
        lRegCurve_phase (I := I) S T x gamma r
          (hr2.mdifferentiableAt (by norm_num)) hrsrc hvel hacc
  have hzder : HasDerivAt z (lPhaseField S T x c (z c)) c :=
    DifferentialGeometry.hasDerivAt_of_punct hpunc hzcont hgcont
  have hveldiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma X c) c := by
    have hsnd := hasFDerivAt_snd.comp_hasDerivAt c hzder
    change HasDerivAt (chartRepAtBase (I := I) x gamma X) _ c at hsnd
    have hx : x = gamma c := rfl
    rw [hx, chartRepAtBase_foot] at hsnd
    exact hsnd.differentiableAt
  have hphase := lPhase_accel (I := I) S T x z c hzder hzc
  have hcurve : lPhaseCurve (I := I) x z =ᶠ[𝓝 c] gamma := by
    filter_upwards [hxsrc'] with r hrsrc
    simp only [lPhaseCurve, z, chartCurve]
    exact (extChartAt I x).left_inv (by
      simpa only [extChartAt_source] using hrsrc)
  have hvelEq : ∀ᶠ r in 𝓝 c,
      (lPhaseVel (I := I) x z r : E) = (X r : E) := by
    filter_upwards [hxsrc'] with r hrsrc
    have hrbase : gamma r ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hrsrc
    simp only [lPhaseVel, lPhaseCurve, z, chartCurve, chartRepAtBase_apply]
    rw [(extChartAt I x).left_inv (by
      simpa only [extChartAt_source] using hrsrc)]
    exact congrArg (fun A : TangentSpace I (gamma r) ↦ (A : E))
      (trivFromE_trivToE (I := I) x hrbase (X r))
  have hcov :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - c ^ 2))
      (lPhaseVel (I := I) x z) X hcurve hvelEq
  refine ⟨hmdiff, hveldiff, ?_⟩
  change
    (covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) gamma X c : E) =
      (lRegAccel S T c (gamma c) (X c) : E)
  rw [← hcov]
  have hphaseE :
      (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
          (lPhaseCurve (I := I) x z) (lPhaseVel (I := I) x z) c : E) =
        (lRegAccel S T c (lPhaseCurve (I := I) x z c)
          (lPhaseVel (I := I) x z c) : E) :=
    congrArg
      (fun A : TangentSpace I (lPhaseCurve (I := I) x z c) ↦ (A : E)) hphase
  exact hphaseE.trans (by
    rw [hcurve.self_of_nhds, hvelEq.self_of_nhds])

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
