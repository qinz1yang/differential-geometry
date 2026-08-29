import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import DifferentialGeometry.Topology.FiberBundleT2

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE.Flow

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def IsLRegCurveOn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (J : Set Real) (x : M) (Z : TangentSpace I x) : Prop :=
  alpha 0 = x ∧
    lVelocity (I := I) alpha 0 = 2 • Z ∧
    ∀ s ∈ J,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I alpha s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) alpha
            (fun r : Real => lVelocity (I := I) alpha r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
            (fun r : Real => lVelocity (I := I) alpha r) s =
          lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem lRegState_contOn
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x} (halpha : IsLRegCurveOn S T alpha J x Z) :
    ContinuousOn
      (fun s => (TotalSpace.mk' E (alpha s)
        (lVelocity (I := I) alpha s) : TangentBundle I M)) J := by
  apply sectionAlongCurve_continuousOn_totalSpace (I := I)
  · intro s hs
    exact (halpha.2.2 s hs).2.1.continuousAt.continuousWithinAt
  · intro s hs
    exact (halpha.2.2 s hs).2.2.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegWitness_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha beta : Real → M} {J K : Set Real} {x : M}
    {Z : TangentSpace I x}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J) (h0J : (0 : Real) ∈ J)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K) (h0K : (0 : Real) ∈ K)
    (halpha : IsLRegCurveOn S T alpha J x Z)
    (hbeta : IsLRegCurveOn S T beta K x Z) :
    Set.EqOn alpha beta (J ∩ K) := by
  let va : ∀ s, TangentSpace I (alpha s) :=
    fun s => lVelocity (I := I) alpha s
  let vb : ∀ s, TangentSpace I (beta s) :=
    fun s => lVelocity (I := I) beta s
  let za : Real → TangentBundle I M := fun s => TotalSpace.mk' E (alpha s) (va s)
  let zb : Real → TangentBundle I M := fun s => TotalSpace.mk' E (beta s) (vb s)
  let U : Set Real := {s | za s = zb s} ∩ (J ∩ K)
  have hdomOpen : IsOpen (J ∩ K) := hJopen.inter hKopen
  have hdomConn : IsPreconnected (J ∩ K) :=
    (hJconn.ordConnected.inter hKconn.ordConnected).isPreconnected
  have hza : ContinuousOn za (J ∩ K) := by
    exact (lRegState_contOn (I := I) halpha).mono inter_subset_left
  have hzb : ContinuousOn zb (J ∩ K) := by
    exact (lRegState_contOn (I := I) hbeta).mono inter_subset_right
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hsJ : s ∈ J := hs.2.1
    have hsK : s ∈ K := hs.2.2
    have hpos : alpha s = beta s := congrArg TotalSpace.proj hs.1
    have hvel : va s = vb s := by
      exact congrArg (fun q : TangentBundle I M => (q.2 : E)) hs.1
    have ha_germ : ∀ᶠ r in 𝓝 s,
        MDifferentiableAt 𝓘(Real, Real) I alpha r ∧
          DifferentiableAt Real
            (chartRepAt (I := I) alpha va r) r ∧
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha va r =
            lRegAccel S T r (alpha r) (va r) := by
      filter_upwards [hJopen.mem_nhds hsJ] with r hr
      obtain ⟨_, hmd, hv, hacc⟩ := halpha.2.2 r hr
      exact ⟨hmd, by simpa only [va] using hv,
        by simpa only [va] using hacc⟩
    have hb_germ : ∀ᶠ r in 𝓝 s,
        MDifferentiableAt 𝓘(Real, Real) I beta r ∧
          DifferentiableAt Real
            (chartRepAt (I := I) beta vb r) r ∧
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) beta vb r =
            lRegAccel S T r (beta r) (vb r) := by
      filter_upwards [hKopen.mem_nhds hsK] with r hr
      obtain ⟨_, hmd, hv, hacc⟩ := hbeta.2.2 r hr
      exact ⟨hmd, by simpa only [vb] using hv,
        by simpa only [vb] using hacc⟩
    have heq : alpha =ᶠ[𝓝 s] beta :=
      lRegCurve_unique_at S hS T s (halpha.2.2 s hsJ).1 hpos
        (by simpa only [va, vb] using hvel) ha_germ hb_germ
    obtain ⟨V, hVsub, hVopen, hsV⟩ := mem_nhds_iff.mp heq
    apply Filter.mem_of_superset
      ((hVopen.inter hdomOpen).mem_nhds ⟨hsV, hs.2⟩)
    intro r hr
    refine ⟨?_, hr.2⟩
    have heq_r : alpha =ᶠ[𝓝 r] beta :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds hr.1) hVsub
    apply TotalSpace.ext heq_r.eq_of_nhds
    apply heq_of_eq
    simp only [za, zb, va, vb, lVelocity]
    rw [heq_r.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
    rfl
  have hclosed : closure U ∩ (J ∩ K) ⊆ U := by
    change closure ({s | za s = zb s} ∩ (J ∩ K)) ∩ (J ∩ K) ⊆
      {s | za s = zb s} ∩ (J ∩ K)
    rw [inter_comm (closure ({s | za s = zb s} ∩ (J ∩ K))) (J ∩ K),
      ← Subtype.image_preimage_val (J ∩ K)
        (closure ({s | za s = zb s} ∩ (J ∩ K))),
      inter_comm {s | za s = zb s} (J ∩ K),
      ← Subtype.image_preimage_val (J ∩ K) {s | za s = zb s},
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro s hs
    rw [mem_preimage, ← closure_subtype] at hs
    revert hs s
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hza_at : ContinuousAt za s :=
        (hza s hs).continuousAt (hdomOpen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hza_at
      · exact continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hzb_at : ContinuousAt zb s :=
        (hzb s hs).continuousAt (hdomOpen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hzb_at
      · exact continuousAt_subtype_val
  have hzero : za 0 = zb 0 := by
    apply TotalSpace.ext (halpha.1.trans hbeta.1.symm)
    exact heq_of_eq (by
      simpa only [za, zb, va, vb] using halpha.2.1.trans hbeta.2.1.symm)
  have hsub : J ∩ K ⊆ U := by
    apply hdomConn.subset_of_closure_inter_subset hUopen
    · exact ⟨0, ⟨⟨h0J, h0K⟩, hzero, h0J, h0K⟩⟩
    · exact hclosed
  intro s hs
  exact congrArg TotalSpace.proj (hsub hs).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegSol_eqOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha beta : Real → M} {J K : Set Real} {s0 : Real}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J) (hs0J : s0 ∈ J)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K) (hs0K : s0 ∈ K)
    (halpha : ∀ s ∈ J,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I alpha s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) alpha
            (fun r : Real => lVelocity (I := I) alpha r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
            (fun r : Real => lVelocity (I := I) alpha r) s =
          lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s))
    (hbeta : ∀ s ∈ K,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I beta s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) beta
            (fun r : Real => lVelocity (I := I) beta r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta
            (fun r : Real => lVelocity (I := I) beta r) s =
          lRegAccel S T s (beta s) (lVelocity (I := I) beta s))
    (hpos : alpha s0 = beta s0)
    (hvel : lVelocity (I := I) alpha s0 =
      lVelocity (I := I) beta s0) :
    Set.EqOn alpha beta (J ∩ K) := by
  let va : ∀ s, TangentSpace I (alpha s) :=
    fun s => lVelocity (I := I) alpha s
  let vb : ∀ s, TangentSpace I (beta s) :=
    fun s => lVelocity (I := I) beta s
  let za : Real → TangentBundle I M := fun s => TotalSpace.mk' E (alpha s) (va s)
  let zb : Real → TangentBundle I M := fun s => TotalSpace.mk' E (beta s) (vb s)
  let U : Set Real := {s | za s = zb s} ∩ (J ∩ K)
  have hdomOpen : IsOpen (J ∩ K) := hJopen.inter hKopen
  have hdomConn : IsPreconnected (J ∩ K) :=
    (hJconn.ordConnected.inter hKconn.ordConnected).isPreconnected
  have hza : ContinuousOn za (J ∩ K) := by
    apply sectionAlongCurve_continuousOn_totalSpace (I := I)
    · intro s hs
      exact (halpha s hs.1).2.1.continuousAt.continuousWithinAt
    · intro s hs
      exact (halpha s hs.1).2.2.1
  have hzb : ContinuousOn zb (J ∩ K) := by
    apply sectionAlongCurve_continuousOn_totalSpace (I := I)
    · intro s hs
      exact (hbeta s hs.2).2.1.continuousAt.continuousWithinAt
    · intro s hs
      exact (hbeta s hs.2).2.2.1
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hsJ : s ∈ J := hs.2.1
    have hsK : s ∈ K := hs.2.2
    have hpos' : alpha s = beta s := congrArg TotalSpace.proj hs.1
    have hvel' : va s = vb s := by
      exact congrArg (fun q : TangentBundle I M => (q.2 : E)) hs.1
    have ha_germ : ∀ᶠ r in 𝓝 s,
        MDifferentiableAt 𝓘(Real, Real) I alpha r ∧
          DifferentiableAt Real (chartRepAt (I := I) alpha va r) r ∧
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha va r =
            lRegAccel S T r (alpha r) (va r) := by
      filter_upwards [hJopen.mem_nhds hsJ] with r hr
      obtain ⟨_, hmd, hv, hacc⟩ := halpha r hr
      exact ⟨hmd, by simpa only [va] using hv,
        by simpa only [va] using hacc⟩
    have hb_germ : ∀ᶠ r in 𝓝 s,
        MDifferentiableAt 𝓘(Real, Real) I beta r ∧
          DifferentiableAt Real (chartRepAt (I := I) beta vb r) r ∧
          covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) beta vb r =
            lRegAccel S T r (beta r) (vb r) := by
      filter_upwards [hKopen.mem_nhds hsK] with r hr
      obtain ⟨_, hmd, hv, hacc⟩ := hbeta r hr
      exact ⟨hmd, by simpa only [vb] using hv,
        by simpa only [vb] using hacc⟩
    have heq : alpha =ᶠ[𝓝 s] beta :=
      lRegCurve_unique_at S hS T s (halpha s hsJ).1 hpos'
        (by simpa only [va, vb] using hvel') ha_germ hb_germ
    obtain ⟨V, hVsub, hVopen, hsV⟩ := mem_nhds_iff.mp heq
    apply Filter.mem_of_superset
      ((hVopen.inter hdomOpen).mem_nhds ⟨hsV, hs.2⟩)
    intro r hr
    refine ⟨?_, hr.2⟩
    have heq_r : alpha =ᶠ[𝓝 r] beta :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds hr.1) hVsub
    apply TotalSpace.ext heq_r.eq_of_nhds
    apply heq_of_eq
    simp only [za, zb, va, vb, lVelocity]
    rw [heq_r.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
    rfl
  have hclosed : closure U ∩ (J ∩ K) ⊆ U := by
    change closure ({s | za s = zb s} ∩ (J ∩ K)) ∩ (J ∩ K) ⊆
      {s | za s = zb s} ∩ (J ∩ K)
    rw [inter_comm (closure ({s | za s = zb s} ∩ (J ∩ K))) (J ∩ K),
      ← Subtype.image_preimage_val (J ∩ K)
        (closure ({s | za s = zb s} ∩ (J ∩ K))),
      inter_comm {s | za s = zb s} (J ∩ K),
      ← Subtype.image_preimage_val (J ∩ K) {s | za s = zb s},
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro s hs
    rw [mem_preimage, ← closure_subtype] at hs
    revert hs s
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hza_at : ContinuousAt za s :=
        (hza s hs).continuousAt (hdomOpen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hza_at
      · exact continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨s, hs⟩
      have hzb_at : ContinuousAt zb s :=
        (hzb s hs).continuousAt (hdomOpen.mem_nhds hs)
      apply ContinuousAt.comp'
      · simpa using hzb_at
      · exact continuousAt_subtype_val
  have hstate : za s0 = zb s0 := by
    apply TotalSpace.ext hpos
    exact heq_of_eq (by simpa only [za, zb, va, vb] using hvel)
  have hsub : J ∩ K ⊆ U := by
    apply hdomConn.subset_of_closure_inter_subset hUopen
    · exact ⟨s0, ⟨⟨hs0J, hs0K⟩, hstate, hs0J, hs0K⟩⟩
    · exact hclosed
  intro s hs
  exact congrArg TotalSpace.proj (hsub hs).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegData_congr
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    {gamma eta : Real → M} (heq : gamma =ᶠ[𝓝 s] eta)
    (heta : T - s ^ 2 ∈ D.regular ∧
      MDifferentiableAt 𝓘(Real, Real) I eta s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) eta
          (fun r : Real => lVelocity (I := I) eta r) s) s ∧
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) eta
          (fun r : Real => lVelocity (I := I) eta r) s =
        lRegAccel S T s (eta s) (lVelocity (I := I) eta s)) :
    T - s ^ 2 ∈ D.regular ∧
      MDifferentiableAt 𝓘(Real, Real) I gamma s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r : Real => lVelocity (I := I) gamma r) s) s ∧
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
          (fun r : Real => lVelocity (I := I) gamma r) s =
        lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  have hpos : gamma s = eta s := heq.eq_of_nhds
  obtain ⟨U, hUsub, hUopen, hsU⟩ := mem_nhds_iff.mp heq
  have hrep :
      chartRepAt (I := I) gamma
          (fun r : Real => lVelocity (I := I) gamma r) s =ᶠ[𝓝 s]
        chartRepAt (I := I) eta
          (fun r : Real => lVelocity (I := I) eta r) s := by
    filter_upwards [hUopen.mem_nhds hsU] with r hr
    have heq_r : gamma =ᶠ[𝓝 r] eta :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hr) hUsub
    have hvel_r := congrArg (fun L => L (1 : Real))
      (heq_r.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I))
    simp only [chartRepAt_apply, lVelocity]
    rw [hpos, heq_r.eq_of_nhds]
    exact congrArg _ hvel_r
  have hchart : chartCurve (I := I) (gamma s) gamma =ᶠ[𝓝 s]
      chartCurve (I := I) (eta s) eta := by
    filter_upwards [heq] with r hr
    simp only [chartCurve]
    rw [hpos, hr]
  have hchart' : chartCurve (I := I) (eta s) gamma =ᶠ[𝓝 s]
      chartCurve (I := I) (eta s) eta := by
    simpa only [hpos] using hchart
  have hmd : MDifferentiableAt 𝓘(Real, Real) I gamma s :=
    heta.2.1.congr_of_eventuallyEq heq
  have hdiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s) s :=
    heta.2.2.1.congr_of_eventuallyEq hrep
  have hcov : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) eta
        (fun r : Real => lVelocity (I := I) eta r) s := by
    simp only [covDerivAlong_def, chartCovDerivAlong_def]
    rw [hpos, hrep.deriv_eq, hrep.eq_of_nhds,
      hchart'.deriv_eq, hchart'.eq_of_nhds]
  have hvel : lVelocity (I := I) gamma s =
      lVelocity (I := I) eta s := by
    simp only [lVelocity]
    rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
    rfl
  refine ⟨heta.1, hmd, hdiff, ?_⟩
  rw [hcov, heta.2.2.2, hpos, hvel]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lPhaseFlow
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (z0 : E × E)
    (hT : T ∈ D.regular)
    (hz0 : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ U : Set (E × E), IsOpen U ∧ z0 ∈ U ∧
        ∃ Phi : (E × E) × Real → E × E,
          (∀ z ∈ U, Phi (z, 0) = z) ∧
          ContDiffOn Real ∞ Phi (U ×ˢ Set.Ioo (-epsilon) epsilon) ∧
          (∀ z ∈ U, ∀ s ∈ Set.Ioo (-epsilon) epsilon,
            HasDerivAt (fun r => Phi (z, r))
              (lPhaseField S T x0 s (Phi (z, s))) s) ∧
          MapsTo (fun q : (E × E) × Real => (q.2, Phi q))
            (U ×ˢ Set.Ioo (-epsilon) epsilon)
            {p : Real × (E × E) |
              T - p.1 ^ 2 ∈ D.regular ∧
                p.2.1 ∈ interior (extChartAt I x0).target} := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let Omega : Set (Real × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ D.regular ∧
      p.2.1 ∈ interior (extChartAt I x0).target}
  let vf : Real × (E × E) → Real × (E × E) := fun p =>
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  let p0 : Real × (E × E) := (0, z0)
  have hOmegaOpen : IsOpen Omega := by
    exact (D.regular_isOpen.preimage
      (continuous_const.sub (continuous_fst.pow 2))).inter
        (isOpen_interior.preimage continuous_snd.fst)
  have hp0 : p0 ∈ Omega := by
    change T - (0 : Real) ^ 2 ∈ D.regular ∧
      z0.1 ∈ interior (extChartAt I x0).target
    exact ⟨by norm_num; exact hT, hz0⟩
  have hvf : ContDiffOn Real ∞ vf Omega := by
    intro p hp
    have hphase := lPhaseField_smoothAt S hS T x0 hp.1 hp.2
    change ContDiffWithinAt Real ∞
      (fun q : Real × (E × E) =>
        ((1 : Real), Function.uncurry (lPhaseField S T x0) q)) Omega p
    exact (contDiffAt_const.prodMk hphase).contDiffWithinAt
  have hsingleton : ({p0} : Set (Real × (E × E))) ⊆ Omega := by
    intro p hp
    have hp_eq : p = p0 := by simpa using hp
    rw [hp_eq]
    exact hp0
  obtain ⟨epsilon, hepsilon, hlocal⟩ :=
    exists_flow_on hOmegaOpen hvf isCompact_singleton hsingleton
  obtain ⟨W, hWopen, hp0W, Psi, hPsi0, hPsiSmooth, hPsiDeriv, hPsiMap⟩ :=
    hlocal p0 (Set.mem_singleton p0)
  let U : Set (E × E) := (fun z => ((0 : Real), z)) ⁻¹' W
  let lift : (E × E) × Real → (Real × (E × E)) × Real := fun q =>
    (((0 : Real), q.1), q.2)
  let Phi : (E × E) × Real → E × E := fun q => (Psi (lift q)).2
  have hUopen : IsOpen U :=
    hWopen.preimage (continuous_const.prodMk continuous_id)
  have hz0U : z0 ∈ U := by
    change ((0 : Real), z0) ∈ W
    exact hp0W
  refine ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hstart := hPsi0 ((0 : Real), z) hz
    simpa only [Phi, lift] using congrArg Prod.snd hstart
  · have hlift : ContDiff Real ∞ lift :=
      (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
    have hliftMap : MapsTo lift (U ×ˢ Set.Ioo (-epsilon) epsilon)
        (W ×ˢ Set.Ioo (-epsilon) epsilon) := by
      rintro ⟨z, s⟩ ⟨hz, hs⟩
      exact ⟨hz, hs⟩
    have hcomp := hPsiSmooth.comp hlift.contDiffOn hliftMap
    simpa only [Phi, lift, Function.comp_apply] using hcomp.snd
  · intro z hz s hs
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi (((0 : Real), z), r)).1 = r := by
      apply DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        (fun r => (Psi (((0 : Real), z), r)).1) hzero
      · intro r hr
        have hderiv := hPsiDeriv ((0 : Real), z) hz r hr
        simpa [vf, Function.comp_def] using
          hasFDerivAt_fst.comp_hasDerivAt r hderiv
      · have hstart := hPsi0 ((0 : Real), z) hz
        exact congrArg Prod.fst hstart
    have hderiv := hPsiDeriv ((0 : Real), z) hz s hs
    simpa [Phi, lift, vf, htime s hs, Function.comp_def] using
      hasFDerivAt_snd.comp_hasDerivAt s hderiv
  · rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi (((0 : Real), z), r)).1 = r := by
      apply DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        (fun r => (Psi (((0 : Real), z), r)).1) hzero
      · intro r hr
        have hderiv := hPsiDeriv ((0 : Real), z) hz r hr
        simpa [vf, Function.comp_def] using
          hasFDerivAt_fst.comp_hasDerivAt r hderiv
      · have hstart := hPsi0 ((0 : Real), z) hz
        exact congrArg Prod.fst hstart
    have hzW : ((0 : Real), z) ∈ W := by
      change ((0 : Real), z) ∈ W at hz
      exact hz
    have hinput : ((((0 : Real), z), s) :
        (Real × (E × E)) × Real) ∈
        W ×ˢ Set.Ioo (-epsilon) epsilon := ⟨hzW, hs⟩
    have hmem := hPsiMap hinput
    change T - (Psi (((0 : Real), z), s)).1 ^ 2 ∈ D.regular ∧
      (Psi (((0 : Real), z), s)).2.1 ∈
        interior (extChartAt I x0).target at hmem
    rw [htime s hs] at hmem
    change T - s ^ 2 ∈ D.regular ∧
      (Phi (z, s)).1 ∈ interior (extChartAt I x0).target
    exact hmem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lPhaseAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (s0 : Real) (z0 : E × E)
    (hT : T - s0 ^ 2 ∈ D.regular)
    (hz0 : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ U : Set (E × E), IsOpen U ∧ z0 ∈ U ∧
        ∃ Phi : (E × E) × Real → E × E,
          (∀ z ∈ U, Phi (z, s0) = z) ∧
          ContDiffOn Real ∞ Phi
            (U ×ˢ Set.Ioo (s0 - epsilon) (s0 + epsilon)) ∧
          (∀ z ∈ U, ∀ s ∈ Set.Ioo (s0 - epsilon) (s0 + epsilon),
            HasDerivAt (fun r => Phi (z, r))
              (lPhaseField S T x0 s (Phi (z, s))) s) ∧
          MapsTo (fun q : (E × E) × Real => (q.2, Phi q))
            (U ×ˢ Set.Ioo (s0 - epsilon) (s0 + epsilon))
            {p : Real × (E × E) |
              T - p.1 ^ 2 ∈ D.regular ∧
                p.2.1 ∈ interior (extChartAt I x0).target} := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let Omega : Set (Real × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ D.regular ∧
      p.2.1 ∈ interior (extChartAt I x0).target}
  let vf : Real × (E × E) → Real × (E × E) := fun p =>
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  let p0 : Real × (E × E) := (s0, z0)
  have hOmegaOpen : IsOpen Omega := by
    exact (D.regular_isOpen.preimage
      (continuous_const.sub (continuous_fst.pow 2))).inter
        (isOpen_interior.preimage continuous_snd.fst)
  have hp0 : p0 ∈ Omega := by
    exact ⟨hT, hz0⟩
  have hvf : ContDiffOn Real ∞ vf Omega := by
    intro p hp
    have hphase := lPhaseField_smoothAt S hS T x0 hp.1 hp.2
    change ContDiffWithinAt Real ∞
      (fun q : Real × (E × E) =>
        ((1 : Real), Function.uncurry (lPhaseField S T x0) q)) Omega p
    exact (contDiffAt_const.prodMk hphase).contDiffWithinAt
  have hsingleton : ({p0} : Set (Real × (E × E))) ⊆ Omega := by
    intro p hp
    have hp_eq : p = p0 := by simpa using hp
    rw [hp_eq]
    exact hp0
  obtain ⟨epsilon, hepsilon, hlocal⟩ :=
    exists_flow_on hOmegaOpen hvf isCompact_singleton hsingleton
  obtain ⟨W, hWopen, hp0W, Psi, hPsi0, hPsiSmooth, hPsiDeriv, hPsiMap⟩ :=
    hlocal p0 (Set.mem_singleton p0)
  let U : Set (E × E) := (fun z => (s0, z)) ⁻¹' W
  let lift : (E × E) × Real → (Real × (E × E)) × Real := fun q =>
    ((s0, q.1), q.2 - s0)
  let Phi : (E × E) × Real → E × E := fun q => (Psi (lift q)).2
  have hUopen : IsOpen U :=
    hWopen.preimage (continuous_const.prodMk continuous_id)
  have hz0U : z0 ∈ U := by
    change (s0, z0) ∈ W
    exact hp0W
  refine ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hstart := hPsi0 (s0, z) hz
    simpa only [Phi, lift, sub_self] using congrArg Prod.snd hstart
  · have hlift : ContDiff Real ∞ lift :=
      (contDiff_const.prodMk contDiff_fst).prodMk
        (contDiff_snd.sub contDiff_const)
    have hliftMap : MapsTo lift
        (U ×ˢ Set.Ioo (s0 - epsilon) (s0 + epsilon))
        (W ×ˢ Set.Ioo (-epsilon) epsilon) := by
      rintro ⟨z, s⟩ ⟨hz, hs⟩
      refine ⟨hz, ?_⟩
      change s - s0 ∈ Set.Ioo (-epsilon) epsilon
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hcomp := hPsiSmooth.comp hlift.contDiffOn hliftMap
    simpa only [Phi, lift, Function.comp_apply] using hcomp.snd
  · intro z hz s hs
    rcases hs with ⟨hslo, hshi⟩
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi ((s0, z), r)).1 = s0 + r := by
      let phi : Real → Real := fun r => (Psi ((s0, z), r)).1 - s0
      have hphi : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
          HasDerivAt phi 1 r := by
        intro r hr
        have hderiv := hPsiDeriv (s0, z) hz r hr
        have hfst := hasFDerivAt_fst.comp_hasDerivAt r hderiv
        simpa [phi, vf, Function.comp_def] using hfst.sub_const s0
      have hphi0 : phi 0 = 0 := by
        have hstart := hPsi0 (s0, z) hz
        simp only [phi]
        rw [congrArg Prod.fst hstart]
        ring
      intro r hr
      have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        phi hzero hphi hphi0 r hr
      change (Psi ((s0, z), r)).1 - s0 = r at h
      linarith
    have hsrel : s - s0 ∈ Set.Ioo (-epsilon) epsilon :=
      ⟨by linarith, by linarith⟩
    have hderiv := hPsiDeriv (s0, z) hz (s - s0) hsrel
    have hsnd0 : HasDerivAt (fun r => (Psi ((s0, z), r)).2)
        (lPhaseField S T x0 (Psi ((s0, z), s - s0)).1
          (Psi ((s0, z), s - s0)).2) (s - s0) := by
      simpa [vf, Function.comp_def] using
        hasFDerivAt_snd.comp_hasDerivAt (s - s0) hderiv
    have hsnd := hsnd0.comp_sub_const s s0
    have htime_s : (Psi ((s0, z), s - s0)).1 = s := by
      rw [htime (s - s0) hsrel]
      ring
    simpa [Phi, lift, vf, htime_s, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using hsnd
  · rintro ⟨z, s⟩ ⟨hz, hs⟩
    rcases hs with ⟨hslo, hshi⟩
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi ((s0, z), r)).1 = s0 + r := by
      let phi : Real → Real := fun r => (Psi ((s0, z), r)).1 - s0
      have hphi : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
          HasDerivAt phi 1 r := by
        intro r hr
        have hderiv := hPsiDeriv (s0, z) hz r hr
        have hfst := hasFDerivAt_fst.comp_hasDerivAt r hderiv
        simpa [phi, vf, Function.comp_def] using hfst.sub_const s0
      have hphi0 : phi 0 = 0 := by
        have hstart := hPsi0 (s0, z) hz
        simp only [phi]
        rw [congrArg Prod.fst hstart]
        ring
      intro r hr
      have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        phi hzero hphi hphi0 r hr
      change (Psi ((s0, z), r)).1 - s0 = r at h
      linarith
    have hsrel : s - s0 ∈ Set.Ioo (-epsilon) epsilon :=
      ⟨by linarith, by linarith⟩
    have hzW : (s0, z) ∈ W := by
      change (s0, z) ∈ W at hz
      exact hz
    have hinput : (((s0, z), s - s0) :
        (Real × (E × E)) × Real) ∈
        W ×ˢ Set.Ioo (-epsilon) epsilon := ⟨hzW, hsrel⟩
    have hmem := hPsiMap hinput
    change T - (Psi ((s0, z), s - s0)).1 ^ 2 ∈ D.regular ∧
      (Psi ((s0, z), s - s0)).2.1 ∈
        interior (extChartAt I x0).target at hmem
    have htime_s : (Psi ((s0, z), s - s0)).1 = s := by
      rw [htime (s - s0) hsrel]
      ring
    rw [htime_s] at hmem
    change T - s ^ 2 ∈ D.regular ∧
      (Phi (z, s)).1 ∈ interior (extChartAt I x0).target
    exact hmem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem exists_lPhaseComp
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x0 : M)
    {C : Set (Real × (E × E))} (hC : IsCompact C)
    (hCreg : C ⊆ {p : Real × (E × E) |
      T - p.1 ^ 2 ∈ D.regular ∧
        p.2.1 ∈ interior (extChartAt I x0).target}) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ p0 ∈ C,
        ∃ U : Set (E × E), IsOpen U ∧ p0.2 ∈ U ∧
          ∃ Phi : (E × E) × Real → E × E,
            (∀ z ∈ U, Phi (z, p0.1) = z) ∧
            ContDiffOn Real ∞ Phi
              (U ×ˢ Set.Ioo (p0.1 - epsilon) (p0.1 + epsilon)) ∧
            (∀ z ∈ U,
              ∀ s ∈ Set.Ioo (p0.1 - epsilon) (p0.1 + epsilon),
                HasDerivAt (fun r => Phi (z, r))
                  (lPhaseField S T x0 s (Phi (z, s))) s) ∧
            MapsTo (fun q : (E × E) × Real => (q.2, Phi q))
              (U ×ˢ Set.Ioo (p0.1 - epsilon) (p0.1 + epsilon))
              {p : Real × (E × E) |
                T - p.1 ^ 2 ∈ D.regular ∧
                  p.2.1 ∈ interior (extChartAt I x0).target} := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let Omega : Set (Real × (E × E)) :=
    {p | T - p.1 ^ 2 ∈ D.regular ∧
      p.2.1 ∈ interior (extChartAt I x0).target}
  let vf : Real × (E × E) → Real × (E × E) := fun p =>
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  have hOmegaOpen : IsOpen Omega := by
    exact (D.regular_isOpen.preimage
      (continuous_const.sub (continuous_fst.pow 2))).inter
        (isOpen_interior.preimage continuous_snd.fst)
  have hvf : ContDiffOn Real ∞ vf Omega := by
    intro p hp
    have hphase := lPhaseField_smoothAt S hS T x0 hp.1 hp.2
    change ContDiffWithinAt Real ∞
      (fun q : Real × (E × E) =>
        ((1 : Real), Function.uncurry (lPhaseField S T x0) q)) Omega p
    exact (contDiffAt_const.prodMk hphase).contDiffWithinAt
  have hCOmega : C ⊆ Omega := by
    simpa only [Omega] using hCreg
  obtain ⟨epsilon, hepsilon, hlocal⟩ :=
    exists_flow_on hOmegaOpen hvf hC hCOmega
  refine ⟨epsilon, hepsilon, ?_⟩
  intro p0 hp0
  obtain ⟨W, hWopen, hp0W, Psi, hPsi0, hPsiSmooth, hPsiDeriv, hPsiMap⟩ :=
    hlocal p0 hp0
  let U : Set (E × E) := (fun z => (p0.1, z)) ⁻¹' W
  let lift : (E × E) × Real → (Real × (E × E)) × Real := fun q =>
    ((p0.1, q.1), q.2 - p0.1)
  let Phi : (E × E) × Real → E × E := fun q => (Psi (lift q)).2
  have hUopen : IsOpen U :=
    hWopen.preimage (continuous_const.prodMk continuous_id)
  have hp0U : p0.2 ∈ U := by
    change (p0.1, p0.2) ∈ W
    exact hp0W
  refine ⟨U, hUopen, hp0U, Phi, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hstart := hPsi0 (p0.1, z) hz
    simpa only [Phi, lift, sub_self] using congrArg Prod.snd hstart
  · have hlift : ContDiff Real ∞ lift :=
      (contDiff_const.prodMk contDiff_fst).prodMk
        (contDiff_snd.sub contDiff_const)
    have hliftMap : MapsTo lift
        (U ×ˢ Set.Ioo (p0.1 - epsilon) (p0.1 + epsilon))
        (W ×ˢ Set.Ioo (-epsilon) epsilon) := by
      rintro ⟨z, s⟩ ⟨hz, hs⟩
      exact ⟨hz, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
    have hcomp := hPsiSmooth.comp hlift.contDiffOn hliftMap
    simpa only [Phi, lift, Function.comp_apply] using hcomp.snd
  · intro z hz s hs
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi ((p0.1, z), r)).1 = p0.1 + r := by
      let phi : Real → Real := fun r => (Psi ((p0.1, z), r)).1 - p0.1
      have hphi : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
          HasDerivAt phi 1 r := by
        intro r hr
        have hderiv := hPsiDeriv (p0.1, z) hz r hr
        have hfst := hasFDerivAt_fst.comp_hasDerivAt r hderiv
        simpa [phi, vf, Function.comp_def] using hfst.sub_const p0.1
      have hphi0 : phi 0 = 0 := by
        have hstart := hPsi0 (p0.1, z) hz
        simp only [phi]
        rw [congrArg Prod.fst hstart]
        ring
      intro r hr
      have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        phi hzero hphi hphi0 r hr
      change (Psi ((p0.1, z), r)).1 - p0.1 = r at h
      linarith
    have hsrel : s - p0.1 ∈ Set.Ioo (-epsilon) epsilon :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hderiv := hPsiDeriv (p0.1, z) hz (s - p0.1) hsrel
    have hsnd0 : HasDerivAt (fun r => (Psi ((p0.1, z), r)).2)
        (lPhaseField S T x0 (Psi ((p0.1, z), s - p0.1)).1
          (Psi ((p0.1, z), s - p0.1)).2) (s - p0.1) := by
      simpa [vf, Function.comp_def] using
        hasFDerivAt_snd.comp_hasDerivAt (s - p0.1) hderiv
    have hsnd := hsnd0.comp_sub_const s p0.1
    have htime_s : (Psi ((p0.1, z), s - p0.1)).1 = s := by
      rw [htime (s - p0.1) hsrel]
      ring
    simpa [Phi, lift, vf, htime_s, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using hsnd
  · rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> linarith
    have htime : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
        (Psi ((p0.1, z), r)).1 = p0.1 + r := by
      let phi : Real → Real := fun r => (Psi ((p0.1, z), r)).1 - p0.1
      have hphi : ∀ r ∈ Set.Ioo (-epsilon) epsilon,
          HasDerivAt phi 1 r := by
        intro r hr
        have hderiv := hPsiDeriv (p0.1, z) hz r hr
        have hfst := hasFDerivAt_fst.comp_hasDerivAt r hderiv
        simpa [phi, vf, Function.comp_def] using hfst.sub_const p0.1
      have hphi0 : phi 0 = 0 := by
        have hstart := hPsi0 (p0.1, z) hz
        simp only [phi]
        rw [congrArg Prod.fst hstart]
        ring
      intro r hr
      have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
        phi hzero hphi hphi0 r hr
      change (Psi ((p0.1, z), r)).1 - p0.1 = r at h
      linarith
    have hsrel : s - p0.1 ∈ Set.Ioo (-epsilon) epsilon :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hzW : (p0.1, z) ∈ W := by
      change (p0.1, z) ∈ W at hz
      exact hz
    have hinput : (((p0.1, z), s - p0.1) :
        (Real × (E × E)) × Real) ∈
        W ×ˢ Set.Ioo (-epsilon) epsilon := ⟨hzW, hsrel⟩
    have hmem := hPsiMap hinput
    change T - (Psi ((p0.1, z), s - p0.1)).1 ^ 2 ∈ D.regular ∧
      (Psi ((p0.1, z), s - p0.1)).2.1 ∈
        interior (extChartAt I x0).target at hmem
    have htime_s : (Psi ((p0.1, z), s - p0.1)).1 = s := by
      rw [htime (s - p0.1) hsrel]
      ring
    rw [htime_s] at hmem
    change T - s ^ 2 ∈ D.regular ∧
      (Phi (z, s)).1 ∈ interior (extChartAt I x0).target
    exact hmem

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem timeVel_smoothAt
    {F : E × Real → E} {Z0 : E} {s0 : Real}
    (hF : ContDiffAt Real ∞ F (Z0, s0)) :
    ContDiffAt Real ∞
      (fun Z : E =>
        fderiv Real (fun s : Real => F (Z, s)) s0 (1 : Real)) Z0 := by
  exact (hF.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem lPhaseSeed_smooth
    {alpha : E × Real → M} {Z0 : E} {s0 : Real} (x0 : M)
    (hsrc : alpha (Z0, s0) ∈ (chartAt H x0).source)
    (halpha : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (Z0, s0)) :
    ContDiffAt Real ∞
      (fun Z : E =>
        (extChartAt I x0 (alpha (Z, s0)),
          fderiv Real
            (fun s : Real => extChartAt I x0 (alpha (Z, s))) s0
            (1 : Real))) Z0 := by
  let F : E × Real → E := fun p => extChartAt I x0 (alpha p)
  have hchart : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, E) ∞
      F (Z0, s0) := by
    exact (contMDiffAt_extChartAt' (I := I) hsrc).comp
      (Z0, s0) halpha
  have hF : ContDiffAt Real ∞ F (Z0, s0) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hchart
  have hincl : ContDiffAt Real ∞ (fun Z : E => (Z, s0)) Z0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hpos : ContDiffAt Real ∞ (fun Z : E => F (Z, s0)) Z0 := by
    simpa only [Function.comp_def] using hF.comp Z0 hincl
  have hvel : ContDiffAt Real ∞
      (fun Z : E =>
        fderiv Real (fun s : Real => F (Z, s)) s0 (1 : Real)) Z0 :=
    timeVel_smoothAt hF
  simpa only [F] using hpos.prodMk hvel

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem lPhaseSeed_vel
    {gamma : Real → M} {s0 : Real} (x0 : M)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s0)
    (hsrc : gamma s0 ∈ (chartAt H x0).source) :
    fderiv Real (fun s : Real => extChartAt I x0 (gamma s)) s0
        (1 : Real) =
      trivToE (I := I) x0 (gamma s0)
        (lVelocity (I := I) gamma s0) := by
  have hcoord :=
    DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) hgamma x0 hsrc
  simpa only [Function.comp_def, lVelocity] using hcoord.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegFamily
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z0 : TangentSpace I x)
    (hT : T ∈ D.regular) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ Set.Ioo (-epsilon) epsilon) ∧
            ∀ Z ∈ V,
              IsLRegCurveOn S T (fun s => alpha (Z, s))
                (Set.Ioo (-epsilon) epsilon) x Z := by
  let seed : E → E × E := fun Z =>
    (extChartAt I x x, (2 : Real) • Z)
  let z0 : E × E := seed Z0
  have hz0pos : z0.1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0, seed] using extChartAt_target_mem_nhds (I := I) x
  obtain ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
    exists_lPhaseFlow S hS T x z0 hT hz0pos
  let V : Set E := seed ⁻¹' U
  have hseed : ContDiff Real ∞ seed := by
    exact contDiff_const.prodMk
      ((contDiff_const : ContDiff Real ∞ (fun _ : E => (2 : Real))).smul contDiff_id)
  have hVopen : IsOpen V := hUopen.preimage hseed.continuous
  have hZ0V : Z0 ∈ V := by
    change seed Z0 ∈ U
    exact hz0U
  let input : E × Real → (E × E) × Real := fun p => (seed p.1, p.2)
  let phase : E × Real → E × E := fun p => Phi (input p)
  let alpha : E × Real → M := fun p =>
    (extChartAt I x).symm (phase p).1
  have hinput : ContDiff Real ∞ input :=
    (hseed.comp contDiff_fst).prodMk contDiff_snd
  have hinputMap : MapsTo input (V ×ˢ Set.Ioo (-epsilon) epsilon)
      (U ×ˢ Set.Ioo (-epsilon) epsilon) := by
    rintro ⟨Z, s⟩ ⟨hZ, hs⟩
    exact ⟨hZ, hs⟩
  have hphase : ContDiffOn Real ∞ phase
      (V ×ˢ Set.Ioo (-epsilon) epsilon) := by
    simpa only [phase, Function.comp_def] using
      hPhiSmooth.comp hinput.contDiffOn hinputMap
  have hphaseMap : MapsTo (fun p : E × Real => (phase p).1)
      (V ×ˢ Set.Ioo (-epsilon) epsilon) (extChartAt I x).target := by
    rintro ⟨Z, s⟩ hmem
    have hmap := hPhiMap (hinputMap hmem)
    exact interior_subset hmap.2
  have halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
      (V ×ˢ Set.Ioo (-epsilon) epsilon) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, E × Real) 𝓘(Real, E) ∞
        (fun p => (phase p).1) (V ×ˢ Set.Ioo (-epsilon) epsilon) :=
      hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    apply (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
    · exact hphaseMD
    · exact hphaseMap
  refine ⟨epsilon, hepsilon, V, hVopen, hZ0V, alpha, halpha, ?_⟩
  intro Z hZ
  let z : Real → E × E := fun s => phase (Z, s)
  let gamma : Real → M := lPhaseCurve (I := I) x z
  let A : ∀ s, TangentSpace I (gamma s) := lPhaseVel (I := I) x z
  have hzU : seed Z ∈ U := by
    change seed Z ∈ U at hZ
    exact hZ
  have hsol : ∀ s ∈ Set.Ioo (-epsilon) epsilon,
      HasDerivAt z (lPhaseField S T x s (z s)) s := by
    intro s hs
    simpa only [z, phase, input] using hPhiDeriv (seed Z) hzU s hs
  have hdata : ∀ s ∈ Set.Ioo (-epsilon) epsilon,
      T - s ^ 2 ∈ D.regular ∧
        (z s).1 ∈ interior (extChartAt I x).target := by
    intro s hs
    have hmem : ((seed Z, s) : (E × E) × Real) ∈
        U ×ˢ Set.Ioo (-epsilon) epsilon := ⟨hzU, hs⟩
    change T - s ^ 2 ∈ D.regular ∧
      (z s).1 ∈ interior (extChartAt I x).target
    exact hPhiMap hmem
  have hzzero : z 0 = seed Z := by
    simpa only [z, phase, input] using hPhi0 (seed Z) hzU
  have hvel : Set.EqOn (fun s => lVelocity (I := I) gamma s) A
      (Set.Ioo (-epsilon) epsilon) := by
    intro s hs
    have hzs := hsol s hs
    have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    exact lPhase_velocity (I := I) x z s hq (hdata s hs).2
  have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
    constructor <;> simpa using hepsilon
  have hgamma0 : gamma 0 = x := by
    simp only [gamma, lPhaseCurve, hzzero, seed]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hvel0 : lVelocity (I := I) gamma 0 = 2 • Z := by
    calc
      lVelocity (I := I) gamma 0 = A 0 := hvel hzero
      _ = 2 • Z := by
        change trivFromE (I := I) x (gamma 0) (z 0).2 = 2 • Z
        rw [hgamma0, hzzero]
        change trivFromE (I := I) x x ((2 : Real) • Z) = (2 : Nat) • Z
        rw [trivFromE_self_apply]
        have hcenterSymm (w : E) :
            (Integral.Measure.centeredChartTangentEquiv (I := I) x).symm w = w := by
          apply (Integral.Measure.centeredChartTangentEquiv (I := I) x).injective
          rw [ContinuousLinearEquiv.apply_symm_apply]
          have hmodel : tangentSpaceModelContinuousLinearEquiv (I := I) x
              (show TangentSpace I x from w) = w := rfl
          exact hmodel.symm.trans
            (Integral.Measure.centeredChartTangentEquiv_apply (I := I) x
              (show TangentSpace I x from w)).symm
        rw [hcenterSymm]
        simp only [two_smul]
        rfl
  have halpha_eq : (fun s => alpha (Z, s)) = gamma := by
    funext s
    rfl
  rw [halpha_eq]
  refine ⟨hgamma0, hvel0, ?_⟩
  intro s hs
  have hzs := hsol s hs
  have hsdata := hdata s hs
  have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
    have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
    simpa [lPhaseField, Function.comp_def] using h
  have hv : HasDerivAt (fun r : Real => (z r).2)
      (lPhaseField S T x s (z s)).2 s := by
    simpa [Function.comp_def] using hasFDerivAt_snd.comp_hasDerivAt s hzs
  have hfield : (fun r => lVelocity (I := I) gamma r) =ᶠ[𝓝 s] A :=
    hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
    simpa only [gamma] using
      lPhaseCurve_mdiff (I := I) x z s hq.differentiableAt hsdata.2
  have hAdiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma A s) s := by
    simpa only [gamma, A] using lPhaseVel_diff (I := I) x z s
      hq.differentiableAt hv.differentiableAt hsdata.2
  have hveldiff : DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s) s :=
    hAdiff.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) gamma hfield)
  refine ⟨hsdata.1, hgamma, hveldiff, ?_⟩
  calc
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun r : Real => lVelocity (I := I) gamma r) s =
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma A s :=
        covDerivAlong_congr_of_eventuallyEq
          (I := I) (S.base.metric (T - s ^ 2)) gamma hfield
    _ = lRegAccel S T s (gamma s) (A s) := by
      simpa only [gamma, A] using
        lPhase_accel S T x z s hzs hsdata.2
    _ = lRegAccel S T s (gamma s)
        (lVelocity (I := I) gamma s) := by
      rw [hfield.eq_of_nhds]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegFamily_step_of
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {alpha : E × Real → M} {V : Set E} {J : Set Real}
    {Z0 : E} {s0 : Real} (x0 : M)
    (hVopen : IsOpen V) (hZ0V : Z0 ∈ V)
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (h0J : (0 : Real) ∈ J) (hs0J : s0 ∈ J)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ J))
    (hcurves : ∀ Z ∈ V,
      IsLRegCurveOn S T (fun s => alpha (Z, s)) J x Z)
    (hZ0src : alpha (Z0, s0) ∈ (chartAt H x0).source)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    {U : Set (E × E)} (hUopen : IsOpen U)
    (hseedU :
      (extChartAt I x0 (alpha (Z0, s0)),
        fderiv Real
          (fun s : Real => extChartAt I x0 (alpha (Z0, s))) s0
          (1 : Real)) ∈ U)
    (Phi : (E × E) × Real → E × E)
    (hPhi0 : ∀ z ∈ U, Phi (z, s0) = z)
    (hPhiSmooth : ContDiffOn Real ∞ Phi
      (U ×ˢ Set.Ioo (s0 - epsilon) (s0 + epsilon)))
    (hPhiDeriv : ∀ z ∈ U,
      ∀ s ∈ Set.Ioo (s0 - epsilon) (s0 + epsilon),
        HasDerivAt (fun r => Phi (z, r))
          (lPhaseField S T x0 s (Phi (z, s))) s)
    (hPhiMap : MapsTo (fun q : (E × E) × Real => (q.2, Phi q))
      (U ×ˢ Set.Ioo (s0 - epsilon) (s0 + epsilon))
      {p : Real × (E × E) |
        T - p.1 ^ 2 ∈ D.regular ∧
          p.2.1 ∈ interior (extChartAt I x0).target}) :
    ∃ W : Set E, IsOpen W ∧ Z0 ∈ W ∧ W ⊆ V ∧
      ∃ beta : E × Real → M,
        ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta
          (W ×ˢ (J ∪ Set.Ioo (s0 - epsilon) (s0 + epsilon))) ∧
        ∀ Z ∈ W,
          IsLRegCurveOn S T (fun s => beta (Z, s))
            (J ∪ Set.Ioo (s0 - epsilon) (s0 + epsilon)) x Z := by
  classical
  let pos : E → M := fun Z => alpha (Z, s0)
  have hprodOpen : IsOpen (V ×ˢ J) := hVopen.prod hJopen
  have hposCont : ContinuousOn pos V := by
    intro Z hZ
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (Z, s0) :=
      (halpha (Z, s0) ⟨hZ, hs0J⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hZ, hs0J⟩)
    have hincl : ContMDiffAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun Y : E => (Y, s0)) Z :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (halphaAt.comp Z hincl).continuousAt.continuousWithinAt
  let V0 : Set E := V ∩ pos ⁻¹' (chartAt H x0).source
  have hV0open : IsOpen V0 :=
    hposCont.isOpen_inter_preimage hVopen (chartAt H x0).open_source
  have hZ0V0 : Z0 ∈ V0 := by
    exact ⟨hZ0V, hZ0src⟩
  let seed : E → E × E := fun Z =>
    (extChartAt I x0 (alpha (Z, s0)),
      fderiv Real (fun s : Real => extChartAt I x0 (alpha (Z, s))) s0
        (1 : Real))
  have hseed : ContDiffOn Real ∞ seed V0 := by
    intro Z hZ
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (Z, s0) :=
      (halpha (Z, s0) ⟨hZ.1, hs0J⟩).contMDiffAt
        (hprodOpen.mem_nhds ⟨hZ.1, hs0J⟩)
    exact (lPhaseSeed_smooth (I := I) x0 hZ.2 halphaAt).contDiffWithinAt
  let W : Set E := V0 ∩ seed ⁻¹' U
  have hWopen : IsOpen W :=
    hseed.continuousOn.isOpen_inter_preimage hV0open hUopen
  have hZ0W : Z0 ∈ W := by
    exact ⟨hZ0V0, hseedU⟩
  have hWV : W ⊆ V := fun _ h => h.1.1
  let K : Set Real := Set.Ioo (s0 - epsilon) (s0 + epsilon)
  have hs0K : s0 ∈ K := by
    exact ⟨by linarith, by linarith⟩
  let input : E × Real → (E × E) × Real := fun p => (seed p.1, p.2)
  let phase : E × Real → E × E := fun p => Phi (input p)
  let eta : E × Real → M := fun p =>
    (extChartAt I x0).symm (phase p).1
  have hinput : ContDiffOn Real ∞ input (W ×ˢ K) := by
    have hseedW : ContDiffOn Real ∞ seed W :=
      hseed.mono (fun _ h => h.1)
    exact (hseedW.comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd
  have hinputMap : MapsTo input (W ×ˢ K) (U ×ˢ K) := by
    rintro ⟨Z, s⟩ ⟨hZ, hs⟩
    exact ⟨hZ.2, hs⟩
  have hphase : ContDiffOn Real ∞ phase (W ×ˢ K) := by
    simpa only [phase, Function.comp_def] using
      hPhiSmooth.comp hinput hinputMap
  have hphaseMap : MapsTo (fun p : E × Real => (phase p).1)
      (W ×ˢ K) (extChartAt I x0).target := by
    intro p hp
    exact interior_subset (hPhiMap (hinputMap hp)).2
  have hetaSmooth : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ eta (W ×ˢ K) := by
    have hphaseMD : ContMDiffOn 𝓘(Real, E × Real) 𝓘(Real, E) ∞
        (fun p => (phase p).1) (W ×ˢ K) := hphase.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphaseMD
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x0).comp
      hphaseMD hphaseMap
  have hetaReg : ∀ Z ∈ W, ∀ s ∈ K,
      T - s ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I (fun r => eta (Z, r)) s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) (fun r => eta (Z, r))
            (fun r : Real => lVelocity (I := I) (fun q => eta (Z, q)) r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun r => eta (Z, r))
            (fun r : Real => lVelocity (I := I) (fun q => eta (Z, q)) r) s =
          lRegAccel S T s (eta (Z, s))
            (lVelocity (I := I) (fun q => eta (Z, q)) s) := by
    intro Z hZ
    let z : Real → E × E := fun s => phase (Z, s)
    let gamma : Real → M := lPhaseCurve (I := I) x0 z
    let A : ∀ s, TangentSpace I (gamma s) := lPhaseVel (I := I) x0 z
    have hzU : seed Z ∈ U := hZ.2
    have hsol : ∀ s ∈ K,
        HasDerivAt z (lPhaseField S T x0 s (z s)) s := by
      intro s hs
      simpa only [z, phase, input] using hPhiDeriv (seed Z) hzU s hs
    have hdata : ∀ s ∈ K,
        T - s ^ 2 ∈ D.regular ∧
          (z s).1 ∈ interior (extChartAt I x0).target := by
      intro s hs
      have hmem : ((seed Z, s) : (E × E) × Real) ∈ U ×ˢ K := ⟨hzU, hs⟩
      change T - s ^ 2 ∈ D.regular ∧
        (z s).1 ∈ interior (extChartAt I x0).target
      exact hPhiMap hmem
    have hvel : Set.EqOn (fun s => lVelocity (I := I) gamma s) A K := by
      intro s hs
      have hzs := hsol s hs
      have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
        have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
        simpa [lPhaseField, Function.comp_def] using h
      exact lPhase_velocity (I := I) x0 z s hq (hdata s hs).2
    intro s hs
    have hzs := hsol s hs
    have hsdata := hdata s hs
    have hq : HasDerivAt (fun r : Real => (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    have hv : HasDerivAt (fun r : Real => (z r).2)
        (lPhaseField S T x0 s (z s)).2 s := by
      simpa [Function.comp_def] using hasFDerivAt_snd.comp_hasDerivAt s hzs
    have hfield : (fun r => lVelocity (I := I) gamma r) =ᶠ[𝓝 s] A :=
      hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
      simpa only [gamma] using
        lPhaseCurve_mdiff (I := I) x0 z s hq.differentiableAt hsdata.2
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) gamma A s) s := by
      simpa only [gamma, A] using lPhaseVel_diff (I := I) x0 z s
        hq.differentiableAt hv.differentiableAt hsdata.2
    have hveldiff : DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r : Real => lVelocity (I := I) gamma r) s) s :=
      hAdiff.congr_of_eventuallyEq
        (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) gamma hfield)
    have hacc : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
          (fun r : Real => lVelocity (I := I) gamma r) s =
        lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
      calc
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r : Real => lVelocity (I := I) gamma r) s =
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma A s :=
            covDerivAlong_congr_of_eventuallyEq
              (I := I) (S.base.metric (T - s ^ 2)) gamma hfield
        _ = lRegAccel S T s (gamma s) (A s) := by
          simpa only [gamma, A] using lPhase_accel S T x0 z s hzs hsdata.2
        _ = lRegAccel S T s (gamma s)
            (lVelocity (I := I) gamma s) := by rw [hfield.eq_of_nhds]
    simpa only [eta, gamma, lPhaseCurve, z] using
      ⟨hsdata.1, hgamma, hveldiff, hacc⟩
  have heta0 : ∀ Z ∈ W, eta (Z, s0) = alpha (Z, s0) := by
    intro Z hZ
    have hz0' : phase (Z, s0) = seed Z := by
      simpa only [phase, input] using hPhi0 (seed Z) hZ.2
    change (extChartAt I x0).symm (phase (Z, s0)).1 = alpha (Z, s0)
    rw [hz0']
    change (extChartAt I x0).symm (extChartAt I x0 (alpha (Z, s0))) =
      alpha (Z, s0)
    apply (extChartAt I x0).left_inv
    rw [extChartAt_source]
    exact hZ.1.2
  have hetaVel : ∀ Z ∈ W,
      lVelocity (I := I) (fun s => eta (Z, s)) s0 =
        lVelocity (I := I) (fun s => alpha (Z, s)) s0 := by
    intro Z hZ
    let z : Real → E × E := fun s => phase (Z, s)
    let gamma : Real → M := lPhaseCurve (I := I) x0 z
    have hzs0 : z s0 = seed Z := by
      simpa only [z, phase, input] using hPhi0 (seed Z) hZ.2
    have hsol := hPhiDeriv (seed Z) hZ.2 s0 hs0K
    have hq : HasDerivAt (fun r : Real => (z r).1) (z s0).2 s0 := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s0 hsol
      simpa [z, phase, input, lPhaseField, Function.comp_def] using h
    have hphaseVel := lPhase_velocity (I := I) x0 z s0 hq
      (hPhiMap (show ((seed Z, s0) : (E × E) × Real) ∈ U ×ˢ K from
        ⟨hZ.2, hs0K⟩)).2
    have hsrc : alpha (Z, s0) ∈ (chartAt H x0).source := hZ.1.2
    have hbase : alpha (Z, s0) ∈
        (trivializationAt E (TangentSpace I) x0).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hsrc
    have hseedVel : (seed Z).2 =
        trivToE (I := I) x0 (alpha (Z, s0))
          (lVelocity (I := I) (fun s => alpha (Z, s)) s0) := by
      exact lPhaseSeed_vel (I := I) x0
        ((hcurves Z (hWV hZ)).2.2 s0 hs0J).2.1 hsrc
    have hetaGamma : (fun s => eta (Z, s)) = gamma := by
      rfl
    have hgamma0 : gamma s0 = alpha (Z, s0) := by
      rw [← hetaGamma]
      exact heta0 Z hZ
    rw [hetaGamma]
    rw [hphaseVel]
    change trivFromE (I := I) x0 (gamma s0) (z s0).2 = _
    rw [hgamma0, hzs0, hseedVel]
    exact trivFromE_trivToE (I := I) x0 hbase _
  have hmatch : ∀ Z ∈ W,
      Set.EqOn (fun s => alpha (Z, s)) (fun s => eta (Z, s)) (J ∩ K) := by
    intro Z hZ
    exact lRegSol_eqOn S hS T hJopen hJconn hs0J isOpen_Ioo
      isPreconnected_Ioo hs0K (hcurves Z (hWV hZ)).2.2 (hetaReg Z hZ)
      (heta0 Z hZ).symm (hetaVel Z hZ).symm
  let beta : E × Real → M := fun p => if p.2 ∈ J then alpha p else eta p
  have hbetaSmooth : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta (W ×ˢ (J ∪ K)) := by
    intro p hp
    by_cases hpJ : p.2 ∈ J
    · have halphaAt : ContMDiffAt
          (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha p :=
        (halpha p ⟨hWV hp.1, hpJ⟩).contMDiffAt
          (hprodOpen.mem_nhds ⟨hWV hp.1, hpJ⟩)
      have heq : beta =ᶠ[𝓝 p] alpha := by
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
      have heq : beta =ᶠ[𝓝 p] eta := by
        filter_upwards [(hWopen.preimage continuous_fst).mem_nhds hp.1,
          (isOpen_Ioo.preimage continuous_snd).mem_nhds hpK] with q hqW hqK
        change q.1 ∈ W at hqW
        change q.2 ∈ K at hqK
        simp only [beta]
        by_cases hqJ : q.2 ∈ J
        · rw [if_pos hqJ]
          exact hmatch q.1 hqW ⟨hqJ, hqK⟩
        · rw [if_neg hqJ]
      exact (hetaAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  refine ⟨W, hWopen, hZ0W, hWV, beta, hbetaSmooth, ?_⟩
  intro Z hZ
  have hbetaAlpha : ∀ s ∈ J,
      (fun r => beta (Z, r)) =ᶠ[𝓝 s] (fun r => alpha (Z, r)) := by
    intro s hs
    filter_upwards [hJopen.mem_nhds hs] with r hr
    simp only [beta]
    rw [if_pos hr]
  have hbetaEta : ∀ s ∈ K,
      (fun r => beta (Z, r)) =ᶠ[𝓝 s] (fun r => eta (Z, r)) := by
    intro s hs
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    simp only [beta]
    by_cases hrJ : r ∈ J
    · rw [if_pos hrJ]
      exact hmatch Z hZ ⟨hrJ, hr⟩
    · rw [if_neg hrJ]
  have hbeta0 : beta (Z, 0) = x := by
    simpa only [beta, if_pos h0J] using (hcurves Z (hWV hZ)).1
  have hbetaVel : lVelocity (I := I) (fun s => beta (Z, s)) 0 = 2 • Z := by
    have heq := hbetaAlpha 0 h0J
    simp only [lVelocity]
    rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
    exact (hcurves Z (hWV hZ)).2.1
  refine ⟨hbeta0, hbetaVel, ?_⟩
  intro s hs
  rcases hs with hsJ | hsK
  · exact lRegData_congr S T s (hbetaAlpha s hsJ)
      ((hcurves Z (hWV hZ)).2.2 s hsJ)
  · exact lRegData_congr S T s (hbetaEta s hsK) (hetaReg Z hZ s hsK)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegFamily_step
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {alpha : E × Real → M} {V : Set E} {J : Set Real}
    {Z0 : E} {s0 : Real}
    (hVopen : IsOpen V) (hZ0V : Z0 ∈ V)
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (h0J : (0 : Real) ∈ J) (hs0J : s0 ∈ J)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ J))
    (hcurves : ∀ Z ∈ V,
      IsLRegCurveOn S T (fun s => alpha (Z, s)) J x Z) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ W : Set E, IsOpen W ∧ Z0 ∈ W ∧ W ⊆ V ∧
        ∃ beta : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta
            (W ×ˢ (J ∪ Set.Ioo (s0 - epsilon) (s0 + epsilon))) ∧
          ∀ Z ∈ W,
            IsLRegCurveOn S T (fun s => beta (Z, s))
              (J ∪ Set.Ioo (s0 - epsilon) (s0 + epsilon)) x Z := by
  let x0 : M := alpha (Z0, s0)
  let z0 : E × E :=
    (extChartAt I x0 (alpha (Z0, s0)),
      fderiv Real (fun s : Real => extChartAt I x0 (alpha (Z0, s))) s0
        (1 : Real))
  have hsrc : alpha (Z0, s0) ∈ (chartAt H x0).source := by
    simpa only [x0] using mem_chart_source H (alpha (Z0, s0))
  have hreg : T - s0 ^ 2 ∈ D.regular :=
    ((hcurves Z0 hZ0V).2.2 s0 hs0J).1
  have hz0 : z0.1 ∈ interior (extChartAt I x0).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0, x0] using
      extChartAt_target_mem_nhds (I := I) (alpha (Z0, s0))
  obtain ⟨epsilon, hepsilon, U, hUopen, hz0U, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
    exists_lPhaseAt S hS T x0 s0 z0 hreg hz0
  obtain ⟨W, hWopen, hZ0W, hWV, beta, hbeta, hcurves'⟩ :=
    lRegFamily_step_of S hS T x x0 hVopen hZ0V hJopen hJconn h0J hs0J
      halpha hcurves hsrc epsilon hepsilon hUopen
      (by simpa only [z0] using hz0U) Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
  exact ⟨epsilon, hepsilon, W, hWopen, hZ0W, hWV, beta, hbeta, hcurves'⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegFamily_extend
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {gamma : Real → M} {J : Set Real} {x : M}
    {Z0 : TangentSpace I x} {s0 : Real}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    (h0J : (0 : Real) ∈ J) (hs0J : s0 ∈ J)
    (hgamma : IsLRegCurveOn S T gamma J x Z0) :
    ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧
      ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
        (0 : Real) ∈ K ∧ s0 ∈ K ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ K) ∧
            ∀ Z ∈ V,
              IsLRegCurveOn S T (fun s => alpha (Z, s)) K x Z := by
  classical
  let Good : Set Real := {s | ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧
    ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
      (0 : Real) ∈ K ∧ s ∈ K ∧
      ∃ alpha : E × Real → M,
        ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
            (V ×ˢ K) ∧
          ∀ Z ∈ V,
            IsLRegCurveOn S T (fun r => alpha (Z, r)) K x Z}
  have hT : T ∈ D.regular := by
    simpa using (hgamma.2.2 0 h0J).1
  have hGood0 : (0 : Real) ∈ Good := by
    obtain ⟨epsilon, hepsilon, V, hVopen, hZ0V, alpha, halpha, hcurves⟩ :=
      exists_lRegFamily S hS T x Z0 hT
    have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
      constructor <;> simpa using hepsilon
    exact ⟨V, hVopen, hZ0V, Set.Ioo (-epsilon) epsilon, isOpen_Ioo,
      isPreconnected_Ioo, hzero, hzero, alpha, halpha, hcurves⟩
  have hGoodOpen : IsOpen Good := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨V, hVopen, hZ0V, K, hKopen, hKconn, h0K, hsK,
      alpha, halpha, hcurves⟩ := hs
    obtain ⟨epsilon, hepsilon, W, hWopen, hZ0W, _hWV,
      beta, hbeta, hcurves'⟩ :=
      lRegFamily_step S hS T x hVopen hZ0V hKopen hKconn h0K hsK
        halpha hcurves
    have hsI : s ∈ Set.Ioo (s - epsilon) (s + epsilon) := by
      exact ⟨by linarith, by linarith⟩
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds hsI)
    intro r hr
    have hUnionOpen : IsOpen (K ∪ Set.Ioo (s - epsilon) (s + epsilon)) :=
      hKopen.union isOpen_Ioo
    have hUnionConn : IsPreconnected
        (K ∪ Set.Ioo (s - epsilon) (s + epsilon)) :=
      hKconn.union s hsK hsI isPreconnected_Ioo
    exact ⟨W, hWopen, hZ0W,
      K ∪ Set.Ioo (s - epsilon) (s + epsilon), hUnionOpen, hUnionConn,
      Or.inl h0K, Or.inr hr, beta, hbeta, hcurves'⟩
  have hseg : Set.uIcc (0 : Real) s0 ⊆ J :=
    hJconn.ordConnected.uIcc_subset h0J hs0J
  have hclosed : closure Good ∩ Set.uIcc (0 : Real) s0 ⊆ Good := by
    rintro s ⟨hscl, hsseg⟩
    have hsJ : s ∈ J := hseg hsseg
    let x0 : M := gamma s
    have hgammaCont : ContinuousOn gamma J := by
      intro t ht
      exact (hgamma.2.2 t ht).2.1.continuousAt.continuousWithinAt
    have hgammaAt : ContinuousAt gamma s :=
      (hgammaCont s hsJ).continuousAt (hJopen.mem_nhds hsJ)
    have hsrcNhds : gamma ⁻¹' (chartAt H x0).source ∈ 𝓝 s := by
      apply hgammaAt.preimage_mem_nhds
      apply (chartAt H x0).open_source.mem_nhds
      simpa only [x0] using mem_chart_source H (gamma s)
    have hlocalNhds : J ∩ gamma ⁻¹' (chartAt H x0).source ∈ 𝓝 s :=
      inter_mem (hJopen.mem_nhds hsJ) hsrcNhds
    obtain ⟨a, b, hsQ, hQnhds, hQsub⟩ :=
      exists_Icc_mem_subset_of_mem_nhds hlocalNhds
    let Q : Set Real := Set.Icc a b
    let X : ∀ t, TangentSpace I (gamma t) :=
      fun t => lVelocity (I := I) gamma t
    let zref : Real → E × E := fun t =>
      (chartCurve (I := I) x0 gamma t,
        chartRepAtBase (I := I) x0 gamma X t)
    have hzrefCont : ContinuousOn zref Q := by
      intro t ht
      have htlocal : t ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub ht
      have htdata := hgamma.2.2 t htlocal.1
      have hphase := lRegCurve_phase S T x0 gamma t htdata.2.1
        htlocal.2 htdata.2.2.1 htdata.2.2.2
      simpa only [zref, X] using hphase.continuousAt.continuousWithinAt
    let C : Set (Real × (E × E)) := (fun t => (t, zref t)) '' Q
    have hC : IsCompact C := by
      exact isCompact_Icc.image_of_continuousOn
        (continuousOn_id.prodMk hzrefCont)
    have hCreg : C ⊆ {p : Real × (E × E) |
        T - p.1 ^ 2 ∈ D.regular ∧
          p.2.1 ∈ interior (extChartAt I x0).target} := by
      rintro p ⟨t, htQ, rfl⟩
      have htlocal : t ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub htQ
      refine ⟨(hgamma.2.2 t htlocal.1).1, ?_⟩
      change extChartAt I x0 (gamma t) ∈
        interior (extChartAt I x0).target
      rw [(isOpen_extChartAt_target (I := I) x0).interior_eq]
      apply (extChartAt I x0).map_source
      rw [extChartAt_source]
      exact htlocal.2
    obtain ⟨epsilon, hepsilon, hphaseLocal⟩ :=
      exists_lPhaseComp S hS T x0 hC hCreg
    have hball : Set.Ioo (s - epsilon) (s + epsilon) ∈ 𝓝 s :=
      Ioo_mem_nhds (sub_lt_self _ hepsilon) (lt_add_of_pos_right _ hepsilon)
    have hnear : Q ∩ Set.Ioo (s - epsilon) (s + epsilon) ∈ 𝓝 s := by
      exact inter_mem (by simpa only [Q] using hQnhds) hball
    obtain ⟨t, ⟨htQ, htball⟩, htGood⟩ :=
      mem_closure_iff_nhds.mp hscl _ hnear
    obtain ⟨V, hVopen, hZ0V, K, hKopen, hKconn, h0K, htK,
      alpha, halpha, hcurves⟩ := htGood
    have htlocal : t ∈ J ∩ gamma ⁻¹' (chartAt H x0).source := hQsub htQ
    have hEq : Set.EqOn (fun r => alpha (Z0, r)) gamma (K ∩ J) :=
      lRegWitness_eq S hS T hKopen hKconn h0K hJopen hJconn h0J
        (hcurves Z0 hZ0V) hgamma
    have hpos : alpha (Z0, t) = gamma t := hEq ⟨htK, htlocal.1⟩
    have heqGerm : (fun r => alpha (Z0, r)) =ᶠ[𝓝 t] gamma :=
      hEq.eventuallyEq_of_mem
        ((hKopen.inter hJopen).mem_nhds ⟨htK, htlocal.1⟩)
    have hvel : lVelocity (I := I) (fun r => alpha (Z0, r)) t =
        lVelocity (I := I) gamma t := by
      simp only [lVelocity]
      rw [heqGerm.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
      rfl
    have hptC : (t, zref t) ∈ C := ⟨t, htQ, rfl⟩
    obtain ⟨U, hUopen, hzrefU, Phi,
      hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
      hphaseLocal (t, zref t) hptC
    have halphaSrc : alpha (Z0, t) ∈ (chartAt H x0).source := by
      rw [hpos]
      exact htlocal.2
    have hseedEq :
        (extChartAt I x0 (alpha (Z0, t)),
          fderiv Real
            (fun r : Real => extChartAt I x0 (alpha (Z0, r))) t
            (1 : Real)) = zref t := by
      apply Prod.ext
      · simp only [zref, chartCurve]
        rw [hpos]
      · have hseedVel := lPhaseSeed_vel (I := I) x0
          ((hcurves Z0 hZ0V).2.2 t htK).2.1 halphaSrc
        calc
          fderiv Real
              (fun r : Real => extChartAt I x0 (alpha (Z0, r))) t
              (1 : Real) =
            trivToE (I := I) x0 (alpha (Z0, t))
              (lVelocity (I := I) (fun r => alpha (Z0, r)) t) := hseedVel
          _ = trivToE (I := I) x0 (gamma t)
              (lVelocity (I := I) gamma t) := by rw [hpos, hvel]
          _ = (zref t).2 := by rfl
    obtain ⟨W, hWopen, hZ0W, _hWV, beta, hbeta, hcurves'⟩ :=
      lRegFamily_step_of S hS T x x0 hVopen hZ0V hKopen hKconn h0K htK
        halpha hcurves halphaSrc epsilon hepsilon hUopen
        (by rw [hseedEq]; exact hzrefU) Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
    have hsNew : s ∈ K ∪ Set.Ioo (t - epsilon) (t + epsilon) := by
      right
      exact ⟨by linarith [htball.2], by linarith [htball.1]⟩
    have htI : t ∈ Set.Ioo (t - epsilon) (t + epsilon) :=
      ⟨by linarith, by linarith⟩
    exact ⟨W, hWopen, hZ0W,
      K ∪ Set.Ioo (t - epsilon) (t + epsilon), hKopen.union isOpen_Ioo,
      hKconn.union t htK htI isPreconnected_Ioo, Or.inl h0K, hsNew,
      beta, hbeta, hcurves'⟩
  have hall : Set.uIcc (0 : Real) s0 ⊆ Good :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hGoodOpen
      ⟨0, Set.left_mem_uIcc, hGood0⟩ hclosed
  exact hall Set.right_mem_uIcc

def LRegCurveWitness
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) (s : Real) : Prop :=
  ∃ alpha : Real → M, ∃ J : Set Real,
    IsOpen J ∧ IsPreconnected J ∧ (0 : Real) ∈ J ∧ s ∈ J ∧
      IsLRegCurveOn S T alpha J x Z

def lRegDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) : Set Real :=
  {s | LRegCurveWitness S T x Z s}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegDomain_isOpen
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) :
    IsOpen (lRegDomain S T x Z) := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨alpha, J, hJ, hJconn, h0, hsJ, halpha⟩ := hs
  apply Filter.mem_of_superset (hJ.mem_nhds hsJ)
  intro r hr
  exact ⟨alpha, J, hJ, hJconn, h0, hr, halpha⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegDomain_preconn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) :
    IsPreconnected (lRegDomain S T x Z) := by
  apply isPreconnected_of_forall 0
  intro s hs
  obtain ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩ := hs
  refine ⟨J, ?_, h0J, hsJ, hJconn⟩
  intro r hr
  exact ⟨alpha, J, hJopen, hJconn, h0J, hr, halpha⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegDomain_seg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {r s : Real}
    (hs : s ∈ lRegDomain S T x Z) (hr0 : 0 ≤ r) (hrs : r ≤ s) :
    r ∈ lRegDomain S T x Z := by
  have hzero : (0 : Real) ∈ lRegDomain S T x Z := by
    obtain ⟨alpha, J, hJopen, hJconn, h0J, _hsJ, halpha⟩ := hs
    exact ⟨alpha, J, hJopen, hJconn, h0J, h0J, halpha⟩
  exact (lRegDomain_preconn S T x Z).ordConnected.out hzero hs ⟨hr0, hrs⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegDomain_reg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {s : Real}
    (hs : s ∈ lRegDomain S T x Z) : T - s ^ 2 ∈ D.regular := by
  obtain ⟨_alpha, _J, _hJopen, _hJconn, _h0J, hsJ, halpha⟩ := hs
  exact (halpha.2.2 s hsJ).1

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem zero_mem_lRegDomain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    (0 : Real) ∈ lRegDomain S T x Z := by
  obtain ⟨epsilon, hepsilon, alpha, hstart, hvel, halpha⟩ :=
    exists_lRegCurve S hS T x Z hT
  have hzero : (0 : Real) ∈ Set.Ioo (-epsilon) epsilon := by
    constructor <;> simpa using hepsilon
  exact ⟨alpha, Set.Ioo (-epsilon) epsilon, isOpen_Ioo,
    isPreconnected_Ioo, hzero, hzero, hstart, hvel, halpha⟩

noncomputable def lRegChosen
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {s : Real}
    (h : LRegCurveWitness S T x Z s) : Real → M :=
  Classical.choose h

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegChosen_spec
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {s : Real}
    (h : LRegCurveWitness S T x Z s) :
    ∃ J : Set Real, IsOpen J ∧ IsPreconnected J ∧
      (0 : Real) ∈ J ∧ s ∈ J ∧
      IsLRegCurveOn S T (lRegChosen S T x Z h) J x Z :=
  Classical.choose_spec h

noncomputable def lRegCurve
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) (s : Real) : M :=
  letI : Decidable (LRegCurveWitness S T x Z s) := Classical.dec _
  if h : LRegCurveWitness S T x Z s then lRegChosen S T x Z h s else x

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegCurve_of_mem
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    {x : M} {Z : TangentSpace I x} {s : Real}
    (hs : s ∈ lRegDomain S T x Z) :
    lRegCurve S T x Z s = lRegChosen S T x Z hs s := by
  change LRegCurveWitness S T x Z s at hs
  unfold lRegCurve
  rw [dif_pos hs]

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_eqOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J) (h0J : (0 : Real) ∈ J)
    (halpha : IsLRegCurveOn S T alpha J x Z) :
    Set.EqOn (lRegCurve S T x Z) alpha J := by
  intro s hs
  have hsdom : s ∈ lRegDomain S T x Z :=
    ⟨alpha, J, hJopen, hJconn, h0J, hs, halpha⟩
  rw [lRegCurve_of_mem hsdom]
  obtain ⟨K, hKopen, hKconn, h0K, hsK, hchosen⟩ :=
    lRegChosen_spec S T x Z hsdom
  exact lRegWitness_eq S hS T hKopen hKconn h0K hJopen hJconn h0J
    hchosen halpha ⟨hsK, hs⟩

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_eqIcc
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T b e : Real)
    (hb : 0 ≤ b) (he : 0 < e)
    {alpha : Real → M} {x : M} {Z : TangentSpace I x}
    (halpha : IsLRegCurveOn S T alpha (Ioo (-e) (b + e)) x Z) :
    Set.EqOn (lRegCurve S T x Z) alpha (Icc (0 : Real) b) := by
  have h0 : (0 : Real) ∈ Ioo (-e) (b + e) := by
    constructor <;> linarith
  have heq := lRegCurve_eqOn S hS T isOpen_Ioo isPreconnected_Ioo h0 halpha
  intro s hs
  exact heq ⟨by linarith [hs.1], by linarith [hs.2]⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z0 : TangentSpace I x} {s0 : Real}
    (hs0 : s0 ∈ lRegDomain S T x Z0) :
    ContMDiffAt (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
      (fun p : E × Real => lRegCurve S T x p.1 p.2) (Z0, s0) := by
  obtain ⟨J, hJopen, hJconn, h0J, hs0J, hchosen⟩ :=
    lRegChosen_spec S T x Z0 hs0
  obtain ⟨V, hVopen, hZ0V, K, hKopen, hKconn, h0K, hs0K,
      alpha, halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hs0J hchosen
  have hVKopen : IsOpen (V ×ˢ K) := hVopen.prod hKopen
  have hp : (Z0, s0) ∈ V ×ˢ K := ⟨hZ0V, hs0K⟩
  have halphaAt : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (Z0, s0) :=
    (halpha (Z0, s0) hp).contMDiffAt (hVKopen.mem_nhds hp)
  apply halphaAt.congr_of_eventuallyEq
  filter_upwards [hVKopen.mem_nhds hp] with p hp'
  exact lRegCurve_eqOn S hS T hKopen hKconn h0K
    (hcurves p.1 hp'.1) hp'.2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_smoothAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z0 : TangentSpace I x) (hT : T ∈ D.regular) :
    ContMDiffAt (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
      (fun p : E × Real => lRegCurve S T x p.1 p.2) (Z0, 0) := by
  exact lRegCurve_smooth S hS T x
    (zero_mem_lRegDomain S hS T x Z0 hT)

def lRegJointDom
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    Set (E × Real) :=
  {p | p.2 ∈ lRegDomain S T x p.1}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegJointDom_open
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M) :
    IsOpen (lRegJointDom S T x) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  change p.2 ∈ lRegDomain S T x p.1 at hp
  obtain ⟨J, hJopen, hJconn, h0J, hpJ, hchosen⟩ :=
    lRegChosen_spec S T x p.1 hp
  obtain ⟨V, hVopen, hpV, K, hKopen, hKconn, h0K, hpK,
      alpha, _halpha, hcurves⟩ :=
    lRegFamily_extend S hS T hJopen hJconn h0J hpJ hchosen
  have hVKopen : IsOpen (V ×ˢ K) := hVopen.prod hKopen
  apply Filter.mem_of_superset (hVKopen.mem_nhds ⟨hpV, hpK⟩)
  intro q hq
  change q.2 ∈ lRegDomain S T x q.1
  exact ⟨fun s => alpha (q.1, s), K, hKopen, hKconn, h0K, hq.2,
    hcurves q.1 hq.1⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_smoothOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M) :
    ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
      (fun p : E × Real => lRegCurve S T x p.1 p.2)
      (lRegJointDom S T x) := by
  intro p hp
  exact (lRegCurve_smooth S hS T x hp).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_c1On
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {b : Real}
    (hb : b ∈ lRegDomain S T x Z) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (lRegCurve S T x Z) (Set.Icc (0 : Real) b) := by
  intro s hs
  have hsDom : s ∈ lRegDomain S T x Z :=
    lRegDomain_seg S T x Z hb hs.1 hs.2
  have hpair : ContMDiffAt (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real)) ∞
      ((fun r : Real ↦ (Z, r)) : Real → E × Real) s :=
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hcomp := (lRegCurve_smooth S hS T x hsDom).comp s hpair
  exact (hcomp.of_le (by norm_num)).contMDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegCurve_of_not_mem
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    {x : M} {Z : TangentSpace I x} {s : Real}
    (hs : s ∉ lRegDomain S T x Z) :
    lRegCurve S T x Z s = x := by
  change ¬LRegCurveWitness S T x Z s at hs
  unfold lRegCurve
  rw [dif_neg hs]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lRegCurve_zero
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lRegCurve S T x Z 0 = x := by
  by_cases h0 : (0 : Real) ∈ lRegDomain S T x Z
  · rw [lRegCurve_of_mem h0]
    obtain ⟨J, hJ, hJconn, hz, hs, hcurve⟩ :=
      lRegChosen_spec S T x Z h0
    exact hcurve.1
  · exact lRegCurve_of_not_mem h0

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_vel_zero
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    lVelocity (I := I) (lRegCurve S T x Z) 0 = (2 : Real) • Z := by
  have h0 : (0 : Real) ∈ lRegDomain S T x Z :=
    zero_mem_lRegDomain S hS T x Z hT
  obtain ⟨J, hJopen, hJconn, h0J, _h0J, hchosen⟩ :=
    lRegChosen_spec S T x Z h0
  have heqOn := lRegCurve_eqOn S hS T hJopen hJconn h0J hchosen
  have heq : lRegCurve S T x Z =ᶠ[𝓝 (0 : Real)]
      lRegChosen S T x Z h0 := by
    filter_upwards [hJopen.mem_nhds h0J] with r hr
    exact heqOn hr
  unfold lVelocity
  rw [Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) heq]
  exact hchosen.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 Z).symm

def lExpDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) : Set Real :=
  {tau | 0 ≤ tau ∧ Real.sqrt tau ∈ lRegDomain S T x Z}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem zero_mem_lExpDomain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    (0 : Real) ∈ lExpDomain S T x Z := by
  exact ⟨le_rfl, by simpa using zero_mem_lRegDomain S hS T x Z hT⟩

noncomputable def lExp
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) (tau : Real) : M :=
  lRegCurve S T x Z (Real.sqrt tau)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExp_vel_sqrt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {tau : Real} (htau : 0 < tau) :
    lVelocity (I := I) (lRegCurve S T x Z) (Real.sqrt tau) =
      (2 * Real.sqrt tau) •
        lVelocity (I := I) (fun r : Real ↦ lExp S T x Z r) tau := by
  let s : Real := Real.sqrt tau
  let gamma : Real → M := fun r ↦ lExp S T x Z r
  have hs : 0 < s := Real.sqrt_pos.2 htau
  have heq : lRegCurve S T x Z =ᶠ[𝓝 s] sqReparam gamma := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    simp only [sqReparam, gamma, lExp, Real.sqrt_sq hr.le]
  have hvel :
      lVelocity (I := I) (lRegCurve S T x Z) s =
        lVelocity (I := I) (sqReparam gamma) s := by
    unfold lVelocity
    rw [Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, Real)) (I' := I) heq]
    rfl
  change lVelocity (I := I) (lRegCurve S T x Z) s =
    (2 * s) • lVelocity (I := I) gamma tau
  have hsq := lVelocity_sq_pos (I := I) gamma s hs
  rw [← hvel] at hsq
  rw [show s ^ 2 = tau by simpa only [s] using Real.sq_sqrt htau.le] at hsq
  exact hsq

def lExpPosDom
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    Set (E × Real) :=
  {p | 0 < p.2 ∧ (p.1, Real.sqrt p.2) ∈ lRegJointDom S T x}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem mem_lExpPosDom
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) (tau : Real) :
    (Z, tau) ∈ lExpPosDom S T x ↔
      0 < tau ∧ tau ∈ lExpDomain S T x Z := by
  simp only [lExpPosDom, lRegJointDom, lExpDomain, mem_ofPred_eq]
  constructor
  · rintro ⟨htau, hreg⟩
    exact ⟨htau, htau.le, hreg⟩
  · rintro ⟨htau, _htau0, hreg⟩
    exact ⟨htau, hreg⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExpPosDom_down
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {sigma tau : Real}
    (htau : (Z, tau) ∈ lExpPosDom S T x)
    (hsigma : 0 < sigma) (hle : sigma ≤ tau) :
    (Z, sigma) ∈ lExpPosDom S T x := by
  rcases (mem_lExpPosDom S T x Z tau).1 htau with ⟨_htau, _htau0, htauDom⟩
  apply (mem_lExpPosDom S T x Z sigma).2
  refine ⟨hsigma, hsigma.le, ?_⟩
  exact lRegDomain_seg S T x Z htauDom (Real.sqrt_nonneg sigma)
    (Real.sqrt_le_sqrt hle)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExpPosDom_reg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x : M) (Z : TangentSpace I x) {tau s : Real}
    (htau : (Z, tau) ∈ lExpPosDom S T x)
    (hs : s ∈ Set.Icc (0 : Real) (Real.sqrt tau)) :
    T - s ^ 2 ∈ D.regular := by
  rcases (mem_lExpPosDom S T x Z tau).1 htau with ⟨_htau, _htau0, htauDom⟩
  exact lRegDomain_reg S T x Z
    (lRegDomain_seg S T x Z htauDom hs.1 hs.2)

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpPosDom_open
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M) :
    IsOpen (lExpPosDom S T x) := by
  let reparam : E × Real → E × Real := fun p => (p.1, Real.sqrt p.2)
  have hreparam : Continuous reparam :=
    continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)
  have hopen : IsOpen ({p : E × Real | 0 < p.2} ∩
      reparam ⁻¹' lRegJointDom S T x) :=
    (isOpen_lt continuous_const continuous_snd).inter
      ((lRegJointDom_open S hS T x).preimage hreparam)
  change IsOpen ({p : E × Real | 0 < p.2} ∩
    reparam ⁻¹' lRegJointDom S T x)
  exact hopen

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_smoothOn
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M) :
    ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
      (fun p : E × Real => lExp S T x p.1 p.2)
      (lExpPosDom S T x) := by
  intro p hp
  let reparam : E × Real → E × Real := fun q => (q.1, Real.sqrt q.2)
  have hreparam : ContDiffAt Real ∞ reparam p :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sqrt hp.1.ne')
  have hreparamMD : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞ reparam p := by
    have h := hreparam.contMDiffAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hcurve := lRegCurve_smooth S hS T x hp.2
  have hcomp := hcurve.comp p hreparamMD
  simpa only [lExp, reparam, Function.comp_def] using
    hcomp.contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lExpFamily
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z0 : TangentSpace I x) (hT : T ∈ D.regular) :
    ∃ delta : Real, 0 < delta ∧
      ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧
        ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞
          (fun p : E × Real => lExp S T x p.1 p.2)
          (V ×ˢ Set.Ioo 0 delta) := by
  obtain ⟨epsilon, hepsilon, V, hVopen, hZ0V, alpha, halpha, hcurves⟩ :=
    exists_lRegFamily S hS T x Z0 hT
  let reparam : E × Real → E × Real := fun p => (p.1, Real.sqrt p.2)
  let beta : E × Real → M := fun p => alpha (reparam p)
  have hsqrt : ContDiffOn Real ∞ Real.sqrt (Set.Ioo 0 (epsilon ^ 2)) :=
    contDiffOn_id.sqrt (fun tau htau => htau.1.ne')
  have hreparam : ContDiffOn Real ∞ reparam
      (V ×ˢ Set.Ioo 0 (epsilon ^ 2)) := by
    apply contDiffOn_fst.prodMk
    exact hsqrt.comp contDiffOn_snd (fun p hp => hp.2)
  have hreparamMD : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞ reparam
      (V ×ˢ Set.Ioo 0 (epsilon ^ 2)) := by
    have h := hreparam.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hreparamMap : MapsTo reparam (V ×ˢ Set.Ioo 0 (epsilon ^ 2))
      (V ×ˢ Set.Ioo (-epsilon) epsilon) := by
    rintro ⟨Z, tau⟩ ⟨hZ, htau⟩
    refine ⟨hZ, ?_, (Real.sqrt_lt' hepsilon).2 htau.2⟩
    exact lt_of_lt_of_le (neg_lt_zero.mpr hepsilon) (Real.sqrt_nonneg tau)
  have hbeta : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ beta
      (V ×ˢ Set.Ioo 0 (epsilon ^ 2)) := by
    exact halpha.comp hreparamMD hreparamMap
  refine ⟨epsilon ^ 2, sq_pos_of_pos hepsilon, V, hVopen, hZ0V, ?_⟩
  apply hbeta.congr
  intro p hp
  have hs := (hreparamMap hp).2
  have heq := lRegCurve_eqOn S hS T isOpen_Ioo isPreconnected_Ioo
    (show (0 : Real) ∈ Set.Ioo (-epsilon) epsilon by
      constructor <;> simpa using hepsilon)
    (hcurves p.1 hp.1) hs
  simpa only [lExp, beta, reparam] using heq

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
@[simp] theorem lExp_zero
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lExp S T x Z 0 = x := by
  simpa only [lExp, Real.sqrt_zero] using lRegCurve_zero S T x Z

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
