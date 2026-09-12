import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

def Field.SmoothOn {c : CurveMap M} (V : c.Field (I := I)) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
    (fun p : ℝ × ℝ => (⟨c.lift p.1 p.2, V p.1 p.2⟩ : TangentBundle I M))
    (univ ×ˢ J)

omit [CompleteSpace E] in
theorem Dt_eq_covDerivAlong (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ) (ht : J ∈ 𝓝 t) :
    c.Dt g J V x t = covDerivAlong (g t) (c.lift x) (V x) t := by
  simp only [Dt, covDerivAlong, chartCovDerivAlong, derivWithin_of_mem_nhds ht]

end CurveMap

variable [SigmaCompactSpace M] [T2Space M]


def connectionVariation (G : SolutionFamily (I := I) (M := M)) (J : Set ℝ)
    (t : ℝ) (p : M) (A B : TangentSpace I p) : TangentSpace I p :=
  derivWithin (fun s => G.connection s (tangentConstAt (I := I) p B) p A) J t

def nablaRicci (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : ℝ :=
  totalNabla0SFun 2 (G.connection t) (G.ricci t) p (Fin.cons A (vec2 B Z))

def riemannVector (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : TangentSpace I p :=
  connectionRiemannCurvatureField (G.connection t)
    (tangentConstAt (I := I) p A) (tangentConstAt (I := I) p B)
    (tangentConstAt (I := I) p Z) p

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hasDerivWithinAt_of_metric_pairings
    (g : SmoothRiemannianMetric I M) (p : M) (V : ℝ → TangentSpace I p)
    (Z : TangentSpace I p) {J : Set ℝ} {t : ℝ}
    (h : ∀ w : TangentSpace I p,
      HasDerivWithinAt (fun r => g.inner p (V r) w) (g.inner p Z w) J t) :
    HasDerivWithinAt V Z J t := by
  classical
  let : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TangentSpace I p)
  have hrec (w : TangentSpace I p) :
      (∑ i, g.inner p w (metricSharp g p (b.coord i)) • b i) = w := by
    simp only [inner_metricSharp_right]
    exact b.sum_repr w
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => (h (metricSharp g p (b.coord i))).smul_const (b i))
  simpa only [hrec] using hsum

variable [hBoundary : I.Boundaryless]
include hBoundary

omit [SigmaCompactSpace M] in
private theorem hasDerivWithinAt_spatialConnection {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    HasDerivWithinAt
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A)
      (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A) (Icc a b) t := by
  let S : SolutionOn (I := I) (M := M) D := ⟨B.family⟩
  let delta : ℝ → TangentSpace I p := fun r =>
    CovariantDerivative.difference (LeviCivita (S.base.metric r))
      (LeviCivita (S.base.metric 0)) p V A
  let Z := connectionVariationSpeed S t p V A
  have hvec : HasDerivWithinAt delta Z (Icc a b) t :=
    hasDerivWithinAt_of_metric_pairings (S.base.metric 0) p delta Z
      (fun w => hasDerivWithinAt_connectionDifference_pairing S B.equation
        (B.regular.trans D.regular_subset) (B.regular ht) p V A w)
  let fixed := B.family.connection 0 (tangentConstAt (I := I) p V) p A
  have hdelta (r : ℝ) : delta r =
      B.family.connection r (tangentConstAt (I := I) p V) p A - fixed := by
    have h := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
      (S.base.metric r) (S.base.metric 0)
      (mdifferentiableAt_tangentConstAt_self (I := I) p V) A
    simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference,
      tangentConstAt_self, delta, fixed, S, SolutionFamily.connection, LeviCivita] using h
  have hsum := hvec.add_const fixed
  have hf : (fun r => delta r + fixed) =
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A) := by
    funext r
    rw [hdelta, sub_add_cancel]
  rw [hf] at hsum
  exact hsum

omit [SigmaCompactSpace M] in
private theorem connectionVariation_eq_nativeSpeed {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    connectionVariation B.family (Icc a b) t p A V =
      connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A :=
  (hasDerivWithinAt_spatialConnection B t ht p A V).derivWithin
    ((uniqueDiffOn_Icc B.lt) t ht)

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_eq_metricNablaRic
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) :
    nablaRicci G t p A V Z = metricNablaRic (G.metric t) p (vec3 A V Z) := by
  change metricNablaRic (G.metric t) p (Fin.cons A (vec2 V Z)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_last_two_symm
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) : nablaRicci G t p A V Z = nablaRicci G t p A Z V := by
  simpa only [nablaRicci_eq_metricNablaRic] using
    metricNablaRic_last_two_symm (G.metric t) p A V Z

omit [SigmaCompactSpace M] in
theorem rfs_csf_connection [_sigmaCompactM : SigmaCompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V Z : TangentSpace I p) :
    (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      -nablaRicci B.family t p A V Z - nablaRicci B.family t p V A Z +
        nablaRicci B.family t p Z A V := by
  rw [connectionVariation_eq_nativeSpeed B t ht p A V]
  have hpair :
      (B.family.metric t).inner p
        (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
          t p V A) Z =
      -nablaRicci B.family t p V A Z - nablaRicci B.family t p A V Z +
        nablaRicci B.family t p Z V A := by
    simp only [nablaRicci_eq_metricNablaRic]
    exact inner_metricSharp (B.family.metric t) p
      (koszulRicciCovector
        (DifferentialGeometry.PDE.RicciFlow.nablaRicci
          (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) t p) V A) Z
  rw [hpair, nablaRicci_last_two_symm B.family t p Z V A]
  ring


theorem connectionVariation_tensor {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) :
    (∀ A V, connectionVariation B.family (Icc a b) t p A V =
      connectionVariation B.family (Icc a b) t p V A) ∧
    (∀ A A' V, connectionVariation B.family (Icc a b) t p (A + A') V =
      connectionVariation B.family (Icc a b) t p A V +
      connectionVariation B.family (Icc a b) t p A' V) ∧
    (∀ (r : ℝ) A V, connectionVariation B.family (Icc a b) t p (r • A) V =
      r • connectionVariation B.family (Icc a b) t p A V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A V
    apply metricFlatLinear_injective (B.family.metric t) p
    ext Z
    change (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p V A) Z
    rw [rfs_csf_connection B t ht p A V Z, rfs_csf_connection B t ht p V A Z,
      nablaRicci_last_two_symm B.family t p Z V A]
    ring
  · intro A A' V
    unfold connectionVariation
    simp only [map_add]
    exact derivWithin_fun_add
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt
      (hasDerivWithinAt_spatialConnection B t ht p A' V).differentiableWithinAt
  · intro r A V
    unfold connectionVariation
    simp only [map_smul]
    exact derivWithin_fun_const_smul r
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt


omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem chartGramOnE_sum_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {t : ℝ}
    (hγ : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet) (A B : E) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
          chartCoord (E := E) i A * chartCoord (E := E) j B) =
      g.inner (γ t)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t) A)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t) B) := by
  classical
  rw [inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α A B]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hsrc : γ t ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    rwa [TangentBundle.trivializationAt_baseSet] at hγ
  rw [chartGramOnE_def, chartCurve_def, (extChartAt I α).left_inv hsrc]

omit [SigmaCompactSpace M] in
lemma chartGramOnE_metricFamily_differentiableAt
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (α : M) (γ : ℝ → M) {t : ℝ} (ht : t ∈ D.regular) (hγt : γ t = α)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2)
      (t, chartCurve (I := I) α γ t) := by
  classical
  have hsrc : α ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H α
  have hUt : chartCurve (I := I) α γ t ∈ (extChartAt I α).target := by
    rw [chartCurve_def, hγt]
    exact (extChartAt I α).map_source hsrc
  have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ t) = α := by
    rw [chartCurve_def, hγt]
    exact (extChartAt I α).left_inv hsrc
  let e := trivializationAt E (TangentSpace I) α
  let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hcompOn := B.smooth.frameCompSmooth (e.localFrame b) hframe i j
  have hbase : α ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hcompAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × M =>
        (B.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, α) :=
    hcompOn.contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds ht) (e.open_baseSet.mem_nhds hbase))
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      (extChartAt I α).symm (chartCurve (I := I) α γ t) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) α).contMDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hUt)
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
      (fun q : ℝ × E => (q.1, (extChartAt I α).symm q.2))
      (t, chartCurve (I := I) α γ t) :=
    contMDiffAt_fst.prodMk (hsymm.comp (t, chartCurve (I := I) α γ t) contMDiffAt_snd)
  have hjoint0 := hcompAt.comp_of_eq hmap (by simp only [hinv])
  have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × E =>
        (B.family.metric q.1).inner ((extChartAt I α).symm q.2)
          (e.localFrame b i ((extChartAt I α).symm q.2))
          (e.localFrame b j ((extChartAt I α).symm q.2)))
      (t, chartCurve (I := I) α γ t) := by
    change ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      ((fun q : ℝ × M =>
        (B.family.metric q.1).inner q.2 (e.localFrame b i q.2) (e.localFrame b j q.2)) ∘
        fun q : ℝ × E => (q.1, (extChartAt I α).symm q.2))
      (t, chartCurve (I := I) α γ t)
    exact hjoint0
  have htarget : ∀ᶠ q : ℝ × E in 𝓝 (t, chartCurve (I := I) α γ t),
      q.2 ∈ (extChartAt I α).target :=
    (continuous_snd.tendsto (t, chartCurve (I := I) α γ t)).eventually
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hUt)
  have heq :
      (fun q : ℝ × E =>
        (B.family.metric q.1).inner ((extChartAt I α).symm q.2)
          (e.localFrame b i ((extChartAt I α).symm q.2))
          (e.localFrame b j ((extChartAt I α).symm q.2))) =ᶠ[𝓝 (t, chartCurve (I := I) α γ t)]
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2) := by
    filter_upwards [htarget] with q hq
    have hxsrc : (extChartAt I α).symm q.2 ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hq
    have hxbase : (extChartAt I α).symm q.2 ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      rw [← DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
      exact hxsrc
    rw [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      e.localFrame_apply_of_mem_baseSet b hxbase,
      e.localFrame_apply_of_mem_baseSet b hxbase]
    simp only [e, b, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
      Trivialization.symmL_apply _ hxbase]
  have hcd : ContDiffAt ℝ (∞ : WithTop ℕ∞)
      (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2)
      (t, chartCurve (I := I) α γ t) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hjoint.congr_of_eventuallyEq heq.symm
  exact hcd.differentiableAt (by simp)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H] [I.Boundaryless] in
lemma hasDerivWithinAt_diag {F : ℝ × ℝ → ℝ} {F' : (ℝ × ℝ) →L[ℝ] ℝ}
    {a b : ℝ} {J : Set ℝ} {t : ℝ}
    (hF : HasFDerivWithinAt F F' (J ×ˢ J) (t, t))
    (ha : HasDerivWithinAt (fun s => F (s, t)) a J t)
    (hb : HasDerivWithinAt (fun s => F (t, s)) b J t)
    (ht : t ∈ J) (huniq : UniqueDiffWithinAt ℝ J t) :
    HasDerivWithinAt (fun s => F (s, s)) (a + b) J t := by
  have hφ1 : HasDerivWithinAt (fun s : ℝ => (s, t)) ((1, 0) : ℝ × ℝ) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t)).hasDerivWithinAt
  have h1 : HasDerivWithinAt (fun s => F (s, t)) (F' (1, 0)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (s, t)) (x := t) hφ1 (fun s hs => ⟨hs, ht⟩)
  have he1 : F' (1, 0) = a := (h1.derivWithin huniq).symm.trans (ha.derivWithin huniq)
  have hφ2 : HasDerivWithinAt (fun s : ℝ => (t, s)) ((0, 1) : ℝ × ℝ) J t :=
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun s => F (t, s)) (F' (0, 1)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (t, s)) (x := t) hφ2 (fun s hs => ⟨ht, hs⟩)
  have he2 : F' (0, 1) = b := (h2.derivWithin huniq).symm.trans (hb.derivWithin huniq)
  have hφ : HasDerivWithinAt (fun s : ℝ => (s, s)) ((1, 1) : ℝ × ℝ) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  have hd : HasDerivWithinAt (fun s => F (s, s)) (F' (1, 1)) J t :=
    hF.comp_hasDerivWithinAt (f := fun s : ℝ => (s, s)) (x := t) hφ (fun s hs => ⟨hs, hs⟩)
  refine hd.congr_deriv ?_
  calc F' (1, 1) = F' ((1, 0) + (0, 1)) := by norm_num
    _ = F' (1, 0) + F' (0, 1) := map_add F' (1, 0) (0, 1)
    _ = a + b := by rw [he1, he2]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem Dt_eq_symmL_chart (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ) :
    c.Dt g J V x t =
      (trivializationAt E (TangentSpace I) (c.lift x t)).symmL ℝ (c.lift x t)
        (derivWithin (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r)
            (fun r => V x r)) J t
          + chartChristoffelContraction (I := I) (g t) (c.lift x t)
              (derivWithin (chartCurve (I := I) (c.lift x t) (fun r => c.lift x r)) J t)
              (chartRepAtBase (I := I) (c.lift x t) (fun r => c.lift x r)
                (fun r => V x r) t)
              (chartCurve (I := I) (c.lift x t) (fun r => c.lift x r) t)) := rfl



omit [CompleteSpace E] [TopologicalSpace H] [I.Boundaryless] in
theorem chartCoord_comp_differentiableWithinAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : F → E} {J : Set F} {t : F}
    (i : Fin (Module.finrank ℝ E)) (hX : DifferentiableWithinAt ℝ X J t) :
    DifferentiableWithinAt ℝ (fun s => chartCoord (E := E) i (X s)) J t := by
  set L : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i) with hLdef
  have hLapply : ∀ v : E, L v = chartCoord (E := E) i v := by
    intro v
    rw [hLdef]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rfl
  have h3 : DifferentiableWithinAt ℝ (fun s => L (X s)) J t :=
    L.differentiableAt.comp_differentiableWithinAt (x := t) (f := X) hX
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => hLapply (X s)))
    (hLapply (X t))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem chartRepAtBase_differentiableWithinAt
    {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {J : Set ℝ} {t : ℝ}
    (hV : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ s) (V s) : TangentBundle I M)) J t) :
    DifferentiableWithinAt ℝ (chartRepAtBase (I := I) (γ t) γ V) J t := by
  classical
  let β : M := γ t
  let e := trivializationAt E (TangentSpace I) β
  have hpair := Bundle.contMDiffWithinAt_totalSpace.mp hV
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ t)).baseSet ∈ 𝓝[J] t :=
    hpair.1.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hmem)
  have heq : (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2)
      =ᶠ[𝓝[J] t] chartRepAtBase (I := I) (γ t) γ V := by
    filter_upwards [hpre] with s hs
    rw [chartRepAtBase_apply]
    simp only [TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hs]
  have hcd : ContDiffWithinAt ℝ ∞ (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2) J t :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hpair.2
  have hdiff : DifferentiableWithinAt ℝ (fun s : ℝ =>
        ((trivializationAt E (TangentSpace I) (γ t))
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ s) (V s) :
            TangentBundle I M)).2) J t :=
    hcd.differentiableWithinAt (by norm_num)
  refine hdiff.congr_of_eventuallyEq heq.symm ?_
  rw [chartRepAtBase_apply]
  simp only [TotalSpace.mk']
  rw [(trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_apply (R := ℝ)]
  rw [(trivializationAt E (TangentSpace I) (γ t)).coe_linearMapAt_of_mem hmem]

omit [SigmaCompactSpace M] in
theorem moving_inner_derivative {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (hW : W.SmoothOn (I := I) (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (fun r => (B.family.metric r).inner (c.lift x r) (V x r) (W x r))
      (Icc s u) t =
      (B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric (Icc s u) V x t) (W x t) +
      (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric (Icc s u) W x t) -
      2 * B.family.ricciAt t (c.lift x t) (vec2 (V x t) (W x t)) := by
  classical
  set J : Set ℝ := Icc s u with hJ
  have htJ : t ∈ J := ht
  have huniq : UniqueDiffWithinAt ℝ J t := (uniqueDiffOn_Icc hsu) t htJ
  have hreg : t ∈ D.regular := B.regular (hwindow ht)
  have hsub : J ⊆ D.carrier := fun r hr => D.regular_subset (B.regular (hwindow hr))
  set γ : ℝ → M := fun r => c.lift x r with hγ
  set α : M := c.lift x t with hα
  set Vx : (r : ℝ) → TangentSpace I (γ r) := fun r => V x r with hVx
  set Wx : (r : ℝ) → TangentSpace I (γ r) := fun r => W x r with hWx
  set e := trivializationAt E (TangentSpace I) α with he
  set U : ℝ → E := chartCurve (I := I) α γ with hU
  set Vrep : ℝ → E := chartRepAtBase (I := I) α γ Vx with hVrep
  set Wrep : ℝ → E := chartRepAtBase (I := I) α γ Wx with hWrep
  set Q : ℝ × ℝ → ℝ := fun p => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) (B.family.metric p.1) α i j (U p.2) *
        chartCoord (E := E) i (Vrep p.2) * chartCoord (E := E) j (Wrep p.2) with hQ
  have hbase : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hγsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ γ J t :=
    CurveMap.time_slice_contMDiffWithinAt (I := I) c J hc x t htJ
  have hVsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ r) (Vx r) :
        TangentBundle I M)) J t := by
    have h0 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
        (fun p : ℝ × ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift p.1 p.2) (V p.1 p.2) : TangentBundle I M)) (univ ×ˢ J) (x, t) :=
      (show (V.SmoothOn (I := I) J) from hV) (x, t) ⟨mem_univ x, htJ⟩
    refine h0.comp t ?_ ?_
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    · intro r hr; exact ⟨mem_univ x, hr⟩
  have hWsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ r) (Wx r) :
        TangentBundle I M)) J t := by
    have h0 : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
        (fun p : ℝ × ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (c.lift p.1 p.2) (W p.1 p.2) : TangentBundle I M)) (univ ×ˢ J) (x, t) :=
      (show (W.SmoothOn (I := I) J) from hW) (x, t) ⟨mem_univ x, htJ⟩
    refine h0.comp t ?_ ?_
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    · intro r hr; exact ⟨mem_univ x, hr⟩
  have hUdiff : DifferentiableWithinAt ℝ U J t := by
    have hsm : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ U J t := by
      have hφ : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (extChartAt I α) univ (γ t) :=
        (contMDiffAt_extChartAt (I := I) (x := α) (n := (∞ : WithTop ℕ∞))).contMDiffWithinAt
      exact hφ.comp t hγsm (fun r _ => mem_univ (γ r))
    exact (contMDiffWithinAt_iff_contDiffWithinAt.mp hsm).differentiableWithinAt (by norm_num)
  have hVdiff : DifferentiableWithinAt ℝ Vrep J t :=
    chartRepAtBase_differentiableWithinAt (I := I) (γ := γ) (V := Vx) (J := J) (t := t) hVsm
  have hWdiff : DifferentiableWithinAt ℝ Wrep J t :=
    chartRepAtBase_differentiableWithinAt (I := I) (γ := γ) (V := Wx) (J := J) (t := t) hWsm
  have hsrc : α ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H α
  have hUt : U t ∈ (extChartAt I α).target := by
    simpa only [hU, chartCurve_def] using (extChartAt I α).map_source hsrc
  have hmem : U t ∈ interior (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hUt
  have hVsymm : e.symmL ℝ (γ t) (Vrep t) = Vx t := by
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hbase (Vx t)
    simpa only [hVrep, chartRepAtBase_apply] using h
  have hWsymm : e.symmL ℝ (γ t) (Wrep t) = Wx t := by
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hbase (Wx t)
    simpa only [hWrep, chartRepAtBase_apply] using h
  have hUhas : HasDerivWithinAt U (derivWithin U J t) J t := hUdiff.hasDerivWithinAt
  have hVhas : HasDerivWithinAt Vrep (derivWithin Vrep J t) J t := hVdiff.hasDerivWithinAt
  have hWhas : HasDerivWithinAt Wrep (derivWithin Wrep J t) J t := hWdiff.hasDerivWithinAt
  have h2nd0 := DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartGramAlongCurve_hasDerivWithinAt_covariant (I := I)
    (B.family.metric t) α γ Vrep Wrep
    (uPrime := derivWithin U J) (Vprime := derivWithin Vrep J) (Wprime := derivWithin Wrep J)
    hUhas hmem hVhas hWhas
  set A : E := derivWithin Vrep J t + chartChristoffelContraction (I := I) (B.family.metric t)
    α (derivWithin U J t) (Vrep t) (U t) with hA
  set Bv : E := derivWithin Wrep J t + chartChristoffelContraction (I := I) (B.family.metric t)
    α (derivWithin U J t) (Wrep t) (U t) with hBv
  have hsum1 : (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (B.family.metric t) α l j (U t) *
          chartCoord (E := E) l A * chartCoord (E := E) j (Wrep t)) =
      (B.family.metric t).inner (γ t) (e.symmL ℝ (γ t) A) (e.symmL ℝ (γ t) (Wrep t)) :=
    chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ hbase A (Wrep t)
  have hsum2 : (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) (B.family.metric t) α i l (U t) *
          chartCoord (E := E) i (Vrep t) * chartCoord (E := E) l Bv) =
      (B.family.metric t).inner (γ t) (e.symmL ℝ (γ t) (Vrep t)) (e.symmL ℝ (γ t) Bv) :=
    chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ hbase (Vrep t) Bv
  have hbridgeV : e.symmL ℝ (γ t) A = c.Dt B.family.metric J V x t :=
    Dt_eq_symmL_chart (c := c) (g := B.family.metric) (J := J) (V := V) (x := x) (t := t)
  have hbridgeW : e.symmL ℝ (γ t) Bv = c.Dt B.family.metric J W x t :=
    Dt_eq_symmL_chart (c := c) (g := B.family.metric) (J := J) (V := W) (x := x) (t := t)
  have h2nd : HasDerivWithinAt (fun s : ℝ => Q (t, s))
      ((B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric J V x t) (W x t) +
        (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric J W x t)) J t := by
    have hfun : (fun s : ℝ => chartGramAlongCurve (I := I) (B.family.metric t) α γ Vrep Wrep s) =
        (fun s : ℝ => Q (t, s)) := by
      funext s
      simp only [hQ, chartGramAlongCurve_def, hU]
    rw [hfun] at h2nd0
    refine h2nd0.congr_deriv ?_
    rw [hsum1, hsum2, hWsymm, hVsymm]
    rw [← hbridgeV, ← hbridgeW]
  have h1st : HasDerivWithinAt (fun r : ℝ => Q (r, t))
      (-2 * B.family.ricciAt t α (vec2 (Vx t) (Wx t))) J t := by
    have hm : HasDerivWithinAt (fun s : ℝ => (B.family.metric s).inner α (Vx t) (Wx t))
        (-2 * B.family.ricciAt t α (vec2 (Vx t) (Wx t))) D.carrier t :=
      metric_derivWithin_eq_neg_two_ricci (I := I) (D := D)
        (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) B.equation
        (⟨t, hreg⟩ : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
        α (Vx t) (Wx t)
    refine (hm.mono hsub).congr_of_eventuallyEq ?_ ?_
    · filter_upwards with r
      simp only [hQ]
      rw [chartGramOnE_sum_eq_inner (I := I) (B.family.metric r) α γ (t := t) hbase (Vrep t) (Wrep t),
        hVsymm, hWsymm]
    · simp only [hQ]
      rw [chartGramOnE_sum_eq_inner (I := I) (B.family.metric t) α γ (t := t) hbase (Vrep t) (Wrep t),
        hVsymm, hWsymm]
  have hchart2 : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun q : ℝ × E => chartGramOnE (I := I) (B.family.metric q.1) α i j q.2) (t, U t) :=
    fun i j => chartGramOnE_metricFamily_differentiableAt (I := I) B α γ hreg rfl i j
  have hUpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => U p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := U) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hUdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hVpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => Vrep p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := Vrep) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hVdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hWpair : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => Wrep p.2) (J ×ˢ J) (t, t) :=
    DifferentiableWithinAt.comp (x := (t, t)) (g := Wrep) (f := fun p : ℝ × ℝ => p.2)
      (s := J ×ˢ J) (t := J) hWdiff (differentiableWithinAt_snd (p := (t, t)))
      (fun y hy => hy.2)
  have hinner2 : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ => (p.1, U p.2)) (J ×ˢ J) (t, t) :=
    (differentiableWithinAt_fst (p := (t, t))).prodMk hUpair
  have hQdiff : DifferentiableWithinAt ℝ Q (J ×ˢ J) (t, t) := by
    simp only [hQ]
    refine DifferentiableWithinAt.fun_sum
      (fun i _ => DifferentiableWithinAt.fun_sum (fun j _ => ?_))
    have hG : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ =>
        chartGramOnE (I := I) (B.family.metric p.1) α i j (U p.2)) (J ×ˢ J) (t, t) :=
      (HasFDerivWithinAt.comp (x := (t, t)) (f := fun p : ℝ × ℝ => (p.1, U p.2))
        (s := J ×ˢ J) (t := univ)
        (hchart2 i j).hasFDerivAt.hasFDerivWithinAt hinner2.hasFDerivWithinAt
        (fun y _ => mem_univ _)).differentiableWithinAt
    exact (hG.mul (chartCoord_comp_differentiableWithinAt i hVpair)).mul
      (chartCoord_comp_differentiableWithinAt j hWpair)
  have hdiag := hasDerivWithinAt_diag (F := Q) (F' := fderivWithin ℝ Q (J ×ˢ J) (t, t))
    hQdiff.hasFDerivWithinAt h1st h2nd htJ huniq
  have hEq : (fun r : ℝ => (B.family.metric r).inner (γ r) (Vx r) (Wx r)) =ᶠ[𝓝[J] t]
      (fun r : ℝ => Q (r, r)) := by
    have hcont : ContinuousWithinAt γ J t := hγsm.continuousWithinAt
    filter_upwards [hcont.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)] with r hr
    simp only [hQ]
    have hVs : e.symmL ℝ (γ r) (Vrep r) = Vx r := by
      have h := e.symmL_continuousLinearMapAt (R := ℝ) hr (Vx r)
      simpa only [hVrep, chartRepAtBase_apply] using h
    have hWs : e.symmL ℝ (γ r) (Wrep r) = Wx r := by
      have h := e.symmL_continuousLinearMapAt (R := ℝ) hr (Wx r)
      simpa only [hWrep, chartRepAtBase_apply] using h
    have hsrcr : γ r ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source (I := I)]
      rwa [TangentBundle.trivializationAt_baseSet] at hr
    rw [← hVs, ← hWs,
      inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) (B.family.metric r) α (Vrep r) (Wrep r)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [chartGramOnE_def,
      show (extChartAt I α).symm (U r) = γ r from by
        rw [hU, chartCurve_def]
        exact (extChartAt I α).left_inv hsrcr]
  have hcons := hdiag.congr_of_eventuallyEq hEq (hEq.eq_of_nhdsWithin htJ)
  have hfinal : derivWithin (fun r : ℝ => (B.family.metric r).inner (c.lift x r) (V x r) (W x r))
        (Icc s u) t =
      -2 * B.family.ricciAt t α (vec2 (Vx t) (Wx t)) +
      ((B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric J V x t) (W x t) +
        (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric J W x t)) :=
    hcons.derivWithin huniq
  rw [hfinal]
  simp only [hJ, hVx, hWx]
  ring

theorem pullback_commutator {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) (c.Dx B.family.metric V) x t -
      c.Dx B.family.metric (c.Dt B.family.metric (Icc s u) V) x t =
    riemannVector B.family t (c.lift x t) (c.velocity (Icc s u) x t) (c.X x t) (V x t) +
      connectionVariation B.family (Icc s u) t (c.lift x t) (c.X x t) (V x t) := by
  sorry

theorem pullback_torsion_free {D : RealTimeInterval} {a b s u : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) c.X x t =
      c.Dx B.family.metric (c.velocity (Icc s u)) x t := by
  sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
theorem CurveMap.Dt_eq_covDerivAlong_of_mem_Ioo (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (V : c.Field (I := I))
    {s u x t : ℝ} (ht : t ∈ Ioo s u) :
    c.Dt g (Icc s u) V x t = covDerivAlong (g t) (c.lift x) (V x) t :=
  CurveMap.Dt_eq_covDerivAlong c g (Icc s u) V x t (Icc_mem_nhds ht.1 ht.2)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
