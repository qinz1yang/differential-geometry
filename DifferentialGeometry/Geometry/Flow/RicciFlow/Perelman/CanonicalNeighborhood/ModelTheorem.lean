import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BadPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates
import DifferentialGeometry.Geometry.Metric.Completeness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open scoped Manifold ContDiff



section Datum

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

def OrientationDatum (I : ModelWithCorners Real E H) : Type _ :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M],
    ∀ P : DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.{u, uE, uH} (I := I)
      ancientTimeInterval,
      (letI : TopologicalSpace P.M := P.topology
       letI : ChartedSpace H P.M := P.charted
       PartialDiffeomorph I I P.M M (∞ : WithTop ℕ∞)) → Prop

def trivialOrientationDatum (I : ModelWithCorners Real E H) :
    OrientationDatum.{u, uE, uH} I :=
  fun _ _ _ _ _ => True

end Datum



section Good

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable {D : RealTimeInterval}

def IsOrientedGoodPoint (orient : OrientationDatum I) (eps kappa : Real)
    (S : SolutionOn (I := I) (M := M) D) (x : M) (t : Real) : Prop :=
  ∃ W : KappaModelWitness (I := I) eps kappa S x t, W.IsOrientationPreserving (orient M)

theorem isGoodPoint_of_isOrientedGoodPoint {orient : OrientationDatum I}
    {eps kappa : Real} {S : SolutionOn (I := I) (M := M) D} {x : M} {t : Real}
    (h : IsOrientedGoodPoint (I := I) orient eps kappa S x t) :
    IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t :=
  ⟨h.choose⟩

theorem isOrientedGoodPoint_trivialOrientationDatum_iff {eps kappa : Real}
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t : Real} :
    IsOrientedGoodPoint (I := I) (trivialOrientationDatum I) eps kappa S x t ↔
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t :=
  ⟨fun h => ⟨h.choose⟩, fun h => h.elim fun W => ⟨W, trivial⟩⟩

end Good



section Hypotheses

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]

structure ModelFlowHypotheses (kappa sigma : Real) (Phi : Real → Real)
    (T : Real) (hT : (0 : Real) < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) : Prop where
  isSolution : IsSolutionOn (I := I) S
  one_le_T : 1 ≤ T
  complete : ∀ t ∈ Set.Ico (0 : Real) T,
    DifferentialGeometry.RiemannianMetricComplete (I := I) (S.base.metric t)
  scalarBddAbove : ∀ T' : Real, T' < T →
    ∃ K : Real, ∀ (y : M) (s : Real), s ∈ Set.Icc (0 : Real) T' → S.scalar s y ≤ K
  pinching : PhiAlmostNonnegative (I := I) S (Set.Ico (0 : Real) T) Phi
  noncollapsed : SpatiallyKappaNoncollapsedBelowScale (I := I) S kappa sigma

end Hypotheses



section Statements

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def ModelRadiusWorks (I : ModelWithCorners Real E H)
    (eps kappa sigma : Real) (Phi : Real → Real) (r0 : Real) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
    (T : Real) (hT : (0 : Real) < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
    ModelFlowHypotheses (I := I) kappa sigma Phi T hT S →
    ∀ (x0 : M) (t0 : Real), 1 ≤ t0 → t0 < T → (r0 ^ 2)⁻¹ ≤ S.scalar t0 x0 →
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x0 t0

def SelectedSequenceEventuallyGood (I : ModelWithCorners Real E H)
    (eps kappa sigma : Real) (Phi : Real → Real) (orient : OrientationDatum I) : Prop :=
  ∀ (Mi : ℕ → Type u) [∀ i, TopologicalSpace (Mi i)] [∀ i, ChartedSpace H (Mi i)]
    [∀ i, IsManifold I ∞ (Mi i)] [∀ i, IsManifold I 1 (Mi i)]
    [∀ i, T2Space (Mi i)] [∀ i, SigmaCompactSpace (Mi i)]
    (T : ℕ → Real) (hT : ∀ i, (0 : Real) < T i)
    (S : ∀ i, SolutionOn (I := I) (M := Mi i)
      (RealTimeInterval.closedOpen 0 (T i) (hT i))),
    0 < eps → eps < 1 → 0 < kappa → 0 < sigma →
    Module.finrank Real E = 3 → AdmissiblePinchingFunction Phi →
    (∀ i, ModelFlowHypotheses (I := I) kappa sigma Phi (T i) (hT i) (S i)) →
    ∀ (Tsel : ℕ → Real), (∀ i, Tsel i < T i) →
    ∀ (depth : ℕ → Real) (xhat : ∀ i, Mi i) (that : ℕ → Real) (x : ∀ i, Mi i) (t : ℕ → Real),
    (∀ᶠ i in Filter.atTop, BadPointSelected (I := I) eps kappa (S i) (Tsel i) (depth i)
      (xhat i) (that i) (x i) (t i)) →
    Filter.Tendsto depth Filter.atTop Filter.atTop →
    Filter.Tendsto (fun i => (S i).scalar (t i) (x i)) Filter.atTop Filter.atTop →
    ∀ᶠ i in Filter.atTop, IsOrientedGoodPoint (I := I) orient eps kappa (S i) (x i) (t i)

structure ModelTheoremCounterexample (I : ModelWithCorners Real E H)
    (eps kappa sigma : Real) (Phi : Real → Real) (r0 : Real) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [smooth1 : IsManifold I 1 M]
  [t2 : T2Space M]
  [sigmaCompact : SigmaCompactSpace M]
  T : Real
  hT : (0 : Real) < T
  S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)
  hyp : ModelFlowHypotheses (I := I) kappa sigma Phi T hT S
  x0 : M
  t0 : Real
  one_le_t0 : 1 ≤ t0
  t0_lt_T : t0 < T
  scalar_ge : (r0 ^ 2)⁻¹ ≤ S.scalar t0 x0
  bad : IsBadPoint.{u, uE, uH} (I := I) eps kappa S x0 t0

theorem nonempty_modelTheoremCounterexample_of_not_modelRadiusWorks
    {eps kappa sigma : Real} {Phi : Real → Real} {r0 : Real}
    (h : ¬ ModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi r0) :
    Nonempty (ModelTheoremCounterexample.{u, uE, uH} I eps kappa sigma Phi r0) := by
  by_contra hc
  refine h ?_
  intro M itop ichart ism ism1 it2 isc T hT S hyp x0 t0 h1 h2 h3
  by_contra hbad
  exact hc ⟨{ M := M, topology := itop, charted := ichart, smooth := ism, smooth1 := ism1
              t2 := it2, sigmaCompact := isc, T := T, hT := hT, S := S, hyp := hyp
              x0 := x0, t0 := t0, one_le_t0 := h1, t0_lt_T := h2, scalar_ge := h3
              bad := hbad }⟩

end Statements



section Admissibility

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem icc_subset_carrier_closedOpen {a b : Real} (hb : (0 : Real) < b) (hab : a < b) :
    Set.Icc (0 : Real) a ⊆ (RealTimeInterval.closedOpen 0 b hb).carrier :=
  fun _ hs => ⟨hs.1, lt_of_le_of_lt hs.2 hab⟩

theorem eventually_selected_window_subset_carrier
    {Mi : ℕ → Type u} [∀ i, TopologicalSpace (Mi i)] [∀ i, ChartedSpace H (Mi i)]
    [∀ i, IsManifold I ∞ (Mi i)] [∀ i, IsManifold I 1 (Mi i)]
    {T : ℕ → Real} {hT : ∀ i, (0 : Real) < T i}
    {S : ∀ i, SolutionOn (I := I) (M := Mi i) (RealTimeInterval.closedOpen 0 (T i) (hT i))}
    {eps kappa : Real} (heps : 0 < eps)
    {Tsel depth that t : ℕ → Real} {xhat x : ∀ i, Mi i}
    (hTsel : ∀ i, Tsel i < T i)
    (hsel : ∀ᶠ i in Filter.atTop, BadPointSelected (I := I) eps kappa (S i) (Tsel i)
      (depth i) (xhat i) (that i) (x i) (t i))
    (hQ : Filter.Tendsto (fun i => (S i).scalar (t i) (x i)) Filter.atTop Filter.atTop) :
    ∀ᶠ i in Filter.atTop, ∀ (y : Mi i) (s : Real),
      s ∈ Set.Icc (t i - depth i / (S i).scalar (t i) (x i)) (t i) →
      2 * (S i).scalar (t i) (x i) ≤ (S i).scalar s y →
        Set.Icc (s - (eps * (S i).scalar s y)⁻¹) s ⊆
          (RealTimeInterval.closedOpen 0 (T i) (hT i)).carrier := by
  filter_upwards [hsel, hQ.eventually_ge_atTop (2 / eps)] with i hi hQi
  intro y s hs hR
  have hwin : t i - depth i / (S i).scalar (t i) (x i) ≤ t i :=
    le_trans hs.1 hs.2
  have htT : t i ≤ Tsel i := (hi.window_subset (Set.right_mem_Icc.2 hwin)).2
  exact window_subset_carrier_of_two_mul_scalar_le (I := I) (S := S i) (T := Tsel i)
    (depth := depth i) (Q := (S i).scalar (t i) (x i)) (t := t i) heps hQi hi.depth_ratio
    hi.time_ge htT (icc_subset_carrier_closedOpen (hT i) (hTsel i)) hs hR

end Admissibility



section Endpoint

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem exists_modelRadius_of_selectedSequenceEventuallyGood
    {eps kappa sigma : Real} {Phi : Real → Real}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hdim : Module.finrank Real E = 3) (hPhi : AdmissiblePinchingFunction Phi)
    (orient : OrientationDatum.{u, uE, uH} I)
    (hblock : SelectedSequenceEventuallyGood.{u, uE, uH} I eps kappa sigma Phi orient) :
    ∃ r0 : Real, 0 < r0 ∧ r0 ≤ Real.sqrt eps ∧
      ModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi r0 := by
  by_contra hcontra
  have hcon : ∀ r0 : Real, 0 < r0 → r0 ≤ Real.sqrt eps →
      ¬ ModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi r0 := by
    intro r0 h1 h2 h3
    exact hcontra ⟨r0, h1, h2, h3⟩
  have hsq : (0 : Real) < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hrpos : ∀ n : ℕ, (0 : Real) < min (Real.sqrt eps) (1 / ((n : Real) + 1)) := by
    intro n
    have hn : (0 : Real) < 1 / ((n : Real) + 1) := by positivity
    exact lt_min hsq hn
  have hnat : Filter.Tendsto (fun i : ℕ => (i : Real)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨⌈b⌉₊, fun n hn => ?_⟩
    refine le_trans (Nat.le_ceil b) ?_
    exact_mod_cast hn
  have hCE : ∀ n : ℕ, ModelTheoremCounterexample.{u, uE, uH} I eps kappa sigma Phi
      (min (Real.sqrt eps) (1 / ((n : Real) + 1))) := fun n =>
    (nonempty_modelTheoremCounterexample_of_not_modelRadiusWorks
      (hcon _ (hrpos n) (min_le_left _ _))).some
  let itop : ∀ n : ℕ, TopologicalSpace (hCE n).M := fun n => (hCE n).topology
  let ichart : ∀ n : ℕ, ChartedSpace H (hCE n).M := fun n => (hCE n).charted
  let ism : ∀ n : ℕ, IsManifold I ∞ (hCE n).M := fun n => (hCE n).smooth
  let ism1 : ∀ n : ℕ, IsManifold I 1 (hCE n).M := fun n => (hCE n).smooth1
  let it2 : ∀ n : ℕ, T2Space (hCE n).M := fun n => (hCE n).t2
  let isc : ∀ n : ℕ, SigmaCompactSpace (hCE n).M := fun n => (hCE n).sigmaCompact
  obtain ⟨K, hK⟩ : ∃ K : ℕ → Real, ∀ (i : ℕ) (y : (hCE i).M) (s : Real),
      s ∈ Set.Icc (0 : Real) ((hCE i).t0) → (hCE i).S.scalar s y ≤ K i := by
    choose K hK using fun i : ℕ => (hCE i).hyp.scalarBddAbove ((hCE i).t0) (hCE i).t0_lt_T
    exact ⟨K, hK⟩
  have hQhat : Filter.Tendsto
      (fun i : ℕ => (hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun i => ?_) hnat
    refine le_trans ?_ (hCE i).scalar_ge
    have hden : (0 : Real) < (i : Real) + 1 := by positivity
    have hr : (0 : Real) < min (Real.sqrt eps) (1 / ((i : Real) + 1)) := hrpos i
    have hrle : min (Real.sqrt eps) (1 / ((i : Real) + 1)) ≤ 1 / ((i : Real) + 1) :=
      min_le_right _ _
    have hi0 : (0 : Real) ≤ (i : Real) := Nat.cast_nonneg i
    have hmul : min (Real.sqrt eps) (1 / ((i : Real) + 1)) * ((i : Real) + 1) ≤ 1 := by
      rw [← le_div_iff₀ hden]
      exact hrle
    have hr1 : min (Real.sqrt eps) (1 / ((i : Real) + 1)) ≤ 1 := by
      refine le_trans hrle ?_
      rw [div_le_one hden]
      linarith
    have hsq2 : (0 : Real) < min (Real.sqrt eps) (1 / ((i : Real) + 1)) ^ 2 := pow_pos hr 2
    rw [inv_eq_one_div, le_div_iff₀ hsq2]
    nlinarith [hmul, hr.le, hr1, hi0]
  obtain ⟨hdepthTend, hev⟩ :=
    eventually_exists_badPointSelected (I := I) (Mi := fun i => (hCE i).M)
      (Di := fun i => RealTimeInterval.closedOpen 0 ((hCE i).T) ((hCE i).hT))
      (S := fun i => (hCE i).S) (eps := eps) (kappa := kappa)
      (T := fun i => (hCE i).t0) (K := K) hK (xhat := fun i => (hCE i).x0)
      (that := fun i => (hCE i).t0) (fun i => (hCE i).one_le_t0) (fun _ => le_rfl)
      (fun i => (hCE i).bad) hQhat
  have hchoice : ∀ i : ℕ, ∃ (y : (hCE i).M) (s : Real),
      (∃ (y' : (hCE i).M) (s' : Real), BadPointSelected (I := I) eps kappa ((hCE i).S)
          ((hCE i).t0) (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
          ((hCE i).x0) ((hCE i).t0) y' s') →
        BadPointSelected (I := I) eps kappa ((hCE i).S) ((hCE i).t0)
          (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
          ((hCE i).x0) ((hCE i).t0) y s := by
    intro i
    by_cases h : ∃ (y' : (hCE i).M) (s' : Real), BadPointSelected (I := I) eps kappa
        ((hCE i).S) ((hCE i).t0)
        (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
        ((hCE i).x0) ((hCE i).t0) y' s'
    · obtain ⟨y, s, hy⟩ := h
      exact ⟨y, s, fun _ => hy⟩
    · exact ⟨(hCE i).x0, 0, fun h' => absurd h' h⟩
  choose xsel tsel hxsel using hchoice
  have hsel : ∀ᶠ i in Filter.atTop, BadPointSelected (I := I) eps kappa ((hCE i).S)
      ((hCE i).t0) (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
      ((hCE i).x0) ((hCE i).t0) (xsel i) (tsel i) := by
    filter_upwards [hev] with i hi
    exact hxsel i hi
  have hQsel : Filter.Tendsto (fun i : ℕ => (hCE i).S.scalar (tsel i) (xsel i))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hQhat
    filter_upwards [hsel] with i hi
    exact hi.scalar_ge
  have hgood := hblock (fun i => (hCE i).M) (fun i => (hCE i).T) (fun i => (hCE i).hT)
    (fun i => (hCE i).S) heps heps1 hkappa hsigma hdim hPhi (fun i => (hCE i).hyp)
    (fun i => (hCE i).t0) (fun i => (hCE i).t0_lt_T)
    (fun i => selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
    (fun i => (hCE i).x0) (fun i => (hCE i).t0) xsel tsel hsel hdepthTend hQsel
  obtain ⟨i, hgi, hsi⟩ := (hgood.and hsel).exists
  exact hsi.bad (isGoodPoint_of_isOrientedGoodPoint hgi)

end Endpoint

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
