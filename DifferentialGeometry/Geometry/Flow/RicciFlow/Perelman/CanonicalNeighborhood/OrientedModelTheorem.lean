import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OrientedBadPointSelection

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def OrientedModelRadiusWorks (I : ModelWithCorners Real E H)
    (eps kappa sigma : Real) (Phi : Real → Real) (orient : OrientationDatum I) (r0 : Real) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
    (T : Real) (hT : (0 : Real) < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
    ModelFlowHypotheses (I := I) kappa sigma Phi T hT S →
    ∀ (x0 : M) (t0 : Real), 1 ≤ t0 → t0 < T → (r0 ^ 2)⁻¹ ≤ S.scalar t0 x0 →
      IsOrientedGoodPoint.{u, uE, uH} (I := I) orient eps kappa S x0 t0


theorem modelRadiusWorks_of_oriented
    {eps kappa sigma : Real} {Phi : Real → Real} {orient : OrientationDatum I} {r0 : Real}
    (h : OrientedModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi orient r0) :
    ModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi r0 := by
  intro M itop ichart ism ism1 it2 isc T hT S hyp x0 t0 h1 h2 h3
  exact isGoodPoint_of_isOrientedGoodPoint (h M T hT S hyp x0 t0 h1 h2 h3)


theorem orientedModelRadiusWorks_trivial_iff
    {eps kappa sigma : Real} {Phi : Real → Real} {r0 : Real} :
    OrientedModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi
        (trivialOrientationDatum I) r0 ↔
      ModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi r0 := by
  simp only [OrientedModelRadiusWorks, ModelRadiusWorks,
    isOrientedGoodPoint_trivialOrientationDatum_iff]

def OrientedSelectedSequenceEventuallyGood (I : ModelWithCorners Real E H)
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
    (∀ᶠ i in Filter.atTop, OrientedBadPointSelected (I := I) orient eps kappa (S i) (Tsel i) (depth i)
      (xhat i) (that i) (x i) (t i)) →
    Filter.Tendsto depth Filter.atTop Filter.atTop →
    Filter.Tendsto (fun i => (S i).scalar (t i) (x i)) Filter.atTop Filter.atTop →
    ∀ᶠ i in Filter.atTop, IsOrientedGoodPoint (I := I) orient eps kappa (S i) (x i) (t i)


theorem orientedSelectedSequenceEventuallyGood_trivial_iff
    {eps kappa sigma : Real} {Phi : Real → Real} :
    OrientedSelectedSequenceEventuallyGood.{u, uE, uH} I eps kappa sigma Phi
        (trivialOrientationDatum I) ↔
      SelectedSequenceEventuallyGood.{u, uE, uH} I eps kappa sigma Phi
        (trivialOrientationDatum I) := by
  simp only [OrientedSelectedSequenceEventuallyGood, SelectedSequenceEventuallyGood,
    orientedBadPointSelected_trivial_iff]

private structure OrientedModelTheoremCounterexample (I : ModelWithCorners Real E H)
    (eps kappa sigma : Real) (Phi : Real → Real) (orient : OrientationDatum I) (r0 : Real) where
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
  bad : ¬ IsOrientedGoodPoint.{u, uE, uH} (I := I) orient eps kappa S x0 t0

private theorem nonempty_orientedModelTheoremCounterexample_of_not_orientedModelRadiusWorks
    {eps kappa sigma : Real} {Phi : Real → Real} {orient : OrientationDatum I} {r0 : Real}
    (h : ¬ OrientedModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi orient r0) :
    Nonempty (OrientedModelTheoremCounterexample.{u, uE, uH} I eps kappa sigma Phi orient r0) := by
  by_contra hc
  refine h ?_
  intro M itop ichart ism ism1 it2 isc T hT S hyp x0 t0 h1 h2 h3
  by_contra hbad
  exact hc ⟨{ M := M, topology := itop, charted := ichart, smooth := ism, smooth1 := ism1
              t2 := it2, sigmaCompact := isc, T := T, hT := hT, S := S, hyp := hyp
              x0 := x0, t0 := t0, one_le_t0 := h1, t0_lt_T := h2, scalar_ge := h3
              bad := hbad }⟩

theorem exists_orientedModelRadius_of_selectedSequenceEventuallyGood
    {eps kappa sigma : Real} {Phi : Real → Real}
    (heps : 0 < eps) (heps1 : eps < 1) (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hdim : Module.finrank Real E = 3) (hPhi : AdmissiblePinchingFunction Phi)
    (orient : OrientationDatum.{u, uE, uH} I)
    (hblock : OrientedSelectedSequenceEventuallyGood.{u, uE, uH} I eps kappa sigma Phi orient) :
    ∃ r0 : Real, 0 < r0 ∧ r0 ≤ Real.sqrt eps ∧
      OrientedModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi orient r0 := by
  by_contra hcontra
  have hcon : ∀ r0 : Real, 0 < r0 → r0 ≤ Real.sqrt eps →
      ¬ OrientedModelRadiusWorks.{u, uE, uH} I eps kappa sigma Phi orient r0 := by
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
  have hCE : ∀ n : ℕ, OrientedModelTheoremCounterexample.{u, uE, uH} I eps kappa sigma Phi orient
      (min (Real.sqrt eps) (1 / ((n : Real) + 1))) := fun n =>
    (nonempty_orientedModelTheoremCounterexample_of_not_orientedModelRadiusWorks
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
    eventually_exists_orientedBadPointSelected (I := I) (Mi := fun i => (hCE i).M)
      (Di := fun i => RealTimeInterval.closedOpen 0 ((hCE i).T) ((hCE i).hT))
      (S := fun i => (hCE i).S) (eps := eps) (kappa := kappa)
      (T := fun i => (hCE i).t0) (K := K) hK (xhat := fun i => (hCE i).x0)
      (that := fun i => (hCE i).t0) (fun i => (hCE i).one_le_t0) (fun _ => le_rfl)
      (fun i => (hCE i).bad) hQhat
  have hchoice : ∀ i : ℕ, ∃ (y : (hCE i).M) (s : Real),
      (∃ (y' : (hCE i).M) (s' : Real), OrientedBadPointSelected (I := I) orient eps kappa ((hCE i).S)
          ((hCE i).t0) (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
          ((hCE i).x0) ((hCE i).t0) y' s') →
        OrientedBadPointSelected (I := I) orient eps kappa ((hCE i).S) ((hCE i).t0)
          (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
          ((hCE i).x0) ((hCE i).t0) y s := by
    intro i
    by_cases h : ∃ (y' : (hCE i).M) (s' : Real), OrientedBadPointSelected (I := I) orient eps kappa
        ((hCE i).S) ((hCE i).t0)
        (selectionDepth ((hCE i).S.scalar ((hCE i).t0) ((hCE i).x0)))
        ((hCE i).x0) ((hCE i).t0) y' s'
    · obtain ⟨y, s, hy⟩ := h
      exact ⟨y, s, fun _ => hy⟩
    · exact ⟨(hCE i).x0, 0, fun h' => absurd h' h⟩
  choose xsel tsel hxsel using hchoice
  have hsel : ∀ᶠ i in Filter.atTop, OrientedBadPointSelected (I := I) orient eps kappa ((hCE i).S)
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
  exact hsi.bad hgi

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
