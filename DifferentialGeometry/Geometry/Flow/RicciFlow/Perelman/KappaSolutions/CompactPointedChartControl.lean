import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenChartTimeJets
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem pointed_chart_edist_ne_top [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p x : M) :
    riemannianEDistOf (I := I) g p x ≠ ⊤ := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  exact riemannianEDist_ne_top (I := I) p x

omit [CompleteSpace E] in
theorem exists_precompact_bounded_comparison_open
    [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (p : M) {K : Set M} (hK : IsCompact K) :
    ∃ V : TopologicalSpace.Opens M, K ⊆ V ∧ IsCompact (closure (V : Set M)) ∧
      ∃ A : ℝ, 0 < A ∧ (V : Set M) ⊆ riemannianClosedBallOf (I := I) g p A := by
  classical
  have hd : Continuous (fun x : M => riemannianEDistOf (I := I) g p x) :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist (I := I) g p
  let U (n : ℕ) : Set M := {x | riemannianEDistOf (I := I) g p x < (n : ℝ≥0∞)}
  have hU (n : ℕ) : IsOpen (U n) := isOpen_lt hd continuous_const
  have hcover : K ⊆ ⋃ n, U n := by
    intro x _hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (pointed_chart_edist_ne_top g p x)
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  let A : ℝ := ((s.sup id : ℕ) : ℝ) + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  let V : TopologicalSpace.Opens M :=
    ⟨{x | riemannianEDistOf (I := I) g p x < ENNReal.ofReal A}, isOpen_lt hd continuous_const⟩
  have hVB : (V : Set M) ⊆ riemannianClosedBallOf (I := I) g p A := by
    intro x hx
    change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal A
    exact (hx : riemannianEDistOf (I := I) g p x < ENNReal.ofReal A).le
  refine ⟨V, ?_, (hg.closedEBall_isCompact p A).of_isClosed_subset isClosed_closure
    (closure_minimal hVB (isClosed_le hd continuous_const)), A, hA, hVB⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (hs hx)
  change riemannianEDistOf (I := I) g p x < (n : ℝ≥0∞) at hxn
  change riemannianEDistOf (I := I) g p x < ENNReal.ofReal A
  apply hxn.trans_le
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hn' : (n : ℝ) ≤ ((s.sup id : ℕ) : ℝ) := by
    exact_mod_cast (Finset.le_sup (f := id) hn : n ≤ s.sup id)
  dsimp only [A]
  linarith

omit [CompleteSpace E] [IsManifold I ∞ M] in
theorem uniform_on_compact_of_restricted_chart_bounds
    (V : TopologicalSpace.Opens M) {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V)
    (F : ℕ → ℝ → M → ℝ) (J : Set ℝ)
    (hloc : ∀ p : V, ∀ Q : Set E, IsCompact Q → Q ⊆ (extChartAt I p).target →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ Q,
        F n t ((extChartAt I (p : M)).symm y) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ x ∈ K, F n t x ≤ ε := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk τ hτ x hx hbad using hbad
  obtain ⟨x₀, hx₀, σ, hσ, hlim⟩ := hK.tendsto_subseq hx
  let p : V := ⟨x₀, hKV hx₀⟩
  let y : ℕ → V := fun n => ⟨x (σ n), hKV (hx (σ n))⟩
  have hyt : Tendsto y atTop (𝓝 p) := by
    apply tendsto_subtype_rng.mpr
    exact hlim
  have hcoord : Tendsto (fun n => extChartAt I p (y n)) atTop (𝓝 (extChartAt I p p)) :=
    (continuousAt_extChartAt (I := I) p).tendsto.comp hyt
  obtain ⟨Q, hQ, hpQ, hQt⟩ := exists_compact_between isCompact_singleton
    (isOpen_extChartAt_target (I := I) p) (singleton_subset_iff.mpr (mem_extChartAt_target p))
  obtain ⟨N, hN⟩ := hloc p Q hQ hQt ε hε
  have hindex : Tendsto (fun n => k (σ n)) atTop atTop :=
    (tendsto_atTop_mono hk tendsto_id).comp hσ.tendsto_atTop
  have hyQ := hcoord.eventually (isOpen_interior.mem_nhds (hpQ (mem_singleton _)))
  have hys := hyt.eventually ((isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p))
  obtain ⟨n, hn, hyQn, hysn⟩ := ((hindex.eventually_ge_atTop N).and (hyQ.and hys)).exists
  have hval : (extChartAt I (p : M)).symm (extChartAt I p (y n)) = x (σ n) := by
    rw [← extChartAt_opens_symm_coe V p ((extChartAt I p).map_source hysn)]
    exact congrArg Subtype.val ((extChartAt I p).left_inv hysn)
  have hsmall := hN (k (σ n)) hn (τ (σ n)) (hτ (σ n))
    (extChartAt I p (y n)) (interior_subset hyQn)
  rw [hval] at hsmall
  exact (not_lt_of_ge hsmall) (hbad (σ n))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
