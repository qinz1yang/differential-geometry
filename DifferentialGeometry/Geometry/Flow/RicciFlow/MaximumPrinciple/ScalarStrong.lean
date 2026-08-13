import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle Set Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private theorem exists_positive_scalar_time
    {T : Real} (hT : 0 < T) (u : Real → M → Real)
    (hu : ContinuousOn (fun p : Real × M ↦ u p.1 p.2)
      (spacetimeSlab (M := M) T))
    {x : M} (hx : 0 < u 0 x) :
    ∃ t ∈ Set.Ioo (0 : Real) T, 0 < u t x := by
  let η : Real := u 0 x / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hcurve : ContinuousOn (fun t : Real ↦ u t x) (Set.Icc 0 T) := by
    have hmap : Set.MapsTo (fun t : Real ↦ (t, x)) (Set.Icc 0 T)
        (spacetimeSlab (M := M) T) := by
      intro t ht
      exact ⟨ht, Set.mem_univ x⟩
    simpa using hu.comp (by fun_prop) hmap
  have htarget : Set.Ioi η ∈ nhds (u 0 x) :=
    Ioi_mem_nhds (by dsimp [η]; linarith)
  have hpre : (fun t : Real ↦ u t x) ⁻¹' Set.Ioi η ∈
      nhdsWithin 0 (Set.Icc 0 T) :=
    (hcurve 0 ⟨le_rfl, hT.le⟩).preimage_mem_nhdsWithin htarget
  rcases Metric.mem_nhdsWithin_iff.mp hpre with ⟨ε, hε, hball⟩
  let t : Real := min (T / 2) (ε / 2)
  have ht : 0 < t := lt_min (half_pos hT) (half_pos hε)
  have htT : t < T := (min_le_left _ _).trans_lt (half_lt_self hT)
  have htball : t ∈ Metric.ball (0 : Real) ε := by
    change dist t 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hε)
  have hpos := hball ⟨htball, ⟨ht.le, htT.le⟩⟩
  exact ⟨t, ⟨ht, htT⟩, hη.trans hpos⟩

theorem scalar_curvature_positive_of_nonnegative_initial
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real} (hT : 0 < T)
    (hcarrier : Set.Icc 0 T ⊆ D.carrier)
    (hregular : Set.Ioc 0 T ⊆ D.regular)
    (hinit : ∀ x : M, 0 ≤ S.scalar 0 x)
    {x₀ : M} (hx₀ : 0 < S.scalar 0 x₀)
    (y : M) :
    0 < S.scalar T y := by
  let G : MetricConnectionFamily (I := I) (M := M) Real :=
    flowG (I := I) S
  let X : Real → (x : M) → TangentSpace I x :=
    fun _ x ↦ (0 : TangentSpace I x)
  have hsolution : IsSolutionOn (I := I) S := hS.toIsSolutionOn
  have hmetricSmooth : MetricFamilySmoothOn (I := I) (M := M) D G.metric := by
    exact hsolution.smoothMetric
  have hscalarContinuous : ContinuousOn
      (fun p : Real × M ↦ S.scalar p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact hS.scalarReg.scalar_continuousOn.mono
      (Set.prod_mono hcarrier Set.Subset.rfl)
  have hscalarTime : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real ↦ S.scalar s x)
        (Set.Icc 0 T) t := by
    intro t ht x
    exact hS.scalarReg.scalar_time_within ht hcarrier x
  have hscalarSpace : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (S.scalar t) x := by
    intro t ht x
    exact hS.scalarReg.scalar_space t (hcarrier ht) x
  have hscalarGrad : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      MDiffAt (T% fun y : M ↦
        gradientFun (I := I) (G.metric t) (S.scalar t) y) x := by
    intro t ht x
    exact hS.scalarReg.scalar_grad t (hcarrier ht) x
  have hscalarHeatSuper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s : Real ↦ S.scalar s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (S.scalar t) x := by
    intro t ht htpos x
    let τ : D.RegularTime := ⟨t, hregular ⟨htpos, ht.2⟩⟩
    have hevolution := hS.scalarEvolution G
      (fun _ ↦ rfl) (fun _ ↦ rfl) τ x
    have hderiv : derivWithin (fun s : Real ↦ S.scalar s x)
        (Set.Icc 0 T) t =
        laplacianAt (I := I) G t (S.scalar t) x +
          2 * normSq0S (I := I) (S.family.metric t) x 2
            (S.ricci t x) := by
      exact hevolution.hasDerivAt
        (D.regular_mem_nhds τ.2) |>.hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
    rw [hderiv]
    have hnorm : 0 ≤ normSq0S (I := I) (S.family.metric t) x 2
        (S.ricci t x) := normSq0S_nonneg (I := I) _ x 2 _
    linarith
  have hscalarSuper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X S.scalar t x := by
    intro t ht htpos x
    simpa [parabolicOperatorWithDrift, X, heatOperatorWithDrift,
      heatOperator, driftTerm] using hscalarHeatSuper t ht htpos x
  have hnonnegative : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 ≤ S.scalar t x := by
    exact strict_barrier_nonnegative_of_positive_time
      (I := I) G T X S.scalar hscalarContinuous hinit
      (fun t ht htpos x => hscalarTime t ht x)
      (fun t ht htpos x => hscalarSpace t ht x)
      (fun t ht htpos x => hscalarGrad t ht x)
      (fun t ht htpos x _ ↦ hscalarSuper t ht htpos x)
  obtain ⟨a, ha, hscalarA⟩ :=
    exists_positive_scalar_time (M := M) hT S.scalar hscalarContinuous hx₀
  let T' : Real := T - a
  have hT' : 0 < T' := sub_pos.mpr ha.2
  let G' : MetricConnectionFamily (I := I) (M := M) Real :=
    { metric := fun s ↦ G.metric (s + a)
      connection := fun s ↦ G.connection (s + a)
      metricCompatible := fun s ↦ G.metricCompatible (s + a) }
  let u' : Real → M → Real := fun s x ↦ S.scalar (s + a) x
  have hshift : ∀ s ∈ Set.Icc 0 T', s + a ∈ Set.Icc a T := by
    intro s hs
    constructor
    · linarith [hs.1]
    · dsimp [T'] at hs
      linarith [hs.2]
  have hwindow : Set.Icc a T ⊆ D.regular := by
    intro s hs
    exact hregular ⟨lt_of_lt_of_le ha.1 hs.1, hs.2⟩
  have hmapContinuous : Continuous (fun p : Real × M ↦ (p.1 + a, p.2)) := by
    fun_prop
  have hmap : Set.MapsTo (fun p : Real × M ↦ (p.1 + a, p.2))
      (spacetimeSlab (M := M) T') (Set.Icc a T ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hshift p.1 hp.1, Set.mem_univ p.2⟩
  have hgradOriginal : ∀ (ρ : M → Real),
      ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) ρ p.2)
          (gradientFun (I := I) (G.metric p.1) ρ p.2))
        (Set.Icc a T ×ˢ Set.univ) := by
    intro ρ hρ
    exact G.gradient_norm_sq_continuousOn hmetricSmooth hwindow hρ
  have hlaplacianOriginal : ∀ (ρ : M → Real),
      ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 ρ p.2)
        (Set.Icc a T ×ˢ Set.univ) := by
    intro ρ hρ
    exact G.laplacianAt_continuousOn hmetricSmooth hwindow
      (uniqueDiffOn_Icc (sub_pos.mp hT'))
      (fun _ _ ↦ rfl) hρ
  have hgradContinuous : ∀ (ρ : M → Real),
      ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ →
      ContinuousOn (fun p : Real × M ↦
        (G'.metric p.1).inner p.2
          (gradientFun (I := I) (G'.metric p.1) ρ p.2)
          (gradientFun (I := I) (G'.metric p.1) ρ p.2))
        (spacetimeSlab (M := M) T') := by
    intro ρ hρ
    simpa [G'] using
      (hgradOriginal ρ hρ).comp hmapContinuous.continuousOn hmap
  have hlaplacianContinuous : ∀ (ρ : M → Real),
      ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G' p.1 ρ p.2)
        (spacetimeSlab (M := M) T') := by
    intro ρ hρ
    simpa [G'] using
      (hlaplacianOriginal ρ hρ).comp hmapContinuous.continuousOn hmap
  have huContinuous : ContinuousOn (fun p : Real × M ↦ u' p.1 p.2)
      (spacetimeSlab (M := M) T') := by
    simpa [u'] using
      (hS.scalarReg.scalar_continuousOn.mono
        (Set.prod_mono (hwindow.trans D.regular_subset) Set.Subset.rfl)).comp
          hmapContinuous.continuousOn hmap
  have huNonnegative : ∀ s ∈ Set.Icc 0 T', ∀ x : M, 0 ≤ u' s x := by
    intro s hs x
    exact hnonnegative (s + a)
      ⟨(ha.1.le.trans (hshift s hs).1), (hshift s hs).2⟩ x
  have huTime : ∀ s ∈ Set.Icc 0 T', 0 < s → ∀ x : M,
      DifferentiableWithinAt Real (fun r : Real ↦ u' r x)
        (Set.Icc 0 T') s := by
    intro s hs hspos x
    let τ : D.RegularTime := ⟨s + a, hwindow (hshift s hs)⟩
    have hevolution := hS.scalarEvolution G
      (fun _ ↦ rfl) (fun _ ↦ rfl) τ x
    have htime : HasDerivAt (fun r : Real ↦ S.scalar r x)
        (laplacianAt (I := I) G (s + a) (S.scalar (s + a)) x +
          2 * normSq0S (I := I) (S.family.metric (s + a)) x 2
            (S.ricci (s + a) x)) (s + a) :=
      hevolution.hasDerivAt (D.regular_mem_nhds τ.2)
    exact (htime.comp s ((hasDerivAt_id s).add_const a)).differentiableAt.differentiableWithinAt
  have huSpace : ∀ s ∈ Set.Icc 0 T', 0 < s → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u' s) x := by
    intro s hs hspos x
    exact hS.scalarReg.scalar_space (s + a)
      (D.regular_subset (hwindow (hshift s hs))) x
  have huGrad : ∀ s ∈ Set.Icc 0 T', 0 < s → ∀ x : M,
      MDiffAt (T% fun y : M ↦
        gradientFun (I := I) (G'.metric s) (u' s) y) x := by
    intro s hs hspos x
    exact hS.scalarReg.scalar_grad (s + a)
      (D.regular_subset (hwindow (hshift s hs))) x
  have huSuper : ∀ s ∈ Set.Icc 0 T', 0 < s → ∀ x : M,
      0 ≤ derivWithin (fun r : Real ↦ u' r x) (Set.Icc 0 T') s -
        laplacianAt (I := I) G' s (u' s) x := by
    intro s hs hspos x
    let τ : D.RegularTime := ⟨s + a, hwindow (hshift s hs)⟩
    have hevolution := hS.scalarEvolution G
      (fun _ ↦ rfl) (fun _ ↦ rfl) τ x
    have htime : HasDerivAt (fun r : Real ↦ S.scalar r x)
        (laplacianAt (I := I) G (s + a) (S.scalar (s + a)) x +
          2 * normSq0S (I := I) (S.family.metric (s + a)) x 2
            (S.ricci (s + a) x)) (s + a) :=
      hevolution.hasDerivAt (D.regular_mem_nhds τ.2)
    have hderiv : derivWithin (fun r : Real ↦ u' r x)
        (Set.Icc 0 T') s =
        laplacianAt (I := I) G (s + a) (S.scalar (s + a)) x +
          2 * normSq0S (I := I) (S.family.metric (s + a)) x 2
            (S.ricci (s + a) x) := by
      simpa [u', Function.comp_def] using
        (htime.comp s ((hasDerivAt_id s).add_const a)).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc hT').uniqueDiffWithinAt hs)
    rw [hderiv]
    change 0 ≤
      laplacianAt (I := I) G (s + a) (S.scalar (s + a)) x +
          2 * normSq0S (I := I) (S.family.metric (s + a)) x 2
            (S.ricci (s + a) x) -
        laplacianAt (I := I) G (s + a) (S.scalar (s + a)) x
    have hnorm : 0 ≤ normSq0S (I := I) (S.family.metric (s + a)) x 2
        (S.ricci (s + a) x) := normSq0S_nonneg (I := I) _ x 2 _
    linarith
  have hpositive :=
    scalar_strong_maximum_principle_time_dependent_metric_positive
      (I := I) G' hT' hgradContinuous hlaplacianContinuous u'
      huContinuous huNonnegative huTime huSpace huGrad huSuper
      (t := 0) ⟨le_rfl, hT'.le⟩ (by simpa [u'] using hscalarA) y
  simpa [u', T'] using hpositive

end

end DifferentialGeometry.PDE.RicciFlow
