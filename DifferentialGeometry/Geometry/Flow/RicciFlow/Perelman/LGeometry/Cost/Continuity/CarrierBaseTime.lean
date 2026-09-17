import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.TimeParameter

set_option autoImplicit false
noncomputable section


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold _root_.Topology Interval
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedLagrangian_continuousOn_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ lRegularizedLagrangian S q.1 alpha q.2)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := by
  let U : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier}
  let P := {q : ℝ × ℝ // q ∈ U}
  let timeLift : P → {t : ℝ // t ∈ D.carrier} := fun q ↦ ⟨q.1.1 - q.1.2 ^ 2, q.2⟩
  let velocityLift : P → TangentBundle I M := fun q ↦
    ⟨alpha q.1.2, lVelocity (I := I) alpha q.1.2⟩
  have htime : Continuous timeLift := by
    exact (((continuous_fst.comp continuous_subtype_val).sub
      ((continuous_snd.comp continuous_subtype_val).pow 2)).subtype_mk _)
  have hvel : Continuous velocityLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) halpha).comp
        (continuous_snd.comp continuous_subtype_val)
  have hbase : Continuous (fun q : P ↦ alpha q.1.2) :=
    halpha.continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hS.smoothMetric
      (K := D.carrier) (fun _ ht ↦ ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)
        (lVelocity (I := I) alpha q.1.2)) := by
    have heq : (DifferentialGeometry.metricTimeBundleQuad
        (I := I) S.family.metric D.carrier ∘ fun q : P ↦
          (timeLift q, velocityLift q)) = fun q : P ↦
        (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2)
          (lVelocity (I := I) alpha q.1.2) := by
      funext q
      rfl
    rw [heq] at hkin0
    exact hkin0
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hlag : Continuous (fun q : P ↦
      (1 / 2 : ℝ) *
          (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2)
            (lVelocity (I := I) alpha q.1.2) +
        2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2)) :=
    continuous_const.mul hkin |>.add
      ((continuous_const.mul
        ((continuous_snd.comp continuous_subtype_val).pow 2)).mul hscalar)
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : U.domRestrict (fun q : ℝ × ℝ ↦
      lRegularizedLagrangian S q.1 alpha q.2) = fun q : P ↦
        (1 / 2 : ℝ) *
            (S.base.metric (q.1.1 - q.1.2 ^ 2)).inner (alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2)
              (lVelocity (I := I) alpha q.1.2) +
          2 * q.1.2 ^ 2 * S.scalar (q.1.1 - q.1.2 ^ 2) (alpha q.1.2) := by
    funext q
    rfl
  change Continuous (U.domRestrict (fun q : ℝ × ℝ ↦
    lRegularizedLagrangian S q.1 alpha q.2))
  rw [heq]
  exact hlag

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedAction_continuousWithinAt_of_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (hdown : ∀ {x y : ℝ}, y ∈ D.carrier → x ≤ y → x ∈ D.carrier)
    (T a b : ℝ)
    (hslab : ∀ s ∈ [[a, b]], T - s ^ 2 ∈ D.carrier)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    ContinuousWithinAt (fun R ↦ lRegularizedAction S R alpha a b) (Set.Iic T) T := by
  have hlag := lRegularizedLagrangian_continuousOn_carrier
    (I := I) (M := M) (D := D) S hS alpha halpha
  have hboxAll : ∀ R : ℝ, R ≤ T → ∀ s ∈ [[a, b]], R - s ^ 2 ∈ D.carrier := by
    intro R hR s hs
    exact hdown (hslab s hs) (by linarith [hR, sq_nonneg s])
  have hKsub : Set.Icc (T - 1) T ×ˢ [[a, b]] ⊆
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := by
    rintro ⟨R, s⟩ ⟨hR, hs⟩
    exact hboxAll R hR.2 s hs
  have hcompLag : ContinuousOn (fun q : ℝ × ℝ ↦ lRegularizedLagrangian S q.1 alpha q.2)
      (Set.Icc (T - 1) T ×ˢ [[a, b]]) := hlag.mono hKsub
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hcompLag
  let C₀ : ℝ := max C 0
  have hnb : Set.Icc (T - 1) T ∈ 𝓝[Set.Iic T] T := by
    refine mem_of_superset
      (Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : T - 1 < T)))
        self_mem_nhdsWithin) ?_
    intro R hR
    exact ⟨le_of_lt hR.1, hR.2⟩
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (s := Set.Iic T) (x₀ := T)
    (a := a) (b := b) (bound := fun _ ↦ C₀) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hnb] with R hR
    have hcontOn : ContinuousOn (fun s : ℝ ↦ lRegularizedLagrangian S R alpha s) (Ι a b) :=
      ContinuousOn.comp' (g := fun q : ℝ × ℝ ↦ lRegularizedLagrangian S q.1 alpha q.2)
        (f := fun s : ℝ ↦ (R, s)) (s := Ι a b)
        (t := Set.Icc (T - 1) T ×ˢ [[a, b]]) hcompLag
        (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs ↦ ⟨hR, uIoc_subset_uIcc hs⟩)
    exact hcontOn.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hnb] with R hR
    exact ae_of_all _ (fun s hs ↦ by
      exact (hC (R, s) ⟨hR, uIoc_subset_uIcc hs⟩).trans (le_max_left C 0))
  · refine ae_of_all _ (fun s hs ↦ ?_)
    have hs' : s ∈ [[a, b]] := uIoc_subset_uIcc hs
    refine ContinuousWithinAt.comp
      (g := fun q : ℝ × ℝ ↦ lRegularizedLagrangian S q.1 alpha q.2)
      (f := fun R : ℝ ↦ (R, s))
      (s := Set.Iic T) (t := {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier})
      (x := T) ?_ ?_ ?_
    · exact hlag.continuousWithinAt (hslab s hs')
    · exact (continuous_id.prodMk continuous_const).continuousWithinAt
    · intro R hR
      exact hboxAll R hR s hs'


end DifferentialGeometry.PDE.RicciFlow.Perelman
