import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Compact

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

theorem exists_isSolutionOn_extension_past_right_endpoint [CompactSpace M] {a b : ℝ}
    (hab : a < b) (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le))
    (hS : IsSolutionOn S)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ d : ℝ, ∃ hbd : b < d,
      ∃ S' : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d (hab.trans hbd).le),
        IsSolutionOn S' ∧ (∀ t ≤ b, S'.base.metric t = S.base.metric t) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun q : ℝ × M => (⟨q.2, (S'.base.metric q.1).inner q.2⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
          (Icc a d ×ˢ (univ : Set M)) := by
  obtain ⟨e, hbe, Q, hinit, -, hQjoint, hQpde⟩ :=
    exists_completeBoundedCurvatureSolutionOn_from_time_of_compact (I := I) (M := M)
      (S.base.metric b) b
  obtain ⟨d, hbd, hde⟩ := exists_between hbe
  let gR := Q.solution.base.metric
  have hR : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gR q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc b d ×ˢ (univ : Set M)) :=
    hQjoint.mono (prod_mono (fun t ht => ⟨ht.1, ht.2.trans_lt hde⟩) subset_rfl)
  have hpdeL : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (S.base.metric s).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) t := by
    intro t ht x v w
    have hd := metricDerivAt S hS ⟨t, ht⟩ x v w
    have hr := metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
    erw [hr] at hd
    exact hd
  have hpdeR : ∀ t ∈ Ioo b d, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gR s).inner x v w) (-2 * ricciTensor (gR t) x v w) t :=
    fun t ht x v w =>
      (hQpde t ⟨ht.1.le, ht.2.trans hde⟩ x v w).hasDerivAt (Ici_mem_nhds ht.1)
  have hmatch : S.base.metric b = gR b := hinit.symm
  exact ⟨d, hbd, { base := { metric := fun t => if t ≤ b then S.base.metric t else gR t } },
    isSolutionOn_ite_of_ricciFlow S.base.metric gR hab hbd hjoint hR hpdeL hpdeR hmatch,
    fun t ht => if_pos ht,
    metricCLMSection_jointContMDiffOn_ite_of_ricciFlow S.base.metric gR hab hbd hjoint hR
      hpdeL hpdeR hmatch⟩

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D₁ D₂ : RealTimeInterval}

theorem lRegularizedAccel_congr {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T s : ℝ}
    (h : S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    lRegularizedAccel S₁ T s = lRegularizedAccel S₂ T s := by
  have hscalar : S₁.base.scalar (T - s ^ 2) = S₂.base.scalar (T - s ^ 2) := by
    unfold SolutionFamily.scalar
    rw [h]
  funext x A
  simp only [lRegularizedAccel, SolutionOn.scalar, h, hscalar]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsLRegularizedGeodesicOn.of_metric_eq {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ} {alpha : ℝ → M} {J : Set ℝ}
    (h : IsLRegularizedGeodesicOn S₁ T alpha J)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    IsLRegularizedGeodesicOn S₂ T alpha J := by
  intro s hs
  obtain ⟨-, hdiff, hrep, hacc⟩ := h s hs
  refine ⟨hreg s hs, hdiff, hrep, ?_⟩
  rw [← hmetric s hs, ← lRegularizedAccel_congr (hmetric s hs)]
  exact hacc

theorem IsLRegularizedCurveOn.of_metric_eq {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ} {alpha : ℝ → M} {J : Set ℝ} {x : M}
    {Z : TangentSpace I x} (h : IsLRegularizedCurveOn S₁ T alpha J x Z)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    IsLRegularizedCurveOn S₂ T alpha J x Z :=
  ⟨h.1, h.2.1, h.2.2.of_metric_eq hreg hmetric⟩

theorem HasLRegularizedCurveAt.of_metric_eq_of_le {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T s : ℝ} {x : M} {Z : TangentSpace I x}
    (h : HasLRegularizedCurveAt S₁ T x Z s)
    (hreg : ∀ t ≤ T, t ∈ D₁.regular → t ∈ D₂.regular)
    (hmetric : ∀ t ≤ T, t ∈ D₁.regular → S₁.base.metric t = S₂.base.metric t) :
    HasLRegularizedCurveAt S₂ T x Z s := by
  obtain ⟨alpha, J, hJ, hJc, h0, hs, halpha⟩ := h
  refine ⟨alpha, J, hJ, hJc, h0, hs, halpha.of_metric_eq ?_ ?_⟩
  · exact fun r hr => hreg _ (sub_le_self T (sq_nonneg r)) (halpha.2.2 r hr).1
  · exact fun r hr => hmetric _ (sub_le_self T (sq_nonneg r)) (halpha.2.2 r hr).1

theorem lRegularizedDomain_eq_of_metric_eq_of_le {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ}
    (hreg : ∀ t ≤ T, t ∈ D₁.regular ↔ t ∈ D₂.regular)
    (hmetric : ∀ t ≤ T, t ∈ D₁.regular → S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lRegularizedDomain S₁ T x Z = lRegularizedDomain S₂ T x Z := by
  ext s
  exact ⟨fun h => HasLRegularizedCurveAt.of_metric_eq_of_le h (fun t ht => (hreg t ht).1)
      hmetric,
    fun h => HasLRegularizedCurveAt.of_metric_eq_of_le h (fun t ht => (hreg t ht).2)
      (fun t ht h₂ => (hmetric t ht ((hreg t ht).2 h₂)).symm)⟩

theorem lRegularizedCurve_eq_of_metric_eq_of_le {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} (hS₂ : IsSolutionOn S₂) {T : ℝ}
    (hreg : ∀ t ≤ T, t ∈ D₁.regular ↔ t ∈ D₂.regular)
    (hmetric : ∀ t ≤ T, t ∈ D₁.regular → S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lRegularizedCurve S₁ T x Z = lRegularizedCurve S₂ T x Z := by
  funext s
  by_cases h : HasLRegularizedCurveAt S₁ T x Z s
  · obtain ⟨J, hJ, hJc, h0, hs, hchosen⟩ := lRegularizedChosen_spec S₁ T x Z h
    have h₂ : IsLRegularizedCurveOn S₂ T (lRegularizedChosen S₁ T x Z h) J x Z :=
      hchosen.of_metric_eq
        (fun r hr => (hreg _ (sub_le_self T (sq_nonneg r))).1 (hchosen.2.2 r hr).1)
        (fun r hr => hmetric _ (sub_le_self T (sq_nonneg r)) (hchosen.2.2 r hr).1)
    rw [lRegularizedCurve_of_mem (show s ∈ lRegularizedDomain S₁ T x Z from h)]
    exact (lRegularizedCurve_eqOn S₂ hS₂ T hJ hJc h0 h₂ hs).symm
  · have h' : ¬ HasLRegularizedCurveAt S₂ T x Z s := fun h₂ =>
      h (HasLRegularizedCurveAt.of_metric_eq_of_le h₂ (fun t ht => (hreg t ht).2)
        (fun t ht h₂' => (hmetric t ht ((hreg t ht).2 h₂')).symm))
    unfold lRegularizedCurve
    rw [dif_neg h, dif_neg h']

theorem lExp_eq_of_metric_eq_of_le {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} (hS₂ : IsSolutionOn S₂) {T : ℝ}
    (hreg : ∀ t ≤ T, t ∈ D₁.regular ↔ t ∈ D₂.regular)
    (hmetric : ∀ t ≤ T, t ∈ D₁.regular → S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lExp S₁ T x Z = lExp S₂ T x Z := by
  funext tau
  change lRegularizedCurve S₁ T x Z (Real.sqrt tau) = lRegularizedCurve S₂ T x Z (Real.sqrt tau)
  rw [lRegularizedCurve_eq_of_metric_eq_of_le hS₂ hreg hmetric x Z]

theorem lExpDomain_eq_of_metric_eq_of_le {S₁ : SolutionOn (I := I) (M := M) D₁}
    {S₂ : SolutionOn (I := I) (M := M) D₂} {T : ℝ}
    (hreg : ∀ t ≤ T, t ∈ D₁.regular ↔ t ∈ D₂.regular)
    (hmetric : ∀ t ≤ T, t ∈ D₁.regular → S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lExpDomain S₁ T x Z = lExpDomain S₂ T x Z := by
  unfold lExpDomain
  rw [lRegularizedDomain_eq_of_metric_eq_of_le hreg hmetric x Z]

section Closed

variable {a d₁ d₂ T : ℝ} {h₁ : a ≤ d₁} {h₂ : a ≤ d₂}

private theorem closed_regular_iff_of_le (hT₁ : T < d₁) (hT₂ : T < d₂) {t : ℝ} (ht : t ≤ T) :
    t ∈ (RealTimeInterval.closed a d₁ h₁).regular ↔
      t ∈ (RealTimeInterval.closed a d₂ h₂).regular :=
  ⟨fun h => ⟨h.1, ht.trans_lt hT₂⟩, fun h => ⟨h.1, ht.trans_lt hT₁⟩⟩

theorem lRegularizedDomain_eq_of_closed_metric_eq
    {S₁ : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d₁ h₁)}
    {S₂ : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d₂ h₂)}
    (hT₁ : T < d₁) (hT₂ : T < d₂)
    (hmetric : ∀ t ∈ Ioc a T, S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lRegularizedDomain S₁ T x Z = lRegularizedDomain S₂ T x Z :=
  lRegularizedDomain_eq_of_metric_eq_of_le (fun _ ht => closed_regular_iff_of_le hT₁ hT₂ ht)
    (fun t ht h => hmetric t ⟨h.1, ht⟩) x Z

theorem lRegularizedCurve_eq_of_closed_metric_eq
    {S₁ : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d₁ h₁)}
    {S₂ : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d₂ h₂)}
    (hS₂ : IsSolutionOn S₂) (hT₁ : T < d₁) (hT₂ : T < d₂)
    (hmetric : ∀ t ∈ Ioc a T, S₁.base.metric t = S₂.base.metric t)
    (x : M) (Z : TangentSpace I x) :
    lRegularizedCurve S₁ T x Z = lRegularizedCurve S₂ T x Z :=
  lRegularizedCurve_eq_of_metric_eq_of_le hS₂
    (fun _ ht => closed_regular_iff_of_le hT₁ hT₂ ht) (fun t ht h => hmetric t ⟨h.1, ht⟩) x Z

end Closed

theorem exists_closed_end_lRegularized_extension [CompactSpace M] {a b : ℝ} (hab : a < b)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le))
    (hS : IsSolutionOn S)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ d : ℝ, ∃ hbd : b < d,
      ∃ S' : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a d (hab.trans hbd).le),
        IsSolutionOn S' ∧ (∀ t ≤ b, S'.base.metric t = S.base.metric t) ∧
        (∀ x : M, ∀ Z : TangentSpace I x, (0 : ℝ) ∈ lRegularizedDomain S' b x Z) ∧
        ∀ T < b, ∀ x : M, ∀ Z : TangentSpace I x,
          lRegularizedDomain S' T x Z = lRegularizedDomain S T x Z ∧
            lRegularizedCurve S' T x Z = lRegularizedCurve S T x Z := by
  obtain ⟨d, hbd, S', hS', hmetric, -⟩ :=
    exists_isSolutionOn_extension_past_right_endpoint hab S hS hjoint
  refine ⟨d, hbd, S', hS', hmetric, fun x Z =>
    zero_mem_lRegularizedDomain S' hS' b x Z ⟨hab, hbd⟩, fun T hT x Z => ⟨?_, ?_⟩⟩
  · exact lRegularizedDomain_eq_of_closed_metric_eq (hT.trans hbd) hT
      (fun t ht => hmetric t (ht.2.trans hT.le)) x Z
  · exact lRegularizedCurve_eq_of_closed_metric_eq hS (hT.trans hbd) hT
      (fun t ht => hmetric t (ht.2.trans hT.le)) x Z

end DifferentialGeometry.PDE.RicciFlow.Perelman
