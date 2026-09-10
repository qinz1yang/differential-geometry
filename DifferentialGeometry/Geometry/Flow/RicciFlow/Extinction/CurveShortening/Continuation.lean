import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M] [nonemptyM : Nonempty M]
  [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

omit t2M compactM nonemptyM hBoundary [SigmaCompactSpace M] in
theorem compact_family_regular_homotopy_at_start
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial) :
    ∃ homotopy : C(P × Icc a a, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a a) z, homotopy (p, t) z = (initial p).map z := by
  obtain ⟨loops, hloops⟩ := smooth_immersion_regular_family e initial hinit
  exact ⟨loops.comp ⟨Prod.fst, continuous_fst⟩, fun p _ z => hloops p z⟩

theorem rfs_csf_continuation (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∃ cT : SmoothImmersion (I := I) (M := M),
      (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        letI := smoothImmersionTopology e
        Tendsto
          (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
          (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT)) ∧
      (∃ closed : CurveMap M, closed.IsSolutionOn B.family.metric (Icc a T) ∧
        (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧ (∀ z, closed z T = cT.map z)) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
        extended.IsSolutionOn B.family.metric (Icc a (T + τ)) ∧
        (∀ z t, t ∈ Ico a T → extended z t = c z t)) := by
  sorry

theorem maximal_curvature_unbounded (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (hmax : ∀ u : ℝ, T < u → u ≤ b →
      ¬∃ extended : CurveMap M, extended.IsSolutionOn B.family.metric (Icc a u) ∧
        ∀ z t, t ∈ Ico a T → extended z t = c z t) :
    ∀ K : ℝ, ∃ x t, t ∈ Ico a T ∧ K < c.curvature B.family.metric x t := by
  intro K
  by_contra! hbound
  have hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ max K 0 := by
    intro x t ht
    exact (hbound x t ht).trans (le_max_left K 0)
  obtain ⟨cT, hlimit, hclosed, hextend⟩ :=
    rfs_csf_continuation B haT hTb.le c hc (max K 0) (le_max_right K 0) hcurv
  obtain ⟨τ, hτ, hτb, extended, hsol, heq⟩ := hextend hTb
  exact hmax (T + τ) (lt_add_of_pos_right T hτ) hτb ⟨extended, hsol, heq⟩

theorem rfs_csf_family_dependence (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  sorry

theorem compact_family_solution_continuous
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions := by
  sorry

theorem compact_family_regular_homotopy
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z) :
    ∃ homotopy : C(P × Icc a d, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a d) z, homotopy (p, t) z = solutions p z t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
