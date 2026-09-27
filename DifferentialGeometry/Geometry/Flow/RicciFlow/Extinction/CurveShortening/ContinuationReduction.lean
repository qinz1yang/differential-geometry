import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.FamilyDependence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.FamilyDependenceFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceDimensionOne

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningLoopFamilyExtension_of_uniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (H : CurveShorteningUniformLocalDependence (I := I) (M := M) B d) :
    curveShorteningLoopFamilyExtension (I := I) (M := M) B d had e :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
    have hsub : Icc a (min d (a + (d - a))) = Icc a d := by
      rw [show a + (d - a) = d by ring, min_self]
    have hgoal : ∀ T : ℝ, a ≤ T → Icc a (min d (T + (d - a))) = Icc a d := fun T haT =>
      congrArg (Icc a) (min_eq_left (by linarith : d ≤ T + (d - a)))
    refine ⟨d - a, by linarith, le_rfl, ?_, ?_⟩
    · intro c hc
      obtain ⟨U, hU, hmem, sols, hcont, hsol⟩ :=
        H (SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩) N e
      refine ⟨U, hU, hmem, sols, ?_, ?_⟩
      · rw [hsub]; exact hcont
      · intro p; rw [hsub]; exact hsol p
    · intro T haT hTd c hc U hU sols hcont hsol hmem
      obtain ⟨U', hU', hmem', sols', hcont', hsol'⟩ :=
        H (SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩) N e
      refine ⟨U ∩ U', hU.inter hU', ⟨hmem, hmem'⟩, Set.inter_subset_left,
        fun p => sols' ⟨p.1, p.2.2⟩, ?_, ?_⟩
      · have hmap : Continuous (fun p : ↥(U ∩ U') =>
            (⟨(p : SmoothImmersion (I := I) (M := M)), p.2.2⟩ : ↥U')) :=
          Continuous.subtype_mk continuous_subtype_val _
        rw [hgoal T haT]
        fun_prop
      · rw [hgoal T haT]
        intro p
        exact hsol' ⟨p.1, p.2.2⟩

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningUniformLocalDependence_of_familyExtension
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d)
    (H : ∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
      curveShorteningLoopFamilyExtension (I := I) (M := M) B d had e)
    (hex : ∀ c₀ : SmoothImmersion (I := I) (M := M), ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (Icc a d) ∧ ∀ z, c z a = c₀.map z) :
    CurveShorteningUniformLocalDependence (I := I) (M := M) B d := by
  intro c₀ N' e'
  obtain ⟨c, hc, htr⟩ := hex c₀
  have hslice : SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ = c₀ :=
    (SmoothImmersion.mk.injEq _ _ _ _ _ _).mpr (funext fun z => htr z)
  rw [← hslice]
  simpa only using rfs_csf_family_dependence_of_familyExtension B had c hc e' (H N' e')

omit [CompleteSpace E] compactM nonemptyM in
theorem exists_solutionOn_Icc_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 1)
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {d : ℝ} :
    ∀ c₀ : SmoothImmersion (I := I) (M := M), ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (Icc a d) ∧ ∀ z, c z a = c₀.map z := by
  intro c₀
  refine ⟨staticCurve c₀.map,
    ⟨staticCurve_smoothOn c₀.map c₀.smooth (Icc a d),
      staticCurve_immersedOn c₀.map (Icc a d) c₀.immersed, ?_⟩, fun z => rfl⟩
  intro x t ht
  rw [staticCurve_velocity]
  exact (curvatureVector_eq_zero_of_finrank_eq_one hE B.family.metric
    (staticCurve_smoothOn c₀.map c₀.smooth (Icc a d))
    (staticCurve_immersedOn c₀.map (Icc a d) c₀.immersed) ht).symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
