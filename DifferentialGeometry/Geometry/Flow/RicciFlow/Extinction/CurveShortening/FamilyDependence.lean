import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

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
variable {D : RealTimeInterval} {a b : ℝ}

def CurveShorteningUniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (d : ℝ) : Prop :=
  ∀ (c₀ : SmoothImmersion (I := I) (M := M)) (N : ℕ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ c₀ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem rfs_csf_family_dependence_of_uniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (hdep : CurveShorteningUniformLocalDependence (I := I) (M := M) B d)
    (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  let _ := hdb
  exact hdep (SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩) N e

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShortening_exists_solution_of_uniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {d : ℝ}
    (hdep : CurveShorteningUniformLocalDependence (I := I) (M := M) B d)
    (c₀ : SmoothImmersion (I := I) (M := M)) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    ∃ c : CurveMap M, c.IsSolutionOn B.family.metric (Icc a d) ∧ ∀ z, c z a = c₀.map z := by
  obtain ⟨U, -, hmem, sols, -, hprop⟩ := hdep c₀ N e
  exact ⟨sols ⟨c₀, hmem⟩, (hprop ⟨c₀, hmem⟩).1, (hprop ⟨c₀, hmem⟩).2⟩

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningUniformLocalDependence_of_isEmpty [IsEmpty M]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (d : ℝ) :
    CurveShorteningUniformLocalDependence (I := I) (M := M) B d :=
  fun c₀ _ _ => (inferInstance : IsEmpty M).elim (c₀.map 0)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
