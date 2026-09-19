import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem continuous_smoothImmersion_of_continuous_jets
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (c : P → SmoothImmersion (I := I) (M := M))
    (hjets : ∀ m : ℕ, Continuous (fun q : P × ℝ =>
      iteratedDeriv m (fun x : ℝ => e.map ((c q.1).map x)) q.2)) :
    @Continuous P (SmoothImmersion (I := I) (M := M)) inferInstance
      (smoothImmersionTopology e) c := by
  rw [smoothImmersionTopology, continuous_generateFrom_iff]
  rintro U ⟨d, m, ε, _, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hd : Continuous (iteratedDeriv m
      (fun x : ℝ => e.map (d.map x))) :=
    ContDiff.continuous_iteratedDeriv' m
      (contDiff_infty.mp (e.smooth.comp d.smooth).contDiff m)
  have hnorm : Continuous (fun q : P × ℝ =>
      ‖iteratedDeriv m (fun x : ℝ => e.map ((c q.1).map x)) q.2 -
        iteratedDeriv m (fun x : ℝ => e.map (d.map x)) q.2‖) :=
    ((hjets m).sub (hd.comp continuous_snd)).norm
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro x hx
  exact hnorm.continuousAt.eventually_lt continuousAt_const (hp x hx)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
