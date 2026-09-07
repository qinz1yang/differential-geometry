import DifferentialGeometry.Geometry.Boundary.BoundaryManifold

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open scoped Manifold ContDiff

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [hI : HasSmoothBoundary E H I]

theorem contMDiff_boundaryCorestrict (f : N → M) (hf : ContMDiff J I ∞ f)
    (hboundary : ∀ x, f x ∈ I.boundary M) :
    ContMDiff (M' := BoundaryManifold I M) J hI.boundaryI ∞
      (fun x => ⟨f x, hboundary x⟩) := by
  by_cases hn : Nonempty hI.boundaryH
  · let := hn
    intro x
    let F : N → BoundaryManifold I M := fun y => ⟨f y, hboundary y⟩
    have hF : Continuous F := hf.continuous.subtype_mk _
    have hc := (contMDiffAt_extChartAt (I := I) (x := f x) (n := ∞)).comp x (hf x)
    have hp := hI.projE_contDiff.contMDiff.contMDiffAt.comp x hc
    change ContMDiffAt J hI.boundaryI ∞ F x
    rw [contMDiffAt_iff]
    refine ⟨hF.continuousAt, ?_⟩
    have hraw := (contMDiffAt_iff.mp hp).2
    have hlocal : (extChartAt hI.boundaryI (F x) ∘ F) =ᶠ[nhds x]
        (hI.projE ∘ extChartAt I (f x) ∘ f) := by
      filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
        ((chartAt H (f x)).open_source.mem_nhds (mem_chart_source H (f x)))] with y hy
      have he := BoundaryManifold.inclH_boundaryChart_apply (I := I) (F x) (F y) hy
      have hb : chartAt hI.boundaryH (F x) = BoundaryManifold.boundaryChart (I := I) (F x) := by
        exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) (F x)
      change hI.boundaryI (chartAt hI.boundaryH (F x) (F y)) = hI.projE (I (chartAt H (f x) (f y)))
      rw [hb, ← he, hI.proj_inclH_compat]
    have ht : Filter.Tendsto (extChartAt J x).symm
        (nhdsWithin (extChartAt J x x) (Set.range J)) (nhds x) := by
      rw [Filter.Tendsto, map_extChartAt_symm_nhdsWithin_range]
    have hcomp := hlocal.comp_tendsto ht
    apply hraw.congr_of_eventuallyEq_of_mem
    · change (extChartAt hI.boundaryI (F x) ∘ F ∘ (extChartAt J x).symm) =ᶠ[
        nhdsWithin (extChartAt J x x) (Set.range J)]
        (hI.projE ∘ extChartAt I (f x) ∘ f ∘ (extChartAt J x).symm)
      exact hcomp
    · exact ⟨chartAt G x x, rfl⟩
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hn
    have hEmpty : IsEmpty (BoundaryManifold I M) := BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    intro x
    exact (hEmpty.false (⟨f x, hboundary x⟩ : BoundaryManifold I M)).elim

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
