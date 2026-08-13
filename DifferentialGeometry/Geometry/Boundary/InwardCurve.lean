import DifferentialGeometry.Geometry.Boundary.OutwardNormal

set_option autoImplicit false

noncomputable section

open Set Function Topology Bundle Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem exists_inward_curve (p : BoundaryManifold I M) :
    ∃ gamma : ℝ → M,
      gamma 0 = (p : M) ∧
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) I gamma (Set.Ici 0) 0 ∧
      mfderivWithin 𝓘(ℝ, ℝ) I gamma (Set.Ici 0) 0
          ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) =
        inwardCoord (M := M) p ∧
      ∃ a : ℝ, 0 < a ∧
        Set.MapsTo gamma (Set.Ioc 0 a) (I.interior M) := by
  let z : E := extChartAt I (p : M) (p : M)
  have hzfrontier : z ∈ frontier (Set.range I) := by
    exact p.property
  obtain ⟨epsilon, hepsilon, henters⟩ :=
    hI.inwardCoordE_enters z hzfrontier
  let q : ℝ → E := fun t => z + t • hI.inwardCoordE
  have hq0 : q 0 = z := by
    simp [q]
  have hq_deriv : HasDerivAt q hI.inwardCoordE 0 := by
    simpa [q] using
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const hI.inwardCoordE).const_add z
  have hq_range : q ⁻¹' Set.range I ∈ 𝓝[Set.Ici 0] 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepsilon),
      self_mem_nhdsWithin] with t htupper htnonneg
    change q t ∈ Set.range I
    by_cases htzero : t = 0
    · rw [htzero, hq0]
      exact extChartAt_target_subset_range (I := I) (p : M)
        (mem_extChartAt_target (I := I) (p : M))
    · exact interior_subset (henters t
        ⟨lt_of_le_of_ne htnonneg (Ne.symm htzero), htupper.le⟩)
  let gamma : ℝ → M := (extChartAt I (p : M)).symm ∘ q
  refine ⟨gamma, ?_, ?_, ?_, ?_⟩
  · change (extChartAt I (p : M)).symm (q 0) = (p : M)
    rw [hq0]
    exact extChartAt_to_inv (I := I) (p : M)
  · have hsymm := mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := (p : M)) (mem_extChartAt_target (I := I) (p : M))
    have hq_mdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        q (Set.Ici 0) 0 :=
      hq_deriv.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
    exact hsymm.comp_of_preimage_mem_nhdsWithin_of_eq 0 hq_mdiff hq_range hq0
  · have hsymm := mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := (p : M)) (mem_extChartAt_target (I := I) (p : M))
    have hq_mdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        q (Set.Ici 0) 0 :=
      hq_deriv.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
    have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ)
        (Set.Ici (0 : ℝ)) (0 : ℝ) :=
      (uniqueDiffWithinAt_Ici (0 : ℝ)).uniqueMDiffWithinAt
    have hchain := mfderivWithin_comp_of_preimage_mem_nhdsWithin
      (x := (0 : ℝ)) (by simpa [hq0] using hsymm) hq_mdiff hq_range huniq
    have hsymm_deriv :
        mfderivWithin 𝓘(ℝ, E) I
          ((chartAt H (p : M)).symm ∘ I.symm)
          (Set.range I) z = ContinuousLinearMap.id ℝ E := by
      change mfderivWithin 𝓘(ℝ, E) I (extChartAt I (p : M)).symm
        (Set.range I) z = ContinuousLinearMap.id ℝ E
      dsimp [z]
      exact mfderivWithin_range_extChartAt_symm
    rw [hq0, hsymm_deriv] at hchain
    have happ := congrArg (fun L => L
      ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ))) hchain
    change (mfderivWithin 𝓘(ℝ, ℝ) I
        (((chartAt H (p : M)).symm ∘ I.symm) ∘ q) (Set.Ici 0) 0)
          ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) =
      ((ContinuousLinearMap.id ℝ E).comp
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) q (Set.Ici 0) 0))
          ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) at happ
    have hq_deriv_eq :
        mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) q (Set.Ici 0) 0
            ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) =
          hI.inwardCoordE := by
      rw [mfderivWithin_eq_fderivWithin]
      have heq := hq_deriv.hasFDerivAt.hasFDerivWithinAt.fderivWithin
        (uniqueDiffWithinAt_Ici 0)
      rw [heq]
      change ContinuousLinearMap.toSpanSingleton ℝ hI.inwardCoordE 1 = _
      exact ContinuousLinearMap.toSpanSingleton_apply_one
        (R₁ := ℝ) hI.inwardCoordE
    change (mfderivWithin 𝓘(ℝ, ℝ) I
      (((chartAt H (p : M)).symm ∘ I.symm) ∘ q) (Set.Ici 0) 0)
        ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) = _
    rw [happ]
    change (ContinuousLinearMap.id ℝ E)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) q (Set.Ici 0) 0
        ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ))) = _
    rw [ContinuousLinearMap.id_apply, hq_deriv_eq, inwardCoord_eq]
  · have hq_tendsto : Tendsto q (𝓝[Set.Ici 0] 0)
        (𝓝[Set.range I] z) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hq_range⟩
      have hcont : Tendsto q (𝓝[Set.Ici 0] 0) (𝓝 (q 0)) :=
        hq_deriv.continuousAt.continuousWithinAt
      simpa [hq0] using hcont
    have hq_target : q ⁻¹' (extChartAt I (p : M)).target ∈
        𝓝[Set.Ici 0] 0 :=
      hq_tendsto (extChartAt_target_mem_nhdsWithin (I := I) (p : M))
    obtain ⟨U, hU, hUtarget⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hq_target
    obtain ⟨l, u, h0lu, hluU⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hU
    let a : ℝ := min (epsilon / 2) (u / 2)
    have ha : 0 < a := by
      exact lt_min (half_pos hepsilon) (half_pos h0lu.2)
    refine ⟨a, ha, ?_⟩
    intro t ht
    have hta_epsilon : t < epsilon :=
      lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (half_lt_self hepsilon)
    have hta_u : t < u :=
      lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (half_lt_self h0lu.2)
    have htU : t ∈ U := hluU ⟨h0lu.1.trans ht.1, hta_u⟩
    have hqt_target : q t ∈ (extChartAt I (p : M)).target :=
      hUtarget ⟨htU, ht.1.le⟩
    have hqt_interior_range : q t ∈ interior (Set.range I) :=
      henters t ⟨ht.1, hta_epsilon.le⟩
    have hqt_interior_target : q t ∈
        interior (extChartAt I (p : M)).target :=
      (extChartAt_target_eventuallyEq_of_mem hqt_target).symm.mem_interior
        hqt_interior_range
    have hsource : gamma t ∈ (chartAt H (p : M)).source := by
      change (extChartAt I (p : M)).symm (q t) ∈
        (chartAt H (p : M)).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I (p : M)).map_target hqt_target
    apply (I.isInteriorPoint_iff_of_mem_atlas (M := M) (n := ∞) (by simp)
      (chart_mem_atlas H (p : M)) hsource).2
    change extChartAt I (p : M) (gamma t) ∈
      interior (extChartAt I (p : M)).target
    change extChartAt I (p : M)
      ((extChartAt I (p : M)).symm (q t)) ∈ _
    rw [(extChartAt I (p : M)).right_inv hqt_target]
    exact hqt_interior_target

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
