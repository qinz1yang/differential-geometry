import DifferentialGeometry.Topology.Manifold.OneManifold.DoubleManifold

/-!
# The upper sheet of the double

`doubleIncl x = (x, bdryFn x)` embeds `M` as the upper sheet of `Double M`. In the charts of `M`
and of the double it is `y ↦ c · y₀` with `c ≠ 0` (`c = 1` over the interior, `c = 1 / r` at a
boundary point), so it is smooth with nonvanishing derivative. The double of a connected `M` is
connected (upper and lower sheets meet over the boundary).
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M] [T2Space M]

/-- The upper sheet `x ↦ (x, bdryFn x)` of the double. -/
def doubleIncl (x : M) : Double M :=
  ⟨(x, bdryFn x), by
    change |bdryFn x| = bdryFn x
    exact abs_of_nonneg (bdryFn_nonneg x)⟩

/-- The lower sheet `x ↦ (x, -bdryFn x)` of the double. -/
def doubleInclNeg (x : M) : Double M :=
  ⟨(x, -bdryFn x), by
    change |-bdryFn x| = bdryFn x
    rw [abs_neg]
    exact abs_of_nonneg (bdryFn_nonneg x)⟩

omit [T2Space M] in
theorem doubleIncl_injective : Function.Injective (doubleIncl (M := M)) :=
  fun _ _ h => congrArg (fun q : Double M => q.1.1) h

theorem continuous_doubleIncl : Continuous (doubleIncl (M := M)) :=
  (continuous_id.prodMk continuous_bdryFn).subtype_mk _

theorem continuous_doubleInclNeg : Continuous (doubleInclNeg (M := M)) :=
  (continuous_id.prodMk continuous_bdryFn.neg).subtype_mk _

omit [T2Space M] in
theorem doubleInclNeg_notMem_range {x : M} (hx : x ∉ (𝓡∂ 1).boundary M) :
    doubleInclNeg x ∉ range (doubleIncl (M := M)) := by
  rintro ⟨y, hy⟩
  have h1 : bdryFn y = -bdryFn x := congrArg (fun q : Double M => q.1.2) hy
  have h2 : y = x := congrArg (fun q : Double M => q.1.1) hy
  rw [h2] at h1
  have hpos := bdryFn_pos_iff.mpr hx
  linarith

theorem connectedSpace_double [ConnectedSpace M] [Nonempty ((𝓡∂ 1).boundary M)] :
    ConnectedSpace (Double M) := by
  obtain ⟨p, hp⟩ := (inferInstance : Nonempty ((𝓡∂ 1).boundary M))
  have hpos : IsConnected (range (doubleIncl (M := M))) :=
    isConnected_range continuous_doubleIncl
  have hneg : IsConnected (range (doubleInclNeg (M := M))) :=
    isConnected_range continuous_doubleInclNeg
  have hp0 : bdryFn p = 0 := bdryFn_eq_zero_iff.mpr hp
  have hmeet : doubleIncl p ∈ range (doubleInclNeg (M := M)) := by
    refine ⟨p, Subtype.ext (Prod.ext rfl ?_)⟩
    change -bdryFn p = bdryFn p
    rw [hp0, neg_zero]
  have hunion : range (doubleIncl (M := M)) ∪ range doubleInclNeg = univ := by
    apply eq_univ_of_forall
    intro q
    rcases abs_choice q.1.2 with h | h
    · left
      refine ⟨q.1.1, Subtype.ext (Prod.ext rfl ?_)⟩
      change bdryFn q.1.1 = q.1.2
      rw [← double_snd_abs, h]
    · right
      refine ⟨q.1.1, Subtype.ext (Prod.ext rfl ?_)⟩
      change -bdryFn q.1.1 = q.1.2
      rw [← double_snd_abs, h, neg_neg]
  have hconn := hpos.union ⟨doubleIncl p, mem_range_self p, hmeet⟩ hneg
  rw [hunion] at hconn
  exact connectedSpace_iff_univ.mpr hconn

theorem writtenInExtChartAt_doubleIncl (x : M) :
    ∃ c : ℝ, c ≠ 0 ∧ writtenInExtChartAt (𝓡∂ 1) 𝓘(ℝ, ℝ) x doubleIncl
      =ᶠ[𝓝[range (𝓡∂ 1)] extChartAt (𝓡∂ 1) x x] fun y => c * y 0 := by
  have htarget := extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 1) x
  have hcoord : ∀ y ∈ (extChartAt (𝓡∂ 1) x).target,
      chartCoord (chartAt (EuclideanHalfSpace 1) x) ((extChartAt (𝓡∂ 1) x).symm y) = y 0 := by
    intro y hy
    rw [extChartAt_coe_symm]
    have hy' := (extChartAt_target_subset_range (I := 𝓡∂ 1) x) hy
    have hyt : (𝓡∂ 1).symm y ∈ (chartAt (EuclideanHalfSpace 1) x).target := by
      rw [extChartAt_target] at hy
      exact hy.1
    unfold chartCoord
    rw [Function.comp_apply, (chartAt (EuclideanHalfSpace 1) x).right_inv hyt]
    change ((𝓡∂ 1) ((𝓡∂ 1).symm y)) 0 = y 0
    rw [ModelWithCorners.right_inv _ hy']
  by_cases hx : x ∈ (𝓡∂ 1).boundary M
  · let p : Bdry M := ⟨x, hx⟩
    have hx0 : bdryFn x = 0 := bdryFn_eq_zero_iff.mpr hx
    have hchart : chartAt ℝ (doubleIncl x) = foldChart p := by
      change doubleChartAt (doubleIncl x) = foldChart p
      unfold doubleChartAt
      simp only [show (doubleIncl x).1.2 = 0 from hx0, ↓reduceDIte]
      rfl
    refine ⟨1 / bdryRadius p, one_div_ne_zero (bdryRadius_pos p).ne', ?_⟩
    have hnbhd : (extChartAt (𝓡∂ 1) x).symm ⁻¹' bdryNbhd p ∈
        𝓝[range (𝓡∂ 1)] extChartAt (𝓡∂ 1) x x := by
      have h0 : bdryNbhd p ∈ 𝓝[univ] x := by
        rw [nhdsWithin_univ]
        exact (isOpen_bdryNbhd p).mem_nhds (mem_bdryNbhd_self p)
      have h := extChartAt_preimage_mem_nhdsWithin (I := 𝓡∂ 1) h0
      rwa [preimage_univ, univ_inter] at h
    filter_upwards [htarget, hnbhd] with y hy hyV
    change (extChartAt 𝓘(ℝ, ℝ) (doubleIncl x)) (doubleIncl ((extChartAt (𝓡∂ 1) x).symm y)) = _
    rw [extChartAt_coe, hchart]
    change bdryFn ((extChartAt (𝓡∂ 1) x).symm y) = 1 / bdryRadius p * y 0
    rw [bdryFn_eq_on_bdryNbhd p hyV, hcoord y hy]
    ring
  · have hx0 : bdryFn x ≠ 0 := fun h => hx (bdryFn_eq_zero_iff.mp h)
    have hchart : chartAt ℝ (doubleIncl x) =
        sheetChart (chartAt (EuclideanHalfSpace 1) x) (chart_mem_atlas _ x) (bdryFn x) := by
      change doubleChartAt (doubleIncl x) = _
      unfold doubleChartAt
      simp only [show (doubleIncl x).1.2 ≠ 0 from hx0, ↓reduceDIte]
      rfl
    refine ⟨1, one_ne_zero, ?_⟩
    filter_upwards [htarget] with y hy
    change (extChartAt 𝓘(ℝ, ℝ) (doubleIncl x)) (doubleIncl ((extChartAt (𝓡∂ 1) x).symm y)) = _
    rw [extChartAt_coe, hchart]
    change chartCoord (chartAt (EuclideanHalfSpace 1) x) ((extChartAt (𝓡∂ 1) x).symm y) = 1 * y 0
    rw [hcoord y hy, one_mul]

theorem hasMFDerivAt_doubleIncl (x : M) :
    ∃ c : ℝ, c ≠ 0 ∧ HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) doubleIncl x
      (c • (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) := by
  obtain ⟨c, hc, heq⟩ := writtenInExtChartAt_doubleIncl x
  refine ⟨c, hc, continuous_doubleIncl.continuousAt, ?_⟩
  have hval := heq.eq_of_nhdsWithin (mem_range_self _)
  exact (c • (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)
    ).hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hval

theorem contMDiff_doubleIncl : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (doubleIncl (M := M)) := by
  intro x
  obtain ⟨c, -, heq⟩ := writtenInExtChartAt_doubleIncl x
  rw [contMDiffAt_iff]
  refine ⟨continuous_doubleIncl.continuousAt, ?_⟩
  have hval := heq.eq_of_nhdsWithin (mem_range_self _)
  have hlin : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ (Fin 1) => c * y 0 :=
    contDiff_const.mul (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
  exact hlin.contDiffWithinAt.congr_of_eventuallyEq heq hval

theorem mfderiv_doubleIncl_ne_zero (x : M) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) doubleIncl x (EuclideanSpace.single 0 1) ≠ 0 := by
  obtain ⟨c, hc, h⟩ := hasMFDerivAt_doubleIncl x
  rw [h.mfderiv]
  change c • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 ≠ 0
  simpa using hc

end DifferentialGeometry.Topology.Manifold.OneManifold
