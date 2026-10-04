import DifferentialGeometry.Topology.Ehresmann.SmoothLift
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]

omit [FiniteDimensional ℝ E] in
/-- Spatial full rank is open jointly in the point and the time parameter. -/
theorem isOpen_spatial_surjective_mfderiv
    (h : Y × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) :
    IsOpen {x : Y × ℝ | Surjective (mfderiv I 𝓘(ℝ, F) (fun y => h (y, x.2)) x.1)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x₀ hx₀
  let A : Y × ℝ → E →L[ℝ] F :=
    inTangentCoordinates I 𝓘(ℝ, F) Prod.fst h
      (fun x => mfderiv I 𝓘(ℝ, F) (fun y => h (y, x.2)) x.1) x₀
  have hbase : ContMDiffAt ((I.prod 𝓘(ℝ)).prod I) 𝓘(ℝ, F) ∞
      (fun q : (Y × ℝ) × Y => h (q.2, q.1.2)) (x₀, x₀.1) :=
    (hh _).comp _ (contMDiffAt_snd.prodMk contMDiffAt_fst.snd)
  have hA : ContinuousAt A x₀ :=
    (hbase.mfderiv (fun x : Y × ℝ => fun y : Y => h (y, x.2)) Prod.fst
      contMDiffAt_fst (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousAt
  have hA₀ : A x₀ = mfderiv I 𝓘(ℝ, F) (fun y => h (y, x₀.2)) x₀.1 := by
    dsimp only [A]
    erw [inTangentCoordinates_eq_mfderiv_comp_abuse (f := Prod.fst)
      (g := h) (x₀ := x₀) (x := x₀) (mem_chart_source H x₀.1)
      (mem_chart_source F (h x₀))]
    simp only [mfderiv_extChartAt_self, mfderivWithin_range_extChartAt_symm]
    ext v
    rfl
  have hAsurj : Surjective (A x₀) := by
    rw [hA₀]
    exact hx₀
  let hsplit := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hAsurj
  let R := hsplit.rightInverse
  have hAR : (A x₀).comp R = ContinuousLinearMap.id ℝ F := by
    ext v
    exact hsplit.rightInverse_rightInverse v
  have hnear : ∀ᶠ x in 𝓝 x₀, ((A x).comp R).IsInvertible := by
    change (fun x => (A x).comp R) ⁻¹'
      {L : F →L[ℝ] F | L.IsInvertible} ∈ 𝓝 x₀
    apply (hA.clm_comp (continuousAt_const (y := R))).preimage_mem_nhds
    apply ContinuousLinearEquiv.isOpen.mem_nhds
    rw [hAR]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  have hsource : ∀ᶠ x : Y × ℝ in 𝓝 x₀, x.1 ∈ (chartAt H x₀.1).source :=
    continuous_fst.continuousAt.eventually
      ((chartAt H x₀.1).open_source.mem_nhds (mem_chart_source H x₀.1))
  have htarget : ∀ᶠ x in 𝓝 x₀, h x ∈ (chartAt F (h x₀)).source :=
    hh.continuous.continuousAt.eventually
      ((chartAt F (h x₀)).open_source.mem_nhds (mem_chart_source F (h x₀)))
  filter_upwards [hnear, hsource, htarget] with x hx hxs hxt
  have hsurj : Surjective (A x) := by
    intro v
    obtain ⟨w, hw⟩ := hx.surjective v
    exact ⟨R w, hw⟩
  dsimp only [A] at hsurj
  erw [inTangentCoordinates_eq_mfderiv_comp (f := Prod.fst)
    (g := h) (x₀ := x₀) (x := x) hxs hxt] at hsurj
  let L := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) (h x₀)) (h x)
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt
    (by simpa only [extChartAt_source] using hxt)
  intro v
  obtain ⟨w, hw⟩ := hsurj (L v)
  refine ⟨mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀.1).symm (range I)
    (extChartAt I x₀.1 x.1) w, ?_⟩
  exact hL.injective hw

/-- An open property holding on a level has one uniform norm margin on a compact set. -/
theorem exists_norm_margin_of_compact_level
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    {K : Set X} (hK : IsCompact K) {f : X → V} (hf : Continuous f)
    (a : V) {U : Set X} (hU : IsOpen U) (hlevel : ∀ x ∈ K, f x = a → x ∈ U) :
    ∃ ε > 0, ∀ x ∈ K, ‖f x - a‖ < ε → x ∈ U := by
  have hbad : IsCompact (f '' (K \ U)) :=
    (hK.diff hU).image hf
  have ha : a ∈ (f '' (K \ U))ᶜ := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (hlevel x hx.1 heq)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hbad.isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨ε, hε, fun x hx hnorm => ?_⟩
  by_contra hxu
  exact hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hnorm) ⟨x, ⟨hx, hxu⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Level-only spatial transversality gives a uniform band on a compact spatial buffer. -/
theorem exists_band_margin_of_level_surjective
    (h : Y × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) (a : F)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    {Q : Set Y} (hQ : IsCompact Q) :
    ∃ ε > 0, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Q, ‖h (y, τ) - a‖ < ε →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y) := by
  obtain ⟨ε, hε, hm⟩ := exists_norm_margin_of_compact_level
    (hQ.prod isCompact_Icc) hh.continuous a (isOpen_spatial_surjective_mfderiv h hh)
    (fun x hx heq => hreg x.2 hx.2 x.1 heq)
  exact ⟨ε, hε, fun τ hτ y hy => hm (y, τ) ⟨hy, hτ⟩⟩

end DifferentialGeometry.Topology.Ehresmann
