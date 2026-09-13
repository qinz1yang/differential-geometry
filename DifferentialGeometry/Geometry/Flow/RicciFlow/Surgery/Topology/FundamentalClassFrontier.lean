import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealization
import DifferentialGeometry.Topology.Manifold.PuncturedConnected

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def noncompactThreeManifoldTopHomologyVanishing : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    [ConnectedSpace X] [NoncompactSpace X], Subsingleton (IntegralHomology X 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

omit [IsManifold ThreeModel ∞ M] in
theorem not_isOpen_singleton_of_chartedSpace (x : M) : ¬ IsOpen ({x} : Set M) := by
  intro hopen
  have hx : x ∈ (chartAt ThreeSpace x).source := mem_chart_source ThreeSpace x
  have hmem : (chartAt ThreeSpace x) '' ({x} : Set M) ∈ 𝓝 ((chartAt ThreeSpace x) x) :=
    (chartAt ThreeSpace x).image_mem_nhds hx (hopen.mem_nhds rfl)
  rw [image_singleton] at hmem
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨v, hv⟩ : ∃ v : ThreeSpace, v ≠ 0 := exists_ne 0
  let c : ℝ := r / (2 * (‖v‖ + 1))
  have hcpos : 0 < c := by positivity
  have hcle : c * ‖v‖ < r := by
    have h1 : c * (‖v‖ + 1) = r / 2 := by
      simp only [c]
      field_simp
    nlinarith [norm_nonneg v]
  have hmem2 : (chartAt ThreeSpace x) x + c • v ∈
      Metric.ball ((chartAt ThreeSpace x) x) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (chartAt ThreeSpace x) x + c • v - (chartAt ThreeSpace x) x = c • v := by
      simp
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    exact hcle
  have hne : (chartAt ThreeSpace x) x + c • v ≠ (chartAt ThreeSpace x) x := by
    intro h
    have hzero : c • v = 0 := by
      have h2 := congrArg (fun z => z - (chartAt ThreeSpace x) x) h
      simpa only [add_sub_cancel_left, sub_self] using h2
    rcases smul_eq_zero.mp hzero with h' | h'
    · exact hcpos.ne' h'
    · exact hv h'
  exact hne (mem_singleton_iff.mp (hball hmem2))

omit [IsManifold ThreeModel ∞ M] in
theorem not_isCompact_compl_singleton [T2Space M] (x : M) : ¬ IsCompact ({x}ᶜ : Set M) :=
  fun hK => not_isOpen_singleton_of_chartedSpace x (isClosed_compl_iff.mp hK.isClosed)

omit [IsManifold ThreeModel ∞ M] in
theorem noncompactSpace_compl_singleton [T2Space M] (x : M) :
    NoncompactSpace ({x}ᶜ : Set M) := by
  refine ⟨fun hc => ?_⟩
  have hrange : Subtype.val '' (univ : Set ↥({x}ᶜ : Set M)) = ({x}ᶜ : Set M) := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨y, hy⟩, trivial, rfl⟩
  have hK : IsCompact ({x}ᶜ : Set M) := by
    rw [← hrange]
    exact hc.image continuous_subtype_val
  exact not_isCompact_compl_singleton x hK

omit [IsManifold ThreeModel ∞ M] in
theorem connectedSpace_compl_singleton [ConnectedSpace M] (x : M) :
    ConnectedSpace ({x}ᶜ : Set M) := by
  have hdim : 1 < Module.rank ℝ ThreeSpace := by
    rw [← Module.finrank_eq_rank (R := ℝ) (M := ThreeSpace)]
    norm_num
  exact isConnected_iff_connectedSpace.mp
    (ChartedSpace.isPathConnected_compl_singleton (E := ThreeSpace) hdim x).isConnected

theorem subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
    [ConnectedSpace M] [T2Space M] (h : noncompactThreeManifoldTopHomologyVanishing.{u})
    (x : M) : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3) := by
  let U : TopologicalSpace.Opens M := ⟨({x}ᶜ : Set M), isClosed_singleton.isOpen_compl⟩
  have hconn : ConnectedSpace U := connectedSpace_compl_singleton (M := M) x
  have hnonc : NoncompactSpace U := noncompactSpace_compl_singleton (M := M) x
  exact h U

theorem exists_unique_fundamentalClass_of_surjective_and_injective
    (o : TangentOrientationSection M)
    [ConnectedSpace M] (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3))
    (hinj : Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_local_realization o hprop x₀
    (hsurj (localOrientationClass o x₀)) hinj

theorem exists_unique_fundamentalClass_of_noncompactThreeManifoldTopHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3))
    (h : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_surjective_and_injective o hprop x₀ hsurj
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀
      (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        h x₀))

theorem exists_fundamentalClass_generator_of_surjective_and_injective
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x₀))
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3))
    (hinj : Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃ z : IntegralHomology M 3,
      (∀ y : M, absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y) ∧
        Function.Bijective (fun k : ℤ => k • z) := by
  obtain ⟨z, hz, -⟩ :=
    exists_unique_fundamentalClass_of_surjective_and_injective o hprop x₀ hsurj hinj
  refine ⟨z, hz, ?_, ?_⟩
  · intro a b hab
    refine hlocal.injective ?_
    have h := congrArg (absoluteToRelative M ({x₀}ᶜ) 3) hab
    simpa only [map_zsmul, hz x₀] using h
  · intro w
    obtain ⟨k, hk⟩ := hlocal.surjective (absoluteToRelative M ({x₀}ᶜ) 3 w)
    exact ⟨k, hinj (by rw [map_zsmul, hz x₀]; exact hk)⟩

theorem exists_fundamentalClass_generator_of_noncompactThreeManifoldTopHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x₀))
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3))
    (h : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃ z : IntegralHomology M 3,
      (∀ y : M, absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y) ∧
        Function.Bijective (fun k : ℤ => k • z) :=
  exists_fundamentalClass_generator_of_surjective_and_injective o hprop x₀ hlocal hsurj
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀
      (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        h x₀))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
