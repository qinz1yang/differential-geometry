import DifferentialGeometry.Topology.PiecewiseLinear.Approximation
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Topology Filter
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold (AtlasOn)

universe u

variable {n : ℕ}

section Bridge

variable {X : Type u} [MetricSpace X] [SecondCountableTopology X]

theorem exists_atlasOn_union_of_plApproximation (hA : PLApproximation.{u} n) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (A : AtlasOn (plGroupoid n) U)
    (B : AtlasOn (plGroupoid n) V) : Nonempty (AtlasOn (plGroupoid n) (U ∪ V)) := by
  classical
  set O := U ∩ V with hO_def
  have hO : IsOpen O := hU.inter hV
  let φ : X → ℝ := fun x => if Oᶜ.Nonempty then Metric.infDist x Oᶜ / 2 else 1
  have hφcont : ContinuousOn φ O := by
    by_cases hne : Oᶜ.Nonempty
    · have hrepr : φ = fun x => Metric.infDist x Oᶜ / 2 := by
        ext x
        simp [φ, hne]
      rw [hrepr]
      exact ((Metric.continuous_infDist_pt _).div_const 2).continuousOn
    · have hrepr : φ = fun _ => 1 := by
        ext x
        simp [φ, hne]
      rw [hrepr]
      exact continuousOn_const
  have hφpos : ∀ x ∈ O, 0 < φ x := by
    intro x hx
    by_cases hne : Oᶜ.Nonempty
    · have hpos : 0 < Metric.infDist x Oᶜ :=
        (hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (notMem_compl_iff.mpr hx)
      change 0 < (if Oᶜ.Nonempty then Metric.infDist x Oᶜ / 2 else 1)
      rw [if_pos hne]
      positivity
    · change 0 < (if Oᶜ.Nonempty then Metric.infDist x Oᶜ / 2 else 1)
      rw [if_neg hne]
      exact one_pos
  obtain ⟨f, hfs, hft, hfφ, hfPL⟩ := hA (A.restrict hV) (B.restrict hU)
    (OpenPartialHomeomorph.ofSet O hO) rfl (inter_comm U V) φ hφcont hφpos
  have hfO : ∀ x ∈ O, f x ∈ O := by
    intro x hx
    have hx' : x ∈ f.source := by rw [hfs]; exact hx
    have := f.map_source hx'
    rw [hft] at this
    exact ⟨this.2, this.1⟩
  have hfsO : ∀ y ∈ O, f.symm y ∈ O := by
    intro y hy
    have hy' : y ∈ f.target := by rw [hft]; exact ⟨hy.2, hy.1⟩
    have := f.map_target hy'
    rwa [hfs] at this
  have hfl : ∀ x ∈ O, f.symm (f x) = x := fun x hx => f.left_inv (by rw [hfs]; exact hx)
  have hfr : ∀ y ∈ O, f (f.symm y) = y :=
    fun y hy => f.right_inv (by rw [hft]; exact ⟨hy.2, hy.1⟩)
  have hclose : ∀ x ∈ O, Oᶜ.Nonempty → dist x (f x) < Metric.infDist x Oᶜ / 2 := by
    intro x hx hne
    have h := hfφ x hx
    change dist (f x) x < (if Oᶜ.Nonempty then Metric.infDist x Oᶜ / 2 else 1) at h
    rw [if_pos hne, dist_comm] at h
    exact h
  let Ff : X → X := fun x => if x ∈ O then f x else x
  let Fi : X → X := fun x => if x ∈ O then f.symm x else x
  have hFf_mem : ∀ x ∈ O, Ff x = f x := fun x hx => if_pos hx
  have hFf_not : ∀ x, x ∉ O → Ff x = x := fun x hx => if_neg hx
  have hFi_mem : ∀ x ∈ O, Fi x = f.symm x := fun x hx => if_pos hx
  have hFi_not : ∀ x, x ∉ O → Fi x = x := fun x hx => if_neg hx
  have hleft : ∀ x, Fi (Ff x) = x := by
    intro x
    by_cases hx : x ∈ O
    · rw [hFf_mem x hx, hFi_mem _ (hfO x hx), hfl x hx]
    · rw [hFf_not x hx, hFi_not x hx]
  have hright : ∀ y, Ff (Fi y) = y := by
    intro y
    by_cases hy : y ∈ O
    · rw [hFi_mem y hy, hFf_mem _ (hfsO y hy), hfr y hy]
    · rw [hFi_not y hy, hFf_not y hy]
  have hcontF : Continuous Ff := by
    rw [continuous_iff_continuousAt]
    intro x₀
    by_cases hx₀ : x₀ ∈ O
    · have hev : f =ᶠ[𝓝 x₀] Ff := by
        filter_upwards [hO.mem_nhds hx₀] with x hx using (hFf_mem x hx).symm
      exact (f.continuousAt (by rw [hfs]; exact hx₀)).congr hev
    · rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨ε / 2, by positivity, ?_⟩
      intro x hx
      rw [hFf_not x₀ hx₀]
      by_cases hxO : x ∈ O
      · rw [hFf_mem x hxO]
        have hne : Oᶜ.Nonempty := ⟨x₀, hx₀⟩
        have h1 := hclose x hxO hne
        have h2 : Metric.infDist x Oᶜ ≤ dist x x₀ := Metric.infDist_le_dist_of_mem hx₀
        calc dist (f x) x₀ ≤ dist (f x) x + dist x x₀ := dist_triangle _ _ _
          _ < ε := by rw [dist_comm (f x) x]; linarith
      · rw [hFf_not x hxO]
        linarith
  have hcontFi : Continuous Fi := by
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : y₀ ∈ O
    · have hev : f.symm =ᶠ[𝓝 y₀] Fi := by
        filter_upwards [hO.mem_nhds hy₀] with y hy using (hFi_mem y hy).symm
      exact (f.symm.continuousAt
        (by rw [OpenPartialHomeomorph.symm_source, hft]; exact ⟨hy₀.2, hy₀.1⟩)).congr hev
    · rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨ε / 2, by positivity, ?_⟩
      intro y hy
      rw [hFi_not y₀ hy₀]
      by_cases hyO : y ∈ O
      · rw [hFi_mem y hyO]
        have hxO : f.symm y ∈ O := hfsO y hyO
        have hne : Oᶜ.Nonempty := ⟨y₀, hy₀⟩
        have h1 := hclose _ hxO hne
        rw [hfr y hyO] at h1
        have h2 : Metric.infDist (f.symm y) Oᶜ ≤ dist (f.symm y) y₀ :=
          Metric.infDist_le_dist_of_mem hy₀
        have h3 : dist (f.symm y) y₀ ≤ dist (f.symm y) y + dist y y₀ := dist_triangle _ _ _
        linarith
      · rw [hFi_not y hyO]
        linarith
  let F : X ≃ₜ X :=
    { toFun := Ff, invFun := Fi, left_inv := hleft, right_inv := hright,
      continuous_toFun := hcontF, continuous_invFun := hcontFi }
  have hF : ∀ x, F x = Ff x := fun _ => rfl
  have hFU : F '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxO : x ∈ O
      · rw [hF, hFf_mem x hxO]
        exact (hfO x hxO).1
      · rw [hF, hFf_not x hxO]
        exact hx
    · intro hy
      by_cases hyO : y ∈ O
      · refine ⟨f.symm y, (hfsO y hyO).1, ?_⟩
        rw [hF, hFf_mem _ (hfsO y hyO), hfr y hyO]
      · exact ⟨y, hy, by rw [hF, hFf_not y hyO]⟩
  refine ⟨((A.transport F).congr hFU).union B ?_⟩
  rintro _ ⟨e, he, rfl⟩ e' he'
  have hG := hfPL (e.restrOpen V hV) ⟨e, he, rfl⟩ (e'.restrOpen U hU) ⟨e', he', rfl⟩
  refine (plGroupoid n).mem_of_eqOnSource hG ?_
  have hkey : ∀ x ∈ e.source, F x ∈ e'.source → x ∈ O := by
    intro x hx hFx
    by_contra hxO
    rw [hF, hFf_not x hxO] at hFx
    exact hxO ⟨A.source_subset e he hx, B.source_subset e' he' hFx⟩
  have hL : ∀ y, y ∈ ((F.symm.toOpenPartialHomeomorph ≫ₕ e).symm ≫ₕ e').source ↔
      y ∈ e.target ∧ F (e.symm y) ∈ e'.source := by
    intro y
    constructor
    · rintro ⟨⟨hy, -⟩, hFy⟩
      exact ⟨hy, hFy⟩
    · rintro ⟨hy, hFy⟩
      exact ⟨⟨hy, trivial⟩, hFy⟩
  have hR : ∀ y, y ∈ ((e.restrOpen V hV).symm ≫ₕ f ≫ₕ e'.restrOpen U hU).source ↔
      y ∈ e.target ∧ e.symm y ∈ V ∧ e.symm y ∈ O ∧ f (e.symm y) ∈ e'.source ∧
        f (e.symm y) ∈ U := by
    intro y
    constructor
    · rintro ⟨⟨hy, hyV⟩, hyf, hfe, hfU⟩
      refine ⟨hy, hyV, ?_, hfe, hfU⟩
      have hyf' : e.symm y ∈ f.source := hyf
      rw [hfs] at hyf'
      exact hyf'
    · rintro ⟨hy, hyV, hyO, hfe, hfU⟩
      refine ⟨⟨hy, hyV⟩, ?_, hfe, hfU⟩
      change e.symm y ∈ f.source
      rw [hfs]
      exact hyO
  refine ⟨?_, ?_⟩
  · ext y
    rw [hL, hR]
    constructor
    · rintro ⟨hy, hFy⟩
      have hxO : e.symm y ∈ O := hkey _ (e.map_target hy) hFy
      rw [hF, hFf_mem _ hxO] at hFy
      exact ⟨hy, hxO.2, hxO, hFy, (hfO _ hxO).1⟩
    · rintro ⟨hy, -, hxO, hfy, -⟩
      refine ⟨hy, ?_⟩
      rw [hF, hFf_mem _ hxO]
      exact hfy
  · intro y hy
    obtain ⟨hy, hFy⟩ := (hL y).mp hy
    have hxO : e.symm y ∈ O := hkey _ (e.map_target hy) hFy
    change e' (F (e.symm y)) = e' (f (e.symm y))
    rw [hF, hFf_mem _ hxO]

theorem exists_atlasOn_union_of_plApproximation_of_metrizable (hA : PLApproximation.{u} n)
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (A : AtlasOn (plGroupoid n) U) (B : AtlasOn (plGroupoid n) V) :
    Nonempty (AtlasOn (plGroupoid n) (U ∪ V)) := by
  have hsc : SecondCountableTopology Y := inferInstance
  let _ : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  have hsc' : SecondCountableTopology Y := hsc
  exact exists_atlasOn_union_of_plApproximation hA hU hV A B

end Bridge

section Induction

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem exists_atlasOn_univ_of_plApproximation (hA : PLApproximation.{u} n) :
    Nonempty (AtlasOn (plGroupoid n) (univ : Set X)) := by
  classical
  have hsc : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (H := EuclideanSpace ℝ (Fin n)) (M := X)
  have hlc : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin n)) (M := X)
  have key : ∀ s : Finset X,
      Nonempty (AtlasOn (plGroupoid n)
        (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) x).source)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨(AtlasOn.empty _).congr (by simp)⟩
    | insert a s _ ih =>
      obtain ⟨A⟩ := ih
      have hUopen : IsOpen (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :=
        isOpen_biUnion fun x _ => (chartAt _ x).open_source
      set e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) :=
        chartAt (EuclideanSpace ℝ (Fin n)) a with he
      obtain ⟨C⟩ := exists_atlasOn_union_of_plApproximation_of_metrizable hA hUopen
        e.open_source A (AtlasOn.ofOpenPartialHomeomorph e)
      exact ⟨C.congr (by rw [Finset.set_biUnion_insert, union_comm])⟩
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := X)).elim_nhds_subcover
    (fun x : X => (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    fun x _ => chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨A⟩ := key t
  exact ⟨A.congr (univ_subset_iff.mp ht)⟩

theorem exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation
    (hA : PLApproximation.{u} n) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
      letI := C
      HasGroupoid X (plGroupoid n) := by
  obtain ⟨A⟩ := exists_atlasOn_univ_of_plApproximation (X := X) hA
  exact ⟨A.chartedSpace, A.hasGroupoid⟩

end Induction

end DifferentialGeometry.Topology.PiecewiseLinear
