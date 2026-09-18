import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchChartPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem isPLHomeomorphOn_iUnion_of_forall {ι : Type*} {U : ι → Set E}
    {V : ι → Set (ℝ × ℝ × ℝ)} {Φ : E → ℝ × ℝ × ℝ} (hU : ∀ i, IsOpen (U i))
    (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i)) :
    IsPLHomeomorphOn Φ (⋃ i, U i) (⋃ i, V i) := by
  have himage : Φ '' (⋃ i, U i) = ⋃ i, V i := by
    rw [image_iUnion]
    exact iUnion_congr fun i => (hPL i).image_eq
  refine ⟨himage ▸ hinj.bijOn_image, ?_, ?_⟩
  · refine isPiecewiseAffineOn_of_locally fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    refine ⟨U i, hU i, hi, ?_⟩
    rw [inter_eq_right.mpr (subset_iUnion U i)]
    exact (hPL i).isPiecewiseAffineOn
  · refine isPiecewiseAffineOn_of_locally fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    refine ⟨V i, hV i, hi, ?_⟩
    rw [inter_eq_right.mpr (subset_iUnion V i)]
    refine ((hPL i).isPiecewiseAffineOn_invFunOn).congr fun w hw => ?_
    have h1 : Function.invFunOn Φ (U i) w ∈ U i := (hPL i).bijOn.surjOn.mapsTo_invFunOn hw
    have h2 : Φ (Function.invFunOn Φ (U i) w) = w := (hPL i).bijOn.invOn_invFunOn.2 hw
    have hwU : w ∈ Φ '' (⋃ i, U i) := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hw⟩
    have h3 : Function.invFunOn Φ (⋃ i, U i) w ∈ ⋃ i, U i :=
      (hinj.bijOn_image).surjOn.mapsTo_invFunOn hwU
    have h4 : Φ (Function.invFunOn Φ (⋃ i, U i) w) = w :=
      (hinj.bijOn_image).invOn_invFunOn.2 hwU
    exact hinj h3 (mem_iUnion.mpr ⟨i, h1⟩) (h4.trans h2.symm)

omit [FiniteDimensional ℝ E] in
theorem exists_chart_branch_chain {ι : Type*} {U : ι → Set E} {V : ι → Set (ℝ × ℝ × ℝ)}
    {Φ : E → ℝ × ℝ × ℝ} {A B S T W : Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i))
    (hA : ∀ i, ∀ y ∈ U i, y ∈ A → (Φ y).2.2 = 0)
    (hB : ∀ i, ∀ y ∈ U i, y ∈ B → (Φ y).2.1 = 0)
    (hthird : ∀ i, U i ∩ T = ∅)
    (hSU : S ⊆ ⋃ i, U i) (hUW : (⋃ i, U i) ⊆ W) :
    ∃ O : Set E, IsOpen O ∧ S ⊆ O ∧ O ⊆ W ∧ O ∩ T = ∅ ∧
      IsPLHomeomorphOn Φ O (⋃ i, V i) ∧
        (∀ y ∈ O, y ∈ A → (Φ y).2.2 = 0) ∧ (∀ y ∈ O, y ∈ B → (Φ y).2.1 = 0) := by
  refine ⟨⋃ i, U i, isOpen_iUnion hU, hSU, hUW, ?_,
    isPLHomeomorphOn_iUnion_of_forall hU hV hPL hinj, ?_, ?_⟩
  · rw [iUnion_inter]
    exact iUnion_eq_empty.mpr hthird
  · intro y hy hyA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hA i y hi hyA
  · intro y hy hyB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hB i y hi hyB

theorem exists_openPartialHomeomorph_branch_chain {ι : Type*} {U : ι → Set E}
    {V : ι → Set (ℝ × ℝ × ℝ)} {Φ : E → ℝ × ℝ × ℝ} {A B S T W : Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hPL : ∀ i, IsPLHomeomorphOn Φ (U i) (V i)) (hinj : InjOn Φ (⋃ i, U i))
    (hA : ∀ i, ∀ y ∈ U i, y ∈ A → (Φ y).2.2 = 0)
    (hB : ∀ i, ∀ y ∈ U i, y ∈ B → (Φ y).2.1 = 0)
    (hthird : ∀ i, U i ∩ T = ∅)
    (hSU : S ⊆ ⋃ i, U i) (hUW : (⋃ i, U i) ⊆ W) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ), S ⊆ e.source ∧ e.source ⊆ W ∧
      e.source ∩ T = ∅ ∧ IsPiecewiseAffineOn e e.source ∧
        IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0) ∧
            (∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0) := by
  have hglue := isPLHomeomorphOn_iUnion_of_forall hU hV hPL hinj
  refine ⟨hglue.toOpenPartialHomeomorph (isOpen_iUnion hU) (isOpen_iUnion hV), hSU, hUW, ?_,
    hglue.isPiecewiseAffineOn, hglue.isPiecewiseAffineOn_invFunOn, ?_, ?_⟩
  · change (⋃ i, U i) ∩ T = ∅
    rw [iUnion_inter]
    exact iUnion_eq_empty.mpr hthird
  · intro y hy hyA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hA i y hi hyA
  · intro y hy hyB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hB i y hi hyB

end DifferentialGeometry.Topology.PiecewiseLinear
