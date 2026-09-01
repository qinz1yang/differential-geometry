import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.Weights.Convergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff BigOperators Topology

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

noncomputable def bumpNum {ι : Type*} [DecidableEq ι]
    (χ : E' → Real) (ψ : ι → E' → Real) (J : ι → E' → E')
    (i0 : ι) (i : ι) (z : E') : Real :=
  if i = i0 then ψ i0 (J i0 z) else χ (J i0 z) * ψ i (J i z)

omit [NormedAddCommGroup E'] [NormedSpace Real E'] in
theorem bumpNum_nonneg {ι : Type*} [DecidableEq ι]
    {χ : E' → Real} {ψ : ι → E' → Real} {J : ι → E' → E'} {i0 : ι}
    (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t) (i : ι) (z : E') :
    0 ≤ bumpNum χ ψ J i0 i z := by
  by_cases h : i = i0 <;> simp only [bumpNum, h]
  · exact hψ i0 _
  · exact mul_nonneg (hχ _) (hψ i _)

omit [NormedAddCommGroup E'] [NormedSpace Real E'] in
theorem bumpWeights_data {ι : Type} [DecidableEq ι] [Fintype ι]
    {s : Set E'} {U : ι → Set E'} {χ : E' → Real} {ψ : ι → E' → Real}
    {J : ι → E' → E'} {i0 : ι}
    (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t)
    (hne : ∀ z ∈ s, (∑ j, bumpNum χ ψ J i0 j z) ≠ 0)
    (hactive : ∀ z ∈ s, ∀ i, bumpNum χ ψ J i0 i z ≠ 0 → z ∈ U i) :
    centerAverage.WeightDataOn s U
      (fun z i => normWeights (bumpNum χ ψ J i0) i z) :=
  normWeights_data (fun z _hz i => bumpNum_nonneg hχ hψ i z) hne hactive

omit [NormedAddCommGroup E'] [NormedSpace Real E'] in
theorem bumpNum_delta {ι : Type*} [DecidableEq ι]
    {χ : E' → Real} {ψ : ι → E' → Real} {J : ι → E' → E'}
    {i0 : ι} {x₀ : E'} (hχ0 : χ (J i0 x₀) = 0) :
    (∀ j, j ≠ i0 → bumpNum χ ψ J i0 j x₀ = 0) ∧
      bumpNum χ ψ J i0 i0 x₀ = ψ i0 (J i0 x₀) := by
  refine ⟨fun j hj => ?_, by simp [bumpNum]⟩
  simp [bumpNum, hj, hχ0]

omit [NormedAddCommGroup E'] [NormedSpace Real E'] in
theorem bumpNum_delta' {ι : Type*} [DecidableEq ι]
    {χ : E' → Real} {ψ : ι → E' → Real} {J : ι → E' → E'}
    {i0 : ι} {x₀ : E'} (hψ0 : ∀ j, j ≠ i0 → ψ j (J j x₀) = 0) :
    (∀ j, j ≠ i0 → bumpNum χ ψ J i0 j x₀ = 0) ∧
      bumpNum χ ψ J i0 i0 x₀ = ψ i0 (J i0 x₀) := by
  refine ⟨fun j hj => ?_, by simp [bumpNum]⟩
  simp [bumpNum, hj, hψ0 j hj]

theorem bumpNum_contDiffOn {ι : Type*} [DecidableEq ι]
    {U : Set E'} {χ : E' → Real} {ψ : ι → E' → Real}
    {J : ι → E' → E'} {i0 : ι}
    (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (hψ : ∀ i, ContDiff Real (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (J i) U) (i : ι) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (bumpNum χ ψ J i0 i) U := by
  by_cases h : i = i0
  · subst h
    exact ContDiffOn.congr ((hψ i).comp_contDiffOn (hJ i))
      (fun z _ => by simp [bumpNum])
  · have h1 : ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => χ (J i0 z)) U :=
      hχ.comp_contDiffOn (hJ i0)
    have h2 : ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => ψ i (J i z)) U :=
      (hψ i).comp_contDiffOn (hJ i)
    exact ContDiffOn.congr (h1.mul h2) (fun z _ => by simp [bumpNum, h])

theorem bumpNumConv {ι : Type*} [DecidableEq ι] [ProperSpace E']
    {U : Set E'} (hU : IsOpen U)
    {χ : E' → Real} {ψ : ι → E' → Real}
    {J : ι → Nat → E' → E'} {Jinf : ι → E' → E'} {i0 : ι}
    (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (hψ : ∀ i, ContDiff Real (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, MapCInfConvOnCompacts U (J i) (Jinf i))
    (hJc : ∀ i k, ContDiffOn Real (∞ : WithTop ℕ∞) (J i k) U)
    (hJinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf i) U) (i : ι) :
    MapCInfConvOnCompacts U (fun k => bumpNum χ ψ (fun j => J j k) i0 i)
      (bumpNum χ ψ Jinf i0 i) := by
  have hread : ∀ (g : E' → Real), ContDiff Real (∞ : WithTop ℕ∞) g → ∀ j : ι,
      MapCInfConvOnCompacts U (fun k z => g (J j k z)) (fun z => g (Jinf j z)) := by
    intro g hg j
    exact MapCInfConvOnCompacts.comp hU isOpen_univ (hJ j)
      (mapCInfConv_const (U := (Set.univ : Set E')) g) (hJc j) (hJinfc j)
      (fun _ => hg.contDiffOn) hg.contDiffOn
      (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  by_cases h : i = i0
  · subst h
    have := hread (ψ i) (hψ i) i
    refine this.congr hU (fun k z _ => ?_) (fun z _ => ?_) <;> simp [bumpNum]
  · have h1 := hread χ hχ i0
    have h2 := hread (ψ i) (hψ i) i
    have hmul := mapCInfConv_mul hU h1 h2
      (fun k => hχ.comp_contDiffOn (hJc i0 k)) (hχ.comp_contDiffOn (hJinfc i0))
      (fun k => (hψ i).comp_contDiffOn (hJc i k)) ((hψ i).comp_contDiffOn (hJinfc i))
    refine hmul.congr hU (fun k z _ => ?_) (fun z _ => ?_) <;> simp [bumpNum, h]

theorem bumpNumDeltaOfNorm {ι : Type*} [DecidableEq ι] [HasContDiffBump E']
    {χ : E' → Real} (f : ι → ContDiffBump (0 : E'))
    {J : ι → E' → E'} {i0 : ι} {x₀ : E'}
    (hfar : ∀ j, j ≠ i0 → (f j).rOut ≤ ‖J j x₀‖) :
    (∀ j, j ≠ i0 → bumpNum χ (fun i => ⇑(f i)) J i0 j x₀ = 0) ∧
      bumpNum χ (fun i => ⇑(f i)) J i0 i0 x₀ = f i0 (J i0 x₀) :=
  bumpNum_delta' (fun j hj => (f j).zero_of_le_dist
    (by rw [dist_zero_right]; exact hfar j hj))

theorem bumpNumLowOfMem {ι : Type*} [DecidableEq ι] [HasContDiffBump E']
    {χ : E' → Real} (f : ι → ContDiffBump (0 : E'))
    {J : ι → E' → E'} {i0 : ι} {z : E'} {j : ι} {δ : Real}
    (hmem : ‖J j z‖ ≤ (f j).rIn)
    (hχδ : j ≠ i0 → δ ≤ χ (J i0 z)) (hδ1 : j = i0 → δ ≤ 1) :
    δ ≤ bumpNum χ (fun i => ⇑(f i)) J i0 j z := by
  have hone : f j (J j z) = 1 :=
    (f j).one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hmem)
  by_cases h : j = i0
  · subst h
    simpa [bumpNum, hone] using hδ1 rfl
  · simpa [bumpNum, h, hone] using hχδ h

omit [NormedAddCommGroup E'] [NormedSpace Real E'] in
theorem bumpNum_sum_low {ι : Type*} [DecidableEq ι] [Fintype ι]
    {χ : E' → Real} {ψ : ι → E' → Real} {J : ι → E' → E'} {i0 : ι}
    (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t)
    {z : E'} {δ : Real} (h : ∃ j, δ ≤ bumpNum χ ψ J i0 j z) :
    δ ≤ ∑ j, bumpNum χ ψ J i0 j z := by
  obtain ⟨j, hj⟩ := h
  exact le_trans hj (Finset.single_le_sum
    (fun j' _ => bumpNum_nonneg hχ hψ j' z) (Finset.mem_univ j))

theorem bumpNum_sum_one {ι : Type*} [DecidableEq ι] [Fintype ι]
    [HasContDiffBump E'] {χ : E' → Real} (f : ι → ContDiffBump (0 : E'))
    {J : ι → E' → E'} {i0 : ι} {z : E'}
    (hχ : ∀ t, 0 ≤ χ t)
    (hcover : ∃ j, ‖J j z‖ ≤ (f j).rIn)
    (hbase : χ (J i0 z) ≠ 1 → ‖J i0 z‖ ≤ (f i0).rIn) :
    1 ≤ ∑ j, bumpNum χ (fun i => ⇑(f i)) J i0 j z := by
  apply bumpNum_sum_low hχ (fun i t => (f i).nonneg)
  by_cases hχ1 : χ (J i0 z) = 1
  · obtain ⟨j, hj⟩ := hcover
    refine ⟨j, bumpNumLowOfMem f hj ?_ ?_⟩
    · intro _hj
      rw [hχ1]
    · intro _hj
      exact le_rfl
  · refine ⟨i0, bumpNumLowOfMem f (hbase hχ1) ?_ ?_⟩
    · intro hi
      exact (hi rfl).elim
    · intro _hi
      exact le_rfl

theorem weightsSlot {ι : Type*} [DecidableEq ι] [Fintype ι] [ProperSpace E']
    {U : Set E'} (hU : IsOpen U)
    {χ : E' → Real} {ψ : ι → E' → Real}
    {J : ι → Nat → E' → E'} {Jinf : ι → E' → E'} {i0 : ι}
    {δ : Real} (hδ : 0 < δ)
    (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (hψ : ∀ i, ContDiff Real (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, MapCInfConvOnCompacts U (J i) (Jinf i))
    (hJc : ∀ i k, ContDiffOn Real (∞ : WithTop ℕ∞) (J i k) U)
    (hJinfc : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf i) U)
    (hlow : ∀ k, ∀ z ∈ U, δ < ∑ j, bumpNum χ ψ (fun j' => J j' k) i0 j z)
    (hlowinf : ∀ z ∈ U, δ < ∑ j, bumpNum χ ψ Jinf i0 j z) (i : ι)
    (kn : Nat → Nat) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U
      (fun n => normWeights (bumpNum χ ψ (fun j => J j (kn n)) i0) i)
      (normWeights (bumpNum χ ψ Jinf i0) i) := by
  have hsingle : MapCInfConvOnCompacts U
      (fun k => normWeights (bumpNum χ ψ (fun j => J j k) i0) i)
      (normWeights (bumpNum χ ψ Jinf i0) i) := by
    refine normWeightsConv hU hδ (fun j => bumpNumConv hU hχ hψ hJ hJc hJinfc j)
      (fun k j => bumpNum_contDiffOn hχ hψ (fun j' => hJc j' k) j)
      (fun j => bumpNum_contDiffOn hχ hψ hJinfc j) hlow hlowinf i
  exact hsingle.comp_tendsto_atTop hkn

end HCGCompactness
end DifferentialGeometry
