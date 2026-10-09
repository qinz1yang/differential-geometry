import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WeightedDisplacement

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology NNReal

namespace DifferentialGeometry.Analysis

theorem norm_iteratedFDeriv_weighted_displacement_sub_translate_le_of_active_bounds
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : Finset ι) {U : Set H} (hU : IsOpen U)
    {w : ι → H → ℝ} {Q : H → H →L[ℝ] H} {m : ℕ}
    (hw : ∀ i ∈ S, ContDiffOn ℝ m (w i) U)
    (hw1 : ∀ y ∈ U, ∑ i ∈ S, w i y = 1)
    (hQ : ContDiffOn ℝ m Q U) (P : H →L[ℝ] H) (c : ι → H) (o : H)
    {x : H} (hx : x ∈ U) {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (A B D R a : ℝ≥0)
    (hwjet : ∀ j, j ≤ m → (∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖) ≤ B * (r⁻¹) ^ j)
    (hQjet : ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => Q y - P) x‖ ≤ A * δ * (r⁻¹) ^ j)
    (hc : ∀ i ∈ S, (∃ y ∈ U, w i y ≠ 0) → ‖c i - o‖ ≤ D * r)
    (hPc : ∀ i ∈ S, (∃ y ∈ U, w i y ≠ 0) → ‖P (c i - o)‖ ≤ a * δ * r)
    (hxnorm : ‖x - o‖ ≤ R * r) :
    ∀ n, n ≤ m →
      ‖iteratedFDeriv ℝ n
        (fun z => Q z (z - ∑ i ∈ S, w i z • c i) - P (z - o)) x‖ ≤
          ((2 : ℝ) ^ n * A * (max (R : ℝ) 1 + D * B) + a * B) *
            δ * r * (r⁻¹) ^ n := by
  classical
  let J : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
  have hJS : J ⊆ S := Finset.filter_subset _ _
  have hzero (i : ι) (hi : i ∈ S) (hnot : i ∉ J) (y : H) (hy : y ∈ U) :
      w i y = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hi, y, hy, hne⟩)
  have hweights (y : H) (hy : y ∈ U) : (∑ i ∈ J, w i y) = 1 := by
    have heq : (∑ i ∈ J, w i y) = ∑ i ∈ S, w i y :=
      Finset.sum_subset hJS (fun i hi hnot => hzero i hi hnot y hy)
    exact heq.trans (hw1 y hy)
  have hsum (y : H) (hy : y ∈ U) :
      (∑ i ∈ S, w i y • c i) = ∑ i ∈ J, w i y • c i := by
    exact (Finset.sum_subset hJS (fun i hi hnot => by
      rw [hzero i hi hnot y hy, zero_smul])).symm
  have hjetzero (j : ℕ) (i : ι) (hi : i ∈ S) (hnot : i ∉ J) :
      iteratedFDeriv ℝ j (w i) x = 0 := by
    have heq : w i =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hzero i hi hnot y hy
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (heq.iteratedFDeriv ℝ j).self_of_nhds
  let V : Set H := (fun z : H => o + z) ⁻¹' U
  let w' : ι → H → ℝ := fun i z => w i (o + z)
  let Q' : H → H →L[ℝ] H := fun z => Q (o + z)
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hox : o + (x - o) = x := by abel
  have hxV : x - o ∈ V := by change o + (x - o) ∈ U; rw [hox]; exact hx
  have hw' (i : ι) (hi : i ∈ J) : ContDiffOn ℝ m (w' i) V :=
    (hw i (hJS hi)).comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz)
  have hQ' : ContDiffOn ℝ m Q' V :=
    hQ.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz)
  have hwtrans (i : ι) (j : ℕ) :
      iteratedFDeriv ℝ j (w' i) (x - o) = iteratedFDeriv ℝ j (w i) x := by
    simpa only [w', hox] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := w i) j o (x - o))
  have hwjet' (j : ℕ) (hj : j ≤ m) :
      (∑ i ∈ J, ‖iteratedFDeriv ℝ j (w' i) (x - o)‖) ≤ B * (r⁻¹) ^ j := by
    simp only [hwtrans]
    have heq : (∑ i ∈ J, ‖iteratedFDeriv ℝ j (w i) x‖) =
        ∑ i ∈ S, ‖iteratedFDeriv ℝ j (w i) x‖ :=
      Finset.sum_subset hJS (fun i hi hnot => by rw [hjetzero j i hi hnot, norm_zero])
    rw [heq]
    exact hwjet j hj
  have hQjet' (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z => Q' z - P) (x - o)‖ ≤ A * δ * (r⁻¹) ^ j := by
    have heq := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun y => Q y - P) j o (x - o)
    change iteratedFDeriv ℝ j (fun z => Q' z - P) (x - o) = _ at heq
    rw [heq, hox]
    exact hQjet j hj
  have hlocal := norm_iteratedFDeriv_weighted_displacement_sub_le J hV hw' hQ' P
    (fun i => c i - o) hxV hr hδ A B D R a hwjet' hQjet'
    (fun i hi => hc i (hJS hi) (Finset.mem_filter.mp hi).2)
    (fun i hi => hPc i (hJS hi) (Finset.mem_filter.mp hi).2) hxnorm
  let f : H → H := fun z => Q z (z - ∑ i ∈ S, w i z • c i) - P (z - o)
  have heq : (fun z => Q' z (z - ∑ i ∈ J, w' i z • (c i - o)) - P z)
      =ᶠ[𝓝 (x - o)] (fun z => f (o + z)) := by
    filter_upwards [hV.mem_nhds hxV] with z hz
    have hzU : o + z ∈ U := hz
    have hcenters : (∑ i ∈ J, w i (o + z) • (c i - o)) =
        (∑ i ∈ J, w i (o + z) • c i) - o := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hweights (o + z) hzU,
        one_smul]
    have hargs : z - (∑ i ∈ J, w i (o + z) • (c i - o)) =
        (o + z) - ∑ i ∈ S, w i (o + z) • c i := by
      rw [hcenters, hsum (o + z) hzU]
      abel
    change Q (o + z) (z - ∑ i ∈ J, w i (o + z) • (c i - o)) - P z =
      Q (o + z) ((o + z) - ∑ i ∈ S, w i (o + z) • c i) - P ((o + z) - o)
    rw [hargs, show (o + z) - o = z by abel]
  intro n hn
  have h := hlocal n hn
  rw [(heq.iteratedFDeriv ℝ n).self_of_nhds] at h
  rw [iteratedFDeriv_comp_add_left, hox] at h
  exact h

end DifferentialGeometry.Analysis
