import DifferentialGeometry.Topology.Morse.BoundaryPerturbation
import DifferentialGeometry.Topology.Manifold.FunctionExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

private theorem exists_contDiff_boundaryMorsePerturbation_sub
    {n : ℕ} (d : Fin n → ℝ) (b : ContDiffBump (0 : Fin n → ℝ))
    {a : ℝ} (ha : 0 < a) {V : Set (Fin (n + 1) → ℝ)} (hV : IsOpen V)
    (hbox : {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V) :
    ∃ k : (Fin (n + 1) → ℝ) → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      tsupport k ⊆ V ∧ ∀ z, 0 ≤ z 0 →
        k z = boundaryMorsePerturbation d b a z - ((∑ i : Fin n, d i * z i.succ ^ 2) + z 0) := by
  let B : Set (Fin (n + 1) → ℝ) :=
    {z | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut}
  have hB : IsCompact B := by
    have hcons : Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) :=
      Continuous.finCons (A := fun _ : Fin (n + 1) => ℝ) continuous_fst continuous_snd
    have heq : B = (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) ''
        (Set.Icc 0 a ×ˢ Metric.closedBall 0 b.rOut) := by
      ext z
      constructor
      · intro hz
        exact ⟨(z 0, Fin.tail z), ⟨⟨hz.1, hz.2.1⟩,
          by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2.2⟩,
          Fin.cons_self_tail z⟩
      · rintro ⟨⟨u, x⟩, ⟨hu, hx⟩, rfl⟩
        exact ⟨hu.1, hu.2, by simpa only [Metric.mem_closedBall, dist_zero_right, Fin.tail_cons] using hx⟩
    rw [heq]
    exact (isCompact_Icc.prod (isCompact_closedBall _ _)).image hcons
  obtain ⟨C, hC, hBC, hCV⟩ := exists_compact_between hB hV hbox
  obtain ⟨η, hηzero, hηone, hηrange⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, Fin (n + 1) → ℝ)
      isOpen_interior.isClosed_compl hB.isClosed
      (Set.disjoint_left.mpr (fun z hz hzB => hz (hBC hzB))) (n := ⊤)
  let k := fun z => η z *
    (boundaryMorsePerturbation d b a z - ((∑ i : Fin n, d i * z i.succ ^ 2) + z 0))
  have hkC : tsupport k ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro z hz
    by_contra hzC
    have hη : η z = 0 := hηzero (fun hzi => hzC (interior_subset hzi))
    exact hz (by simp only [k, hη, zero_mul])
  refine ⟨k, ?_, hC.of_isClosed_subset (isClosed_tsupport k) hkC, hkC.trans hCV, ?_⟩
  · apply (contMDiff_iff_contDiff.mp η.contMDiff).mul
    exact (contDiff_boundaryMorsePerturbation d b a).sub (by fun_prop)
  · intro z hz
    by_cases hzB : z ∈ B
    · change η z * _ = _
      rw [hηone hzB]
      exact one_mul _
    · have hout : a ≤ z 0 ∨ b.rOut ≤ ‖Fin.tail z‖ := by
        by_cases hza : z 0 ≤ a
        · exact Or.inr (le_of_not_ge (fun hnorm => hzB ⟨hz, hza, hnorm⟩))
        · exact Or.inl (le_of_not_ge hza)
      have heq : boundaryMorsePerturbation d b a z =
          (∑ i : Fin n, d i * z i.succ ^ 2) + z 0 := by
        rcases hout with h | h
        · exact boundaryMorsePerturbation_eq_of_le d b ha z h
        · exact boundaryMorsePerturbation_eq_of_le_norm d b a z h
      simp only [k, heq, sub_self, mul_zero]

theorem exists_contMDiff_boundaryMorsePerturbation_in_chart
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (d : Fin n → ℝ) (b : ContDiffBump (0 : Fin n → ℝ))
    (D : Set M) (hD : ∀ x : U, (x : M) ∈ D ↔ 0 ≤ (c x).val 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (v : ℝ)
    (hchart : ∀ x : U, (x : M) ∈ D →
      f x = v + ((∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0))
    {a : ℝ} (ha : 0 < a)
    (hbox : {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧ HasCompactSupport (g - f) ∧
      tsupport (g - f) ⊆ U ∧
      (∀ x : U, (x : M) ∈ D → g x = v + boundaryMorsePerturbation d b a (c x)) ∧
      Set.EqOn g f (U : Set M)ᶜ ∧ ∀ x ∈ D, g x - f x ∈ Set.Icc 0 (2 * a) := by
  obtain ⟨k, hk, hks, hkV, hkhalf⟩ :=
    exists_contDiff_boundaryMorsePerturbation_sub d b ha V.isOpen hbox
  obtain ⟨h, hh, hhs, hhc, hhimage, hhU, hhzero⟩ :=
    Diffeomorph.exists_contMDiff_extension_of_hasCompactSupport c hk.contMDiff.contMDiffOn hks hkV
  let g := fun x => f x + h x
  have hdiff : g - f = h := by
    funext x
    exact add_sub_cancel_left (f x) (h x)
  have hformula (x : U) (hx : (x : M) ∈ D) :
      g x = v + boundaryMorsePerturbation d b a (c x) := by
    dsimp [g]
    rw [hhc x, hkhalf (c x) ((hD x).mp hx), hchart x hx]
    ring
  have hout : Set.EqOn g f (U : Set M)ᶜ := by
    intro x hx
    dsimp [g]
    rw [hhzero hx, Pi.zero_apply, add_zero]
  refine ⟨g, hf.add hh, hdiff.symm ▸ hhs, hdiff.symm ▸ hhU, hformula, hout, ?_⟩
  intro x hx
  by_cases hxU : x ∈ U
  · rw [hformula ⟨x, hxU⟩ hx, hchart ⟨x, hxU⟩ hx, add_sub_add_left_eq_sub]
    exact boundaryMorsePerturbation_sub_mem_Icc d b ha (c ⟨x, hxU⟩)
      ((hD ⟨x, hxU⟩).mp hx)
  · rw [hout hxU, sub_self]
    exact ⟨le_rfl, by positivity⟩

end DifferentialGeometry.Topology.Morse
