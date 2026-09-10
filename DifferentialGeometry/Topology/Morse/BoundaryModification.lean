import DifferentialGeometry.Topology.Morse.BoundaryPerturbation
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Manifold.FunctionExtension
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

open Set in
private theorem mem_interior_iff_pos_of_halfspace_chart
    {M : Type*} [TopologicalSpace M] {n : ℕ}
    (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Fin (n + 1) → ℝ))
    (c : U ≃ₜ V) (D : Set M)
    (hD : ∀ x : U, (x : M) ∈ D ↔ 0 ≤ (c x).val 0) (x : U) :
    (x : M) ∈ interior D ↔ 0 < (c x).val 0 := by
  let q : U → ℝ := fun y => (c y).val 0
  have hq : Continuous q :=
    (continuous_apply 0).comp (continuous_subtype_val.comp c.continuous)
  have ho : IsOpenMap q :=
    (isOpenMap_eval 0).comp (V.isOpen.isOpenMap_subtype_val.comp c.isOpenMap)
  have hset : (Subtype.val : U → M) ⁻¹' D = q ⁻¹' Ici 0 := by
    ext y
    exact hD y
  change x ∈ (Subtype.val : U → M) ⁻¹' interior D ↔ x ∈ q ⁻¹' Ioi 0
  have hU : (Subtype.val : U → M) ⁻¹' interior D =
      interior ((Subtype.val : U → M) ⁻¹' D) :=
    U.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val D
  rw [hU, hset,
    ← ho.preimage_interior_eq_interior_preimage hq (Ici 0), interior_Ici]

open Set in
private theorem fderiv_eq_of_eqOn_halfspace
    {n : ℕ} {F G : (Fin (n + 1) → ℝ) → ℝ}
    {V : Set (Fin (n + 1) → ℝ)} {x : Fin (n + 1) → ℝ}
    (hV : IsOpen V) (hxV : x ∈ V) (hx : 0 ≤ x 0)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (heq : EqOn F G (V ∩ {z | 0 ≤ z 0})) :
    fderiv ℝ F x = fderiv ℝ G x := by
  have hu : UniqueDiffOn ℝ {z : Fin (n + 1) → ℝ | 0 ≤ z 0} := by
    simpa only [Set.pi, mem_singleton_iff, forall_eq, mem_Ici] using
      (UniqueDiffOn.pi (I := ({0} : Set (Fin (n + 1))))
        (s := fun _ : Fin (n + 1) => Ici (0 : ℝ))
        (fun _ _ => uniqueDiffOn_Ici 0))
  have hs : UniqueDiffWithinAt ℝ (V ∩ {z | 0 ≤ z 0}) x := by
    simpa only [inter_comm] using (hu x hx).inter (hV.mem_nhds hxV)
  rw [← fderivWithin_eq_fderiv hs hF, ← fderivWithin_eq_fderiv hs hG]
  exact fderivWithin_congr' heq ⟨hxV, hx⟩

private theorem mfderiv_eq_of_halfspace_chart
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (F : (Fin (n + 1) → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hmodel : ∀ y : U, 0 ≤ (c y).val 0 → g y = F (c y))
    (x : U) (hx : 0 ≤ (c x).val 0) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ)
      (fun z : V => g (c.symm z)) (c x) = fderiv ℝ F (c x).val := by
  let f : V → ℝ := fun z => g (c.symm z)
  have hf : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) ∞ f :=
    (hg.comp contMDiff_subtype_val).comp c.symm.contMDiff
  let G : (Fin (n + 1) → ℝ) → ℝ := Subtype.val.extend f 0
  have hGval (z : V) : G z = f z := Subtype.val_injective.extend_apply f 0 z
  have hGeq : (fun z : V => G z) = f := funext hGval
  have hGsm : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) ∞ G (c x).val := by
    apply (contMDiffAt_subtype_iff (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) (x := c x)).mp
    rw [hGeq]
    exact hf.contMDiffAt
  have hGdiff := (contMDiffAt_iff_contDiffAt.mp hGsm).differentiableAt (by simp)
  have heq : Set.EqOn G F ((V : Set (Fin (n + 1) → ℝ)) ∩ {z | 0 ≤ z 0}) := by
    intro z hz
    rw [hGval ⟨z, hz.1⟩]
    have hm := hmodel (c.symm ⟨z, hz.1⟩) (by
      simpa only [c.apply_symm_apply, Set.mem_ofPred_eq] using hz.2)
    simpa only [f, c.apply_symm_apply] using hm
  have hder := fderiv_eq_of_eqOn_halfspace V.isOpen (c x).property hx hGdiff
    (hF.differentiable (by simp) (c x).val) heq
  change mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) f (c x) = _
  rw [← hGeq]
  change mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) (G ∘ Subtype.val) (c x) = _
  rw [mfderiv_comp (c x) (hGsm.mdifferentiableAt (by simp))
    (hasMFDerivAt_subtype_val (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) V (c x)).mdifferentiableAt]
  apply ContinuousLinearMap.ext
  intro v
  change mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) G (c x).val
    (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ)
      (Subtype.val : V → (Fin (n + 1) → ℝ)) (c x) v) = _
  rw [mfderiv_subtype_val_apply]
  rw [mfderiv_eq_fderiv, hder]
  rfl

private theorem isCriticalPointAt_iff_of_halfspace_chart
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (F : (Fin (n + 1) → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hmodel : ∀ y : U, 0 ≤ (c y).val 0 → g y = F (c y))
    (x : U) (hx : 0 ≤ (c x).val 0) :
    IsCriticalPointAt I g (x : M) ↔
      IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) F (c x).val := by
  calc
    IsCriticalPointAt I g (x : M) ↔ IsCriticalPointAt I (fun y : U => g y) x :=
      (isCriticalPointAt_subtype_iff U (f := g) (x := x)).symm
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) (fun z : V => g (c.symm z)) (c x) := by
      simpa only [c.symm_apply_apply, Function.comp_def] using
        (isCriticalPointAt_comp_diffeomorph_iff c.symm (by simp)
          (f := fun y : U => g y) (x := c x)).symm
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) F (c x).val := by
      simp only [IsCriticalPointAt, mfderiv_eq_of_halfspace_chart c g hg F hF hmodel x hx,
        mfderiv_eq_fderiv]
      rfl

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

theorem exists_pos_isCriticalPointAt_boundaryMorseChart_iff
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    {r : ℕ∞ω} (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V r) (hr : r ≠ 0)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) (v : ℝ) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ g : M → ℝ,
      (∀ y : U, 0 ≤ (c y).val 0 → g y = v + boundaryMorsePerturbation d b a (c y)) →
      ∀ x : U, 0 < (c x).val 0 →
        (IsCriticalPointAt I g (x : M) ↔ (c x).val = Fin.cons (a / 2) 0) := by
  obtain ⟨δ, hδ, hcritical⟩ := exists_pos_boundaryMorsePerturbation_critical d hd b
  refine ⟨δ, hδ, ?_⟩
  intro a ha g hmodel x hx
  let F := fun z : V => g (c.symm z)
  let G := fun z : V => v + boundaryMorsePerturbation d b a z
  have heq : F =ᶠ[𝓝 (c x)] G := by
    have ho : IsOpen {z : V | 0 < (z : Fin (n + 1) → ℝ) 0} :=
      isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val)
    filter_upwards [ho.mem_nhds hx] with z hz
    have hm := hmodel (c.symm z) (by simpa only [c.apply_symm_apply] using hz.le)
    simpa only [F, G, c.apply_symm_apply] using hm
  calc
    IsCriticalPointAt I g (x : M) ↔ IsCriticalPointAt I (fun y : U => g y) x :=
      (isCriticalPointAt_subtype_iff U (f := g) (x := x)).symm
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) F (c x) := by
      simpa only [F, c.symm_apply_apply, Function.comp_def] using
        (isCriticalPointAt_comp_diffeomorph_iff c.symm hr
          (f := fun y : U => g y) (x := c x)).symm
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) G (c x) := by
      unfold IsCriticalPointAt
      rw [heq.mfderiv_eq]
      exact Iff.rfl
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
        (fun z => v + boundaryMorsePerturbation d b a z) (c x).val :=
      isCriticalPointAt_subtype_iff (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) V
        (f := fun z => v + boundaryMorsePerturbation d b a z) (x := c x)
    _ ↔ IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
        (boundaryMorsePerturbation d b a) (c x).val := by
      simp only [IsCriticalPointAt, mfderiv_eq_fderiv, fderiv_const_add]
      exact Iff.rfl
    _ ↔ (c x).val = Fin.cons (a / 2) 0 := (hcritical a ha).1 (c x) hx.le

theorem isNondegenerateCriticalPointAt_and_sigNeg_boundaryMorseChart
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    {r : ℕ∞ω} (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V r) (hr : 2 ≤ r)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) (v : ℝ)
    {a : ℝ} (ha : 0 < a) {g : M → ℝ}
    (hmodel : ∀ y : U, 0 ≤ (c y).val 0 → g y = v + boundaryMorsePerturbation d b a (c y))
    (x : U) (hx : (c x).val = Fin.cons (a / 2) 0) :
    IsNondegenerateCriticalPointAt I g (x : M) ∧
      _root_.sigNeg (chartHessianAt (fun z => g ((extChartAt I (x : M)).symm z))
        (extChartAt I (x : M) (x : M))) = {i | d i < 0}.ncard := by
  let B := fun z : Fin (n + 1) → ℝ => v + boundaryMorsePerturbation d b a z
  let G := fun z : V => B z
  have hB : ContDiff ℝ ∞ B :=
    contDiff_const.add (contDiff_boundaryMorsePerturbation d b a)
  have hG : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) ∞ G :=
    hB.contMDiff.comp contMDiff_subtype_val
  have hG2 : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ) 2 G (c x) :=
    hG.contMDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBderiv : fderiv ℝ B = fderiv ℝ (boundaryMorsePerturbation d b a) := by
    funext z
    exact fderiv_const_add v
  have hBH (z : Fin (n + 1) → ℝ) :
      chartHessianAt B z = chartHessianAt (boundaryMorsePerturbation d b a) z := by
    ext u
    change fderiv ℝ (fderiv ℝ B) z u u =
      fderiv ℝ (fderiv ℝ (boundaryMorsePerturbation d b a)) z u u
    rw [hBderiv]
  have hPnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
      (boundaryMorsePerturbation d b a) (c x).val := by
    rw [hx]
    exact isNondegenerateCriticalPointAt_boundaryMorsePerturbation d hd b ha.ne'
  have hBcrit : IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) B (c x).val := by
    have hh := hPnd.1
    rw [IsCriticalPointAt, mfderiv_eq_fderiv] at hh ⊢
    change fderiv ℝ B (c x).val = 0
    rw [hBderiv]
    exact hh
  have hBnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) B (c x).val := by
    refine ⟨hBcrit, ?_⟩
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      PartialEquiv.refl_symm, id_eq, hBH] using hPnd.2
  have hGnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) G (c x) :=
    (isNondegenerateCriticalPointAt_subtype_iff
      (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) V (f := B) (x := c x)).mpr hBnd
  have hxpos : 0 < (c x).val 0 := by
    rw [hx]
    change 0 < a / 2
    linarith [ha]
  have heq : (fun y : U => g y) =ᶠ[𝓝 x] G ∘ c := by
    have ho : IsOpen {y : U | 0 < (c y).val 0} :=
      isOpen_lt continuous_const ((continuous_apply 0).comp
        (continuous_subtype_val.comp c.continuous))
    filter_upwards [ho.mem_nhds hxpos] with y hy
    exact hmodel y hy.le
  have hcomp : IsNondegenerateCriticalPointAt I (G ∘ c) x :=
    (isNondegenerateCriticalPointAt_comp_diffeomorph_iff c hr hG2).mpr hGnd
  have hgU : IsNondegenerateCriticalPointAt I (fun y : U => g y) x :=
    (isNondegenerateCriticalPointAt_congr_eventuallyEq (I := I) heq).mpr hcomp
  refine ⟨(isNondegenerateCriticalPointAt_subtype_iff (I := I) U).mp hgU, ?_⟩
  have ht : Filter.Tendsto (extChartAt I x).symm
      (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [ContinuousAt, extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := I) x)
  have heqChart : (fun z => g (((extChartAt I x).symm z : U) : M))
      =ᶠ[𝓝 (extChartAt I x x)] fun z => G (c ((extChartAt I x).symm z)) := by
    simpa only [Function.comp_def] using heq.comp_tendsto ht
  calc
    _ = _root_.sigNeg (chartHessianAt
        (fun z => g (((extChartAt I x).symm z : U) : M)) (extChartAt I x x)) :=
      congrArg _root_.sigNeg (chartHessianAt_subtype (I := I) U g x).symm
    _ = _root_.sigNeg (chartHessianAt (fun z => G (c ((extChartAt I x).symm z)))
        (extChartAt I x x)) :=
      congrArg _root_.sigNeg (chartHessianAt_congr_eventuallyEq heqChart)
    _ = _root_.sigNeg (chartHessianAt (fun z => G ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ)
        (c x)).symm z)) (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c x) (c x))) :=
      sigNeg_chartHessianAt_comp_diffeomorph c hr hG2 hGnd.1
    _ = _root_.sigNeg (chartHessianAt B (c x).val) := by
      rw [chartHessianAt_subtype (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) V B (c x)]
      simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        PartialEquiv.refl_symm, id_eq]
    _ = _root_.sigNeg (chartHessianAt (boundaryMorsePerturbation d b a)
        (Fin.cons (a / 2) 0)) := by rw [hBH, hx]
    _ = {i | d i < 0}.ncard := sigNeg_chartHessianAt_boundaryMorsePerturbation d b ha.le

private theorem mfderiv_boundaryMorseChart_normal_zero
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (d : Fin n → ℝ) (b : ContDiffBump (0 : Fin n → ℝ)) (v : ℝ)
    {a : ℝ} (ha : a ≠ 0)
    (hmodel : ∀ y : U, 0 ≤ (c y).val 0 →
      g y = v + boundaryMorsePerturbation d b a (c y))
    (x : U) (hx : (c x).val = 0) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ)) (g (x : M))
      (mfderiv I 𝓘(ℝ) g (x : M)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) I c.symm (c x) (Fin.cons 1 0))) = -1 := by
  have hsub : mfderiv I 𝓘(ℝ) (fun y : U => g y) x = mfderiv I 𝓘(ℝ) g (x : M) := by
    change mfderiv I 𝓘(ℝ) (g ∘ Subtype.val) x = _
    rw [mfderiv_comp x (hg.mdifferentiable (by simp) x)
      (hasMFDerivAt_subtype_val (I := I) U x).mdifferentiableAt]
    apply ContinuousLinearMap.ext
    intro w
    exact congrArg (mfderiv I 𝓘(ℝ) g (x : M)) (mfderiv_subtype_val_apply U x w)
  have heq' : mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ)
      (fun z : V => g (c.symm z)) (c x) (Fin.cons 1 0) =
      mfderiv I 𝓘(ℝ) g (x : M)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) I c.symm (c x) (Fin.cons 1 0)) := by
    have hh := mfderiv_comp_apply_of_eq (c x)
      ((hg.comp contMDiff_subtype_val).mdifferentiable (by simp) x)
      (c.symm.mdifferentiable (by simp) (c x)) (c.symm_apply_apply x) (Fin.cons 1 0)
    change mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ)
      (fun z : V => g (c.symm z)) (c x) (Fin.cons 1 0) =
      mfderiv I 𝓘(ℝ) (fun y : U => g y) x
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) I c.symm (c x) (Fin.cons 1 0)) at hh
    rw [hsub] at hh
    exact hh
  have hjet := mfderiv_eq_of_halfspace_chart c g hg
    (fun z => v + boundaryMorsePerturbation d b a z)
    (contDiff_const.add (contDiff_boundaryMorsePerturbation d b a)) hmodel x
    (by rw [hx]; exact le_rfl)
  have hcurve : HasDerivAt (fun t : ℝ => (Fin.cons t 0 : Fin (n + 1) → ℝ))
      (Fin.cons 1 0) 0 := (hasDerivAt_id 0).finCons (hasDerivAt_const 0 (0 : Fin n → ℝ))
  have hnormal := ((contDiff_boundaryMorsePerturbation d b a).differentiable (by simp)
    (Fin.cons (0 : ℝ) (0 : Fin n → ℝ))).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hr : fderiv ℝ (fun z => v + boundaryMorsePerturbation d b a z) (0 : Fin (n + 1) → ℝ)
      (Fin.cons 1 0) = -1 := by
    rw [fderiv_const_add]
    have hzero : (Fin.cons (0 : ℝ) (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) = 0 := by ext i; cases i using Fin.cases <;> rfl
    rw [hzero] at hnormal
    exact hnormal.deriv.symm.trans (deriv_boundaryMorsePerturbation_normal_zero d b ha)
  rw [← heq', hjet]
  change fderiv ℝ (fun z => v + boundaryMorsePerturbation d b a z) (c x).val
    (Fin.cons 1 0) = (-1 : ℝ)
  rw [hx]
  exact hr

theorem exists_boundaryMorsePerturbation_with_criticalPoint_in_chart
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens (Fin (n + 1) → ℝ)}
    (c : Diffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) U V ∞)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ))
    (D : Set M) (hD : ∀ x : U, (x : M) ∈ D ↔ 0 ≤ (c x).val 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (v : ℝ)
    (hchart : ∀ x : U, (x : M) ∈ D →
      f x = v + ((∑ i : Fin n, d i * (c x).val i.succ ^ 2) + (c x).val 0)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      {z : Fin (n + 1) → ℝ | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ V →
      ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧ HasCompactSupport (g - f) ∧
        tsupport (g - f) ⊆ U ∧
        (∀ x : U, (x : M) ∈ D → g x = v + boundaryMorsePerturbation d b a (c x)) ∧
        Set.EqOn g f (U : Set M)ᶜ ∧
        (∀ x ∈ D, g x - f x ∈ Set.Icc 0 (2 * a)) ∧
        ∃ p : U, (p : M) ∈ interior D ∧ (c p).val = Fin.cons (a / 2) 0 ∧
          IsNondegenerateCriticalPointAt I g (p : M) ∧
          _root_.sigNeg (chartHessianAt (fun z => g ((extChartAt I (p : M)).symm z))
            (extChartAt I (p : M) (p : M))) = {i | d i < 0}.ncard ∧
          (∀ x : U, 0 < (c x).val 0 → (IsCriticalPointAt I g (x : M) ↔ x = p)) ∧
          (∀ x ∈ D, IsCriticalPointAt I g x ↔
            x = (p : M) ∨ (x ∉ (U : Set M) ∧ IsCriticalPointAt I f x)) ∧
          ∃ q : U, (q : M) ∈ frontier D ∧ (c q).val = 0 ∧
            tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ)) (g (q : M))
              (mfderiv I 𝓘(ℝ) g (q : M)
                (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) I c.symm (c q) (Fin.cons 1 0))) = -1 := by
  obtain ⟨δ, hδ, hcritical⟩ :=
    exists_pos_boundaryMorsePerturbation_critical d hd b
  refine ⟨δ, hδ, ?_⟩
  intro a ha hbox
  obtain ⟨g, hg, hgs, hgU, hmodel, hout, hbound⟩ :=
    exists_contMDiff_boundaryMorsePerturbation_in_chart c d b D hD f hf v hchart ha.1 hbox
  have hcenter : Fin.cons (a / 2) (0 : Fin n → ℝ) ∈ V := by
    apply hbox
    simp only [Set.mem_ofPred_eq, Fin.cons_zero, Fin.tail_cons, norm_zero]
    exact ⟨by linarith [ha.1], by linarith [ha.1], b.rOut_pos.le⟩
  let p : U := c.symm ⟨Fin.cons (a / 2) 0, hcenter⟩
  have hp : (c p).val = Fin.cons (a / 2) 0 :=
    congrArg Subtype.val (c.apply_symm_apply _)
  have hp0 : 0 < (c p).val 0 := by rw [hp]; exact half_pos ha.1
  have hpD : (p : M) ∈ interior D :=
    (mem_interior_iff_pos_of_halfspace_chart U V c.toHomeomorph D hD p).mpr hp0
  have hm (x : U) (hx : 0 ≤ (c x).val 0) :
      g x = v + boundaryMorsePerturbation d b a (c x) := hmodel x ((hD x).mpr hx)
  have hnd := isNondegenerateCriticalPointAt_and_sigNeg_boundaryMorseChart c
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) d hd b v ha.1 hm p hp
  have hlocal (x : U) (hx : 0 ≤ (c x).val 0) : IsCriticalPointAt I g (x : M) ↔ x = p := by
    rw [isCriticalPointAt_iff_of_halfspace_chart c g hg
      (fun z => v + boundaryMorsePerturbation d b a z)
      (contDiff_const.add (contDiff_boundaryMorsePerturbation d b a)) hm x hx]
    have heq : IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ)
        (fun z => v + boundaryMorsePerturbation d b a z) (c x).val ↔
        IsCriticalPointAt 𝓘(ℝ, Fin (n + 1) → ℝ) (boundaryMorsePerturbation d b a) (c x).val := by
      simp only [IsCriticalPointAt, mfderiv_eq_fderiv, fderiv_const_add]
      rfl
    rw [heq, (hcritical a ha).1 (c x) hx]
    constructor
    · intro heq
      apply c.injective
      exact Subtype.ext (heq.trans hp.symm)
    · rintro rfl
      exact hp
  refine ⟨g, hg, hgs, hgU, hmodel, hout, hbound, p, hpD, hp, hnd.1, hnd.2,
    fun x hx => hlocal x hx.le, ?_, ?_⟩
  · intro x hxD
    by_cases hxU : x ∈ (U : Set M)
    · have hxnonneg := (hD ⟨x, hxU⟩).mp hxD
      rw [hlocal ⟨x, hxU⟩ hxnonneg]
      simp only [hxU, not_true_eq_false, false_and, or_false, Subtype.ext_iff]
    · have hxS : x ∉ tsupport (g - f) := fun hx => hxU (hgU hx)
      have hgf : g =ᶠ[𝓝 x] f := by
        filter_upwards [(isClosed_tsupport (g - f)).isOpen_compl.mem_nhds hxS] with y hy
        have hy0 : (g - f) y = 0 := image_eq_zero_of_notMem_tsupport hy
        exact sub_eq_zero.mp hy0
      have hxp : x ≠ (p : M) := by
        intro heq
        exact hxU (heq.symm ▸ p.property)
      simp only [IsCriticalPointAt, hgf.mfderiv_eq, hxp, false_or, hxU,
        not_false_eq_true, true_and]
      rfl
  · have hzero : (0 : Fin (n + 1) → ℝ) ∈ V := by
      apply hbox
      simp only [Set.mem_ofPred_eq, Pi.zero_apply]
      refine ⟨le_rfl, ha.1.le, ?_⟩
      change ‖(0 : Fin n → ℝ)‖ ≤ b.rOut
      simpa only [norm_zero] using b.rOut_pos.le
    let q : U := c.symm ⟨0, hzero⟩
    have hq : (c q).val = 0 := congrArg Subtype.val (c.apply_symm_apply _)
    refine ⟨q, ?_, hq, mfderiv_boundaryMorseChart_normal_zero c g hg d b v ha.1.ne' hm q hq⟩
    refine ⟨subset_closure ((hD q).mpr (by rw [hq]; exact le_rfl)), ?_⟩
    intro hqi
    have hpos := (mem_interior_iff_pos_of_halfspace_chart U V c.toHomeomorph D hD q).mp hqi
    change 0 < (c q).val 0 at hpos
    rw [hq] at hpos
    exact lt_irrefl 0 hpos

end DifferentialGeometry.Topology.Morse
