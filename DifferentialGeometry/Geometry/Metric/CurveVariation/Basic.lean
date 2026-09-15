import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UnitInterval

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

def riemannianCurveVariation (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
    ∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))

theorem riemannianCurveVariation_comp_le (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b := by
  unfold riemannianCurveVariation
  refine iSup_le fun p => ?_
  calc
    _ ≤ ∑ i ∈ Finset.range p.1,
        (L : ℝ≥0∞) * riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
      Finset.sum_le_sum fun i _ => hf _ _
    _ = (L : ℝ≥0∞) * ∑ i ∈ Finset.range p.1,
        riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right (α := ℝ≥0∞)
      (le_iSup (fun q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc a b} =>
        ∑ i ∈ Finset.range q.1,
          riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p) (L : ℝ≥0∞)

section CurveLengthVariation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [RegularSpace M']

theorem riemannianCurveVariation_eq_eVariationOn
    (g : SmoothRiemannianMetric I' M') (γ : ℝ → M') (a b : ℝ) :
    riemannianCurveVariation g γ a b =
      (letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E' (TangentSpace I' : M' → Type _) :=
         ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : PseudoEMetricSpace M' := .ofRiemannianMetric I' M'
       eVariationOn γ (Icc a b)) := rfl

end CurveLengthVariation

theorem riemannianCurveVariation_mono (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    riemannianCurveVariation g γ c d ≤ riemannianCurveVariation g γ a b := by
  simp only [riemannianCurveVariation]
  refine iSup_le fun p => ?_
  exact le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} =>
      ∑ i ∈ Finset.range q.1,
        riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)))
    ⟨p.1, ⟨p.2.1, p.2.2.1,
      fun i => ⟨hac.trans (p.2.2.2 i).1, (p.2.2.2 i).2.trans hdb⟩⟩⟩

theorem riemannianCurveVariation_comp_le_of_local [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N)
    (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveVariation g γ a b ≠ ⊤ →
      riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b)
    {γ : ℝ → M} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hfin : riemannianCurveVariation g γ a b ≠ ⊤) :
    riemannianCurveVariation h (f ∘ γ) a b ≤ L * riemannianCurveVariation g γ a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  rw [riemannianCurveVariation_eq_eVariationOn g γ a b,
    riemannianCurveVariation_eq_eVariationOn h (f ∘ γ) a b]
  by_cases hab : a ≤ b
  · have hloc' : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
        ∀ (c d : ℝ) (η : ℝ → M), c ≤ d → ContinuousOn η (Icc c d) →
          MapsTo η (Icc c d) V → riemannianCurveVariation g η c d ≠ ⊤ →
          eVariationOn (f ∘ η) (Icc c d) ≤ (L : ℝ≥0∞) * eVariationOn η (Icc c d) := by
      intro x
      obtain ⟨U, hU, hUU⟩ := hloc x
      refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
      intro c d η hcd hη hmap hfind
      have h1 := hUU c d η hcd hη (fun t ht => interior_subset (hmap ht)) hfind
      rwa [riemannianCurveVariation_eq_eVariationOn h (f ∘ η) c d,
        riemannianCurveVariation_eq_eVariationOn g η c d] at h1
    choose V hVo hxV hfV using hloc'
    let curve : Icc a b → M := fun t => γ t
    have hc : Continuous curve := hγ.domRestrict
    obtain ⟨t, ht0, htm, ⟨n, htn⟩, htV⟩ :=
      exists_monotone_Icc_subset_open_cover_Icc hab
        (c := fun i => curve ⁻¹' V i)
        (fun i => hc.isOpen_preimage _ (hVo i))
        (by intro z _; exact mem_iUnion.mpr ⟨curve z, hxV (curve z)⟩)
    let u : ℕ → ℝ := fun i => (t i : ℝ)
    have hu : Monotone u := fun i j hij => htm hij
    have hu0 : u 0 = a := ht0
    have hun : u n = b := htn n le_rfl
    have hpiece (i : ℕ) : eVariationOn (f ∘ γ) (Icc (u i) (u (i + 1))) ≤
        (L : ℝ≥0∞) * eVariationOn γ (Icc (u i) (u (i + 1))) := by
      obtain ⟨j, hj⟩ := htV i
      refine hfV j (u i) (u (i + 1)) γ (hu (Nat.le_succ i)) ?_ ?_ ?_
      · exact hγ.mono (Icc_subset_Icc (t i).2.1 (t (i + 1)).2.2)
      · intro z hz
        have hzab : z ∈ Icc a b :=
          ⟨(t i).2.1.trans hz.1, hz.2.trans (t (i + 1)).2.2⟩
        have hmem : (⟨z, hzab⟩ : Icc a b) ∈ Icc (t i) (t (i + 1)) := ⟨hz.1, hz.2⟩
        exact hj hmem
      · exact ne_top_of_le_ne_top hfin
          (riemannianCurveVariation_mono g γ (t i).2.1 (t (i + 1)).2.2)
    calc eVariationOn (f ∘ γ) (Icc a b)
        = ∑ i ∈ Finset.range n, eVariationOn (f ∘ γ) (Icc (u i) (u (i + 1))) := by
          rw [eVariationOn.sum' (f ∘ γ) hu, hu0, hun]
      _ ≤ ∑ i ∈ Finset.range n,
            (L : ℝ≥0∞) * eVariationOn γ (Icc (u i) (u (i + 1))) :=
          Finset.sum_le_sum fun i _ => hpiece i
      _ = (L : ℝ≥0∞) * eVariationOn γ (Icc a b) := by
          rw [← Finset.mul_sum, eVariationOn.sum' γ hu, hu0, hun]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simp


theorem riemannianEDistOf_le_riemannianCurveVariation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    riemannianEDistOf g (γ a) (γ b) ≤ riemannianCurveVariation g γ a b := by
  let u : ℕ → ℝ := fun n => if n = 0 then a else b
  have hu : Monotone u := by
    intro m n hmn
    simp only [u]
    split_ifs with hm hn hn
    · exact le_rfl
    · exact hab
    · exact (hm (Nat.eq_zero_of_le_zero (hn ▸ hmn))).elim
    · exact le_rfl
  have hs : ∀ n, u n ∈ Icc a b := by
    intro n
    simp only [u]
    split_ifs
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  have h := le_iSup (f := fun p : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc a b} =>
    ∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))) ⟨1, ⟨u, hu, hs⟩⟩
  simpa only [Finset.sum_range_one, u, Nat.zero_eq, ↓reduceIte, Nat.zero_add, Nat.one_ne_zero,
    riemannianEDistOf_comm, riemannianCurveVariation] using h

theorem riemannianCurveVariation_le_pathELength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    (let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     riemannianCurveVariation g γ a b ≤ pathELength I γ a b) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  unfold riemannianCurveVariation
  refine iSup_le fun p => ?_
  obtain ⟨n, ⟨u, hu, hs⟩⟩ := p
  have htele : ∀ n : ℕ, ∑ i ∈ Finset.range n, pathELength I γ (u i) (u (i + 1)) =
      pathELength I γ (u 0) (u n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pathELength_add (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]
  calc ∑ i ∈ Finset.range n, riemannianEDistOf g (γ (u (i + 1))) (γ (u i))
      ≤ ∑ i ∈ Finset.range n, pathELength I γ (u i) (u (i + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [riemannianEDistOf_comm]
        exact riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc (hs i).1 (hs (i + 1)).2)) rfl rfl (hu (Nat.le_succ i))
    _ = pathELength I γ (u 0) (u n) := htele n
    _ ≤ pathELength I γ a b := pathELength_mono (hs 0).1 (hs n).2
theorem riemannianCurveVariation_eq_zero_of_apply_eq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} {q : M}
    (h : ∀ t ∈ Icc a b, γ t = q) : riemannianCurveVariation g γ a b = 0 := by
  unfold riemannianCurveVariation
  refine le_antisymm (iSup_le fun p => ?_) bot_le
  have hsum : (∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [h _ (p.2.2.2 (i + 1)), h _ (p.2.2.2 i)]
      exact riemannianEDistOf_self g q
  rw [hsum]

theorem riemannianCurveVariation_comp_le_of_mapsTo
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N)
    (U : Set M) {ell : ℝ}
    (hf : ∀ y ∈ U, ∀ z ∈ U, riemannianEDistOf h (f y) (f z) ≤
      ENNReal.ofReal ell * riemannianEDistOf g y z)
    (γ : ℝ → M) (a b : ℝ) (hγ : MapsTo γ (Icc a b) U) :
    riemannianCurveVariation h (fun t => f (γ t)) a b ≤
      ENNReal.ofReal ell * riemannianCurveVariation g γ a b := by
  unfold riemannianCurveVariation
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1,
        riemannianEDistOf h (f (γ (p.2.1 (i + 1)))) (f (γ (p.2.1 i)))
      ≤ ∑ i ∈ Finset.range p.1, ENNReal.ofReal ell *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ =>
          hf _ (hγ (p.2.2.2 (i + 1))) _ (hγ (p.2.2.2 i))
    _ = ENNReal.ofReal ell * ∑ i ∈ Finset.range p.1,
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        (Finset.mul_sum ..).symm
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
          ENNReal.ofReal ell * ∑ i ∈ Finset.range q.1,
            riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) :=
        le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} =>
          ENNReal.ofReal ell * ∑ i ∈ Finset.range q.1,
            riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

theorem riemannianCurveVariation_congr
    (g : SmoothRiemannianMetric I M) {γ δ : ℝ → M} {a b : ℝ}
    (heq : EqOn γ δ (Icc a b)) :
    riemannianCurveVariation g γ a b = riemannianCurveVariation g δ a b := by
  unfold riemannianCurveVariation
  apply iSup_congr
  intro p
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq (p.2.2.2 i), heq (p.2.2.2 (i + 1))]


end DifferentialGeometry.Geometry
