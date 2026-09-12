import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Topology.Connected.FiniteEDistance
import DifferentialGeometry.Geometry.Metric.WeakLength
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

def riemannianCurveLength (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
    ∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))

theorem riemannianCurveLength_comp_le (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  unfold riemannianCurveLength
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

section ChartedSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M]

theorem regularSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : WeaklyLocallyCompactSpace M := inferInstance
  have : R1Space M := T2Space.r1Space
  infer_instance

theorem sigmaCompactSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    [SecondCountableTopology M] : SigmaCompactSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

end ChartedSpaceInstances

section CurveLengthVariation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [RegularSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_eq_eVariationOn
    (g : SmoothRiemannianMetric I' M') (γ : ℝ → M') (a b : ℝ) :
    riemannianCurveLength g γ a b =
      (letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E' (TangentSpace I' : M' → Type _) :=
         ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : PseudoEMetricSpace M' := .ofRiemannianMetric I' M'
       eVariationOn γ (Icc a b)) := rfl

end CurveLengthVariation

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_mono (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    riemannianCurveLength g γ c d ≤ riemannianCurveLength g γ a b := by
  simp only [riemannianCurveLength]
  refine iSup_le fun p => ?_
  exact le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} =>
      ∑ i ∈ Finset.range q.1,
        riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)))
    ⟨p.1, ⟨p.2.1, p.2.2.1,
      fun i => ⟨hac.trans (p.2.2.2 i).1, (p.2.2.2 i).2.trans hdb⟩⟩⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_comp_le_of_local [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : C(M, N))
    (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {γ : ℝ → M} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hfin : riemannianCurveLength g γ a b ≠ ⊤) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  rw [riemannianCurveLength_eq_eVariationOn g γ a b,
    riemannianCurveLength_eq_eVariationOn h (f ∘ γ) a b]
  by_cases hab : a ≤ b
  · have hloc' : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
        ∀ (c d : ℝ) (η : ℝ → M), c ≤ d → ContinuousOn η (Icc c d) →
          MapsTo η (Icc c d) V → riemannianCurveLength g η c d ≠ ⊤ →
          eVariationOn (f ∘ η) (Icc c d) ≤ (L : ℝ≥0∞) * eVariationOn η (Icc c d) := by
      intro x
      obtain ⟨U, hU, hUU⟩ := hloc x
      refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
      intro c d η hcd hη hmap hfind
      have h1 := hUU c d η hcd hη (fun t ht => interior_subset (hmap ht)) hfind
      rwa [riemannianCurveLength_eq_eVariationOn h (f ∘ η) c d,
        riemannianCurveLength_eq_eVariationOn g η c d] at h1
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
          (riemannianCurveLength_mono g γ (t i).2.1 (t (i + 1)).2.2)
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


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_riemannianCurveLength [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    riemannianEDistOf g (γ a) (γ b) ≤ riemannianCurveLength g γ a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  rw [riemannianCurveLength_eq_eVariationOn]
  exact eVariationOn.edist_le γ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_le_pathELength [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    (let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     riemannianCurveLength g γ a b ≤ pathELength I γ a b) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  unfold riemannianCurveLength
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
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem rfs_local_to_global_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ConnectedSpace M] [ConnectedSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have hMreg : RegularSpace M := regularSpace_of_chartedSpace I
  have hNreg : RegularSpace N := regularSpace_of_chartedSpace J
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  intro x y
  have hMpre : PreconnectedSpace M := ConnectedSpace.toPreconnectedSpace
  have hgfin : riemannianEDistOf g x y ≠ ⊤ :=
    DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y
  let Admissible : Type _ :=
    {γ : ℝ → M // γ 0 = x ∧ γ 1 = y ∧ ContinuousOn γ (Icc 0 1) ∧
      riemannianCurveLength g γ 0 1 ≠ ⊤}
  have hne : Nonempty Admissible := by
    obtain ⟨r, hr1, hr2⟩ := exists_between (lt_top_iff_ne_top.mpr hgfin)
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    exact ⟨⟨γ, hγ0, hγ1, hγsm.continuousOn,
      ne_top_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt hγlen)⟩⟩
  have hinner : riemannianEDistOf h (f x) (f y) ≤
      ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 := by
    refine le_iInf fun γ => ?_
    have h1 : riemannianEDistOf h (f (γ.1 0)) (f (γ.1 1)) ≤
        riemannianCurveLength h (f ∘ γ.1) 0 1 :=
      riemannianEDistOf_le_riemannianCurveLength h (f ∘ γ.1) (by norm_num)
    rw [γ.2.1, γ.2.2.1] at h1
    exact h1.trans (riemannianCurveLength_comp_le_of_local g h f L hloc γ.2.2.2.1 γ.2.2.2.2)
  have hstep : ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 =
      (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 := by
    rw [ENNReal.mul_iInf' (fun hL _ => absurd hL ENNReal.coe_ne_top) (fun _ => hne)]
  have hle : ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 ≤
      riemannianEDistOf g x y := by
    refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    obtain ⟨r', hr1, hr2⟩ := exists_between hr
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    have hfin : riemannianCurveLength g γ 0 1 ≠ ⊤ :=
      ne_top_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt hγlen)
    refine (iInf_le (fun γ : Admissible => riemannianCurveLength g γ.1 0 1)
      ⟨γ, hγ0, hγ1, hγsm.continuousOn, hfin⟩).trans ?_
    exact le_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt (hγlen.trans hr2))
  calc riemannianEDistOf h (f x) (f y)
      ≤ ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 := hinner
    _ = (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 := hstep
    _ ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y := mul_le_mul_right hle _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem rfs_local_to_global_length_of_ne_top [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {x y : M} (hgfin : riemannianEDistOf g x y ≠ ⊤) :
    riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have hMreg : RegularSpace M := regularSpace_of_chartedSpace I
  have hNreg : RegularSpace N := regularSpace_of_chartedSpace J
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  let Admissible : Type _ :=
    {γ : ℝ → M // γ 0 = x ∧ γ 1 = y ∧ ContinuousOn γ (Icc 0 1) ∧
      riemannianCurveLength g γ 0 1 ≠ ⊤}
  have hne : Nonempty Admissible := by
    obtain ⟨r, hr1, hr2⟩ := exists_between (lt_top_iff_ne_top.mpr hgfin)
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    exact ⟨⟨γ, hγ0, hγ1, hγsm.continuousOn,
      ne_top_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt hγlen)⟩⟩
  have hinner : riemannianEDistOf h (f x) (f y) ≤
      ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 := by
    refine le_iInf fun γ => ?_
    have h1 : riemannianEDistOf h (f (γ.1 0)) (f (γ.1 1)) ≤
        riemannianCurveLength h (f ∘ γ.1) 0 1 :=
      riemannianEDistOf_le_riemannianCurveLength h (f ∘ γ.1) (by norm_num)
    rw [γ.2.1, γ.2.2.1] at h1
    exact h1.trans (riemannianCurveLength_comp_le_of_local g h f L hloc γ.2.2.2.1 γ.2.2.2.2)
  have hstep : ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 =
      (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 := by
    rw [ENNReal.mul_iInf' (fun hL _ => absurd hL ENNReal.coe_ne_top) (fun _ => hne)]
  have hle : ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 ≤
      riemannianEDistOf g x y := by
    refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    obtain ⟨r', hr1, hr2⟩ := exists_between hr
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr1
    have hfin : riemannianCurveLength g γ 0 1 ≠ ⊤ :=
      ne_top_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt hγlen)
    refine (iInf_le (fun γ : Admissible => riemannianCurveLength g γ.1 0 1)
      ⟨γ, hγ0, hγ1, hγsm.continuousOn, hfin⟩).trans ?_
    exact le_of_lt ((riemannianCurveLength_le_pathELength g hγsm).trans_lt (hγlen.trans hr2))
  calc riemannianEDistOf h (f x) (f y)
      ≤ ⨅ (γ : Admissible), (L : ℝ≥0∞) * riemannianCurveLength g γ.1 0 1 := hinner
    _ = (L : ℝ≥0∞) * ⨅ (γ : Admissible), riemannianCurveLength g γ.1 0 1 := hstep
    _ ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y := mul_le_mul_right hle _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem rfs_local_to_global_length_of_ne_zero [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0) (hL : L ≠ 0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  intro x y
  by_cases hfin : riemannianEDistOf g x y = ⊤
  · rw [hfin, ENNReal.mul_top (by simpa using hL)]
    exact le_top
  · exact rfs_local_to_global_length_of_ne_top g h f L hloc hfin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem rfs_weak_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N))
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ L * riemannianEDistOf g y z)
    (hdf : letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
      ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤ g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    riemannianCurveLength h (f ∘ γ) a b ≤ riemannianCurveLength g γ a b := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : SigmaCompactSpace M := sigmaCompactSpace_of_chartedSpace I
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : RegularSpace N := regularSpace_of_chartedSpace J
  have : SigmaCompactSpace N := sigmaCompactSpace_of_chartedSpace J
  have hf : ∀ p : M, ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y :=
    fun p => let ⟨U, hU, L, hL⟩ := hloc p; ⟨L, U, hU, hL⟩
  have hdf' : ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J (f : M → N) x → ∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J (f : M → N) x v)
          (mfderiv I J (f : M → N) x v)) ≤ Real.sqrt (g.inner x v v) := by
    filter_upwards [hdf] with x hx hxd v
    exact Real.sqrt_le_sqrt (hx hxd v)
  have hmain := DifferentialGeometry.Geometry.Metric.eVariationOn_comp_le_of_ae_mfderiv
    g h (f : M → N) hf hdf' γ a b hγ
  rw [← riemannianCurveLength_eq_eVariationOn h (f ∘ γ) a b,
    ← riemannianCurveLength_eq_eVariationOn g γ a b] at hmain
  exact hmain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
