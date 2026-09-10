import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ManifoldLocalFlow
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.InwardField
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.CurveUniqueness

open Set Function Filter Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar

private theorem finite_positive_time {α : Type*} (a : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 < f x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ a, ε ≤ f x := by
  classical
  induction a using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x a _ ih =>
    obtain ⟨ε, hε, ha⟩ := ih
    refine ⟨min (f x) ε, lt_min (hf x) hε, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ha y hy)

private theorem integralCurveOn_congr_eqOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) {V : (y : M) → TangentSpace I y}
    {γ η : ℝ → M} {s : Set ℝ} (hγ : IsMIntegralCurveOn γ V s)
    (he : EqOn η γ s) : IsMIntegralCurveOn η V s := by
  intro t ht
  have hd := (hγ t ht).congr_mono he (he ht) subset_rfl
  apply hd.congr_mfderiv
  exact congrArg (fun v : E => (1 : ℝ →L[ℝ] ℝ).smulRight v)
    (congrArg (show M → E from V) (he ht).symm)

theorem exists_uniform_boundary_flow_of_inward
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M]
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ U : TopologicalSpace.Opens M, (𝓡∂ (n + 1)).boundary M ⊆ U ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ F : M × ℝ → M,
        ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
          ((U : Set M) ×ˢ Icc (0 : ℝ) ε) ∧
        (∀ y ∈ U, F (y, 0) = y) ∧
        (∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (Icc (0 : ℝ) ε)) ∧
        (∀ y ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (y, t))) ∧
        ∀ t ∈ Icc (0 : ℝ) ε, InjOn (fun y => F (y, t)) U := by
  classical
  let I := 𝓡∂ (n + 1)
  have hlocal := fun p : BoundaryManifold (𝓡∂ (n + 1)) M =>
    exists_inward_manifold_localFlow p.2 hV (hpos p)
  choose O hO τ hτ Φ hΦ hzero hcurve hi _ _ using hlocal
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover (fun p => (O p : Set M))
    (fun p => (O p).isOpen) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hO ⟨y, hy⟩⟩)
  obtain ⟨ε, hε, hετ⟩ := finite_positive_time a τ hτ
  let U : TopologicalSpace.Opens M :=
    ⟨⋃ p ∈ a, (O p : Set M), isOpen_iUnion fun p => isOpen_iUnion fun _ => (O p).isOpen⟩
  have hindex : ∀ y ∈ U, ∃ p, p ∈ a ∧ y ∈ O p := by
    intro y hy
    change y ∈ ⋃ p ∈ a, (O p : Set M) at hy
    obtain ⟨p, hyp⟩ := mem_iUnion.mp hy
    obtain ⟨hp, hyp⟩ := mem_iUnion.mp hyp
    exact ⟨p, hp, hyp⟩
  let F : M × ℝ → M := fun q => if hy : q.1 ∈ U then
    Φ (hindex q.1 hy).choose q else q.1
  have hsub (p) (hp : p ∈ a) : Icc (0 : ℝ) ε ⊆ Icc (0 : ℝ) (τ p) :=
    Icc_subset_Icc le_rfl (hετ p hp)
  have hagree (p) (hp : p ∈ a) (y : M) (hy : y ∈ O p) :
      EqOn (fun t => F (y, t)) (fun t => Φ p (y, t)) (Icc (0 : ℝ) ε) := by
    have hyU : y ∈ U := mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, hy⟩⟩
    let q := (hindex y hyU).choose
    have hq : q ∈ a ∧ y ∈ O q := (hindex y hyU).choose_spec
    have heq := isMIntegralCurveOn_Icc_unique_of_interior hV hε
      ((hcurve q y hq.2).mono (hsub q hq.1)) ((hcurve p y hy).mono (hsub p hp))
      (fun t ht => hi q y hq.2 t ⟨ht.1, ht.2.le.trans (hετ q hq.1)⟩)
      ((hzero q y hq.2).trans (hzero p y hy).symm)
    intro t ht
    change (if h : y ∈ U then Φ (hindex y h).choose (y, t) else y) = Φ p (y, t)
    rw [dif_pos hyU]
    exact heq ht
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ F
      ((U : Set M) ×ˢ Icc (0 : ℝ) ε) := by
    intro q hq
    obtain ⟨p, hp, hqp⟩ := hindex q.1 hq.1
    have hOevent : ∀ᶠ r : M × ℝ in 𝓝 q, r.1 ∈ O p :=
      ((O p).isOpen.preimage continuous_fst).mem_nhds hqp
    have hmem : (O p : Set M) ×ˢ Icc (0 : ℝ) (τ p) ∈
        𝓝[(U : Set M) ×ˢ Icc (0 : ℝ) ε] q := by
      filter_upwards [hOevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrU
      exact ⟨hr, hsub p hp hrU.2⟩
    have hbase := ((hΦ p) q ⟨hqp, hsub p hp hq.2⟩).mono_of_mem_nhdsWithin hmem
    apply hbase.congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [hOevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrU
    exact hagree p hp r.1 hr hrU.2
  have hFzero : ∀ y ∈ U, F (y, 0) = y := by
    intro y hy
    obtain ⟨p, hp, hyp⟩ := hindex y hy
    exact (hagree p hp y hyp ⟨le_rfl, hε.le⟩).trans (hzero p y hyp)
  have hFcurve : ∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (Icc (0 : ℝ) ε) := by
    intro y hy
    obtain ⟨p, hp, hyp⟩ := hindex y hy
    exact integralCurveOn_congr_eqOn I ((hcurve p y hyp).mono (hsub p hp)) (hagree p hp y hyp)
  have hFint : ∀ y ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, I.IsInteriorPoint (F (y, t)) := by
    intro y hy t ht
    obtain ⟨p, hp, hyp⟩ := hindex y hy
    have he : F (y, t) = Φ p (y, t) := hagree p hp y hyp ⟨ht.1.le, ht.2⟩
    rw [he]
    exact hi p y hyp t ⟨ht.1, ht.2.trans (hετ p hp)⟩
  refine ⟨U, ha, ε, hε, F, hF, hFzero, hFcurve, hFint, ?_⟩
  intro t ht y hy z hz he
  by_cases ht0 : t = 0
  · simpa only [ht0, hFzero y hy, hFzero z hz] using he
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hts : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) ε := Icc_subset_Icc le_rfl ht.2
    have heq := isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right hV htp
      ((hFcurve y hy).mono hts) ((hFcurve z hz).mono hts)
      (fun s hs => hFint y hy s ⟨hs.1, hs.2.le.trans ht.2⟩) he
    simpa only [hFzero y hy, hFzero z hz] using heq ⟨le_rfl, htp.le⟩

theorem exists_uniform_positive_boundary_flow
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      IsCompact (tsupport V) ∧
      (∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
        0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p)) ∧
      ∃ U : TopologicalSpace.Opens M, (𝓡∂ (n + 1)).boundary M ⊆ U ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ F : M × ℝ → M,
          ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
            ((U : Set M) ×ˢ Icc (0 : ℝ) ε) ∧
          (∀ y ∈ U, F (y, 0) = y) ∧
          (∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (Icc (0 : ℝ) ε)) ∧
          (∀ y ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (y, t))) ∧
          ∀ t ∈ Icc (0 : ℝ) ε, InjOn (fun y => F (y, t)) U := by
  obtain ⟨V, hV, hVK, hnormal⟩ := exists_smooth_inwardField hK
  have hpos := fun p => (hnormal p).1
  exact ⟨V, hV, hVK, hpos, exists_uniform_boundary_flow_of_inward hV hpos hK⟩

end Poincare.Manifold.BoundaryCollar
