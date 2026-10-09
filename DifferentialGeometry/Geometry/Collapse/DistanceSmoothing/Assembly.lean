import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalApproximation
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveSoulDiffeomorph
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound

/-!
# Partition-of-unity assembly of local smoothings (LC28, tier T2)

`exists_smoothing_of_local_approximations`: let `f` be `K`-Lipschitz on a complete Riemannian
manifold, `U` open and `C ⊆ U` compact. Suppose every `b ∈ U` has an open relatively compact
`W ∋ b` inside `U` on which, for every `η > 0`, some `f'` smooth on `W` is `η`-close to `f`, with
`f' - f` `L_d`-Lipschitz and `f'` `L_a`-Lipschitz on `W`. Then for all `e, ε' > 0` there is `F`,
smooth on an open neighbourhood of `C`, with `|F - f| < e`, `F = f` off `U`,
`Lip(F - f) ≤ L_d + ε'` and `Lip F ≤ max K L_a + ε'` (both for the Riemannian distance).

The cut-off error `Σ_i |dψ_i| |f_i - f|` is made smaller than `ε'` by choosing the approximation
error after the partition of unity; the global bounds follow from local ones along minimizing
geodesics (`lipschitzWith_of_locally_riemannian`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] in
/-- A smooth function with compact support is Lipschitz for the Riemannian distance. -/
theorem exists_lipschitzWith_of_contMDiff_hasCompactSupport (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) [ConnectedSpace M] {ψ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ)
    (hcs : HasCompactSupport ψ) : ∃ K : ℝ≥0, LipschitzWith K ψ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_constant_of_smooth_compact_support g
    (riemannianMetricComplete_of_isMetricNorm g hEnorm) hψ hcs
  refine ⟨K, fun x y => ?_⟩
  have h := hK x y
  rwa [riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I)] at h

/-- Partition-of-unity assembly of local smoothings with Lipschitz control. -/
theorem exists_smoothing_of_local_approximations (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) {Ld La : ℝ}
    (hLd : 0 ≤ Ld)
    (hloc : ∀ b ∈ U, ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧ (∀ x ∈ W, |f' x - f x| ≤ η) ∧
        (∀ x ∈ W, ∀ x' ∈ W, |(f' x - f x) - (f' x' - f x')| ≤ Ld * dist x x') ∧
        (∀ x ∈ W, ∀ x' ∈ W, |f' x - f' x'| ≤ La * dist x x'))
    {e ε' : ℝ} (he : 0 < e) (hε' : 0 < ε') :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - f x| < e) ∧ (∀ x, x ∉ U → F x = f x) ∧
      (∀ x y, |(F x - f x) - (F y - f y)| ≤ (Ld + ε') * dist x y) ∧
      (∀ x y, |F x - F y| ≤ (max (K : ℝ) La + ε') * dist x y) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨f, univ, isOpen_univ, subset_univ _, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim, fun x _ => rfl, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim⟩
  have : ConnectedSpace M := connectedSpace_of_riemannian g hEnorm
  have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  choose! W hWo hbW hWU hWc happ using hloc
  obtain ⟨C', hC'c, hCC', hC'U⟩ := exists_compact_between hC hU hCU
  obtain ⟨t, ht⟩ := hC'c.elim_finite_subcover (fun b : U => W b) (fun b => hWo b b.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hC'U hx⟩, hbW x (hC'U hx)⟩)
  let ι := {i : U // i ∈ t}
  let V : ι → Set M := fun i => W i.1.1
  have hVo : ∀ i, IsOpen (V i) := fun i => hWo _ i.1.2
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hC'c.isClosed V hVo (by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩)
  have hKψ : ∀ i : ι, ∃ Kψ : ℝ≥0, LipschitzWith Kψ (ψ i) := by
    intro i
    have hcs : HasCompactSupport (ψ i) :=
      (hWc _ i.1.2).of_isClosed_subset (isClosed_tsupport _) ((hψ i).trans subset_closure)
    exact exists_lipschitzWith_of_contMDiff_hasCompactSupport g hEnorm (ψ i).contMDiff hcs
  choose Kψ hKψ using hKψ
  set Ks : ℝ := ∑ i, (Kψ i : ℝ) with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => (Kψ i).coe_nonneg
  set η : ℝ := min (e / 2) (ε' / (Ks + 1)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηKs : η * Ks ≤ ε' := by
    have h1 : η ≤ ε' / (Ks + 1) := min_le_right _ _
    have h2 : η * Ks ≤ ε' / (Ks + 1) * Ks := mul_le_mul_of_nonneg_right h1 hKs0
    have h3 : ε' / (Ks + 1) * Ks ≤ ε' := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have happ' : ∀ i : ι, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' (V i) ∧
      (∀ x ∈ V i, |f' x - f x| ≤ η) ∧
      (∀ x ∈ V i, ∀ x' ∈ V i, |(f' x - f x) - (f' x' - f x')| ≤ Ld * dist x x') ∧
      (∀ x ∈ V i, ∀ x' ∈ V i, |f' x - f' x'| ≤ La * dist x x') :=
    fun i => happ i.1.1 i.1.2 η hη
  choose fi hfism hficl hfid hfia using happ'
  have hsum1 : ∀ x ∈ C', ∑ i, ψ i x = 1 := fun x hx => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_eq_one hx
  have hsumle : ∀ x, ∑ i, ψ i x ≤ 1 := fun x => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_le_one x
  have hzero : ∀ i x, x ∉ V i → ψ i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hψ i h))
  have hmemV : ∀ i x, ψ i x ≠ 0 → x ∈ V i := fun i x hx =>
    hψ i (subset_tsupport _ hx)
  let F : M → ℝ := fun x => f x + ∑ i, ψ i x * (fi i x - f x)
  -- the adapted neighbourhood, with both cases recorded
  have hnbhd' : ∀ x, ∃ Vx ∈ 𝓝 x, ∀ i, ∀ y ∈ Vx,
      (x ∈ tsupport (ψ i) → y ∈ V i) ∧ (x ∉ tsupport (ψ i) → ψ i y = 0) := by
    intro x
    refine ⟨⋂ i, (if x ∈ tsupport (ψ i) then V i else (tsupport (ψ i))ᶜ),
      Filter.iInter_mem.mpr fun i => ?_, fun i y hy => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · split_ifs with h
      · exact (hVo i).mem_nhds (hψ i h)
      · exact (isClosed_tsupport _).isOpen_compl.mem_nhds h
    · have := mem_iInter.1 hy i
      simpa only [hi, ite_true] using this
    · have := mem_iInter.1 hy i
      simp only [hi, ite_false] at this
      exact image_eq_zero_of_notMem_tsupport this
  -- the per-index two-point estimates
  have hterm : ∀ x, ∃ Vx ∈ 𝓝 x, ∀ y ∈ Vx, ∀ y' ∈ Vx, ∀ i,
      |ψ i y * (fi i y - f y) - ψ i y' * (fi i y' - f y')| ≤
        ψ i y * (Ld * dist y y') + Kψ i * dist y y' * η ∧
      ψ i y * |fi i y - fi i y'| ≤ ψ i y * (La * dist y y') ∧
      |(ψ i y - ψ i y') * (fi i y' - f y')| ≤ Kψ i * dist y y' * η := by
    intro x
    obtain ⟨Vx, hVx, hcase⟩ := hnbhd' x
    refine ⟨Vx, hVx, fun y hy y' hy' i => ?_⟩
    have hd := dist_nonneg (x := y) (y := y')
    have hψy := ψ.nonneg i y
    have hKd : |ψ i y - ψ i y'| ≤ Kψ i * dist y y' := by
      rw [← Real.dist_eq]; exact (hKψ i).dist_le_mul y y'
    by_cases hx : x ∈ tsupport (ψ i)
    · have hyV := (hcase i y hy).1 hx
      have hy'V := (hcase i y' hy').1 hx
      have h1 := hfid i y hyV y' hy'V
      have h2 := hficl i y' hy'V
      have h3 := hfia i y hyV y' hy'V
      have hsplit : ψ i y * (fi i y - f y) - ψ i y' * (fi i y' - f y') =
          ψ i y * ((fi i y - f y) - (fi i y' - f y')) + (ψ i y - ψ i y') * (fi i y' - f y') := by
        ring
      have hprod : |(ψ i y - ψ i y') * (fi i y' - f y')| ≤ Kψ i * dist y y' * η := by
        rw [abs_mul]
        exact mul_le_mul hKd h2 (abs_nonneg _) (by positivity)
      refine ⟨?_, mul_le_mul_of_nonneg_left h3 hψy, hprod⟩
      rw [hsplit]
      refine (abs_add_le _ _).trans (add_le_add ?_ hprod)
      rw [abs_mul, abs_of_nonneg hψy]
      exact mul_le_mul_of_nonneg_left h1 hψy
    · have hz := (hcase i y hy).2 hx
      have hz' := (hcase i y' hy').2 hx
      refine ⟨?_, ?_, ?_⟩
      · rw [hz, hz']; simp only [zero_mul, sub_zero, abs_zero]; positivity
      · rw [hz]; simp
      · rw [hz, hz']; simp only [sub_zero, zero_mul, abs_zero]; positivity
  refine ⟨F, interior C', isOpen_interior, hCC', ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness where the partition sums to one
    have hG : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ∑ᶠ i, ψ i x • fi i x) :=
      ψ.contMDiff_finsum_smul fun i x hx =>
        (hfism i).contMDiffAt ((hVo i).mem_nhds (hψ i hx))
    refine hG.contMDiffOn.congr fun x hx => ?_
    have h1 := hsum1 x (interior_subset hx)
    simp only [F, finsum_eq_sum_of_fintype, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, h1, one_mul]
    ring
  · intro x
    have hle : |∑ i, ψ i x * (fi i x - f x)| ≤ ∑ i, ψ i x * η := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (ψ.nonneg i x)]
      by_cases h : ψ i x = 0
      · rw [h]; simp
      · exact mul_le_mul_of_nonneg_left (hficl i x (hmemV i x h)) (ψ.nonneg i x)
    have hle2 : ∑ i, ψ i x * η ≤ η := by
      rw [← Finset.sum_mul]
      nlinarith [hsumle x]
    have hηe : η < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    simp only [F, add_sub_cancel_left]
    linarith
  · intro x hx
    have : ∀ i, ψ i x = 0 := fun i => hzero i x (fun h => hx (hWU _ i.1.2 h))
    simp only [F, this, zero_mul, Finset.sum_const_zero, add_zero]
  · -- the Lipschitz difference
    have hL : LipschitzWith (Real.toNNReal (Ld + ε')) (fun x => F x - f x) := by
      refine lipschitzWith_of_locally_riemannian g hEnorm fun x => ?_
      obtain ⟨Vx, hVx, hest⟩ := hterm x
      refine ⟨Vx, hVx, fun y hy y' hy' => ?_⟩
      rw [Real.coe_toNNReal _ (by positivity)]
      have hd := dist_nonneg (x := y) (y := y')
      simp only [F, add_sub_cancel_left]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (hest y hy y' hy' i).1).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have h1 := hsumle y
      have h2 : (∑ i, ψ i y) * (Ld * dist y y') ≤ Ld * dist y y' := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hLd hd)
        linarith
      have h3 : (∑ i, (Kψ i : ℝ)) * dist y y' * η ≤ ε' * dist y y' := by
        rw [← hKs]
        nlinarith
      nlinarith
    intro x y
    have := hL.dist_le_mul x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this
  · -- the Lipschitz bound of `F`
    have hL : LipschitzWith (Real.toNNReal (max (K : ℝ) La + ε')) F := by
      refine lipschitzWith_of_locally_riemannian g hEnorm fun x => ?_
      obtain ⟨Vx, hVx, hest⟩ := hterm x
      refine ⟨Vx, hVx, fun y hy y' hy' => ?_⟩
      have hmax : 0 ≤ max (K : ℝ) La := le_max_of_le_left K.coe_nonneg
      rw [Real.coe_toNNReal _ (by positivity)]
      have hd := dist_nonneg (x := y) (y := y')
      have hS := hsumle y
      have hS0 : 0 ≤ ∑ i, ψ i y := Finset.sum_nonneg fun i _ => ψ.nonneg i y
      have hfy : |f y - f y'| ≤ K * dist y y' := by
        rw [← Real.dist_eq]; exact hf.dist_le_mul y y'
      have hexp : F y - F y' = (1 - ∑ i, ψ i y) * (f y - f y') +
          ∑ i, ψ i y * (fi i y - fi i y') + ∑ i, (ψ i y - ψ i y') * (fi i y' - f y') := by
        simp only [F, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
        ring
      have hA : |(1 - ∑ i, ψ i y) * (f y - f y')| ≤ (1 - ∑ i, ψ i y) * (max (K : ℝ) La * dist y y') := by
        rw [abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_left (hfy.trans (mul_le_mul_of_nonneg_right
          (le_max_left _ _) hd)) (by linarith)
      have hB : |∑ i, ψ i y * (fi i y - fi i y')| ≤ (∑ i, ψ i y) * (max (K : ℝ) La * dist y y') := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (ψ.nonneg i y)]
        exact ((hest y hy y' hy' i).2.1).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hd) (ψ.nonneg i y))
      have hC3 : |∑ i, (ψ i y - ψ i y') * (fi i y' - f y')| ≤ ε' * dist y y' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (hest y hy y' hy' i).2.2).trans ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← hKs]
        nlinarith
      rw [hexp]
      calc |(1 - ∑ i, ψ i y) * (f y - f y') + ∑ i, ψ i y * (fi i y - fi i y') +
            ∑ i, (ψ i y - ψ i y') * (fi i y' - f y')|
          ≤ |(1 - ∑ i, ψ i y) * (f y - f y')| + |∑ i, ψ i y * (fi i y - fi i y')| +
            |∑ i, (ψ i y - ψ i y') * (fi i y' - f y')| := abs_add_three _ _ _
        _ ≤ (1 - ∑ i, ψ i y) * (max (K : ℝ) La * dist y y') +
            (∑ i, ψ i y) * (max (K : ℝ) La * dist y y') + ε' * dist y y' := by linarith
        _ = (max (K : ℝ) La + ε') * dist y y' := by ring
    intro x y
    have := hL.dist_le_mul x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this

end DifferentialGeometry.Geometry.Collapse
