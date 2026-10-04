import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Boundary.LocalApproximation
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Lipschitz smoothing on a compact manifold with corners (foundation F-d, global part)

`exists_contMDiff_edist_lipschitz_approx` (F-d.3): on a compact manifold with corners, a function
which is `K`-Lipschitz for the `g`-length distance has, for every `η > 0`, a smooth (up to the
boundary) `η`-close approximation which is `(K + η)`-Lipschitz for the same distance.

The local smoothings of `exists_local_lipschitz_approximation_of_corners` are glued by a smooth
partition of unity. The globalisation uses no geodesics and no connectedness: the neighbourhoods on
which the local two-point estimates hold do not depend on the approximation error, so their
Lebesgue number `r₀` (for the extended `g`-distance) is fixed first; pairs at distance `< r₀` lie in
one such neighbourhood, and for pairs at distance `≥ r₀` the approximation error `2η'` is absorbed
into `(η / 2) · d`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- F-d.3: Lipschitz smoothing up to the boundary on a compact manifold with corners, for the
extended `g`-length distance. -/
theorem exists_contMDiff_edist_lipschitz_approx [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {K : ℝ≥0}
    (hf : ∀ x y, ENNReal.ofReal |f x - f y| ≤ K * riemannianEDistOf g x y)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x, |F x - f x| < η) ∧
      ∀ x y, ENNReal.ofReal |F x - F y| ≤ ENNReal.ofReal (K + η) * riemannianEDistOf g x y := by
  classical
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  -- the local Lipschitz constant `La = K κ² ≤ K + η / 2`
  set c : ℝ := η / (2 * (K + 1)) with hc
  have hc0 : 0 < c := by positivity
  set κ : ℝ := Real.sqrt (1 + c) with hκ
  have hκsq : κ ^ 2 = 1 + c := Real.sq_sqrt (by positivity)
  have hκ1 : 1 < κ := by
    rw [hκ, Real.lt_sqrt zero_le_one]
    linarith
  set La : ℝ := (K : ℝ) * κ ^ 2 with hLa
  have hLa0 : 0 ≤ La := by positivity
  have hLaK : La ≤ K + η / 2 := by
    have h1 : (K : ℝ) * c ≤ η / 2 := by
      rw [hc, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [hLa, hκsq]
    nlinarith
  -- local smoothings and a subordinate partition of unity
  choose V hVo hbV happ using fun b => exists_local_lipschitz_approximation_of_corners g hf hκ1 b
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V (fun b _ => (hVo b).mem_nhds (hbV b))
  let ι := {b : M // b ∈ t}
  let W : ι → Set M := fun i => V i.1
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W
    (fun i => hVo i.1) (by
      intro x _
      obtain ⟨b, hbt, hxb⟩ := mem_iUnion₂.mp (ht (mem_univ x))
      exact mem_iUnion.2 ⟨⟨b, hbt⟩, hxb⟩)
  have hsum1 : ∀ x, ∑ i, ψ i x = 1 := fun x => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_eq_one (mem_univ x)
  have hmemW : ∀ i x, x ∈ tsupport (ψ i) → x ∈ W i := fun i x hx => hψ i hx
  -- uniform local Lipschitz constants of the partition functions
  have hKψ : ∀ i : ι, ∃ C : ℝ≥0, ∀ b : M, ∃ O ∈ 𝓝 b, ∀ x ∈ O, ∀ y ∈ O,
      ENNReal.ofReal |ψ i x - ψ i y| ≤ C * riemannianEDistOf g x y := fun i =>
    exists_uniform_local_lipschitz_of_contMDiff g ((ψ i).contMDiff.of_le (mod_cast le_top))
  choose Kψ O hO hOlip using hKψ
  set Ks : ℝ := ∑ i, (Kψ i : ℝ) with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => (Kψ i).coe_nonneg
  -- the good neighbourhoods, independent of the approximation error
  let G : M → Set M := fun x =>
    ((⋂ i, (if x ∈ tsupport (ψ i) then W i else (tsupport (ψ i))ᶜ)) ∩ ⋂ i, O i x) ∩
      {y | riemannianEDistOf g x y < 1}
  have hG : ∀ x, G x ∈ 𝓝 x := by
    intro x
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    refine inter_mem (inter_mem (Filter.iInter_mem.mpr fun i => ?_)
      (Filter.iInter_mem.mpr fun i => hO i x)) (eventually_riemannianEDist_lt I x one_pos)
    split_ifs with h
    · exact (hVo _).mem_nhds (hmemW i x h)
    · exact (isClosed_tsupport _).isOpen_compl.mem_nhds h
  have hGcase : ∀ x, ∀ y ∈ G x, ∀ i, (x ∈ tsupport (ψ i) → y ∈ W i) ∧
      (x ∉ tsupport (ψ i) → ψ i y = 0) := by
    intro x y hy i
    have hyi := mem_iInter.1 hy.1.1 i
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa only [hx, ite_true] using hyi
    · simp only [hx, ite_false] at hyi
      exact image_eq_zero_of_notMem_tsupport hyi
  -- the Lebesgue number of the good neighbourhoods
  obtain ⟨r₀, hr₀, hleb⟩ : ∃ r₀ > 0, ∀ x : M, ∃ z : M,
      {y | riemannianEDistOf g y x < r₀} ⊆ G z := by
    let := inducedEMetricSpace g
    obtain ⟨r₀, hr₀, h⟩ := lebesgue_number_lemma_of_emetric_nhds (c := G) isCompact_univ
      (fun x _ => hG x)
    exact ⟨r₀, hr₀, fun x => h x (mem_univ x)⟩
  set r₁ : ℝ := (min r₀ 1).toReal with hr₁
  have hr₁0 : 0 < r₁ := ENNReal.toReal_pos (lt_min hr₀ one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have hr₁r₀ : ENNReal.ofReal r₁ ≤ r₀ := by
    rw [hr₁, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  -- the approximation error
  set η' : ℝ := min (η / 2) (min (η / 2 / (Ks + 1)) (η * r₁ / 4)) with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη'η : η' < η := (min_le_left _ _).trans_lt (by linarith)
  have hη'Ks : η' * Ks ≤ η / 2 := by
    have h1 : η' ≤ η / 2 / (Ks + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : η / 2 / (Ks + 1) * Ks ≤ η / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hη'r : 2 * η' ≤ η / 2 * r₁ := by
    have h1 : η' ≤ η * r₁ / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  choose fi hfism hficl hfilip using fun i : ι => happ i.1 η' hη'0
  let F : M → ℝ := fun x => ∑ i, ψ i x * fi i x
  have hFf : ∀ x, |F x - f x| ≤ η' := by
    intro x
    have hexp : F x - f x = ∑ i, ψ i x * (fi i x - f x) := by
      simp only [F, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1 x, one_mul]
    rw [hexp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |ψ i x * (fi i x - f x)| ≤ ∑ i, ψ i x * η' := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (ψ.nonneg i x)]
          by_cases h : ψ i x = 0
          · rw [h]; simp
          · exact mul_le_mul_of_nonneg_left
              (hficl i x (hmemW i x (subset_tsupport _ h))) (ψ.nonneg i x)
      _ = η' := by rw [← Finset.sum_mul, hsum1 x, one_mul]
  refine ⟨F, ?_, fun x => (hFf x).trans_lt hη'η, ?_⟩
  · have hS : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ∑ᶠ i, ψ i x • fi i x) :=
      ψ.contMDiff_finsum_smul fun i x hx =>
        (hfism i).contMDiffAt ((hVo i.1).mem_nhds (hmemW i x hx))
    refine hS.congr fun x => ?_
    simp only [F, finsum_eq_sum_of_fintype, smul_eq_mul]
  intro x y
  by_cases hxy : riemannianEDistOf g x y < r₀
  · -- near pairs: the local estimates in one good neighbourhood
    obtain ⟨z, hz⟩ := hleb x
    have hxz : x ∈ G z := hz (by
      change riemannianEDistOf g x x < r₀
      rw [riemannianEDistOf_self]; exact hr₀)
    have hyz : y ∈ G z := hz (by
      change riemannianEDistOf g y x < r₀
      rwa [riemannianEDistOf_comm])
    have hfin : riemannianEDistOf g x y ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (riemannianEDistOf_triangle g x z y)
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · rw [riemannianEDistOf_comm]; exact ne_top_of_lt hxz.2
      · exact ne_top_of_lt hyz.2
    set D : ℝ := (riemannianEDistOf g x y).toReal with hD
    have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
    have hDeq : riemannianEDistOf g x y = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfin).symm
    have hreal : ∀ {u v : ℝ} {C : ℝ}, 0 ≤ C → ENNReal.ofReal |u - v| ≤
        ENNReal.ofReal C * riemannianEDistOf g x y → |u - v| ≤ C * D := by
      intro u v C hC h
      rw [hDeq, ← ENNReal.ofReal_mul hC] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hψ : ∀ i, |ψ i x - ψ i y| ≤ Kψ i * D := fun i =>
      hreal (Kψ i).coe_nonneg (by
        rw [ENNReal.ofReal_coe_nnreal]
        exact hOlip i z x (hxz.1.2 |> mem_iInter.1 <| i) y (hyz.1.2 |> mem_iInter.1 <| i))
    have hA : ∀ i, ψ i x * |fi i x - fi i y| ≤ ψ i x * (La * D) := by
      intro i
      by_cases hzi : z ∈ tsupport (ψ i)
      · exact mul_le_mul_of_nonneg_left (hreal hLa0 (hfilip i x ((hGcase z x hxz i).1 hzi) y
          ((hGcase z y hyz i).1 hzi))) (ψ.nonneg i x)
      · rw [(hGcase z x hxz i).2 hzi]; simp
    have hB : ∀ i, |(ψ i x - ψ i y) * (fi i y - f y)| ≤ Kψ i * D * η' := by
      intro i
      by_cases hzi : z ∈ tsupport (ψ i)
      · rw [abs_mul]
        exact mul_le_mul (hψ i) (hficl i y ((hGcase z y hyz i).1 hzi)) (abs_nonneg _)
          (by positivity)
      · rw [(hGcase z x hxz i).2 hzi, (hGcase z y hyz i).2 hzi]
        simp only [sub_self, zero_mul, abs_zero]
        positivity
    have hexp : F x - F y = ∑ i, ψ i x * (fi i x - fi i y) +
        ∑ i, (ψ i x - ψ i y) * (fi i y - f y) := by
      have h1 : ∑ i, (ψ i x - ψ i y) * f y = 0 := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum1 x, hsum1 y, sub_self, zero_mul]
      have h2 : ∑ i, (ψ i x - ψ i y) * (fi i y - f y) =
          ∑ i, (ψ i x - ψ i y) * fi i y - ∑ i, (ψ i x - ψ i y) * f y := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h2, h1, sub_zero, ← Finset.sum_add_distrib]
      simp only [F, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound : |F x - F y| ≤ (K + η) * D := by
      rw [hexp]
      refine (abs_add_le _ _).trans ?_
      have h1 : |∑ i, ψ i x * (fi i x - fi i y)| ≤ La * D := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |ψ i x * (fi i x - fi i y)| ≤ ∑ i, ψ i x * (La * D) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul, abs_of_nonneg (ψ.nonneg i x)]
              exact hA i
          _ = La * D := by rw [← Finset.sum_mul, hsum1 x, one_mul]
      have h2 : |∑ i, (ψ i x - ψ i y) * (fi i y - f y)| ≤ η / 2 * D := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => hB i).trans ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← hKs]
        nlinarith
      nlinarith
    calc ENNReal.ofReal |F x - F y| ≤ ENNReal.ofReal ((K + η) * D) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (K + η) * riemannianEDistOf g x y := by
          rw [hDeq, ENNReal.ofReal_mul (by positivity)]
  · -- far pairs: the approximation error is absorbed by the distance
    rw [not_lt] at hxy
    by_cases hfin : riemannianEDistOf g x y = ⊤
    · rw [hfin, ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
      exact le_top
    set D : ℝ := (riemannianEDistOf g x y).toReal with hD
    have hDeq : riemannianEDistOf g x y = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfin).symm
    have hrD : r₁ ≤ D := by
      have h := hr₁r₀.trans hxy
      rw [hDeq] at h
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
    have hfxy : |f x - f y| ≤ K * D := by
      have h := hf x y
      rw [hDeq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hK0] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hbound : |F x - F y| ≤ (K + η) * D := by
      have h1 := hFf x
      have h2 := hFf y
      have htri : |F x - F y| ≤ |F x - f x| + |f x - f y| + |F y - f y| := by
        have := abs_add_three (F x - f x) (f x - f y) (f y - F y)
        rw [abs_sub_comm (f y) (F y)] at this
        convert this using 2
        ring
      have h3 : η / 2 * r₁ ≤ η / 2 * D := mul_le_mul_of_nonneg_left hrD (by positivity)
      nlinarith
    calc ENNReal.ofReal |F x - F y| ≤ ENNReal.ofReal ((K + η) * D) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (K + η) * riemannianEDistOf g x y := by
          rw [hDeq, ENNReal.ofReal_mul (by positivity)]

end DifferentialGeometry.Geometry.Collapse
