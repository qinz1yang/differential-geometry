import DifferentialGeometry.Geometry.Metric.Approximation.ProductLimitEvaluation

set_option autoImplicit false

open Set Filter Metric
open scoped Topology


namespace GC.MetricGeometry

universe u v w z
variable {T : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable [∀ i, MetricSpace (T i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace Y]
variable {o : ∀ i, T i} {a : E} {q : Y} {b : ∀ i, Z i} {δ R ε : ℕ → ℝ}

theorem exists_full_product_limit_of_approximate_products_with_given_maps
    (f : ∀ i, PointedBallApprox (o i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (Φ : ∀ i, KleinerLottApprox (o i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (χ : ℕ → ℕ), StrictMono χ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (χ i)) w ∧
        PointedGHConverges (fun i => o (χ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) ∧
          ∃ P τ : ℕ → ℝ, Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (b (χ i)) w (P i) (τ i),
              ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                S ≤ R (χ i) ∧
                ∀ x : BallCarrier (o (χ i)) (R (χ i)), dist x.val (o (χ i)) ≤ S →
                  (dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i ∧
                  ∀ hx : dist ((Φ (χ i)).toFun x.val).snd (b (χ i)) ≤ P i,
                    dist (WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
                      (g i).toFun ⟨((Φ (χ i)).toFun x.val).snd, hx⟩))
                      (e ((f (χ i)).toFun x)) < ζ) := by
  classical
  have h : PointedGHConverges o q := by
    refine ⟨inferInstance, ?_⟩
    intro S η hη hηS
    filter_upwards [hR.eventually (eventually_ge_atTop S),
      hε.eventually (eventually_lt_nhds (by positivity : 0 < η / 2))] with i hiR hiε
    exact ⟨((f i).restrict (by linarith) hiR).enlargeError (by linarith) hηS⟩
  obtain ⟨W, m, w, α, hα, hp, hc, hz, ho⟩ :=
    h.exists_factor_limit_of_approximate_products Φ hδ
  let := m
  let := hp
  let := hc
  let J : ℕ → ℝ := fun i => (i : ℝ) + 1
  let η : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  let K : ℕ → ℝ := fun i => 4 * J i + 4
  have hJone (i : ℕ) : 1 ≤ J i := by dsimp [J]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hJ : Tendsto J atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hηpos (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hηJ (i : ℕ) : 10 * η i < J i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [η, J]
    linarith
  have hηK (i : ℕ) : η i < K i := by dsimp [K]; linarith [hJone i, hηJ i]
  have hηzero : Tendsto η atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  have htail (j : ℕ) : ∀ᶠ i in atTop,
      K j ≤ R (α i) ∧ ε (α i) < η j / 2 ∧ δ (α i) < η j / 24 ∧
        K j + η j < (δ (α i))⁻¹ ∧
        Nonempty (PointedBallApprox (b (α i)) w (K j + η j) (η j / 24)) := by
    have hKpos : 0 < K j := (hηpos j).trans (hηK j)
    filter_upwards [(hR.comp hα.tendsto_atTop).eventually (eventually_ge_atTop (K j)),
      (hε.comp hα.tendsto_atTop).eventually (eventually_lt_nhds (by linarith [hηpos j] : 0 < η j / 2)),
      (hδ.comp hα.tendsto_atTop).eventually (eventually_lt_nhds (by linarith [hηpos j] : 0 < η j / 24)),
      (hδ.comp hα.tendsto_atTop).eventually
        (eventually_lt_nhds (by positivity : 0 < (K j + η j + 1)⁻¹)),
      hz.eventually_approx (R := K j + η j) (ε := η j / 24)
        (by linarith [hηpos j]) (by linarith [hηpos j])]
      with i hiR hiε hiδ hiK hiG
    have hinv : K j + η j < (δ (α i))⁻¹ := by
      have hh := (inv_lt_inv₀ (show 0 < (K j + η j + 1)⁻¹ by positivity)
        (Φ (α i)).error_pos).mpr hiK
      rw [inv_inv] at hh
      linarith
    exact ⟨hiR, hiε, hiδ, hinv, hiG⟩
  obtain ⟨β, hβ, hmaps⟩ := extraction_forall_of_eventually htail
  let g (j : ℕ) : PointedBallApprox (b (α (β j))) w (K j + η j) (η j / 24) :=
    Classical.choice (hmaps j).2.2.2.2
  let A (j : ℕ) : PointedBallApprox (o (α (β j))) q (K j) (η j) :=
    ((f (α (β j))).restrict (by linarith [(hmaps j).2.1, hηK j]) (hmaps j).1).enlargeError
      (by linarith [(hmaps j).2.1]) (hηK j)
  let B (j : ℕ) : PointedBallApprox (o (α (β j))) (WithLp.toLp 2 (a, w)) (K j) (η j) :=
    (Φ (α (β j))).productLimitApprox (g j) (hηpos j) (hηK j)
      (hmaps j).2.2.1 (hmaps j).2.2.2.1
  obtain ⟨e, ψ, he, hψ, hcontrol⟩ :=
    exists_controlled_common_limit_isometry hJone hJ hηzero hηJ A B
  let χ : ℕ → ℕ := fun i => α (β (ψ i))
  have hχ : StrictMono χ := hα.comp (hβ.comp hψ)
  have hK : Tendsto (fun i => K (ψ i)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4
      ((hJ.comp hψ.tendsto_atTop).const_mul_atTop (by norm_num))
  have hP : Tendsto (fun i => K (ψ i) + η (ψ i)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro t
    filter_upwards [hK.eventually (eventually_ge_atTop t)] with i hi
    linarith [hηpos (ψ i)]
  have hτ : Tendsto (fun i => η (ψ i) / 24) atTop (𝓝 0) := by
    simpa only [zero_div, Function.comp_def] using (hηzero.comp hψ.tendsto_atTop).div_const 24
  refine ⟨W, m, w, χ, hχ, hp, hc, (hz.subsequence hβ).subsequence hψ,
    (ho.subsequence hβ).subsequence hψ, e, he,
    (fun i => K (ψ i) + η (ψ i)), (fun i => η (ψ i) / 24), hP, hτ,
    (fun i => g (ψ i)), ?_⟩
  intro S ζ hζ
  filter_upwards [hcontrol S ζ hζ, hK.eventually (eventually_ge_atTop S)] with i hi hiS
  refine ⟨hiS.trans (hmaps (ψ i)).1, ?_⟩
  intro x hxS
  let x' : BallCarrier (o (α (β (ψ i)))) (K (ψ i)) := ⟨x.val, hxS.trans hiS⟩
  have hdom := (Φ (χ i)).productLimitApprox_factor_mem
    (hηpos (ψ i)) (hmaps (ψ i)).2.2.1 (hmaps (ψ i)).2.2.2.1 x'
  refine ⟨hdom, ?_⟩
  intro hx
  have hA : (A (ψ i)).toFun x' = (f (χ i)).toFun x := rfl
  have hB : (B (ψ i)).toFun x' =
      WithLp.toLp 2 (((Φ (χ i)).toFun x.val).fst,
        (g (ψ i)).toFun ⟨((Φ (χ i)).toFun x.val).snd, hx⟩) :=
    (Φ (χ i)).productLimitApprox_apply (g (ψ i)) (hηpos (ψ i)) (hηK (ψ i))
      (hmaps (ψ i)).2.2.1 (hmaps (ψ i)).2.2.2.1 x' hx
  have hh := hi x' hxS
  rwa [hA, hB] at hh

end GC.MetricGeometry
