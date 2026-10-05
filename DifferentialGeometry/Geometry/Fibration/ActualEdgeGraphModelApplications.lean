import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModel

/-!
# Consumers of EGP06's model graph

* `egpModelGraph_lower_bound`: the own block `(a, 1)` gives the model derivative `T = DΦ_i(a)` the
  lower bound `|x| ≤ ‖T x‖` — EGP07's "the identity component of `T_x` gives lower norm one" — and
  `egp06_model` gives the upper bound `‖T x‖ ≤ C†|x|`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The derivative of a continuous linear map after a differentiable curve. -/
theorem fderiv_clm_comp_apply_KC3 {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) {h : ℝ → G} {a : ℝ}
    (hh : DifferentiableAt ℝ h a) (x : ℝ) : fderiv ℝ (L ∘ h) a x = L (fderiv ℝ h a x) := by
  rw [fderiv_comp a L.differentiableAt hh, L.fderiv]
  rfl

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **The model derivative is bounded below by the own block**: `|x| ≤ ‖DΦ_i(a) x‖` for every
`a, x` (the own edge tag `i` carries `(a, 1)`). -/
theorem egpModelGraph_lower_bound
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {i : X}
    (hi : i ∈ L.edge.centres) (sgn c : CGPTag L Z → ℝ) (a x : ℝ) :
    ‖x‖ ≤ ‖fderiv ℝ (egpModelGraph L Z i sgn c) a x‖ := by
  let j : L.edge.finite_centres.toFinset := ⟨i, (Set.Finite.mem_toFinset _).mpr hi⟩
  have hcomp := fderiv_blockGraph_apply_KC3
    (fun t => (contDiff_egpModelComponent L Z i sgn c t).differentiable (by simp)) a x
    (.inr (.inr (.inl j)))
  have hown : egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) =
      fun a => blockLift_KC3 (WithLp.toLp 2 (a, (1 : ℝ))) := by
    simp only [egpModelComponent, j, ite_true]
  obtain ⟨v₁, hv₁def⟩ : ∃ v : WithLp 2 (ℝ × ℝ), v = WithLp.toLp 2 ((1 : ℝ), (0 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀def⟩ : ∃ v : WithLp 2 (ℝ × ℝ), v = WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) := ⟨_, rfl⟩
  have hfun : (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) =
      fun a => ContinuousLinearMap.toSpanSingleton ℝ v₁ a + v₀ := by
    funext a
    rw [ContinuousLinearMap.toSpanSingleton_apply, hv₁def, hv₀def, ← WithLp.toLp_smul,
      ← WithLp.toLp_add]
    congr 1
    simp
  have hv₁ : ‖v₁‖ = 1 := by
    rw [hv₁def, WithLp.prod_norm_eq_of_L2]
    simp
  have hd : HasFDerivAt (fun a : ℝ => ContinuousLinearMap.toSpanSingleton ℝ v₁ a + v₀)
      (ContinuousLinearMap.toSpanSingleton ℝ v₁) a :=
    (ContinuousLinearMap.toSpanSingleton ℝ v₁).hasFDerivAt.add_const v₀
  have hW0d : Differentiable ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) :=
    own_block_bounds_KC3.1.differentiable (by simp)
  have hW0x : fderiv ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) a x =
      x • v₁ := by
    rw [hfun, hd.fderiv]
    rfl
  have hval : fderiv ℝ (egpModelComponent L Z i sgn c (.inr (.inr (.inl j)))) a x =
      blockLift_KC3 (x • v₁) := by
    rw [hown]
    change fderiv ℝ (blockLift_KC3 ∘ fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) :
      WithLp 2 (ℝ × ℝ))) a x = _
    rw [fderiv_clm_comp_apply_KC3 blockLift_KC3 (hW0d a), hW0x]
  have hnorm : ‖blockLift_KC3 (x • v₁)‖ = ‖x‖ := by
    rw [norm_blockLift_apply_KC3, norm_smul, hv₁, mul_one]
  calc ‖x‖ = ‖fderiv ℝ (egpModelGraph L Z i sgn c) a x (.inr (.inr (.inl j)))‖ := by
        rw [← hnorm, ← hval, ← hcomp]
        rfl
    _ ≤ ‖fderiv ℝ (egpModelGraph L Z i sgn c) a x‖ := PiLp.norm_apply_le _ _

end DifferentialGeometry.Geometry.Collapse
