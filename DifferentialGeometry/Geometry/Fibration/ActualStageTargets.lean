import DifferentialGeometry.Geometry.Fibration.ActualStageClouds

/-!
# GAF02's stage targets `Q_j` as subspaces, with `π_{Q_j} = blockRestrict`

Blueprint `master207B.tex`, FC01 (`Q₁ = H`, `Q₂ = H₀ ⊕ H_s ⊕ H_e`, `Q₃ = H₀ ⊕ H_s`, B:105–112),
FC27 (B:1658) and GAF02 (B:5797). The stage maps `Ψ_j(z) = z + ψ_j(z)(P_j(π_{Q_j} z) − π_{Q_j} z)`
of GAF02 use the orthogonal projections onto the stage targets; FC33's `P_j = π_{Q_j} ∘ p_j`
needs the planes of the (CS) tests inside `Q_j`.

* Generic: `blockRestrict_idem_GAF3` (idempotent), `inner_blockRestrict_GAF3` (symmetric),
  `blockRestrict_eq_starProjection_GAF3` (`π_s` is the orthogonal projection onto its range),
  `mem_range_blockRestrict_iff_GAF3`, `range_fderiv_le_range_blockRestrict_GAF3` (a map with values
  in `range π_s` has derivative ranges in `range π_s`).
* `gafStageQ L Z st = range π_{Q_st}`; `gafStageQ_starProjection` (`π_{Q_st}` is `blockRestrict`),
  `gafStageQ_starProjection_globalMap` (`π_{Q_st} ∘ 𝓔⁰ = π_st𝓔⁰`), `mem_gafStageQ_iff`,
  `gafCloudEnlarged_subset_gafStageQ`, `gafCloud_subset_gafStageQ` (the stage clouds lie in `Q_st`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {κ : Type*} [DecidableEq κ] {V : κ → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]

/-- `π_s` is idempotent. -/
theorem blockRestrict_idem_GAF3 (s : Finset κ) :
    (blockRestrict (V := V) s).comp (blockRestrict s) = blockRestrict s := by
  rw [blockRestrict_comp, Finset.inter_self]

/-- `π_s` is symmetric. -/
theorem inner_blockRestrict_GAF3 [Fintype κ] (s : Finset κ) (x y : BlockSpace V) :
    ⟪blockRestrict s x, y⟫_ℝ = ⟪x, blockRestrict s y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockRestrict_apply, blockRestrict_apply]
  split_ifs <;> simp

/-- Membership in the range of `π_s` is being fixed by `π_s`. -/
theorem mem_range_blockRestrict_iff_GAF3 {s : Finset κ} {v : BlockSpace V} :
    v ∈ (blockRestrict (V := V) s).range ↔ blockRestrict s v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change (blockRestrict s).comp (blockRestrict s) w = blockRestrict s w
    rw [blockRestrict_idem_GAF3]
  · intro h
    exact ⟨v, h⟩

variable [Fintype κ] [∀ i, FiniteDimensional ℝ (V i)]

/-- `π_s` is the orthogonal projection onto its range. -/
theorem blockRestrict_eq_starProjection_GAF3 (s : Finset κ) :
    ((blockRestrict (V := V) s).range).starProjection = blockRestrict s := by
  have hP : IsStarProjection (blockRestrict (V := V) s) := by
    refine ⟨blockRestrict_idem_GAF3 s, ?_⟩
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    exact ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      fun x y => inner_blockRestrict_GAF3 s x y).symm
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  exact h.symm

omit [Fintype κ] [∀ i, FiniteDimensional ℝ (V i)] in
/-- A map with values in `range π_s` (i.e. `π_s ∘ f = f`) has derivative ranges in `range π_s`. -/
theorem range_fderiv_le_range_blockRestrict_GAF3 [Finite κ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset κ) (f : E → BlockSpace V)
    (hf : ∀ u, blockRestrict s (f u) = f u) (a : E) :
    (fderiv ℝ f a).range ≤ (blockRestrict (V := V) s).range := by
  cases nonempty_fintype κ
  by_cases hd : DifferentiableAt ℝ f a
  · have hcomp : HasFDerivAt (fun u => blockRestrict (V := V) s (f u))
        ((blockRestrict (V := V) s).comp (fderiv ℝ f a)) a :=
      (blockRestrict (V := V) s).hasFDerivAt.comp a hd.hasFDerivAt
    have hfun : (fun u => blockRestrict (V := V) s (f u)) = f := funext hf
    rw [hfun] at hcomp
    rw [hcomp.fderiv]
    rintro v ⟨w, rfl⟩
    exact ⟨fderiv ℝ f a w, rfl⟩
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rintro v ⟨w, rfl⟩
    exact ⟨0, by simp⟩

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- GAF02's stage target `Q_st = range π_{Q_st}` (`Q₁ = H`, `Q₂`, `Q₃` of FC01). -/
def gafStageQ (st : Fin 3) : Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)) :=
  (blockRestrict (gafStageTags L Z st)).range

open Classical in
/-- The orthogonal projection onto `Q_st` is `blockRestrict` of the stage tags. -/
theorem gafStageQ_starProjection (st : Fin 3) :
    (gafStageQ L Z st).starProjection = blockRestrict (gafStageTags L Z st) :=
  blockRestrict_eq_starProjection_GAF3 _

open Classical in
/-- `π_{Q_st} ∘ 𝓔⁰ = π_st𝓔⁰` (`cgpProjMap` of the stage tags). -/
theorem gafStageQ_starProjection_globalMap (st : Fin 3) (p : X) :
    (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) =
      cgpProjMap L Z (gafStageTags L Z st) p := by
  rw [gafStageQ_starProjection]
  rfl

variable {L Z} in
open Classical in
theorem mem_gafStageQ_iff {st : Fin 3} {v : BlockSpace (fun _ : CGPTag L Z => ℝ²)} :
    v ∈ gafStageQ L Z st ↔ blockRestrict (gafStageTags L Z st) v = v :=
  mem_range_blockRestrict_iff_GAF3

/-- The enlarged stage cloud lies in `Q_st`. -/
theorem gafCloudEnlarged_subset_gafStageQ (st : Fin 3) :
    gafCloudEnlarged L Z st ⊆ (gafStageQ L Z st : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) := by
  classical
  rintro _ ⟨p, -, rfl⟩
  exact ⟨cgpGlobalMap L Z p, rfl⟩

/-- The stage cloud lies in `Q_st`. -/
theorem gafCloud_subset_gafStageQ (st : Fin 3) :
    gafCloud L Z st ⊆ (gafStageQ L Z st : Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) := by
  classical
  rintro _ ⟨p, -, rfl⟩
  exact ⟨cgpGlobalMap L Z p, rfl⟩

end DifferentialGeometry.Geometry.Collapse
