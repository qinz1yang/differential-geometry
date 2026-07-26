import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping

/-!
# Reverse-Christoffel order-peeling: order-`2k` chart Hilbert-Schmidt control
by the order-`0` content of the iterated covariant gradients

The forward order-dropping bound `covGrad_toHs_norm_le` shows that one covariant
derivative *costs* one Sobolev order: `‖∇T‖_{H^σ} ≤ C · ‖T‖_{H^{σ+1}}`.  This
file proves the **opposite** (order-peeling) inequality, the analytic heart of
the reverse Sobolev bridge:

  `tensorPouSobolevHsNorm g k T
     ≤ C · ∑_{j ∈ range (2k + 1)} tensorPouSobolevHsNorm g 0 (∇^j T)`,

i.e. the order-`2k` Hilbert-Schmidt chart-Sobolev norm of `T` is controlled by
the order-`0` chart-Sobolev norms (the bare `L²` content of the chart-frame
scalar components) of the iterated covariant gradients `∇^j T`, `j ≤ 2k`.

## The peeling identity (reverse of the chart formula)

The bidirectional chart formula `tensorChartComponentRaw_covGrad` reads, for a
smooth compactly-supported `(r, s)`-tensor `S`,

  `raw(∇S)_{Idx, (m ::ᵥ Jdx')}
     = euclidPartial m (chartPushedRaw I α (raw S_{Idx, Jdx'}))
       + covDerivLowerOrderTerm`.

Rearranged it expresses one chart-Euclidean coordinate partial of a component of
`S` as a component of `∇S` minus a zeroth-order Christoffel correction:

  `euclidPartial m (raw S_{Idx, Jdx'})
     = raw(∇S)_{Idx, (m ::ᵥ Jdx')} - covDerivLowerOrderTerm`.

Iterating this, every order-`j` Fréchet derivative of a chart-pulled component of
`T` is, up to lower-order Christoffel-coefficient corrections of all the `∇^i T`
(`i ≤ j`), an order-`0` component of `∇^j T`.  The corrections are controlled by
the uniform `C^•` Christoffel data of the compact manifold
(`exists_lowerOrderCoeff_uniform_bound`), exactly as in the forward direction.

## Main results

* `iteratedFDeriv_rawPull_norm_le_iteratedCovGrad_content` — the **pointwise
  operator-norm reverse-peeling**: the order-`j` Fréchet-derivative operator norm
  of a chart-pulled component of any smooth compactly-supported tensor `S` is
  bounded by a uniform constant times the sum over `i ≤ j` of the order-`0`
  content (sum of component magnitudes) of `∇^i S`, on the compact
  partition-of-unity kernel.

* `exists_tensorPouSobolevHsNorm_le_iteratedCovGrad_zero_sum` — the **headline
  reverse-bridge order-peeling**:
  `tensorPouSobolevHsNorm g k T ≤ ENNReal.ofReal C ·
    ∑_{j ∈ range (2k+1)} tensorPouSobolevHsNorm g 0 (∇^j T)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section ReversePeeling

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Expansion of a vector in `EuclN` along the standard basis. -/
private lemma euclN_basis_expansion (v : EuclN) :
    v = ∑ j : Fin (Module.finrank ℝ E), v j • EuclideanSpace.single j (1 : ℝ) := by
  classical
  have h_pi_decomp : (fun i : Fin (Module.finrank ℝ E) => v i) =
      ∑ j : Fin (Module.finrank ℝ E),
        (v j) • ((Pi.single j (1 : ℝ)) : Fin (Module.finrank ℝ E) → ℝ) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [smul_eq_mul]
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_apply, if_neg hj.symm, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h_v_toLp : v = WithLp.toLp 2 (fun i : Fin (Module.finrank ℝ E) => v i) := rfl
  have h_rhs :
      (∑ j : Fin (Module.finrank ℝ E), v j • EuclideanSpace.single j (1 : ℝ) : EuclN) =
        ∑ j : Fin (Module.finrank ℝ E),
          v j • WithLp.toLp 2 ((Pi.single j (1 : ℝ)) : Fin (Module.finrank ℝ E) → ℝ) := by
    refine Finset.sum_congr rfl (fun j _ => ?_); rfl
  rw [h_rhs]
  conv_lhs => rw [h_v_toLp, h_pi_decomp]
  rw [show (WithLp.toLp 2 : (Fin (Module.finrank ℝ E) → ℝ) → EuclN) =
      (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ)).symm from rfl]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearEquiv.map_smul]

/-- The standard Euclidean basis tuple at a multi-index `α : Fin m → Fin n`. -/
private def basisTupleE {m : ℕ} (α : Fin m → Fin (Module.finrank ℝ E)) :
    Fin m → EuclN :=
  fun i => EuclideanSpace.single (α i) (1 : ℝ)

/-- Each component of `basisTupleE α` has norm one. -/
private lemma basisTupleE_norm_one {m : ℕ}
    (α : Fin m → Fin (Module.finrank ℝ E)) (i : Fin m) :
    ‖basisTupleE (E := E) α i‖ = 1 := by
  simp only [basisTupleE, PiLp.norm_single]; simp

/-- The product of the component norms of `basisTupleE α` is one. -/
private lemma basisTupleE_prod_norms {m : ℕ}
    (α : Fin m → Fin (Module.finrank ℝ E)) :
    (∏ i : Fin m, ‖basisTupleE (E := E) α i‖) = 1 :=
  Finset.prod_eq_one (fun i _ => basisTupleE_norm_one (E := E) α i)

/-- Each coordinate of a vector in `EuclN` has absolute value bounded by the
norm. -/
private lemma euclN_coord_abs_le_norm (v : EuclN) (i : Fin (Module.finrank ℝ E)) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i) ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), (v j) ^ 2 := by
    have h_single : (v i) ^ 2 = ∑ j ∈ ({i} : Finset (Fin (Module.finrank ℝ E))),
        (v j) ^ 2 := by simp
    rw [h_single]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => sq_nonneg _)
  have h_norm_eq : ‖v‖ = Real.sqrt (∑ j : Fin (Module.finrank ℝ E), (v j) ^ 2) := by
    rw [EuclideanSpace.norm_eq v]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_norm_eq, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h_sq

/-- **The L¹ basis bound for a continuous multilinear map on `EuclN`.** The
operator norm is bounded by the sum of the absolute values of the
basis-tuple evaluations. -/
private theorem opNorm_le_sum_basisE {m : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ) :
    ‖f‖ ≤ ∑ α : Fin m → Fin (Module.finrank ℝ E), |f (basisTupleE (E := E) α)| := by
  classical
  set S : ℝ := ∑ α : Fin m → Fin (Module.finrank ℝ E),
    |f (basisTupleE (E := E) α)| with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun α _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hS_nn (fun v => ?_)
  have h_v_eq : v = fun i : Fin m =>
      ∑ j : Fin (Module.finrank ℝ E),
        (v i j) • EuclideanSpace.single j (1 : ℝ) := by
    funext i; exact euclN_basis_expansion (v i)
  conv_lhs => rw [h_v_eq]
  have h_sum_expand :
      f (fun i : Fin m =>
          ∑ j : Fin (Module.finrank ℝ E),
            (v i j) • EuclideanSpace.single j (1 : ℝ)) =
        ∑ α : Fin m → Fin (Module.finrank ℝ E),
          f (fun i => (v i (α i)) •
            EuclideanSpace.single (α i) (1 : ℝ)) := by
    have h := f.toMultilinearMap.map_sum
      (g := fun (i : Fin m) (j : Fin (Module.finrank ℝ E)) =>
        (v i j) • EuclideanSpace.single j (1 : ℝ))
    convert h using 1
  rw [h_sum_expand]
  refine (norm_sum_le _ _).trans ?_
  have h_norm_eq : ∀ α : Fin m → Fin (Module.finrank ℝ E),
      ‖f (fun i => (v i (α i)) •
          EuclideanSpace.single (α i) (1 : ℝ))‖ =
        |f (fun i => (v i (α i)) •
          EuclideanSpace.single (α i) (1 : ℝ))| := fun α => rfl
  rw [Finset.sum_congr rfl (fun α _ => h_norm_eq α)]
  have h_map_smul : ∀ (α : Fin m → Fin (Module.finrank ℝ E)),
      f (fun i => (v i (α i)) •
          EuclideanSpace.single (α i) (1 : ℝ)) =
        (∏ i : Fin m, v i (α i)) • f (basisTupleE (E := E) α) := by
    intro α
    classical
    have h := f.toMultilinearMap.map_smul_univ
      (fun i : Fin m => v i (α i))
      (fun i : Fin m => EuclideanSpace.single (α i) (1 : ℝ))
    simpa [basisTupleE] using h
  have h_each : ∀ α : Fin m → Fin (Module.finrank ℝ E),
      |f (fun i => (v i (α i)) •
          EuclideanSpace.single (α i) (1 : ℝ))| ≤
        |f (basisTupleE (E := E) α)| * ∏ i : Fin m, ‖v i‖ := by
    intro α
    rw [h_map_smul α, smul_eq_mul, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod
    · intros; exact abs_nonneg _
    · intro i _; exact euclN_coord_abs_le_norm (v i) (α i)
  refine le_trans (Finset.sum_le_sum (fun α _ => h_each α)) ?_
  rw [← Finset.sum_mul]

/-- The basis-tuple evaluation is bounded by the operator norm. -/
private lemma abs_apply_basisTupleE_le_opNorm {m : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ)
    (α : Fin m → Fin (Module.finrank ℝ E)) :
    |f (basisTupleE (E := E) α)| ≤ ‖f‖ := by
  have h := f.le_opNorm (basisTupleE (E := E) α)
  rw [basisTupleE_prod_norms (E := E) α, mul_one] at h
  exact h

/-- The Euclidean pull-back of a raw `(r, s)`-component of a tensor `S`:
the chart-frame scalar component post-composed with the chart inverse and the
Euclidean representation map.  (A non-private analogue of the forward file's
`rawPull`, usable across tensor valences.) -/
def rawPullR (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
    ∘ (extChartAt I α).symm
    ∘ (toEuclidean (E := E)).symm

lemma rawPullR_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      rawPullR (I := I) (M := M) g r s S α Idx Jdx := rfl

/-- `rawPullR` is `C^∞` on the (open) Euclidean chart target. -/
lemma rawPullR_contDiffOn (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (rawPullR (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  refine (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s S α Idx Jdx).congr (fun y hy => ?_)
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]; rfl

lemma rawPullR_contDiffAt (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawPullR (I := I) (M := M) g r s S α Idx Jdx) y :=
  (rawPullR_contDiffOn (I := I) (M := M) g r s S α Idx Jdx).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

/-- Near an interior point of the chart target, `chartPushedRaw I α (raw S
component)` agrees with the plain `rawPullR` of the same component, so their
iterated Fréchet derivatives coincide there. -/
private lemma chartPushedRaw_eventuallyEq_rawPullR (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) =ᶠ[nhds y]
      rawPullR (I := I) (M := M) g r s S α Idx Jdx := by
  filter_upwards [(chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy] with z hz
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]; rfl

/-- The order-`0` chart content of `S` at chart `α` and point `y`: the sum over
all component multi-index pairs of the magnitude of the chart-pulled raw
component.  This is the (square-root-free) `L¹` analogue of the order-`0`
Hilbert-Schmidt content. -/
def zeroContentR (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (y : EuclN) : ℝ :=
  ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y|

lemma zeroContentR_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (y : EuclN) :
    0 ≤ zeroContentR (I := I) (M := M) g r s S α y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- A single chart-pulled raw component magnitude is bounded by the order-`0`
content. -/
lemma abs_rawPullR_le_zeroContentR (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    |rawPullR (I := I) (M := M) g r s S α Idx Jdx y| ≤
      zeroContentR (I := I) (M := M) g r s S α y := by
  classical
  set f : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun q => |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y| with hf
  have h : f ⟨Idx, Jdx⟩ ≤ ∑ q, f q :=
    Finset.single_le_sum (f := f) (fun q _ => abs_nonneg _) (Finset.mem_univ _)
  simpa [zeroContentR, hf] using h

/-- **The rearranged chart formula.** At an interior chart-target point `y`, the
`m`-th coordinate partial of a chart-pulled raw component of `S` equals the
chart-pulled raw `(m ::ᵥ Jdx')`-component of `covGrad S` minus the zeroth-order
Christoffel correction `covDerivLowerOrderTerm`. -/
lemma fderiv_rawPullR_single_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (rawPullR (I := I) (M := M) g r s S α Idx Jdx') y
        (EuclideanSpace.single m 1) =
      rawPullR (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)
          α Idx (Matrix.vecCons m Jdx') y -
        covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx' y := by
  classical
  have hJ0 : (Matrix.vecCons m Jdx' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0 = m := rfl
  have hJtail : Matrix.vecTail (Matrix.vecCons m Jdx' :
      Fin (s + 1) → Fin (Module.finrank ℝ E)) = Jdx' := by
    funext j; simp [Matrix.vecTail, Matrix.vecCons]
  have hform := tensorChartComponentRaw_covGrad (I := I) (M := M) g r s S α Idx
    (Matrix.vecCons m Jdx') hy
  rw [hJ0, hJtail] at hform
  have h_fderiv_eq :
      euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx')) y =
        fderiv ℝ (rawPullR (I := I) (M := M) g r s S α Idx Jdx') y
          (EuclideanSpace.single m 1) := by
    rw [euclidPartial_def]
    have h_ev := chartPushedRaw_eventuallyEq_rawPullR (I := I) (M := M)
      g r s S α Idx Jdx' hy
    rw [Filter.EventuallyEq.fderiv_eq h_ev]
  have hform' :
      rawPullR (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)
          α Idx (Matrix.vecCons m Jdx') y =
        fderiv ℝ (rawPullR (I := I) (M := M) g r s S α Idx Jdx') y
            (EuclideanSpace.single m 1) +
          covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx' y := by
    rw [rawPullR, Function.comp_apply, Function.comp_apply]
    rw [hform, h_fderiv_eq]
  linarith [hform']

lemma exists_iteratedFDeriv_norm_bound_on_compactR
    {f : EuclN → ℝ} {s : Set EuclN} (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    {K : Set EuclN} (hK : IsCompact K) (hKs : K ⊆ s) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ≤ N, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ C := by
  classical
  have h_uniq : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have h_per_order : ∀ l : ℕ, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ Cl := by
    intro l
    by_cases hKne : K.Nonempty
    · have h_iter_contOn : ContinuousOn (fun y => iteratedFDerivWithin ℝ l f s y) s :=
        hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) h_uniq
      have h_iter_K : ContinuousOn (iteratedFDerivWithin ℝ l f s) K :=
        h_iter_contOn.mono hKs
      have h_norm_K : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ l f s y‖) K :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _, hy₀_max⟩ := hK.exists_isMaxOn hKne h_norm_K
      refine ⟨‖iteratedFDerivWithin ℝ l f s y₀‖, norm_nonneg _, fun y hy => ?_⟩
      have h₁ : ‖iteratedFDerivWithin ℝ l f s y‖ ≤
          ‖iteratedFDerivWithin ℝ l f s y₀‖ := hy₀_max hy
      rwa [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) l hs (hKs hy)] at h₁
    · exact ⟨0, le_refl _, fun y hy => absurd ⟨y, hy⟩ hKne⟩
  choose Cl hCl_nn hCl using h_per_order
  refine ⟨(Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ Cl, ?_, ?_⟩
  · exact le_trans (hCl_nn 0)
      (Finset.le_sup' Cl (Finset.mem_range.mpr (Nat.succ_pos N)))
  · intro l hl y hy
    exact (hCl l y hy).trans
      (Finset.le_sup' Cl (Finset.mem_range.mpr (by omega)))

/-- **The uniform lower-order Christoffel-coefficient bound** (re-derived).  Over
all the lower-order correction coefficients `covDerivLowerOrderCoeff` — for the
differentiation direction `m`, the source input multi-index `Idx`, the source
output multi-index `Jdx'`, and the target multi-index pair `p` — up to iterated
Fréchet order `N`, the operator norm is bounded by a single non-negative `C` on
the compact partition-of-unity kernel `chartImagePOUTsupport α`. -/
lemma exists_lowerOrderCoeff_uniform_boundR
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) y‖ ≤ C := by
  classical
  have hK_compact : IsCompact (chartImagePOUTsupport (I := I) (M := M) α) :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_per : ∀ (w : Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))),
      ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
        ‖iteratedFDeriv ℝ l
          (covDerivLowerOrderCoeff (I := I) (M := M) g r s α w.1 w.2.1
            w.2.2.2.1 w.2.2.1 w.2.2.2.2) y‖ ≤ Cw :=
    fun w => exists_iteratedFDeriv_norm_bound_on_compactR
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α w.1 w.2.1
        w.2.2.2.1 w.2.2.1 w.2.2.2.2)
      h_open hK_compact hK_sub N
  choose Cw hCw_nn hCw using h_per
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))))).sup'
      ⟨⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩, Finset.mem_univ _⟩ Cw, ?_, ?_⟩
  · refine le_trans (hCw_nn ⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩) ?_
    exact Finset.le_sup' Cw (Finset.mem_univ _)
  · intro m Idx Jdx' p l hl y hy
    exact (hCw ⟨m, Idx, Jdx', p⟩ l hl y hy).trans
      (Finset.le_sup' Cw (Finset.mem_univ ⟨m, Idx, Jdx', p⟩))

/-- **One-order Fréchet peeling.** For `u` smooth on the open chart target and
`y` in it, `‖D^{j+1} u y‖ ≤ n^j · ∑_m ‖D^j (euclidPartial m u) y‖`. -/
lemma iteratedFDeriv_succ_norm_le_sum_euclidPartial
    {u : EuclN → ℝ} {O : Set EuclN} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (j : ℕ) {y : EuclN} (hy : y ∈ O) :
    ‖iteratedFDeriv ℝ (j + 1) u y‖ ≤
      ((Module.finrank ℝ E) ^ j : ℝ) *
        ∑ m : Fin (Module.finrank ℝ E),
          ‖iteratedFDeriv ℝ j
            (fun z => euclidPartial (E := E) m u z) y‖ := by
  classical
  have h_uniq : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  have hfd_cdOn : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z) O :=
    hu.fderiv_of_isOpen hO (by rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl])
  have h_op := opNorm_le_sum_basisE (E := E) (iteratedFDeriv ℝ (j + 1) u y)
  have h_peel : ∀ β : Fin (j + 1) → Fin (Module.finrank ℝ E),
      |(iteratedFDeriv ℝ (j + 1) u y) (basisTupleE (E := E) β)| ≤
        ‖iteratedFDeriv ℝ j
          (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) y‖ := by
    intro β
    have h_snoc : (basisTupleE (E := E) β) =
        Fin.snoc (fun i : Fin j => EuclideanSpace.single (β i.castSucc) (1 : ℝ))
          (EuclideanSpace.single (β (Fin.last j)) (1 : ℝ)) := by
      funext i
      induction i using Fin.lastCases with
      | last => simp [basisTupleE]
      | cast k => simp [basisTupleE]
    rw [h_snoc, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
    have hfd_cd_at : ContDiffAt ℝ ∞ (fun z => fderiv ℝ u z) y :=
      hfd_cdOn.contDiffAt (hO.mem_nhds hy)
    have h_clm : iteratedFDeriv ℝ j (fun z => fderiv ℝ u z) y
          (fun i : Fin j => EuclideanSpace.single (β i.castSucc) (1 : ℝ))
          (EuclideanSpace.single (β (Fin.last j)) (1 : ℝ)) =
        iteratedFDeriv ℝ j
          (fun z => (fderiv ℝ u z) (EuclideanSpace.single (β (Fin.last j)) (1 : ℝ))) y
          (fun i : Fin j => EuclideanSpace.single (β i.castSucc) (1 : ℝ)) := by
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
            (f := fun z => fderiv ℝ u z) j hO hy,
          ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
            (f := fun z => (fderiv ℝ u z) (EuclideanSpace.single (β (Fin.last j)) (1 : ℝ)))
            j hO hy]
      exact (iteratedFDerivWithin_clm_apply_const_apply h_uniq hfd_cdOn
        (by exact_mod_cast le_top) hy).symm
    rw [h_clm]
    have h_funeq : (fun z => (fderiv ℝ u z) (EuclideanSpace.single (β (Fin.last j)) (1 : ℝ)))
        = (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) := rfl
    rw [h_funeq]
    exact abs_apply_basisTupleE_le_opNorm (E := E)
      (iteratedFDeriv ℝ j (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) y)
      (fun i : Fin j => β i.castSucc)
  calc ‖iteratedFDeriv ℝ (j + 1) u y‖
      ≤ ∑ β : Fin (j + 1) → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ (j + 1) u y) (basisTupleE (E := E) β)| := h_op
    _ ≤ ∑ β : Fin (j + 1) → Fin (Module.finrank ℝ E),
          ‖iteratedFDeriv ℝ j
            (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) y‖ :=
        Finset.sum_le_sum (fun β _ => h_peel β)
    _ ≤ ((Module.finrank ℝ E) ^ j : ℝ) *
          ∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ j
              (fun z => euclidPartial (E := E) m u z) y‖ := by
        rw [Finset.mul_sum]
        have h_eq : (∑ β : Fin (j + 1) → Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) y‖) =
            ∑ w : Fin (Module.finrank ℝ E) × (Fin j → Fin (Module.finrank ℝ E)),
                ‖iteratedFDeriv ℝ j
                  (fun z => euclidPartial (E := E) w.1 u z) y‖ := by
          refine (Fintype.sum_equiv
            (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin (Module.finrank ℝ E)))
            (fun w => ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E) w.1 u z) y‖)
            (fun β => ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E) (β (Fin.last j)) u z) y‖)
            (fun w => ?_)).symm
          change ‖iteratedFDeriv ℝ j (fun z => euclidPartial (E := E) w.1 u z) y‖ =
              ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E)
                  ((Fin.snocEquiv (fun _ : Fin (j + 1) =>
                    Fin (Module.finrank ℝ E)) w) (Fin.last j)) u z) y‖
          have hlast : (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin (Module.finrank ℝ E)) w)
              (Fin.last j) = w.1 := by
            simp [Fin.snocEquiv]
          rw [hlast]
        rw [h_eq, Fintype.sum_prod_type]
        refine Finset.sum_le_sum (fun m _ => ?_)
        simp only
        rw [Finset.sum_const, Finset.card_univ]
        rw [show (Fintype.card (Fin j → Fin (Module.finrank ℝ E))) =
            (Module.finrank ℝ E) ^ j by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]]
        rw [nsmul_eq_mul]
        push_cast
        exact le_refl _

lemma lowerOrderTerm_iteratedFDeriv_norm_leR
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M) (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx' : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j
        (fun z => covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx' z) y‖ ≤
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l
              (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) y‖ *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPullR (I := I) (M := M) g r s S α p.1 p.2) y‖ := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  set Lfun : EuclN → ℝ := fun z =>
    ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2 z *
        rawPullR (I := I) (M := M) g r s S α p.1 p.2 z with hLfun_def
  have hL_eq : (fun z => covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx' z)
      = Lfun := by
    funext z
    rw [hLfun_def, covDerivLowerOrderTerm_def]
    rfl
  rw [hL_eq, ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Lfun) j h_open hy]
  have h_coeff_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2)
        s_set y := fun p =>
    ((covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1
      Jdx' p.2).of_le (by exact_mod_cast le_top)) y hy
  have h_raw_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j (rawPullR (I := I) (M := M) g r s S α p.1 p.2)
        s_set y := fun p =>
    ((rawPullR_contDiffOn (I := I) (M := M) g r s S α p.1 p.2).of_le
      (by exact_mod_cast le_top)) y hy
  have h_prod_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j
        (fun z => covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2 z *
          rawPullR (I := I) (M := M) g r s S α p.1 p.2 z) s_set y := fun p =>
    (h_coeff_cdwa p).mul (h_raw_cdwa p)
  rw [iteratedFDerivWithin_fun_sum_apply h_uniq hy (fun p _ => h_prod_cdwa p)]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p _ => ?_))
  have h_coeff_cdon : ContDiffOn ℝ j
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) s_set :=
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1
      Jdx' p.2).of_le (by exact_mod_cast le_top)
  have h_raw_cdon : ContDiffOn ℝ j
      (rawPullR (I := I) (M := M) g r s S α p.1 p.2) s_set :=
    (rawPullR_contDiffOn (I := I) (M := M) g r s S α p.1 p.2).of_le
      (by exact_mod_cast le_top)
  have hmul := norm_iteratedFDerivWithin_mul_le h_coeff_cdon h_raw_cdon h_uniq hy
    (le_refl (j : WithTop ℕ∞))
  refine le_trans hmul (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2)
        l h_open hy,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := rawPullR (I := I) (M := M) g r s S α p.1 p.2) (j - l) h_open hy]

lemma exists_christoffel_bound_valence_range
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (P N : ℕ) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ p ≤ P,
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin (s + p) → Fin (Module.finrank ℝ E))
        (q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + p) → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx q.1 Jdx' q.2)
            y‖ ≤ Γ := by
  classical
  have hper : ∀ p : ℕ, ∃ Γ : ℝ, 0 ≤ Γ ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin (s + p) → Fin (Module.finrank ℝ E))
        (q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + p) → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx q.1 Jdx' q.2)
            y‖ ≤ Γ :=
    fun p => exists_lowerOrderCoeff_uniform_boundR (I := I) (M := M) g r (s + p) α N
  choose Γf hΓf_nn hΓf using hper
  refine ⟨(Finset.range (P + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos P)⟩ Γf, ?_, ?_⟩
  · exact le_trans (hΓf_nn 0)
      (Finset.le_sup' Γf (Finset.mem_range.mpr (Nat.succ_pos P)))
  · intro p hp m Idx Jdx' q l hl y hy
    exact (hΓf p m Idx Jdx' q l hl y hy).trans
      (Finset.le_sup' Γf (Finset.mem_range.mpr (by omega)))

/-- **The pointwise reverse-peeling.** Fix a smooth compactly-supported tensor
`T`, a chart `α`, and an order bound `P`.  For every Fréchet order `j ≤ P` there
is a non-negative constant `C` such that for every order `l ≤ j`, every `p` with
`p + l ≤ P`, every component `(Idx, Jdx)` of `∇^p T`, and every `y` in the
compact kernel `chartImagePOUTsupport α`,
`‖D^l (rawPullR (∇^p T) Idx Jdx) y‖ ≤ C · ∑_{i ≤ l} zeroContentR (∇^{p+i} T) α y`.
The single constant `C` covers all orders `l ≤ j`, which is what the Leibniz
lower-order term of the inductive step consumes. -/
lemma iteratedFDeriv_rawPullR_le_zeroContent_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : ℕ) :
    ∀ j : ℕ, j ≤ P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s)
        (l : ℕ), l ≤ j → ∀ (p : ℕ), p + l ≤ P →
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin (s + p) → Fin (Module.finrank ℝ E)),
          ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
            ‖iteratedFDeriv ℝ l
                (rawPullR (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) y‖ ≤
              C * ∑ i ∈ Finset.range (l + 1),
                zeroContentR (I := I) (M := M) g r (s + (p + i))
                  (iteratedCovGrad g r s (p + i) T) α y := by
  classical
  obtain ⟨Γ, hΓ_nn, hΓ⟩ :=
    exists_christoffel_bound_valence_range (I := I) (M := M) g r s α P P
  set n : ℕ := Module.finrank ℝ E with hn_def
  intro j
  induction j with
  | zero =>
      intro _hP
      refine ⟨1, zero_le_one, fun T l hl p _ Idx Jdx y hy => ?_⟩
      have hl0 : l = 0 := Nat.le_zero.mp hl
      subst hl0
      rw [norm_iteratedFDeriv_zero,
        show (Finset.range (0 + 1)) = {0} from rfl, Finset.sum_singleton]
      simp only [Nat.add_zero, one_mul]
      have h1 := abs_rawPullR_le_zeroContentR (I := I) (M := M) g r (s + p)
        (iteratedCovGrad g r s p T) α Idx Jdx y
      calc ‖rawPullR (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx y‖
          = |rawPullR (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx y| := Real.norm_eq_abs _
        _ ≤ zeroContentR (I := I) (M := M) g r (s + (p + 0))
              (iteratedCovGrad g r s (p + 0) T) α y := by
            rw [Nat.add_zero]; exact h1
  | succ j ih =>
      intro hjP
      obtain ⟨Cj, hCj_nn, hCj⟩ := ih (by omega)
      set Np : ℝ := (n : ℝ) ^ (r + (s + P)) with hNp_def
      have hNp_nn : 0 ≤ Np := by positivity
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n); exact_mod_cast this
      set Cstep : ℝ := (n : ℝ) ^ j *
        (Cj + (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj) with hCstep_def
      have hCstep_nn : 0 ≤ Cstep := by
        rw [hCstep_def]; positivity
      refine ⟨max Cj ((n : ℝ) * Cstep), le_max_of_le_left hCj_nn, ?_⟩
      intro T l hl p hpl Idx Jdx y hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hl) with hlj | hlj
      · have hl' : l ≤ j := by omega
        have hbase := hCj T l hl' p (by omega) Idx Jdx y hy
        refine le_trans hbase ?_
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact Finset.sum_nonneg (fun i _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
      · subst hlj
        have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α :=
          chartImagePOUTsupport_subset_target (I := I) (M := M) α hy
        set RHSsum : ℝ := ∑ i ∈ Finset.range ((j + 1) + 1),
          zeroContentR (I := I) (M := M) g r (s + (p + i))
            (iteratedCovGrad g r s (p + i) T) α y with hRHSsum_def
        have hRHSsum_nn : 0 ≤ RHSsum :=
          Finset.sum_nonneg (fun i _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
        set Cm : ℝ := Cj + (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj with hCm_def
        have hCm_nn : 0 ≤ Cm := by rw [hCm_def]; positivity
        have h_perm : ∀ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ j
                (fun z => euclidPartial (E := E) m
                  (rawPullR (I := I) (M := M) g r (s + p)
                    (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖ ≤
              Cm * RHSsum := by
          intro m
          set u : EuclN → ℝ := rawPullR (I := I) (M := M) g r (s + p)
            (iteratedCovGrad g r s p T) α Idx Jdx with hu_def
          set A : EuclN → ℝ := rawPullR (I := I) (M := M) g r ((s + p) + 1)
            (covGrad (I := I) (M := M) g r (s + p) (iteratedCovGrad g r s p T))
            α Idx (Matrix.vecCons m Jdx) with hA_def
          set B : EuclN → ℝ := fun z => covDerivLowerOrderTerm (I := I) (M := M)
            g r (s + p) (iteratedCovGrad g r s p T) α m Idx Jdx z with hB_def
          have h_evEq : (fun z => euclidPartial (E := E) m u z) =ᶠ[nhds y]
              (fun z => A z - B z) := by
            have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
              chartTargetEuclid_isOpen (I := I) (M := M) α
            filter_upwards [h_open.mem_nhds hy_mem] with z hz
            rw [euclidPartial_def]
            exact fderiv_rawPullR_single_eq (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α m Idx Jdx hz
          rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq j).self_of_nhds]
          have hA_cdAt : ContDiffAt ℝ ∞ A y :=
            rawPullR_contDiffAt (I := I) (M := M) g r ((s + p) + 1)
              (covGrad (I := I) (M := M) g r (s + p) (iteratedCovGrad g r s p T))
              α Idx (Matrix.vecCons m Jdx) hy_mem
          have hB_cdAt : ContDiffAt ℝ ∞ B y := by
            rw [hB_def]
            have h_cdOn := covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
              g r (s + p) (iteratedCovGrad g r s p T) α m Idx Jdx
              (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
                (I := I) (M := M) g r (s + p) (iteratedCovGrad g r s p T) α Idx' Jdx')
            exact h_cdOn.contDiffAt
              ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy_mem)
          have hjle : (j : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
          rw [show (fun z => A z - B z) = (A - B) from rfl,
            iteratedFDeriv_sub_apply (hA_cdAt.of_le hjle) (hB_cdAt.of_le hjle)]
          refine le_trans (norm_sub_le _ _) ?_
          have h_lead : ‖iteratedFDeriv ℝ j A y‖ ≤ Cj * RHSsum := by
            have hstep := hCj T j (le_refl j) (p + 1) (by omega) Idx
              (Matrix.vecCons m Jdx) y hy
            have hA_eq : iteratedFDeriv ℝ j A y =
                iteratedFDeriv ℝ j
                  (rawPullR (I := I) (M := M) g r (s + (p + 1))
                    (iteratedCovGrad g r s (p + 1) T) α Idx (Matrix.vecCons m Jdx)) y := rfl
            rw [hA_eq]
            refine le_trans hstep ?_
            apply mul_le_mul_of_nonneg_left _ hCj_nn
            calc (∑ i ∈ Finset.range (j + 1),
                  zeroContentR (I := I) (M := M) g r (s + ((p + 1) + i))
                    (iteratedCovGrad g r s ((p + 1) + i) T) α y)
                = ∑ i ∈ Finset.range (j + 1),
                    zeroContentR (I := I) (M := M) g r (s + (p + (i + 1)))
                      (iteratedCovGrad g r s (p + (i + 1)) T) α y := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [show (p + 1) + i = p + (i + 1) by ring]
              _ ≤ RHSsum := by
                  rw [hRHSsum_def]
                  rw [Finset.sum_range_succ' (fun i =>
                    zeroContentR (I := I) (M := M) g r (s + (p + i))
                      (iteratedCovGrad g r s (p + i) T) α y) (j + 1)]
                  have hlast_nn : 0 ≤ zeroContentR (I := I) (M := M) g r (s + (p + 0))
                      (iteratedCovGrad g r s (p + 0) T) α y :=
                    zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _
                  linarith
          have h_lower : ‖iteratedFDeriv ℝ j B y‖ ≤
              (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj * RHSsum := by
            have hleib := lowerOrderTerm_iteratedFDeriv_norm_leR (I := I) (M := M)
              g r (s + p) (iteratedCovGrad g r s p T) α m Idx Jdx j hy_mem
            rw [hB_def]
            refine le_trans hleib ?_
            have hp_le_P : p ≤ P := by omega
            have h_per : ∀ q : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin (s + p) → Fin (Module.finrank ℝ E)),
                (∑ l' ∈ Finset.range (j + 1),
                  (j.choose l' : ℝ) *
                    ‖iteratedFDeriv ℝ l'
                      (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                        q.1 Jdx q.2) y‖ *
                    ‖iteratedFDeriv ℝ (j - l')
                      (rawPullR (I := I) (M := M) g r (s + p)
                        (iteratedCovGrad g r s p T) α q.1 q.2) y‖) ≤
                  ((2 : ℝ) ^ j) * (Γ * Cj * RHSsum) := by
              intro q
              have h1 : (∑ l' ∈ Finset.range (j + 1),
                  (j.choose l' : ℝ) *
                    ‖iteratedFDeriv ℝ l'
                      (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                        q.1 Jdx q.2) y‖ *
                    ‖iteratedFDeriv ℝ (j - l')
                      (rawPullR (I := I) (M := M) g r (s + p)
                        (iteratedCovGrad g r s p T) α q.1 q.2) y‖) ≤
                  ∑ l' ∈ Finset.range (j + 1),
                    (j.choose l' : ℝ) * (Γ * Cj * RHSsum) := by
                refine Finset.sum_le_sum (fun l' hl' => ?_)
                have hl'j : l' ≤ j := by have := Finset.mem_range.mp hl'; omega
                have hl'P : l' ≤ P := le_trans hl'j (by omega)
                have hΓ_bd : ‖iteratedFDeriv ℝ l'
                    (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                      q.1 Jdx q.2) y‖ ≤ Γ :=
                  hΓ p hp_le_P m Idx Jdx q l' hl'P y hy
                have hraw_bd : ‖iteratedFDeriv ℝ (j - l')
                    (rawPullR (I := I) (M := M) g r (s + p)
                      (iteratedCovGrad g r s p T) α q.1 q.2) y‖ ≤ Cj * RHSsum := by
                  have hsub : j - l' ≤ j := Nat.sub_le j l'
                  have hpj : p + j ≤ P := by omega
                  have hpP : p + (j - l') ≤ P :=
                    le_trans (Nat.add_le_add_left hsub p) hpj
                  have hih := hCj T (j - l') hsub p hpP q.1 q.2 y hy
                  refine le_trans hih ?_
                  apply mul_le_mul_of_nonneg_left _ hCj_nn
                  rw [hRHSsum_def]
                  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                    (fun i _ _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
                  have hle : j - l' + 1 ≤ j + 1 + 1 :=
                    Nat.succ_le_succ (le_trans (Nat.sub_le j l') (Nat.le_succ j))
                  intro x hx
                  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hle)
                have h_choose_nn : 0 ≤ (j.choose l' : ℝ) := by positivity
                have hraw_nn : 0 ≤ ‖iteratedFDeriv ℝ (j - l')
                    (rawPullR (I := I) (M := M) g r (s + p)
                      (iteratedCovGrad g r s p T) α q.1 q.2) y‖ := norm_nonneg _
                have hΓCj_nn : 0 ≤ Γ * Cj * RHSsum := by positivity
                calc (j.choose l' : ℝ) *
                      ‖iteratedFDeriv ℝ l'
                        (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                          q.1 Jdx q.2) y‖ *
                      ‖iteratedFDeriv ℝ (j - l')
                        (rawPullR (I := I) (M := M) g r (s + p)
                          (iteratedCovGrad g r s p T) α q.1 q.2) y‖
                    ≤ (j.choose l' : ℝ) * Γ * (Cj * RHSsum) := by
                      have ha : (j.choose l' : ℝ) *
                          ‖iteratedFDeriv ℝ l'
                            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                              q.1 Jdx q.2) y‖ ≤ (j.choose l' : ℝ) * Γ :=
                        mul_le_mul_of_nonneg_left hΓ_bd h_choose_nn
                      calc (j.choose l' : ℝ) *
                            ‖iteratedFDeriv ℝ l'
                              (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                                q.1 Jdx q.2) y‖ *
                            ‖iteratedFDeriv ℝ (j - l')
                              (rawPullR (I := I) (M := M) g r (s + p)
                                (iteratedCovGrad g r s p T) α q.1 q.2) y‖
                          ≤ ((j.choose l' : ℝ) * Γ) * (Cj * RHSsum) := by
                            refine mul_le_mul ha hraw_bd hraw_nn ?_
                            positivity
                        _ = (j.choose l' : ℝ) * Γ * (Cj * RHSsum) := by ring
                  _ = (j.choose l' : ℝ) * (Γ * Cj * RHSsum) := by ring
              have h2 : (∑ l' ∈ Finset.range (j + 1), (j.choose l' : ℝ)) = (2 : ℝ) ^ j := by
                rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
              calc (∑ l' ∈ Finset.range (j + 1),
                    (j.choose l' : ℝ) *
                      ‖iteratedFDeriv ℝ l'
                        (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                          q.1 Jdx q.2) y‖ *
                      ‖iteratedFDeriv ℝ (j - l')
                        (rawPullR (I := I) (M := M) g r (s + p)
                          (iteratedCovGrad g r s p T) α q.1 q.2) y‖)
                  ≤ ∑ l' ∈ Finset.range (j + 1), (j.choose l' : ℝ) * (Γ * Cj * RHSsum) := h1
                _ = ((2 : ℝ) ^ j) * (Γ * Cj * RHSsum) := by
                    rw [← Finset.sum_mul, h2]
            calc (∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin (s + p) → Fin (Module.finrank ℝ E)),
                  ∑ l' ∈ Finset.range (j + 1),
                    (j.choose l' : ℝ) *
                      ‖iteratedFDeriv ℝ l'
                        (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m Idx
                          q.1 Jdx q.2) y‖ *
                      ‖iteratedFDeriv ℝ (j - l')
                        (rawPullR (I := I) (M := M) g r (s + p)
                          (iteratedCovGrad g r s p T) α q.1 q.2) y‖)
                ≤ ∑ _q : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin (s + p) → Fin (Module.finrank ℝ E)),
                    ((2 : ℝ) ^ j) * (Γ * Cj * RHSsum) :=
                  Finset.sum_le_sum (fun q _ => h_per q)
              _ = (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin (s + p) → Fin (Module.finrank ℝ E))) : ℝ) *
                    (((2 : ℝ) ^ j) * (Γ * Cj * RHSsum)) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              _ ≤ (Np : ℝ) * (((2 : ℝ) ^ j) * (Γ * Cj * RHSsum)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [show (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin (s + p) → Fin (Module.finrank ℝ E)))) =
                      n ^ (r + (s + p)) by
                    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
                      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]]
                  rw [hNp_def]
                  exact_mod_cast pow_le_pow_right₀ hn1 (by omega)
              _ = (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj * RHSsum := by ring
          calc ‖iteratedFDeriv ℝ j A y‖ + ‖iteratedFDeriv ℝ j B y‖
              ≤ Cj * RHSsum + (Np : ℝ) * ((2 : ℝ) ^ j) * Γ * Cj * RHSsum :=
                add_le_add h_lead h_lower
            _ = Cm * RHSsum := by rw [hCm_def]; ring
        have h_peel := iteratedFDeriv_succ_norm_le_sum_euclidPartial (E := E)
          (u := rawPullR (I := I) (M := M) g r (s + p)
            (iteratedCovGrad g r s p T) α Idx Jdx)
          (O := chartTargetEuclid (I := I) (M := M) α)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (rawPullR_contDiffOn (I := I) (M := M) g r (s + p)
            (iteratedCovGrad g r s p T) α Idx Jdx) j hy_mem
        have h_sum_le : (∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ j
              (fun z => euclidPartial (E := E) m
                (rawPullR (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖) ≤
            (n : ℝ) * (Cm * RHSsum) := by
          calc (∑ m : Fin (Module.finrank ℝ E),
                ‖iteratedFDeriv ℝ j
                  (fun z => euclidPartial (E := E) m
                    (rawPullR (I := I) (M := M) g r (s + p)
                      (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖)
              ≤ ∑ _m : Fin (Module.finrank ℝ E), Cm * RHSsum :=
                Finset.sum_le_sum (fun m _ => h_perm m)
            _ = (n : ℝ) * (Cm * RHSsum) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn_def]
        have h_final : ‖iteratedFDeriv ℝ (j + 1)
            (rawPullR (I := I) (M := M) g r (s + p)
              (iteratedCovGrad g r s p T) α Idx Jdx) y‖ ≤
            ((n : ℝ) * Cstep) * RHSsum := by
          calc ‖iteratedFDeriv ℝ (j + 1)
                (rawPullR (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad g r s p T) α Idx Jdx) y‖
              ≤ ((Module.finrank ℝ E) ^ j : ℝ) *
                  ∑ m : Fin (Module.finrank ℝ E),
                    ‖iteratedFDeriv ℝ j
                      (fun z => euclidPartial (E := E) m
                        (rawPullR (I := I) (M := M) g r (s + p)
                          (iteratedCovGrad g r s p T) α Idx Jdx) z) y‖ := h_peel
            _ ≤ ((Module.finrank ℝ E) ^ j : ℝ) * ((n : ℝ) * (Cm * RHSsum)) := by
                apply mul_le_mul_of_nonneg_left h_sum_le (by positivity)
            _ = ((n : ℝ) * Cstep) * RHSsum := by
                rw [hCstep_def, hCm_def, hn_def]; ring
        refine le_trans h_final ?_
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) hRHSsum_nn

/-- The order-`0` Hilbert-Schmidt content of `S` at chart `α`, point `y`: the sum
over all component pairs of the *squared* chart-pulled raw component. -/
private def hsZeroContentR (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (y : EuclN) : ℝ :=
  ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y| ^ 2

private lemma hsZeroContentR_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (y : EuclN) :
    0 ≤ hsZeroContentR (I := I) (M := M) g r s S α y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **Cauchy–Schwarz on the order-`0` content.** `zeroContentR² ≤ Np ·
hsZeroContentR`, where `Np` is the number of component pairs of `S`. -/
private lemma zeroContentR_sq_le_card_mul_hsZeroContentR
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (y : EuclN) :
    (zeroContentR (I := I) (M := M) g r s S α y) ^ 2 ≤
      (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) : ℝ) *
        hsZeroContentR (I := I) (M := M) g r s S α y := by
  classical
  rw [zeroContentR, hsZeroContentR]
  have hcs : (∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y|) ^ 2 ≤
      ((Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))))
      (f := fun q => |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y|)
  rw [Finset.card_univ] at hcs
  exact hcs

/-- The pushed partition-of-unity weight `ρ_α` vanishes at chart-target points
outside the compact kernel `chartImagePOUTsupport α`. -/
private lemma pouPull_eq_zero_off_kernelR (α : M) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  by_contra hne
  have hb_supp : b ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hne)
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_round : (extChartAt I α) b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  apply hy_off
  refine ⟨(extChartAt I α) b, ⟨b, hb_supp, rfl⟩, ?_⟩
  rw [h_round]; simp

/-- **The per-chart pointwise integrand bound.** For a chart `α`, an order `k`,
and `y` in the chart target, the partition-of-unity-weighted full order-`2k`
Hilbert-Schmidt sum of the chart-pulled `(r, s)`-components of `T` is bounded by
`C · ρ_α · ∑_{i ≤ 2k} hsZeroContentR (∇^i T)`. -/
private lemma reverse_pointwise_integrand_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g r s) {y : EuclN},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
      ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
        C *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ i ∈ Finset.range (2 * k + 1),
              hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y) := by
  classical
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum (I := I) (M := M) g r s α (2 * k)
      (2 * k) (le_refl _)
  set n : ℕ := Module.finrank ℝ E with hn_def
  set NpT : ℝ := (Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) : ℝ) with hNpT_def
  set Npmax : ℝ := (n : ℝ) ^ (r + (s + 2 * k)) with hNpmax_def
  have hNpT_nn : 0 ≤ NpT := by positivity
  have hNpmax_nn : 0 ≤ Npmax := by positivity
  refine ⟨NpT * ((2 * k + 1 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * k)) *
      (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax), by positivity, ?_⟩
  intro T y hy
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
  set Z : ℝ := ∑ i ∈ Finset.range (2 * k + 1),
    hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
      (iteratedCovGrad g r s (0 + i) T) α y with hZ_def
  have hZ_nn : 0 ≤ Z := Finset.sum_nonneg (fun i _ =>
    hsZeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
  by_cases hyK : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · have hblock : ∀ (IJ : (Fin r → Fin n) × (Fin s → Fin n)) (j : ℕ),
        j ∈ Finset.range (2 * k + 1) →
        (∑ bIdx : Fin j → Fin n,
          |(iteratedFDeriv ℝ j
                (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2) ≤
          ((n : ℝ) ^ (2 * k)) *
            (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z) := by
      intro IJ j hj
      have hjk : j ≤ 2 * k := by have := Finset.mem_range.mp hj; omega
      set Fop : ℝ := ‖iteratedFDeriv ℝ j
        (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y‖ with hFop_def
      have h_eval_le : ∀ bIdx : Fin j → Fin n,
          |(iteratedFDeriv ℝ j
              (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2 ≤ Fop ^ 2 := by
        intro bIdx
        have h_le := abs_apply_basisTupleE_le_opNorm (E := E)
          (iteratedFDeriv ℝ j (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y) bIdx
        have h_abs_nn : 0 ≤ |(iteratedFDeriv ℝ j
            (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
            (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| := abs_nonneg _
        refine pow_le_pow_left₀ h_abs_nn ?_ 2
        simpa [basisTupleE, EuclideanSpace.basisFun_apply, hn_def] using h_le
      have hFop_le : Fop ≤ Cpeel * ∑ i ∈ Finset.range (j + 1),
          zeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y := by
        have := hCpeel T j hjk 0 (by omega) IJ.1 IJ.2 y hyK
        simpa using this
      have hFop_sq : Fop ^ 2 ≤ Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z := by
        have hFop_nn : 0 ≤ Fop := norm_nonneg _
        have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 1),
            zeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y :=
          Finset.sum_nonneg (fun i _ => zeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
        have h1 : Fop ^ 2 ≤ Cpeel ^ 2 * (∑ i ∈ Finset.range (j + 1),
            zeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y) ^ 2 := by
          have := pow_le_pow_left₀ hFop_nn hFop_le 2
          rw [mul_pow] at this; exact this
        have h2 : (∑ i ∈ Finset.range (j + 1),
            zeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y) ^ 2 ≤
            ((j + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 1),
              (zeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y) ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
            (f := fun i => zeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y)
          rwa [Finset.card_range] at this
        have h3 : (∑ i ∈ Finset.range (j + 1),
            (zeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y) ^ 2) ≤ Npmax * Z := by
          have hstep : ∀ i ∈ Finset.range (j + 1),
              (zeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y) ^ 2 ≤
              Npmax * hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y := by
            intro i hi
            have hcs := zeroContentR_sq_le_card_mul_hsZeroContentR (I := I) (M := M)
              g r (s + (0 + i)) (iteratedCovGrad g r s (0 + i) T) α y
            refine le_trans hcs ?_
            apply mul_le_mul_of_nonneg_right _
              (hsZeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
            rw [show (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin (s + (0 + i)) → Fin (Module.finrank ℝ E)))) =
                n ^ (r + (s + (0 + i))) by
              rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
                Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add, hn_def]]
            rw [hNpmax_def]
            have hexp : r + (s + (0 + i)) ≤ r + (s + 2 * k) := by
              have := Finset.mem_range.mp hi; omega
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
              have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n); exact_mod_cast this
            exact_mod_cast pow_le_pow_right₀ hn1 hexp
          calc (∑ i ∈ Finset.range (j + 1),
                (zeroContentR (I := I) (M := M) g r (s + (0 + i))
                  (iteratedCovGrad g r s (0 + i) T) α y) ^ 2)
              ≤ ∑ i ∈ Finset.range (j + 1),
                  Npmax * hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                    (iteratedCovGrad g r s (0 + i) T) α y :=
                Finset.sum_le_sum hstep
            _ = Npmax * ∑ i ∈ Finset.range (j + 1),
                  hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                    (iteratedCovGrad g r s (0 + i) T) α y := by rw [Finset.mul_sum]
            _ ≤ Npmax * Z := by
                apply mul_le_mul_of_nonneg_left _ hNpmax_nn
                rw [hZ_def]
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                  (fun i _ _ => hsZeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _)
                intro x hx
                exact Finset.mem_range.mpr
                  (lt_of_lt_of_le (Finset.mem_range.mp hx)
                    (Nat.succ_le_succ hjk))
        calc Fop ^ 2
            ≤ Cpeel ^ 2 * (∑ i ∈ Finset.range (j + 1),
                zeroContentR (I := I) (M := M) g r (s + (0 + i))
                  (iteratedCovGrad g r s (0 + i) T) α y) ^ 2 := h1
          _ ≤ Cpeel ^ 2 * (((j + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 1),
              (zeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ Cpeel ^ 2 * (((2 * k + 1 : ℕ) : ℝ) * (Npmax * Z)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul _ h3 (by positivity) (by positivity)
              exact_mod_cast Nat.succ_le_succ hjk
          _ = Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z := by ring
      calc (∑ bIdx : Fin j → Fin n,
            |(iteratedFDeriv ℝ j
                  (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2)
          ≤ ∑ _bIdx : Fin j → Fin n, Fop ^ 2 :=
            Finset.sum_le_sum (fun bIdx _ => h_eval_le bIdx)
        _ = ((n : ℝ) ^ j) * Fop ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            congr 1
            rw [show (Fintype.card (Fin j → Fin n)) = n ^ j by
              rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]]
            push_cast; ring
        _ ≤ ((n : ℝ) ^ (2 * k)) * (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z) := by
            apply mul_le_mul _ hFop_sq (sq_nonneg _) (by positivity)
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
              have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n); exact_mod_cast this
            exact pow_le_pow_right₀ hn1 hjk
    have hLHS_le : (∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ bIdx : Fin j → Fin n,
            |(iteratedFDeriv ℝ j
                  (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2) ≤
        NpT * ((2 * k + 1 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * k)) *
          (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z) := by
      have hper_IJ : ∀ IJ : (Fin r → Fin n) × (Fin s → Fin n),
          (∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin n,
              |(iteratedFDeriv ℝ j
                    (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2) ≤
          ((2 * k + 1 : ℕ) : ℝ) * (((n : ℝ) ^ (2 * k)) *
            (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z)) := by
        intro IJ
        calc (∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin n,
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2)
            ≤ ∑ _j ∈ Finset.range (2 * k + 1),
                ((n : ℝ) ^ (2 * k)) *
                  (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z) :=
              Finset.sum_le_sum (fun j hj => hblock IJ j hj)
          _ = ((2 * k + 1 : ℕ) : ℝ) * (((n : ℝ) ^ (2 * k)) *
              (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc (∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin n,
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2)
          ≤ ∑ _IJ : (Fin r → Fin n) × (Fin s → Fin n),
              ((2 * k + 1 : ℕ) : ℝ) * (((n : ℝ) ^ (2 * k)) *
                (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z)) :=
            Finset.sum_le_sum (fun IJ _ => hper_IJ IJ)
        _ = NpT * ((2 * k + 1 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * k)) *
            (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpT_def]; ring
    calc ρ * (∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin n,
              |(iteratedFDeriv ℝ j
                    (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2)
        ≤ ρ * (NpT * ((2 * k + 1 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * k)) *
            (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax * Z)) :=
          mul_le_mul_of_nonneg_left hLHS_le hρ_nn
      _ = (NpT * ((2 * k + 1 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * k)) *
            (Cpeel ^ 2 * ((2 * k + 1 : ℕ) : ℝ) * Npmax)) * (ρ * Z) := by ring
  · have hρ0 : ρ = 0 :=
      pouPull_eq_zero_off_kernelR (I := I) (M := M) α y hy hyK
    rw [hρ0]; simp

/-- AEMeasurability of one Hilbert-Schmidt integrand term (a partition-of-unity-
weighted squared basis-evaluation of an iterated derivative of a raw component). -/
private lemma rawPullRIntegrand_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (l : ℕ)
    (bIdx : Fin l → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN => ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawPullR (I := I) (M := M) g r s S α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_iter_contOn :
      ContinuousOn (iteratedFDeriv ℝ l (rawPullR (I := I) (M := M) g r s S α q.1 q.2))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    have h_cd : ContDiffAt ℝ ∞ (rawPullR (I := I) (M := M) g r s S α q.1 q.2) y :=
      rawPullR_contDiffAt (I := I) (M := M) g r s S α q.1 q.2 hy
    exact (h_cd.continuousAt_iteratedFDeriv (k := l)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_eval : ContinuousOn
      (fun y : EuclN => (iteratedFDeriv ℝ l (rawPullR (I := I) (M := M) g r s S α q.1 q.2) y)
          (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (continuous_eval_const _).comp_continuousOn h_iter_contOn
  have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).continuous
  have h_inner : ContinuousOn
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (continuousOn_extChartAt_symm α).comp
      (toEuclidean (E := E)).symm.continuous.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hpou : ContinuousOn
      (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    hPOU_cont.comp_continuousOn h_inner
  have h_real : ContinuousOn
      (fun y : EuclN => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawPullR (I := I) (M := M) g r s S α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    hpou.mul (h_eval.abs.pow 2)
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (h_real.aestronglyMeasurable h_open.measurableSet).aemeasurable

/-- The chart-`α` Hilbert-Schmidt inner double-sum-of-integrals of a tensor `S`
equals the integral of the partition-of-unity-weighted full Hilbert-Schmidt
content.  (Tonelli for finite sums + `ofReal` of a non-negative finite sum.) -/
private lemma sumIntegrals_eq_integral_sumR
    (g : SmoothRiemannianMetric I M) (r' s' : ℕ) (S : SmoothCcTensor g r' s')
    (α : M) (K : ℕ) :
    (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                  (Fin s' → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  |(iteratedFDeriv ℝ j
                        (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
  classical
  have h_bIdx : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))) (j : ℕ),
      (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ j
    rw [MeasureTheory.lintegral_finset_sum' _
      (fun bIdx _ => rawPullRIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)]
  have h_j : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))),
      (∑ j ∈ Finset.range K,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ
    have hmeas : ∀ j ∈ Finset.range K,
        AEMeasurable (fun y : EuclN =>
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
      intro j _
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
        (fun bIdx (_ : bIdx ∈ Finset.univ) =>
          rawPullRIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)
      refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
      rw [Finset.sum_apply]
    rw [MeasureTheory.lintegral_finset_sum' _ hmeas]
  calc (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
      = ∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
            ∂(volume : Measure EuclN) := by
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [← h_j IJ]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← h_bIdx IJ j]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
              (Fin s' → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        have hmeas2 : ∀ IJ ∈ (Finset.univ : Finset ((Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)))),
            AEMeasurable (fun y : EuclN =>
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
              ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
          intro IJ _
          have h := Finset.aemeasurable_sum (Finset.range K)
            (fun j (_ : j ∈ Finset.range K) =>
              (Finset.aemeasurable_sum
                (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
                (fun bIdx (_ : bIdx ∈ Finset.univ) =>
                  rawPullRIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)).congr
                (Filter.EventuallyEq.of_eq (funext (fun y => by rw [Finset.sum_apply]))))
          refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
          rw [Finset.sum_apply]
        rw [MeasureTheory.lintegral_finset_sum' _ hmeas2]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                    (Fin s' → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range K,
                  ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                    |(iteratedFDeriv ℝ j
                          (rawPullR (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        refine setLIntegral_congr_fun
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
        set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
        have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun IJ _ => mul_nonneg hρ_nn (Finset.sum_nonneg
              (fun j _ => Finset.sum_nonneg (fun bIdx _ => sq_nonneg _))))]
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun j _ => mul_nonneg hρ_nn (Finset.sum_nonneg (fun bIdx _ => sq_nonneg _)))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg (fun bIdx _ => mul_nonneg hρ_nn (sq_nonneg _))]

/-- The chart-`α` order-`0` inner sum of `∇^i T` equals the integral of the
partition-of-unity-weighted order-`0` Hilbert-Schmidt content `hsZeroContentR`. -/
private lemma rhsInner_eq_integral_hsZeroContent
    (g : SmoothRiemannianMetric I M) (r s i : ℕ) (T : SmoothCcTensor g r s)
    (α : M) :
    (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin (s + (0 + i)) → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * 0 + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPullR (I := I) (M := M) g r (s + (0 + i))
                          (iteratedCovGrad g r s (0 + i) T) α IJ.1 IJ.2) y)
                      (fun ii => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx ii))| ^ 2)
              ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α y)
        ∂(volume : Measure EuclN) := by
  classical
  rw [sumIntegrals_eq_integral_sumR (I := I) (M := M) g r (s + (0 + i))
    (iteratedCovGrad g r s (0 + i) T) α (2 * 0 + 1)]
  refine setLIntegral_congr_fun
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
  congr 1
  congr 1
  rw [hsZeroContentR]
  refine Finset.sum_congr rfl (fun IJ _ => ?_)
  rw [show (Finset.range (2 * 0 + 1)) = {0} from rfl, Finset.sum_singleton]
  rw [Fintype.sum_unique (fun bIdx : Fin 0 → Fin (Module.finrank ℝ E) =>
    |(iteratedFDeriv ℝ 0
        (rawPullR (I := I) (M := M) g r (s + (0 + i))
          (iteratedCovGrad g r s (0 + i) T) α IJ.1 IJ.2) y)
      (fun ii => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx ii))| ^ 2)]
  rw [iteratedFDeriv_zero_apply]

/-- **The per-chart inner bound.** For each chart `α`, the chart-`α` order-`2k`
Hilbert-Schmidt inner sum of `T` is bounded by `ofReal C` times the sum over
`i ≤ 2k` of the chart-`α` order-`0` inner sums of `∇^i T`. -/
private lemma reverse_per_alpha_inner_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (C : ℝ) (hC_nn : 0 ≤ C)
    (hpt : ∀ {y : EuclN}, y ∈ chartTargetEuclid (I := I) (M := M) α →
      ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawPullR (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
        C *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ i ∈ Finset.range (2 * k + 1),
              hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y)) :
    (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN)) ≤
      ENNReal.ofReal C *
        ∑ i ∈ Finset.range (2 * k + 1),
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin (s + (0 + i)) → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * 0 + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r (s + (0 + i))
                                (iteratedCovGrad g r s (0 + i) T) α IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun ii => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx ii))| ^ 2)
                  ∂(volume : Measure EuclN)) := by
  classical
  simp only [rawPullR_eq (I := I) (M := M)]
  rw [sumIntegrals_eq_integral_sumR (I := I) (M := M) g r s T α (2 * k + 1)]
  rw [show (∑ i ∈ Finset.range (2 * k + 1),
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin (s + (0 + i)) → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * 0 + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPullR (I := I) (M := M) g r (s + (0 + i))
                          (iteratedCovGrad g r s (0 + i) T) α IJ.1 IJ.2) y)
                      (fun ii => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx ii))| ^ 2)
              ∂(volume : Measure EuclN))) =
      ∑ i ∈ Finset.range (2 * k + 1),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) T) α y)
          ∂(volume : Measure EuclN) from
    Finset.sum_congr rfl (fun i _ =>
      rhsInner_eq_integral_hsZeroContent (I := I) (M := M) g r s i T α)]
  rw [← MeasureTheory.lintegral_finset_sum']
  swap
  · intro i _
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hcont : ContinuousOn
        (fun y : EuclN => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have hpou : ContinuousOn
          (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
        have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).continuous
        refine hPOU_cont.comp_continuousOn ?_
        refine (continuousOn_extChartAt_symm α).comp
          (toEuclidean (E := E)).symm.continuous.continuousOn ?_
        intro y hy
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
        exact hy
      have hhs : ContinuousOn
          (fun y : EuclN => hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y)
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine continuousOn_finset_sum _ (fun q _ => ?_)
        have h_cont : ContinuousOn
            (rawPullR (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad g r s (0 + i) T) α q.1 q.2)
            (chartTargetEuclid (I := I) (M := M) α) :=
          (rawPullR_contDiffOn (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α q.1 q.2).continuousOn
        exact (h_cont.abs.pow 2)
      exact hpou.mul hhs
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hcont.aestronglyMeasurable h_open.measurableSet).aemeasurable
  rw [← MeasureTheory.lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top (r := C))]
  refine setLIntegral_mono_ae'
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    (Filter.Eventually.of_forall (fun y hy => ?_))
  have hpt' := hpt hy
  have h_rhs_nn : 0 ≤ ((chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        ∑ i ∈ Finset.range (2 * k + 1),
          hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y :=
    mul_nonneg ((chartAtlasPOU I M).nonneg α _)
      (Finset.sum_nonneg (fun i _ => hsZeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _))
  rw [show (∑ i ∈ Finset.range (2 * k + 1),
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y)) =
      ENNReal.ofReal (∑ i ∈ Finset.range (2 * k + 1),
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          hsZeroContentR (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y) from
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ((chartAtlasPOU I M).nonneg α _)
      (hsZeroContentR_nonneg (I := I) (M := M) _ _ _ _ _ _))).symm]
  rw [← ENNReal.ofReal_mul hC_nn, ← Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal hpt'

/-- The chart-`α` order-`2k` Hilbert-Schmidt inner sum of `T` (the per-chart
summand of `tensorPouSobolevHsNormSq g k T`). -/
@[reducible] private def reverseLhsInner (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : SmoothCcTensor g r s) (α : M) : ℝ≥0∞ :=
  ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
    ∑ j ∈ Finset.range (2 * k + 1),
      ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

/-- The chart-`α` order-`0` Hilbert-Schmidt inner sum of `∇^i T` (the per-chart
summand of `tensorPouSobolevHsNormSq g 0 (∇^i T)`). -/
@[reducible] private def reverseRhsInner (g : SmoothRiemannianMetric I M) (r s _k : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (i : ℕ) : ℝ≥0∞ :=
  ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin (s + (0 + i)) → Fin (Module.finrank ℝ E)),
    ∑ j ∈ Finset.range (2 * 0 + 1),
      ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r (s + (0 + i))
                        (iteratedCovGrad g r s (0 + i) T) α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun ii => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx ii))| ^ 2)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

/-- **The squared-norm reverse order-peeling.** There is a non-negative constant
`C` such that for every smooth compactly-supported `(r, s)`-tensor `T`,
`tensorPouSobolevHsNormSq g k T ≤ ENNReal.ofReal C ·
  ∑_{i ∈ range (2k+1)} tensorPouSobolevHsNormSq g 0 (∇^i T)`. -/
private lemma exists_tensorPouSobolevHsNormSq_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        tensorPouSobolevHsNormSq (I := I) (M := M) g k T ≤
          ENNReal.ofReal C *
            ∑ i ∈ Finset.range (2 * k + 1),
              tensorPouSobolevHsNormSq (I := I) (M := M) g 0
                (iteratedCovGrad g r s (0 + i) T) := by
  classical
  choose Cα hCα_nn hCα using fun α =>
    reverse_pointwise_integrand_le (I := I) (M := M) g r s k α
  set actF : Finset M := chartAtlasPOU_activeFinset I M with hactF_def
  set Cmax : ℝ := ∑ α ∈ actF, Cα α with hCmax_def
  have hCmax_nn : 0 ≤ Cmax := Finset.sum_nonneg (fun α _ => hCα_nn α)
  have hCmax_ge : ∀ α ∈ actF, Cα α ≤ Cmax :=
    fun α hα => Finset.single_le_sum (fun β _ => hCα_nn β) hα
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩
  rw [tensorPouSobolevHsNormSq_eq_inner_sum]
  have h_perα : ∀ α : M,
      (reverseLhsInner (I := I) (M := M) g r s k T α) ≤
        ENNReal.ofReal Cmax * ∑ i ∈ Finset.range (2 * k + 1),
          reverseRhsInner (I := I) (M := M) g r s k T α i := by
    intro α
    by_cases hα : α ∈ actF
    · have hbound := reverse_per_alpha_inner_bound (I := I) (M := M) g r s k T α
        (Cα α) (hCα_nn α) (fun {y} hy => hCα α T hy)
      refine le_trans hbound ?_
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hCmax_ge α hα)) (zero_le _)
    · have hρ0 : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
        chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
      have hlhs0 : reverseLhsInner (I := I) (M := M) g r s k T α = 0 := by
        unfold reverseLhsInner
        refine Finset.sum_eq_zero (fun IJ _ => Finset.sum_eq_zero (fun j _ =>
          Finset.sum_eq_zero (fun bIdx _ => ?_)))
        refine MeasureTheory.setLIntegral_eq_zero
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
        simp only [Pi.zero_apply]
        have hzero : ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = 0 := hρ0 _
        rw [hzero, zero_mul, ENNReal.ofReal_zero]
      rw [hlhs0]; exact zero_le _
  simp only [reverseLhsInner, reverseRhsInner] at h_perα
  refine le_trans (ENNReal.tsum_le_tsum h_perα) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorPouSobolevHsNormSq_eq_inner_sum]

/-- For a finite family of `ℝ≥0∞`, the sum of squares is bounded by the square of
the sum (cross terms are non-negative). -/
private lemma enn_sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  calc ∑ i ∈ s, f i ^ 2
      = ∑ i ∈ s, f i * f i := by simp [sq]
    _ ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j :=
        Finset.sum_le_sum (fun i hi => by
          gcongr
          exact Finset.single_le_sum (fun j _ => zero_le _) hi)
    _ = (∑ i ∈ s, f i) * (∑ j ∈ s, f j) := by rw [← Finset.sum_mul]
    _ = (∑ i ∈ s, f i) ^ 2 := by rw [sq]

/-- **The reverse-Christoffel order-peeling.** There is a non-negative constant
`C` such that for every smooth compactly-supported `(r, s)`-tensor `T`, the
order-`2k` Hilbert-Schmidt chart-Sobolev norm of `T` is bounded by `C` times the
sum, over `j ≤ 2k`, of the order-`0` Hilbert-Schmidt chart-Sobolev norms of the
iterated covariant gradients `∇^j T`:
`tensorPouSobolevHsNorm g k T ≤ ENNReal.ofReal C ·
  ∑_{j ∈ range (2k+1)} tensorPouSobolevHsNorm g 0 (∇^j T)`.

This is the order-peeling half of the reverse Sobolev bridge: the higher-order
chart-Sobolev content of `T` is recovered, up to uniform Christoffel-controlled
constants, from the order-`0` content of its iterated covariant gradients. -/
theorem exists_tensorPouSobolevHsNorm_le_iteratedCovGrad_zero_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g k T ≤
          ENNReal.ofReal C *
            ∑ j ∈ Finset.range (2 * k + 1),
              tensorPouSobolevHsNorm (I := I) (M := M) g 0
                (iteratedCovGrad g r s j T) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := exists_tensorPouSobolevHsNormSq_le (I := I) (M := M) g r s k
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, fun T => ?_⟩
  set a : ℕ → ℝ≥0∞ := fun j => tensorPouSobolevHsNorm (I := I) (M := M) g 0
    (iteratedCovGrad g r s (0 + j) T) with ha_def
  have hsq : (tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2 ≤
      ENNReal.ofReal C₀ * ∑ j ∈ Finset.range (2 * k + 1), (a j) ^ 2 := by
    have h := hC₀ T
    rw [tensorPouSobolevHsNormSq] at h
    simp only [tensorPouSobolevHsNormSq, ha_def] at h ⊢
    exact h
  have hsq' : (tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2 ≤
      ENNReal.ofReal C₀ * (∑ j ∈ Finset.range (2 * k + 1), a j) ^ 2 := by
    refine le_trans hsq ?_
    gcongr
    exact enn_sum_sq_le_sq_sum (Finset.range (2 * k + 1)) a
  have hrpow : ((tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal C₀ * (∑ j ∈ Finset.range (2 * k + 1), a j) ^ 2) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hsq' (by norm_num)
  have hlhs : ((tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2) ^ (1 / 2 : ℝ) =
      tensorPouSobolevHsNorm (I := I) (M := M) g k T := by
    rw [← ENNReal.rpow_natCast (tensorPouSobolevHsNorm (I := I) (M := M) g k T) 2,
      ← ENNReal.rpow_mul]
    norm_num
  have hrhs : (ENNReal.ofReal C₀ * (∑ j ∈ Finset.range (2 * k + 1), a j) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt C₀) * ∑ j ∈ Finset.range (2 * k + 1), a j := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    · rw [ENNReal.ofReal_rpow_of_nonneg hC₀_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
    · rw [← ENNReal.rpow_natCast (∑ j ∈ Finset.range (2 * k + 1), a j) 2,
        ← ENNReal.rpow_mul]
      norm_num
  rw [hlhs, hrhs] at hrpow
  have hreindex : (∑ j ∈ Finset.range (2 * k + 1), a j) =
      ∑ j ∈ Finset.range (2 * k + 1),
        tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change tensorPouSobolevHsNorm (I := I) (M := M) g 0
        (iteratedCovGrad g r s (0 + j) T) =
      tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T)
    rw [show (0 + j) = j from Nat.zero_add j]
  rw [hreindex] at hrpow
  exact hrpow

end ReversePeeling

end DifferentialGeometry.PDE.RicciFlow

end
