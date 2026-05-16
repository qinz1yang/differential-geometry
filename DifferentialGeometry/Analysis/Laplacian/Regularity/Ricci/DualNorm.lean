import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianCandidate
import DifferentialGeometry.Geometry.Gradient

/-!
# Chart-local expression for the metric-Riesz dual norm of the Ricci covector

For a smooth Riemannian metric `g` on a smooth manifold `(M, g)` and a smooth
scalar `φ : C^∞⟮I, M; ℝ⟯`, the function

```
b ↦ ‖ricciTensor g b (∇φ b, ·)‖²_{g-Riesz dual}
```

is the squared `g`-Riesz dual norm of the cotangent vector
`ricciTensor g b (∇φ b, ·) : T_bM →L ℝ`. By the Riesz isomorphism, this equals
`g_b(R(b), R(b))` where `R(b) := metricSharp g b (ricciTensor g b (∇φ b, ·)).toLinearMap`.

In chart coordinates at `α : M`, on the chart base set, this admits the
explicit formula

```
g(R(b), R(b)) = ∑_{i, j} α_i(b) · α_j(b) · chartInvGramMatrix g α b i j,
```

where `α_i(b) := ricciTensor g b (∇φ b, chartBasisVecFiber α i b)` are the
chart-basis coordinates of the covector. Both `α_i(b)` and
`chartInvGramMatrix g α b i j` are smooth in `b` on the chart base set, so
the sum is smooth.

This file establishes:

* `chartRicciDualNormSq g α φ : M → ℝ` — the chart-local explicit
  expression for `g(R, R)`.
* `chartRicciDualNormSq_contMDiffOn` — smoothness on the chart base set.
* `chartRicciDualNormSq_eq_inner` — the chart-local expression equals
  `g_b(R(b), R(b))` for `b` on the chart base set.

The eventual goal is to assemble a finite chart cover into a global sup
bound, but that piece is deferred to follow-up work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace RicciDualNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The chart-basis components of the Ricci covector

For a smooth scalar `φ`, the function
`b ↦ ricciTensor g b (∇φ b) (chartBasisVecFiber α j b)`
gives the `j`-th chart-basis component of the cotangent vector
`ricciTensor g b (∇φ b, ·) : T_bM →L ℝ`. These components are smooth on
the chart base set. -/

/-- The `j`-th chart-basis component of the Ricci-applied covector
`Ric(∇φ b, ·)` at point `b`, in the chart at `α`. -/
noncomputable def ricciCovectorChartCoord
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) (b : M) : ℝ :=
  ricciTensor (I := I) g b (gradFun (I := I) g φ b)
    (chartBasisVecFiber (I := I) α j b)

@[simp] lemma ricciCovectorChartCoord_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) (b : M) :
    ricciCovectorChartCoord (I := I) g α φ j b =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (chartBasisVecFiber (I := I) α j b) := rfl

/-- The chart-basis component is smooth on the chart base set. The argument:
`ricciTensor g b` is a smooth (0,2)-tensor section, `gradFun g φ` is a smooth
tangent section (globally), and `chartBasisVec α j` is a smooth tangent section
on the base set. Applying the smooth (0,2)-tensor bilinearly to the two
sections produces a smooth scalar (on the base set). -/
theorem ricciCovectorChartCoord_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (ricciCovectorChartCoord (I := I) g α φ j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- View the Ricci tensor as a (0,2)-tensor smooth section globally.
  have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
        (ricciTensor (I := I) g b)) :=
    ricciTensor_contMDiff (I := I) g
  -- Gradient `∇φ` is smooth globally.
  have hGrad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g φ b)) :=
    gradFun_contMDiff_total_section (I := I) g φ.contMDiff
  -- Chart-basis vector is smooth on the base set.
  have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_contMDiffOn (I := I) α j
  -- Apply ContMDiffOn.clm_bundle_apply₂ to combine.
  have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b,
          ricciTensor (I := I) g b
            (gradFun (I := I) g φ b)
            (chartBasisVecFiber (I := I) α j b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic.contMDiffOn hGrad.contMDiffOn hBasis
  -- The target equals `fun b => ricciTensor g b (∇φ b) (chartBasisVec α j b)` definitionally.
  change ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (chartBasisVecFiber (I := I) α j b))
      (trivializationAt E (TangentSpace I) α).baseSet
  intro b hb
  have hpb := happ b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

/-! ## The chart-local expression for `g(R, R)`

`R(b) := metricSharp g b (Ric(∇φ b, ·).toLinearMap)` is the `g`-Riesz lift of
the Ricci-applied covector. By the Riesz identity and the chart-coordinate
expansion,

```
g_b(R(b), R(b)) = ∑_{i, j} α_i(b) · α_j(b) · G⁻¹_{ij}(b),
```

where `α_j(b) := ricciCovectorChartCoord g α φ j b` and `G⁻¹_{ij}(b) :=
chartInvGramMatrix g α b i j`. -/

/-- The chart-local expression for the `g`-Riesz dual norm squared of the
Ricci covector, in the chart at `α`. -/
noncomputable def chartRicciDualNormSq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ricciCovectorChartCoord (I := I) g α φ i b *
      ricciCovectorChartCoord (I := I) g α φ j b *
      chartInvGramMatrix (I := I) g α b i j

@[simp] lemma chartRicciDualNormSq_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    chartRicciDualNormSq (I := I) g α φ b =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ricciCovectorChartCoord (I := I) g α φ i b *
          ricciCovectorChartCoord (I := I) g α φ j b *
          chartInvGramMatrix (I := I) g α b i j := rfl

/-! ## Smoothness of the chart-local expression -/

/-- The chart-local expression for `g(R, R)` is smooth on the chart base
set. Each summand is a product of three smooth functions: two copies of
`ricciCovectorChartCoord` and one of `chartInvGramMatrix`. -/
theorem chartRicciDualNormSq_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartRicciDualNormSq (I := I) g α φ)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartRicciDualNormSq
  refine contMDiffOn_finset_sum (fun i _ => ?_)
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  -- Each summand: `ricciCovectorChartCoord i · ricciCovectorChartCoord j · chartInvGramMatrix ij`.
  have h1 := ricciCovectorChartCoord_contMDiffOn (I := I) g α φ i
  have h2 := ricciCovectorChartCoord_contMDiffOn (I := I) g α φ j
  have h3 := chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  exact (h1.mul h2).mul h3

/-! ## Continuity on the chart base set -/

/-- The chart-local expression is continuous on the chart base set. -/
theorem chartRicciDualNormSq_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) :
    ContinuousOn (chartRicciDualNormSq (I := I) g α φ)
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (chartRicciDualNormSq_contMDiffOn (I := I) g α φ).continuousOn

/-! ## Sup on compact subsets of the chart base set

For a compact subset `K` of the chart base set, the chart-local expression
attains a finite supremum. This is the chart-local building block for the
global sup. -/

/-- For a compact subset `K` of the chart base set, the chart-local
expression attains a non-negative finite supremum. -/
theorem chartRicciDualNormSq_bdd_on_compact
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {K : Set M} (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, chartRicciDualNormSq (I := I) g α φ b ≤ C := by
  classical
  -- Continuity on K (restriction of continuity on baseSet).
  have h_cont : ContinuousOn (chartRicciDualNormSq (I := I) g α φ) K :=
    (chartRicciDualNormSq_continuousOn (I := I) g α φ).mono hK_subset
  -- Image of compact under continuous-on is compact, hence bounded.
  by_cases hK_ne : K.Nonempty
  · -- K nonempty: use exists_isMaxOn.
    obtain ⟨b_max, hb_max_mem, hb_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne h_cont
    refine ⟨max (chartRicciDualNormSq (I := I) g α φ b_max) 0, le_max_right _ _, ?_⟩
    intro b hb
    have h := hb_max hb
    -- h : chartRicciDualNormSq g α φ b ≤ chartRicciDualNormSq g α φ b_max.
    exact h.trans (le_max_left _ _)
  · -- K empty: trivially bounded by 0.
    refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    exfalso; exact hK_ne ⟨b, hb⟩

/-! ## The Riesz lift of the Ricci covector

The pointwise `R(b) := metricSharp g b (Ric(∇φ b, ·).toLinearMap)`. -/

/-- The Riesz lift of the Ricci covector `Ric(∇φ b, ·)` at `b`. -/
noncomputable def ricciSharp (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) : TangentSpace I b :=
  metricSharp (I := I) g b
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap

@[simp] lemma ricciSharp_def (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    ricciSharp (I := I) g φ b =
      metricSharp (I := I) g b
        (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap := rfl

/-- Defining identity: `g_b(R(b), w) = Ric(∇φ b, w)` for any tangent vector `w`. -/
lemma inner_ricciSharp (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) (w : TangentSpace I b) :
    g.inner b (ricciSharp (I := I) g φ b) w =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b) w := by
  rw [ricciSharp_def]
  exact inner_metricSharp (I := I) g b
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b)).toLinearMap w

/-- Symmetric form: `g_b(w, R(b)) = Ric(∇φ b, w)` for any `w`. -/
lemma inner_ricciSharp_right (g : SmoothRiemannianMetric I M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) (w : TangentSpace I b) :
    g.inner b w (ricciSharp (I := I) g φ b) =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b) w := by
  rw [g.symm b w (ricciSharp (I := I) g φ b)]
  exact inner_ricciSharp (I := I) g φ b w

/-! ## Chart-basis decomposition of `ricciSharp`

We claim `ricciSharp g φ b` equals
`∑_k (∑_j G⁻¹_{kj} α_j(b)) • e_k(b)` on the base set, where `α_j(b)`
are the chart-coordinate covector components and `G⁻¹_{kj}(b)` is the
inverse Gram matrix. This is the chart-coordinate formula for the
Riesz dual lift. -/

/-- The chart-coordinate expansion coefficient for `ricciSharp`. -/
noncomputable def ricciSharpChartCoeff
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (k : Fin (Module.finrank ℝ E)) (b : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α b k j *
      ricciCovectorChartCoord (I := I) g α φ j b

@[simp] lemma ricciSharpChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (k : Fin (Module.finrank ℝ E)) (b : M) :
    ricciSharpChartCoeff (I := I) g α φ k b =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b k j *
          ricciCovectorChartCoord (I := I) g α φ j b := rfl

/-- The chart-local linear-combination representative of `ricciSharp`. -/
noncomputable def ricciSharpChartLocal
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (b : M) : TangentSpace I b :=
  ∑ k : Fin (Module.finrank ℝ E),
    ricciSharpChartCoeff (I := I) g α φ k b •
      chartBasisVecFiber (I := I) α k b

/-! ## Key Riesz identity for the chart-local sharp

For `b` in the chart base set and any `k`, we have
`g_b(ricciSharpChartLocal, e_k(b)) = ricciCovectorChartCoord g α φ k b`. -/

/-- The chart-local inner-product identity for the Riesz lift in chart
coordinates. The proof mirrors `inner_gradChartLocal_chartBasis`. -/
lemma inner_ricciSharpChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (chartBasisVecFiber (I := I) α k b) =
      ricciCovectorChartCoord (I := I) g α φ k b := by
  classical
  unfold ricciSharpChartLocal
  -- LHS: g.inner b (∑ i, a_i • e_i) e_k = ∑ i, a_i * G_{ik}
  -- where `a_i = ricciSharpChartCoeff i b`.
  rw [show g.inner b (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              chartBasisVecFiber (I := I) α i b)
            (chartBasisVecFiber (I := I) α k b) =
          ∑ i, ricciSharpChartCoeff (I := I) g α φ i b *
            g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · -- finite-sum expansion of g.inner.
    rw [show (g.inner b (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                chartBasisVecFiber (I := I) α i b)) =
            (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                g.inner b (chartBasisVecFiber (I := I) α i b)) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  -- Substitute `ricciSharpChartCoeff i b = ∑ j, G⁻¹_{ij} α_j(b)`.
  have ha : ∀ i, ricciSharpChartCoeff (I := I) g α φ i b =
      ∑ j, chartInvGramMatrix (I := I) g α b i j *
        ricciCovectorChartCoord (I := I) g α φ j b := fun i => rfl
  rw [show ∑ i, ricciSharpChartCoeff (I := I) g α φ i b *
            g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartBasisVecFiber (I := I) α k b) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
              ricciCovectorChartCoord (I := I) g α φ j b) *
              chartGramMatrix (I := I) g α b i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    rfl
  -- Now interchange sums and use the Gram-inverse identity.
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
              ricciCovectorChartCoord (I := I) g α φ j b) *
                chartGramMatrix (I := I) g α b i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
              chartGramMatrix (I := I) g α b i k) *
            ricciCovectorChartCoord (I := I) g α φ j b from ?_]
  swap
  · rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α b i j *
                ricciCovectorChartCoord (I := I) g α φ j b) *
                  chartGramMatrix (I := I) g α b i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α b i j *
                  chartGramMatrix (I := I) g α b i k) *
                  ricciCovectorChartCoord (I := I) g α φ j b from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  -- Now use ∑ i, Ginv_{ij} * G_{ik} = δ_{jk}.
  have hsym : ∀ i, chartGramMatrix (I := I) g α b i k =
      chartGramMatrix (I := I) g α b k i := fun i => g.symm b _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
        chartGramMatrix (I := I) g α b i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α b i j *
              chartGramMatrix (I := I) g α b i k) =
            (∑ i, chartGramMatrix (I := I) g α b k i *
              chartInvGramMatrix (I := I) g α b i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    have hidentity : (chartGramMatrix (I := I) g α b *
          chartInvGramMatrix (I := I) g α b) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α b i j *
            chartGramMatrix (I := I) g α b i k) *
              ricciCovectorChartCoord (I := I) g α φ j b =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            ricciCovectorChartCoord (I := I) g α φ j b from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ## `ricciSharpChartLocal` equals `ricciSharp` on the base set

Two tangent vectors agree iff their inner products with all chart-basis
vectors agree (since `chartBasisFamily` is a basis). Combining the
chart-local inner-product identity with the defining identity for
`ricciSharp`, we conclude. -/

/-- On the chart base set, the chart-local linear-combination representative
of the Riesz dual equals the abstract pointwise Riesz dual `ricciSharp`. -/
lemma ricciSharpChartLocal_eq_ricciSharp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ricciSharpChartLocal (I := I) g α φ b =
      ricciSharp (I := I) g φ b := by
  classical
  apply metricFlatLinear_injective (I := I) g b
  ext v
  change g.inner b (ricciSharpChartLocal (I := I) g α φ b) v =
    g.inner b (ricciSharp (I := I) g φ b) v
  -- Replace the RHS by `Ric(∇φ b, v)` via `inner_ricciSharp`.
  rw [inner_ricciSharp (I := I) g φ b v]
  -- Decompose `v = ∑ k, c k • e_k b`.
  set bs : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
    chartBasisFamily (I := I) α hb
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => bs.repr v k
  have hv_decomp : v = ∑ k, c k • chartBasisVecFiber (I := I) α k b := by
    have h1 : v = ∑ k, bs.repr v k • bs k := (bs.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartBasisFamily_apply (I := I) α hb k]
  rw [hv_decomp]
  -- LHS and RHS are both linear in `v`, so commute with the finite sum.
  rw [show g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (∑ k, c k • chartBasisVecFiber (I := I) α k b) =
        ∑ k, c k * g.inner b (ricciSharpChartLocal (I := I) g α φ b)
          (chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show (ricciTensor (I := I) g b (gradFun (I := I) g φ b))
        (∑ k, c k • chartBasisVecFiber (I := I) α k b) =
        ∑ k, c k *
          (ricciTensor (I := I) g b (gradFun (I := I) g φ b))
            (chartBasisVecFiber (I := I) α k b) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_ricciSharpChartLocal_chartBasis (I := I) g α φ hb k]
  rfl

/-! ## The identity: `chartRicciDualNormSq = g(R, R)` on the base set

The chart-local formula `chartRicciDualNormSq g α φ b` equals
`g_b(R(b), R(b))` where `R(b) := ricciSharp g φ b`. -/

/-- Helper: pointwise bilinear expansion of
`g.inner b ricciSharpChartLocal ricciSharpChartLocal`. The inner-product
of two linear combinations expands as a double Gram-matrix sum. -/
private lemma inner_ricciSharpChartLocal_self_eq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯) (b : M) :
    g.inner b (ricciSharpChartLocal (I := I) g α φ b)
        (ricciSharpChartLocal (I := I) g α φ b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          chartGramMatrix (I := I) g α b k l := by
  classical
  unfold ricciSharpChartLocal
  -- Use chartGramMatrix_dotProduct_mulVec, the standard bilinear expansion.
  have hexpand :
      g.inner b
          (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              chartBasisVecFiber (I := I) α i b)
          (∑ j, ricciSharpChartCoeff (I := I) g α φ j b •
              chartBasisVecFiber (I := I) α j b)
        = ∑ i, ∑ j, (ricciSharpChartCoeff (I := I) g α φ i b *
            ricciSharpChartCoeff (I := I) g α φ j b) *
            g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (chartBasisVecFiber (I := I) α j b) := by
    have hL :
        g.inner b
            (∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
                chartBasisVecFiber (I := I) α i b)
          = ∑ i, ricciSharpChartCoeff (I := I) g α φ i b •
              g.inner b (chartBasisVecFiber (I := I) α i b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner b (chartBasisVecFiber (I := I) α i b)
            (∑ j, ricciSharpChartCoeff (I := I) g α φ j b •
                chartBasisVecFiber (I := I) α j b)
          = ∑ j, ricciSharpChartCoeff (I := I) g α φ j b *
              g.inner b
                (chartBasisVecFiber (I := I) α i b)
                (chartBasisVecFiber (I := I) α j b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rfl

/-- Algebraic identity: `∑ k l, r_k r_l G_{kl} = ∑ i j α_i α_j G⁻¹_{ij}` on the
chart base set, where `r_k = ∑ j G⁻¹_{kj} α_j`. Uses the Gram-inverse
identity `G * G⁻¹ = 1`. -/
private lemma sum_sharp_coeff_gram_eq_invGram
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          chartGramMatrix (I := I) g α b k l =
      chartRicciDualNormSq (I := I) g α φ b := by
  classical
  -- Goal: `∑ k l r_k r_l G_{kl} = ∑ i j α_i α_j G⁻¹_{ij}`.
  -- Strategy: each summand `r_k r_l G_{kl}` expands. We separately establish
  -- the key matrix identity `∑ k l Ginv_{ki} Ginv_{lj} G_{kl} = Ginv_{ij}`
  -- and then assemble.
  set N := Module.finrank ℝ E with hN_def
  -- Abbreviations.
  set α' : Fin N → ℝ :=
    fun i => ricciCovectorChartCoord (I := I) g α φ i b with hα'_def
  set Ginv : Fin N → Fin N → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g α b i j with hGinv_def
  set G : Fin N → Fin N → ℝ :=
    fun i j => chartGramMatrix (I := I) g α b i j with hG_def
  -- Helper: the inner sum ∑ k Ginv_{ki} G_{kl} = δ_{li} via G * Ginv = 1.
  have hsym : ∀ k l, G k l = G l k := fun k l => by
    rw [hG_def]; exact g.symm b _ _
  have hinner : ∀ i l, (∑ k, Ginv k i * G k l) =
      if l = i then (1 : ℝ) else 0 := by
    intro i l
    rw [show (∑ k, Ginv k i * G k l) =
        (∑ k, G l k * Ginv k i) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro k _
      rw [hsym k l]; ring
    have hid : (chartGramMatrix (I := I) g α b *
            chartInvGramMatrix (I := I) g α b) l i =
        if l = i then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb]
      rw [Matrix.one_apply]
    change (∑ k, G l k * Ginv k i) =
        if l = i then (1 : ℝ) else 0
    rw [hG_def, hGinv_def]
    rw [← hid, Matrix.mul_apply]
  -- Key auxiliary: ∑ k l Ginv_{ki} Ginv_{lj} G_{kl} = Ginv_{ij}.
  have hkrInv : ∀ i j, (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) = Ginv i j := by
    intro i j
    rw [show (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) =
        (∑ l, Ginv l j * (∑ k, Ginv k i * G k l)) from ?_]
    swap
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [show (∑ l, Ginv l j * (∑ k, Ginv k i * G k l)) =
        (∑ l, Ginv l j * (if l = i then (1 : ℝ) else 0)) from
      Finset.sum_congr rfl (fun l _ => by rw [hinner i l])]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro l _ hli
      rw [if_neg hli, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  -- Main computation. The full identity is:
  --   ∑ k l r_k r_l G_{kl} = ∑ i j α_i α_j Ginv_{ij}.
  -- Strategy: prove via an auxiliary identity `f`, where:
  --   f k l := r_k r_l G_{kl} = ∑ i j α_i α_j Ginv_{ki} Ginv_{lj} G_{kl}.
  -- Then the LHS = ∑ k l f k l = ∑ i j α_i α_j (∑ k l Ginv_{ki} Ginv_{lj} G_{kl})
  --             = ∑ i j α_i α_j Ginv_{ij} (using hkrInv).
  -- Key Reorganization: by Finset.sum_comm applied recursively,
  -- ∑ k l ∑ i j X(k,l,i,j) = ∑ i j ∑ k l X(k,l,i,j).
  -- This can be derived from `Finset.sum_comm` applied 4 times in a chain,
  -- but we use a cleaner form via `Finset.sum_product`.
  have hLHS_full :
      (∑ k, ∑ l,
        ricciSharpChartCoeff (I := I) g α φ k b *
          ricciSharpChartCoeff (I := I) g α φ l b *
          chartGramMatrix (I := I) g α b k l) =
      ∑ i, ∑ j, α' i * α' j * Ginv i j := by
    -- Step 1: convert each summand using the definition of `ricciSharpChartCoeff`.
    have hstep1 :
        ∀ k l, ricciSharpChartCoeff (I := I) g α φ k b *
            ricciSharpChartCoeff (I := I) g α φ l b *
            chartGramMatrix (I := I) g α b k l =
          ∑ i, ∑ j, α' i * α' j * (Ginv k i * Ginv l j * G k l) := by
      intro k l
      rw [ricciSharpChartCoeff_def, ricciSharpChartCoeff_def]
      -- The LHS is `(∑ i Ginv_{ki} α_i) * (∑ j Ginv_{lj} α_j) * G_{kl}`.
      rw [show (∑ i, chartInvGramMatrix (I := I) g α b k i *
                ricciCovectorChartCoord (I := I) g α φ i b) =
              ∑ i, Ginv k i * α' i from
            Finset.sum_congr rfl (fun i _ => by rw [hα'_def, hGinv_def])]
      rw [show (∑ j, chartInvGramMatrix (I := I) g α b l j *
                ricciCovectorChartCoord (I := I) g α φ j b) =
              ∑ j, Ginv l j * α' j from
            Finset.sum_congr rfl (fun j _ => by rw [hα'_def, hGinv_def])]
      rw [show chartGramMatrix (I := I) g α b k l = G k l from rfl]
      -- (∑ i, Ginv_{ki} α_i) * (∑ j, Ginv_{lj} α_j) = ∑ i, ∑ j, (Ginv_{ki} α_i)(Ginv_{lj} α_j).
      rw [Finset.sum_mul_sum]
      -- Now (∑ i, ∑ j, (Ginv_{ki} α_i)(Ginv_{lj} α_j)) * G_{kl}.
      -- Push G_{kl} inside the outer sum, then the inner sum, then ring.
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    -- Substitute hstep1.
    have hLHS_subst :
        (∑ k, ∑ l,
          ricciSharpChartCoeff (I := I) g α φ k b *
            ricciSharpChartCoeff (I := I) g α φ l b *
            chartGramMatrix (I := I) g α b k l) =
        ∑ k, ∑ l, ∑ i, ∑ j,
          α' i * α' j * (Ginv k i * Ginv l j * G k l) :=
      Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => hstep1 k l))
    rw [hLHS_subst]
    -- Step 2: 4-way sum reorganization via product sums.
    -- ∑ k l i j X = ∑ (kl) (ij) X = ∑ (ij) (kl) X = ∑ i j ∑ k l X.
    -- Use Finset.sum_product to fold double sums into pair sums.
    have hsumprod1 :
        (∑ k, ∑ l, ∑ i, ∑ j,
            α' i * α' j * (Ginv k i * Ginv l j * G k l)) =
        ∑ kl ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
          ∑ ij ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
            α' ij.1 * α' ij.2 * (Ginv kl.1 ij.1 * Ginv kl.2 ij.2 * G kl.1 kl.2) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_product]
    rw [hsumprod1]
    -- Now swap: ∑ kl ∑ ij = ∑ ij ∑ kl (single sum_comm).
    rw [Finset.sum_comm]
    -- Now: ∑ ij ∑ kl X.
    -- Unfold ∑ ij into ∑ i ∑ j and pull α_i α_j out of inner sum.
    have hsumprod2 :
        (∑ ij ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
          ∑ kl ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
            α' ij.1 * α' ij.2 * (Ginv kl.1 ij.1 * Ginv kl.2 ij.2 * G kl.1 kl.2)) =
        ∑ i, ∑ j, ∑ k, ∑ l,
            α' i * α' j * (Ginv k i * Ginv l j * G k l) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.sum_product]
    rw [hsumprod2]
    -- Factor α_i α_j out of inner ∑ k ∑ l.
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [show (∑ k, ∑ l, α' i * α' j * (Ginv k i * Ginv l j * G k l)) =
        α' i * α' j * (∑ k, ∑ l, Ginv k i * Ginv l j * G k l) from ?_]
    · rw [hkrInv]
    -- Pull α' i * α' j out of the double sum.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.mul_sum]
  rw [hLHS_full]
  unfold chartRicciDualNormSq
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hα'_def, hGinv_def]

/-- **Identity step.** On the chart base set, the chart-local explicit
expression for `g(R, R)` equals `g_b(ricciSharp g φ b, ricciSharp g φ b)`. -/
theorem chartRicciDualNormSq_eq_inner_ricciSharp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartRicciDualNormSq (I := I) g α φ b =
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) := by
  classical
  -- Step 1: replace `R(b)` by the chart-local sum `ricciSharpChartLocal g α φ b`.
  rw [← ricciSharpChartLocal_eq_ricciSharp (I := I) g α φ hb]
  -- Step 2: expand the bilinear inner product as a double Gram-matrix sum.
  rw [inner_ricciSharpChartLocal_self_eq (I := I) g α φ b]
  -- Step 3: invoke the algebraic identity.
  exact (sum_sharp_coeff_gram_eq_invGram (I := I) g α φ hb).symm

/-! ## Compatibility: `chartRicciDualNormSq` is non-negative on the base set

As `g_b(R, R) ≥ 0` from positive-definiteness of `g`, the chart-local
expression inherits non-negativity. -/

/-- The chart-local expression `chartRicciDualNormSq g α φ b` is
non-negative on the chart base set. -/
theorem chartRicciDualNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 ≤ chartRicciDualNormSq (I := I) g α φ b := by
  rw [chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α φ hb]
  exact metric_inner_self_nonneg (I := I) (M := M) g b _

/-! ## Pointwise Cauchy-Schwarz bound

The pointwise CS-style bound is
`|Ric(∇φ b, w)|² ≤ g_b(R(b), R(b)) · g_b(w, w)` for any `w`. This bound
combined with the global sup over `b` gives the L² Lipschitz bound. -/

/-- **Cauchy-Schwarz for the Ricci pairing.** For any tangent vector `w`,
the squared pointwise pairing is bounded by the product of the dual norm
squared and `g_b(w, w)`. -/
lemma ricciPairing_cs_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (b : M) (w : TangentSpace I b) :
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b) w) ^ 2 ≤
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) *
        g.inner b w w := by
  -- `Ric(∇φ b, w) = g(R(b), w)` from `inner_ricciSharp`.
  rw [show ricciTensor (I := I) g b (gradFun (I := I) g φ b) w =
        g.inner b (ricciSharp (I := I) g φ b) w from
      (inner_ricciSharp (I := I) g φ b w).symm]
  -- Apply standard Cauchy-Schwarz for `g`.
  exact metric_inner_cauchy_schwarz_sq (I := I) (M := M) g b _ w

/-- Same statement using the chart-local formula. -/
lemma ricciPairing_cs_sq_chartLocal
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I b) :
    (ricciTensor (I := I) g b (gradFun (I := I) g φ b) w) ^ 2 ≤
      chartRicciDualNormSq (I := I) g α φ b * g.inner b w w := by
  rw [chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α φ hb]
  exact ricciPairing_cs_sq (I := I) g φ b w

/-! ## Global sup bound via finite chart cover

On a compact manifold `M`, we assemble the chart-local bounds into a global
sup bound for `g_b(R(b), R(b))` over all `b : M`. The strategy:

1. The chart-atlas POU has finitely many indices `α ∈ chartAtlasPOU_finset`
   with nonempty support, since `M` is compact.
2. For each such `α`, `tsupport (chartAtlasPOU α)` is compact (closed in
   compact `M`) and contained in `(chartAt H α).source = trivializationAt
   baseSet at α`. The chart-local `chartRicciDualNormSq g α φ` is continuous
   on the base set, hence bounded on the tsupport by some `C_α ≥ 0`.
3. The global bound is `C := max_{α ∈ finset} C_α + 1 ≥ 0`.
4. For any `b ∈ M`, since the POU values sum to 1 on `univ`, at least one
   `α ∈ finset` has `(chartAtlasPOU α) b > 0`, hence `b ∈ tsupport
   (chartAtlasPOU α)`. At this `α`, the chart-local formula gives
   `g(R(b), R(b)) = chartRicciDualNormSq g α φ b ≤ C_α ≤ C`. -/

section GlobalBound

variable [CompactSpace M]

/-- The chart-`α` tsupport of the partition of unity, on a compact manifold,
is itself compact. -/
private lemma tsupport_chartAtlasPOU_compact (α : M) :
    IsCompact (tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)) :=
  isClosed_tsupport _ |>.isCompact

/-- The chart-`α` tsupport of the partition of unity is contained in the
chart base set. -/
private lemma tsupport_chartAtlasPOU_subset_baseSet (α : M) :
    tsupport (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  have hsrc : x ∈ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α hx
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsrc

/-- **Per-chart compact bound.** For each `α`, the chart-local expression
`chartRicciDualNormSq g α φ` is bounded on the tsupport of the chart-`α` POU. -/
private lemma chartRicciDualNormSq_bdd_on_chart_tsupport
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ tsupport (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x),
      chartRicciDualNormSq (I := I) g α φ b ≤ C :=
  chartRicciDualNormSq_bdd_on_compact (I := I) g α φ
    (tsupport_chartAtlasPOU_compact (I := I) (M := M) α)
    (tsupport_chartAtlasPOU_subset_baseSet (I := I) (M := M) α)

/-- The global Ricci dual norm-squared bound: there exists a non-negative
constant `C` such that `g_b(R(b), R(b)) ≤ C` for all `b : M`. -/
theorem exists_global_ricci_dual_normSq_bound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C := by
  classical
  -- Step 1: For each α, get the per-chart bound C_α.
  have hbound_each : ∀ α, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ tsupport (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x),
      chartRicciDualNormSq (I := I) g α φ b ≤ C := fun α =>
    chartRicciDualNormSq_bdd_on_chart_tsupport (I := I) (M := M) g φ α
  choose Cfn hCfn_nn hCfn_bdd using hbound_each
  -- Step 2: Let S = chartAtlasPOU_finset. We show M itself is nonempty;
  -- hence S nonempty so we can use Finset.sup' (the version that doesn't
  -- need OrderBot).
  by_cases hM_ne : Nonempty M
  · -- M nonempty: pick any point and find S nonempty.
    let b₀ : M := Classical.arbitrary M
    obtain ⟨α_seed, _hα_seed_pos⟩ : ∃ α, 0 < (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b₀ :=
      (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b₀)
    have hα_seed_supp : (Function.support ((chartAtlasPOU I M) α_seed)).Nonempty :=
      ⟨b₀, ne_of_gt _hα_seed_pos⟩
    have hα_seed_mem : α_seed ∈ chartAtlasPOU_finset (I := I) (M := M) := by
      rw [chartAtlasPOU_finset_mem]
      exact hα_seed_supp
    have hS_ne : (chartAtlasPOU_finset (I := I) (M := M)).Nonempty :=
      ⟨α_seed, hα_seed_mem⟩
    refine ⟨(chartAtlasPOU_finset (I := I) (M := M)).sup' hS_ne Cfn, ?_, ?_⟩
    · -- non-negativity: Cfn α_seed ≥ 0 and (S.sup' Cfn) ≥ Cfn α_seed.
      exact le_trans (hCfn_nn α_seed)
        (Finset.le_sup' (f := Cfn) hα_seed_mem)
    · intro b
      obtain ⟨α₀, hα₀_pos⟩ : ∃ α, 0 < (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b :=
        (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b)
      have hα₀_supp : (Function.support ((chartAtlasPOU I M) α₀)).Nonempty :=
        ⟨b, ne_of_gt hα₀_pos⟩
      have hα₀_mem : α₀ ∈ chartAtlasPOU_finset (I := I) (M := M) := by
        rw [chartAtlasPOU_finset_mem]
        exact hα₀_supp
      have hb_tsupp : b ∈ tsupport (fun x : M =>
          (chartAtlasPOU I M α₀ : C^∞⟮I, M; ℝ⟯) x) :=
        subset_tsupport _ (ne_of_gt hα₀_pos)
      have hb_base : b ∈ (trivializationAt E (TangentSpace I) α₀).baseSet :=
        tsupport_chartAtlasPOU_subset_baseSet (I := I) (M := M) α₀ hb_tsupp
      have hg_eq : g.inner b (ricciSharp (I := I) g φ b)
            (ricciSharp (I := I) g φ b) =
          chartRicciDualNormSq (I := I) g α₀ φ b :=
        (chartRicciDualNormSq_eq_inner_ricciSharp (I := I) g α₀ φ hb_base).symm
      rw [hg_eq]
      have hb_le_Cα₀ : chartRicciDualNormSq (I := I) g α₀ φ b ≤ Cfn α₀ :=
        hCfn_bdd α₀ b hb_tsupp
      exact le_trans hb_le_Cα₀ (Finset.le_sup' (f := Cfn) hα₀_mem)
  · -- M empty: trivially bounded by 0.
    refine ⟨0, le_refl 0, ?_⟩
    intro b
    exact absurd ⟨b⟩ hM_ne

end GlobalBound

end RicciDualNorm
end Laplacian
end Analysis
end DifferentialGeometry

end
