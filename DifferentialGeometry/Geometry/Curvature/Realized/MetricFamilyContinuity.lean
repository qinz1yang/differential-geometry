import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Tensor.RSTensor.Coordinates.TensorRSModelEvalBasis
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Bundle continuity of tensor families from frame components

This file supplies the *converse* of `Tensor0SFamilyContinuousOnSet.eval_continuous`:
a constructor producing the joint total-space continuity predicate
`Tensor0SFamilyContinuousOnSet` from the continuity of a tensor family's scalar
components in a local trivialization frame.

The constructor is the reusable keystone for packaging chart-coordinate
regularity into bundled tensor-section continuity (`metricTensor_cont`,
`ricciCont`, `rm04Cont`, ... of `MetricFamilySmoothOn`/`IsSolutionOn`).  It is
stated in the inner-product-space setting because the model basis
`chartModelBasis` and the evaluation equivalence `eval0SCLE` are tied to the
Euclidean structure; the realized Ricci-flow consumers all live there.
-/

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Keystone constructor: bundle continuity from frame-component continuity.**

A time-dependent `(0,s)` tensor family `A` is jointly continuous as a tensor
section over `{t ∈ K} × M` as soon as, for every base trivialization centre `x₀`,
its scalar components against the local trivialization frame
`(trivializationAt E (TangentSpace I) x₀).symmL` applied to the model basis are
jointly continuous on that trivialization's domain.

This is the converse of `Tensor0SFamilyContinuousOnSet.eval_continuous` (which
projects a continuous section to continuous components).  The proof runs through
`FiberBundle.continuousAt_totalSpace` — continuity in the total space is base
continuity plus fibre-coordinate continuity — and the finite-dimensional
evaluation homeomorphism `eval0SCLE`, which turns fibre-coordinate continuity
into the continuity of the basis components. -/
theorem tensor0SFamilyContinuousOnSet_of_chartComp
    {s : Nat} {K : Set Real}
    (A : (t : Real) → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (N : M → Set M) (hN : ∀ x₀ : M, N x₀ ∈ nhds x₀)
    (hcomp : ∀ (x₀ : M) (idx : Fin s → Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          A q.1.1 q.2
            (fun k : Fin s =>
              (trivializationAt E (TangentSpace I) x₀).symmL Real q.2
                (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))))
        {q : {t : Real // t ∈ K} × M | q.2 ∈ N x₀}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  unfold Tensor0SFamilyContinuousOnSet
  rw [continuous_iff_continuousAt]
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_snd.continuousAt, ?_⟩
  -- Normalise the fibre-coordinate goal to the clean form centred at `q₀.2`.
  show ContinuousAt
      (fun q : {t : Real // t ∈ K} × M =>
        (trivializationAt (Tensor0SModel s Real E)
          (fun x : M => Tensor0SSpace s I x) q₀.2
            ⟨q.2, A q.1.1 q.2⟩).2) q₀
  -- The neighbourhood of `q₀` on which the component continuity is supplied.
  have hopen : {q : {t : Real // t ∈ K} × M | q.2 ∈ N q₀.2} ∈ nhds q₀ :=
    continuous_snd.continuousAt.preimage_mem_nhds (hN q₀.2)
  -- Through the evaluation homeomorphism, fibre-coordinate continuity is
  -- equivalent to the continuity of every basis component.
  have key : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M =>
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
          ((trivializationAt (Tensor0SModel s Real E)
            (fun x : M => Tensor0SSpace s I x) q₀.2
              ⟨q.2, A q.1.1 q.2⟩).2)) q₀ := by
    rw [continuousAt_pi]
    intro idx
    have hpt :
        (fun q : {t : Real // t ∈ K} × M =>
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M => Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx)
          = fun q : {t : Real // t ∈ K} × M =>
              A q.1.1 q.2
                (fun k : Fin s =>
                  (trivializationAt E (TangentSpace I) q₀.2).symmL Real q.2
                    (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))) := by
      funext q
      rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE_apply]
      rw [show ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)
            = (A q.1.1 q.2).compContinuousLinearMap
                (fun _ : Fin s =>
                  (trivializationAt E (TangentSpace I) q₀.2).symmL Real q.2) from rfl]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [hpt]
    exact (hcomp q₀.2 idx).continuousAt hopen
  -- Recover the fibre-coordinate continuity from the components by composing
  -- with the inverse homeomorphism.
  have hsymm :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s).symm.continuous
  have hcongr : (fun q : {t : Real // t ∈ K} × M =>
      (trivializationAt (Tensor0SModel s Real E)
        (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)
      = fun q : {t : Real // t ∈ K} × M =>
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s).symm
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
              ((trivializationAt (Tensor0SModel s Real E)
                (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)) := by
    funext q
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hcongr]
  exact hsymm.continuousAt.comp key

/-- Keystone, phrased in the canonical chart-basis frame `chartBasisVecFiber`.

This is the form curvature consumers plug into: the chart-basis frame
`chartBasisVecFiber x₀ i x = (trivializationAt E (TangentSpace I) x₀).symm x (chartModelBasis i)`
is definitionally the `symmL` frame used by `tensor0SFamilyContinuousOnSet_of_chartComp`, so
this is a thin restatement that avoids re-deriving the `symmL`/`symm` identification at every
call site (metric, Ricci, Riemann). -/
theorem tensor0SFamilyContinuousOnSet_of_chartBasisComp
    {s : Nat} {K : Set Real}
    (A : (t : Real) → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (N : M → Set M) (hN : ∀ x₀ : M, N x₀ ∈ nhds x₀)
    (hcomp : ∀ (x₀ : M) (idx : Fin s → Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          A q.1.1 q.2
            (fun k : Fin s =>
              DifferentialGeometry.Integral.Measure.chartBasisVecFiber
                (I := I) x₀ (idx k) q.2))
        {q : {t : Real // t ∈ K} × M | q.2 ∈ N x₀}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  apply tensor0SFamilyContinuousOnSet_of_chartComp A N hN
  intro x₀ idx
  have heq :
      (fun q : {t : Real // t ∈ K} × M =>
        A q.1.1 q.2
          (fun k : Fin s =>
            (trivializationAt E (TangentSpace I) x₀).symmL Real q.2
              (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))))
        = fun q : {t : Real // t ∈ K} × M =>
            A q.1.1 q.2
              (fun k : Fin s =>
                DifferentialGeometry.Integral.Measure.chartBasisVecFiber
                  (I := I) x₀ (idx k) q.2) := by
    funext q
    congr 1
  rw [heq]
  exact hcomp x₀ idx

/-- **First consumer of the keystone: metric bundle continuity from chart-Gram
continuity.**

For a time-dependent Riemannian metric family `g` whose chart-Gram matrix entries
are jointly continuous (in `(t, x)`) on each chart trivialization domain, the
bundled metric tensor family `(t, x) ↦ metricTensorField (g t) x` is jointly
continuous as a `(0,2)` tensor section over `{t ∈ K} × M`.

This discharges the `metricTensor_cont` field of `MetricFamilySmoothOn` from the
raw chart-Gram regularity exposed by short-time existence. -/
theorem metricTensorCont_of_chartGram
    {K : Set Real} (g : Real → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (g q.1.1) x₀ q.2 i j)
        {q : {t : Real // t ∈ K} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
  intro x₀ idx
  have heq :
      (fun q : {t : Real // t ∈ K} × M =>
        metricTensorField (I := I) (g q.1.1) q.2
          (fun k : Fin 2 =>
            DifferentialGeometry.Integral.Measure.chartBasisVecFiber
              (I := I) x₀ (idx k) q.2))
        = fun q : {t : Real // t ∈ K} × M =>
            DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
              (g q.1.1) x₀ q.2 (idx 0) (idx 1) := by
    funext q
    rw [metricTensorField_apply,
      DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  rw [heq]
  exact hgram x₀ (idx 0) (idx 1)

section MetricCLMSection

variable [NeZero (Module.finrank ℝ E)]

namespace MetricCLMSectionAux

/-- For a metric `g` and a base point `α`, the value of the metric bilinear-CLM section read
in coordinates at the chart-`α` trivialization (centred at `α`, same base point `x ∈ baseSet`),
evaluated on two fixed model-space test vectors `v, w : E`, expands as the chart-Gram bilinear
sum: it is `∑ᵢⱼ (repr v)ᵢ (repr w)ⱼ · chartGramMatrix g α x i j`.  The matrix entries are exactly
the chart-Gram entries, so a joint-in-`(t, x)` smoothness of `chartGramMatrix (g_DT ·) α · i j`
transports to joint smoothness of this scalar (with `v, w` fixed). -/
private lemma inCoordinates_metric_eq_chartGram_sum
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) α x α x (g.inner x) v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          Integral.Measure.chartGramMatrix (I := I) g α x i j := by
  classical
  have hxR : x ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := Set.mem_univ x
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
    (x₀ := α) (x := x) (ϕ := g.inner x) (v := v) (w := w) hx hx hxR]
  rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hxR]
  set e := trivializationAt E (TangentSpace I) α with he
  change g.inner x (e.symmL ℝ x v) (e.symmL ℝ x w) = _
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb
  have hvdec : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hwdec : w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
  have hsymm_v : e.symmL ℝ x v = ∑ i, b.repr v i • chartBasisVecFiber (I := I) α i x := by
    conv_lhs => rw [hvdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]; rfl
  have hsymm_w : e.symmL ℝ x w = ∑ j, b.repr w j • chartBasisVecFiber (I := I) α j x := by
    conv_lhs => rw [hwdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]; rfl
  rw [hsymm_v, hsymm_w]
  have hL :
      g.inner x (∑ i, b.repr v i • chartBasisVecFiber (I := I) α i x)
        = ∑ i, b.repr v i • g.inner x (chartBasisVecFiber (I := I) α i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, g_inner_eq_chartGramMatrix_basis]
  ring

end MetricCLMSectionAux

set_option linter.unusedVariables false in
/-- **Joint `(t, b)` smoothness of the metric bilinear-CLM bundle section from chart-Gram data.**

The metric family's bilinear-CLM bundle section `(t, b) ↦ ⟨b, (g_DT t).inner b⟩` — the operator
section of the `Hom(TM, Hom(TM, ℝ))`-bundle carrying the per-time metric — is jointly `C∞` in
`(t, b)` on `Ioo 0 T ×ˢ univ`, given that every chart-Gram matrix entry
`p ↦ chartGramMatrix (g_DT p.1) x₀ p.2 i j` is jointly `C∞` (`hgram_DT`).

This is the converse readoff of `ContMDiffOn.clm_bundle_apply₂`: at each interior point `q₀` the
Hom-bundle section's smoothness is read in coordinates (`contMDiffAt_hom_bundle`) and reduced via
`contMDiffAt_clm_of_pointwise` (twice, once per bilinear slot) to the scalar coordinate entries,
which — by `inCoordinates_metric_eq_chartGram_sum` — are finite `(repr · ·)`-weighted sums of the
chart-Gram entries `chartGramMatrix (g_DT ·) q₀.2 · i j`, each jointly `C∞` by `hgram_DT` at the
chart centred at `q₀.2`.  Discharges the `hgInnerBase` hypothesis of
`metric_clm_section_jointContMDiffOn_along_orbit`. -/
theorem metricCLMSection_jointContMDiffOn_of_chartGram
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g_DT q.1).inner q.2)))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  classical
  open MetricCLMSectionAux in
  intro q₀ hq₀
  refine (?_ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
      ((g_DT q.1).inner q.2))) q₀).contMDiffWithinAt
  set α : M := q₀.2 with hα
  -- A neighbourhood (within the open product) on which `q.2 ∈ baseSet α`.
  have hbase0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- Reduce the operator-valued `inCoordinates` smoothness to per-slot scalar smoothness.
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(ℝ, ℝ).prod I) (X := ℝ × M)
  intro v
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(ℝ, ℝ).prod I) (X := ℝ × M)
  intro w
  -- The scalar `inCoordinates(...)(v)(w)` is, near `q₀`, the chart-Gram bilinear sum.
  have hgram_sum : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j) q₀ := by
    intro i j
    have hmem : q₀ ∈ Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet := by
      refine ⟨hq₀.1, ?_⟩
      rw [hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
    have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      isOpen_Ioo.prod (trivializationAt E (TangentSpace I) α).open_baseSet
    exact ((hgram_DT α i j) q₀ hmem).contMDiffAt (hopen.mem_nhds hmem)
  have hscalar : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j) q₀ := by
    refine ContMDiffAt.sum (fun i _ => ?_)
    refine ContMDiffAt.sum (fun j _ => ?_)
    exact (contMDiffAt_const (c := ((chartModelBasis E).repr v i *
      (chartModelBasis E).repr w j : ℝ))).mul (hgram_sum i j)
  -- Identify the two functions on a neighbourhood within the open product where `q.2 ∈ baseSet α`.
  refine hscalar.congr_of_eventuallyEq ?_
  have hnhds : (trivializationAt E (TangentSpace I) α).baseSet ∈ nhds q₀.2 :=
    (trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hbase0
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ nhds q₀ :=
    (continuous_snd.continuousAt (x := q₀)).preimage_mem_nhds hnhds
  filter_upwards [hpre] with p hp
  change ((ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] ℝ) α p.2 α p.2 ((g_DT p.1).inner p.2)) v) w = _
  exact inCoordinates_metric_eq_chartGram_sum (I := I) (g_DT p.1) α hp v w

end MetricCLMSection

namespace Tensor0SFamilyContinuousOnSet

/-- **Pullback of bundle continuity under a diffeomorphism.**  If a time-dependent `(0,s)` tensor
family `A` on `N` is jointly continuous, then so is its `Φ`-pullback on `M`,
`(t, x) ↦ (A t (Φ x)).compContinuousLinearMap (fun _ => dΦₓ)`.

Proved through the component constructor `tensor0SFamilyContinuousOnSet_of_chartBasisComp` on `M`:
in each `M`-chart, the pullback component on a chart-basis slot is `A` evaluated at `Φ x` on the
pushed-forward slots `dΦₓ (chartBasisVecFiber …)`, whose continuity is `hA.eval_continuous` with the
pushed chart-basis section `tangentMap Φ ∘ chartBasisVec` (smooth on the chart, then `Φ.continuous_tangentMap`). -/
theorem pullback
    {s : Nat} {K : Set Real}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [IsManifold I 1 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (A : (t : Real) → (x : N) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := N) s x)
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := N) s K A)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => (A t (Φ x)).compContinuousLinearMap
        (fun _ : Fin s => mfderiv I I (Φ : M → N) x)) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
  intro x₀ idx
  rw [continuousOn_iff_continuous_restrict]
  have hslot : ∀ k : Fin s, Continuous
      (fun p : {q : {t : Real // t ∈ K} × M //
            q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
        TotalSpace.mk' E (E := fun y : N => TangentSpace I y) (Φ p.1.2)
          (mfderiv I I (Φ : M → N) p.1.2
            (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2))) := by
    intro k
    have hcomp :
        (fun p : {q : {t : Real // t ∈ K} × M //
              q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
          TotalSpace.mk' E (E := fun y : N => TangentSpace I y) (Φ p.1.2)
            (mfderiv I I (Φ : M → N) p.1.2
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2)))
          = (tangentMap I I (Φ : M → N)) ∘
              (fun p => DifferentialGeometry.Integral.Measure.chartBasisVec (I := I) x₀ (idx k) p.1.2) := by
      funext p; rfl
    rw [hcomp]
    refine (Φ.contMDiff.continuous_tangentMap (by simp)).comp ?_
    exact (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn
        (I := I) x₀ (idx k)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  have hev := hA.eval_continuous
      (P := {q : {t : Real // t ∈ K} × M //
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
      (τ := fun p => p.1.1.1) (b := fun p => Φ p.1.2)
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
      (fun p => p.1.1.2)
      (Φ.continuous.comp (continuous_snd.comp continuous_subtype_val))
      hslot
  refine hev.congr ?_
  intro p
  rfl

/-- **Restriction of bundle continuity to an open submanifold.**  If a time-dependent `(0,s)`
tensor family `A` on `M` is jointly continuous, then so is its restriction to an open submanifold
`U ↪ M`, `(t, x) ↦ A t ↑x`.

Restriction-analog of `Tensor0SFamilyContinuousOnSet.pullback` along the open inclusion
`Subtype.val : U → M` (a `C∞` local diffeomorphism).  Proved through the component constructor
`tensor0SFamilyContinuousOnSet_of_chartBasisComp` on `U`: in each `U`-chart, the restricted
component on a chart-basis slot is `A` evaluated at `↑x` on the pushed-forward slots
`d(Subtype.val)_x (chartBasisVecFiber …)`, whose continuity is `hA.eval_continuous` with the pushed
chart-basis section `tangentMap Subtype.val ∘ chartBasisVec` (smooth on the chart, then
`continuous_tangentMap`); the `mfderiv_subtype_val = id` collapse identifies the composed section
with `A t ↑x`. -/
theorem restrictOpen
    {s : Nat} {K : Set Real}
    (A : (t : Real) → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    Tensor0SFamilyContinuousOnSet (I := I) (M := U) s K
      (fun t (x : U) => A t (x : M)) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp (M := U)
    (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
  intro x₀ idx
  rw [continuousOn_iff_continuous_restrict]
  -- The `U`-chart-basis slot pushed to `M` by `d(Subtype.val)` is a continuous section over `M`.
  have hslot : ∀ k : Fin s, Continuous
      (fun p : {q : {t : Real // t ∈ K} × U //
            q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) ((p.1.2 : M))
          (mfderiv I I (Subtype.val : U → M) p.1.2
            (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2))) := by
    intro k
    have hcomp :
        (fun p : {q : {t : Real // t ∈ K} × U //
              q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) ((p.1.2 : M))
            (mfderiv I I (Subtype.val : U → M) p.1.2
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2)))
          = (tangentMap I I (Subtype.val : U → M)) ∘
              (fun p => DifferentialGeometry.Integral.Measure.chartBasisVec (I := I) x₀ (idx k) p.1.2) := by
      funext p; rfl
    rw [hcomp]
    refine ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).continuous_tangentMap
      (by simp)).comp ?_
    exact (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn
        (I := I) x₀ (idx k)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  have hev := hA.eval_continuous
      (P := {q : {t : Real // t ∈ K} × U //
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
      (τ := fun p => p.1.1.1) (b := fun p => (p.1.2 : M))
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
      (fun p => p.1.1.2)
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
      hslot
  refine hev.congr ?_
  intro p
  simp only [Set.restrict_apply, mfderiv_subtype_val_apply]
  rfl

end Tensor0SFamilyContinuousOnSet

end DifferentialGeometry.Integral.Connection
