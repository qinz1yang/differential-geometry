import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Bundle.OrthonormalFrame
import DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import DifferentialGeometry.Geometry.Metric.BundlePullback
import DifferentialGeometry.Geometry.Metric.MetricFiberData.Hom
import DifferentialGeometry.Geometry.Metric.MetricFiberData.Topology

noncomputable section

namespace Bundle

variable {B : Type*} (U V : B → Type*)
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [∀ x, FiniteDimensional ℝ (U x)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def homRiemannianMetric : RiemannianMetric (fun x => U x →L[ℝ] V x) :=
  (RiemannianMetric.ofInnerProductSpace (fun x =>
    PiLp 2 (fun _ : Fin (Module.finrank ℝ (U x)) => V x))).pullback id
      (fun x => (stdOrthonormalBasis ℝ (U x)).continuousLinearMapEquiv)

@[simp] theorem homRiemannianMetric_inner (x : B) (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U V).inner x A C = ContinuousLinearMap.hilbertSchmidtInner A C := by
  exact (ContinuousLinearMap.hilbertSchmidtInner_eq_inner
    (stdOrthonormalBasis ℝ (U x)) A C).symm

theorem homRiemannianMetric_inner_eq_sum {ι : Type*} [Fintype ι]
    (x : B) (b : OrthonormalBasis ι ℝ (U x)) (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U V).inner x A C =
      ∑ i, inner ℝ (A (b i)) (C (b i)) := by
  rw [homRiemannianMetric_inner, ContinuousLinearMap.hilbertSchmidtInner_eq_sum b]

open DifferentialGeometry.Tensor0SBundle in
theorem homRiemannianMetric_eq_metricFiberData [∀ x, FiniteDimensional ℝ (V x)] :
    homRiemannianMetric U V = MetricFiberData.riemannianMetric (fun x =>
      MetricFiberData.homCLM (MetricFiberData.ofInnerProductSpace (F := U x))
        (MetricFiberData.ofInnerProductSpace (F := V x))) := by
  apply RiemannianMetric.ext
  intro x A C
  rw [homRiemannianMetric_inner_eq_sum U V x (stdOrthonormalBasis ℝ (U x))]
  exact (MetricFiberData.hom_inner_eq_sum_orthonormalBasis
    (stdOrthonormalBasis ℝ (U x)) A.toLinearMap C.toLinearMap).symm

variable {B' : Type*} (U' V' : B' → Type*)
  [∀ x, NormedAddCommGroup (U' x)] [∀ x, InnerProductSpace ℝ (U' x)]
  [∀ x, FiniteDimensional ℝ (U' x)]
  [∀ x, NormedAddCommGroup (V' x)] [∀ x, InnerProductSpace ℝ (V' x)]

theorem homRiemannianMetric_inner_congr
    (x : B) (y : B') (eU : U x ≃ₗᵢ[ℝ] U' y) (eV : V x →ₗᵢ[ℝ] V' y)
    (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U' V').inner y
        (eV.toContinuousLinearMap.comp (A.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap))
        (eV.toContinuousLinearMap.comp (C.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      (homRiemannianMetric U V).inner x A C := by
  simp only [homRiemannianMetric_inner]
  exact ContinuousLinearMap.hilbertSchmidtInner_congr eU eV A C

end Bundle

namespace Bundle

open Filter
open scoped Manifold ContDiff Topology

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {FU FV : Type*}
  [NormedAddCommGroup FU] [NormedSpace ℝ FU]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  (U V : B → Type*) [TopologicalSpace (TotalSpace FU U)]
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [∀ x, FiniteDimensional ℝ (U x)]
  [FiberBundle FU U] [VectorBundle ℝ FU U]
  [TopologicalSpace (TotalSpace FV V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle FV V] [VectorBundle ℝ FV V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n FU U IB]
  [IsContMDiffRiemannianBundle IB n FU U]
  [IsContMDiffRiemannianBundle IB n FV V]

local instance homModelNormedAddCommGroup : NormedAddCommGroup (FU →L[ℝ] FV) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (E := FU) (F := FV)

local instance homModelNormedSpace : NormedSpace ℝ (FU →L[ℝ] FV) :=
  ContinuousLinearMap.toNormedSpace

local instance homDualModelNormedAddCommGroup :
    NormedAddCommGroup ((FU →L[ℝ] FV) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (E := FU →L[ℝ] FV) (F := ℝ)

local instance homDualModelNormedSpace : NormedSpace ℝ ((FU →L[ℝ] FV) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance homBilinearModelNormedAddCommGroup :
    NormedAddCommGroup ((FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (E := FU →L[ℝ] FV)
    (F := (FU →L[ℝ] FV) →L[ℝ] ℝ)

local instance homBilinearModelNormedSpace :
    NormedSpace ℝ ((FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem contMDiff_hilbertSchmidtInnerSL :
    ContMDiff IB (IB.prod 𝓘(ℝ, (FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ)) n
      (fun x => (⟨x, ContinuousLinearMap.hilbertSchmidtInnerSL (U := U x) (V := V x)⟩ :
        TotalSpace ((FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ)
          (fun x => (U x →L[ℝ] V x) →L[ℝ] (U x →L[ℝ] V x) →L[ℝ] ℝ))) := by
  classical
  intro x₀
  let b₀ := stdOrthonormalBasis ℝ (U x₀)
  obtain ⟨S, hS, hx₀, e, he, heON, he₀⟩ :=
    exists_contMDiff_orthonormal_sections (I := IB) (F := FU) (m := n) x₀ b₀ b₀.orthonormal
  obtain ⟨g, hg, hinner⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle IB n FV V).exists_contMDiff
  let ev := fun i x => ContinuousLinearMap.apply ℝ (V x) (e i x)
  have hev (i) : ContMDiffOn IB
      (IB.prod 𝓘(ℝ, (FU →L[ℝ] FV) →L[ℝ] FV)) n
      (fun x => (⟨x, ev i x⟩ : TotalSpace ((FU →L[ℝ] FV) →L[ℝ] FV)
        (fun x => (U x →L[ℝ] V x) →L[ℝ] V x))) S :=
    (he i).clm_bundle_eval (F₂ := FV) (U₂ := V)
  have hbil (i) : ContMDiffOn IB
      (IB.prod 𝓘(ℝ, (FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ)) n
      (fun x => (⟨x, (g x).bilinearComp (ev i x) (ev i x)⟩ :
        TotalSpace ((FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ)
          (fun x => (U x →L[ℝ] V x) →L[ℝ] (U x →L[ℝ] V x) →L[ℝ] ℝ))) S :=
    hg.contMDiffOn.clm_bundle_bilinearComp (hev i) (hev i)
  have hsum := ContMDiffOn.sum_section (s := Finset.univ) (fun i _ => hbil i)
  have heq (x : B) (hx : x ∈ S) :
      (∑ i, (g x).bilinearComp (ev i x) (ev i x)) =
        ContinuousLinearMap.hilbertSchmidtInnerSL (U := U x) (V := V x) := by
    let t₀ := trivializationAt FU U x₀
    let t := trivializationAt FU U x
    have hdim : Fintype.card (Fin (Module.finrank ℝ (U x₀))) = Module.finrank ℝ (U x) := by
      rw [Fintype.card_fin]
      exact (t₀.continuousLinearEquivAt ℝ x₀ (mem_baseSet_trivializationAt FU U x₀)).toLinearEquiv.finrank_eq.trans
        (t.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt FU U x)).toLinearEquiv.finrank_eq.symm
    let bx := OrthonormalBasis.mk (heON x hx)
      ((heON x hx).linearIndependent.span_eq_top_of_card_eq_finrank' hdim).ge
    ext A C
    simp only [sum_apply, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.hilbertSchmidtInnerSL_apply]
    rw [ContinuousLinearMap.hilbertSchmidtInner_eq_sum bx]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hinner]
    simp only [bx, OrthonormalBasis.coe_mk]
    rfl
  apply (hsum.contMDiffAt (hS.mem_nhds hx₀)).congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hx₀] with x hx
  exact congrArg (fun A => (⟨x, A⟩ :
    TotalSpace ((FU →L[ℝ] FV) →L[ℝ] (FU →L[ℝ] FV) →L[ℝ] ℝ)
      (fun x => (U x →L[ℝ] V x) →L[ℝ] (U x →L[ℝ] V x) →L[ℝ] ℝ))) (heq x hx).symm


def homContMDiffRiemannianMetric :
    ContMDiffRiemannianMetric IB n (FU →L[ℝ] FV) (fun x => U x →L[ℝ] V x) where
  inner x := ContinuousLinearMap.hilbertSchmidtInnerSL
  symm x A C := by
    simp only [ContinuousLinearMap.hilbertSchmidtInnerSL_apply]
    exact ContinuousLinearMap.hilbertSchmidtInner_comm A C
  pos x A hA := by
    simp only [ContinuousLinearMap.hilbertSchmidtInnerSL_apply]
    exact ContinuousLinearMap.hilbertSchmidtInner_self_pos hA
  isVonNBounded x := by
    simpa only [homRiemannianMetric_inner, ContinuousLinearMap.hilbertSchmidtInnerSL_apply]
      using (homRiemannianMetric U V).isVonNBounded x
  contMDiff := contMDiff_hilbertSchmidtInnerSL U V

@[simp]
theorem homContMDiffRiemannianMetric_inner (x : B) (A C : U x →L[ℝ] V x) :
    (homContMDiffRiemannianMetric (IB := IB) (n := n) (FU := FU) (FV := FV) U V).inner x A C =
      ContinuousLinearMap.hilbertSchmidtInner A C :=
  ContinuousLinearMap.hilbertSchmidtInnerSL_apply A C

@[simp]
theorem homContMDiffRiemannianMetric_toRiemannianMetric :
    (homContMDiffRiemannianMetric (IB := IB) (n := n) (FU := FU) (FV := FV) U V).toRiemannianMetric =
      homRiemannianMetric U V := by
  apply RiemannianMetric.ext
  intro x A C
  exact (homContMDiffRiemannianMetric_inner (IB := IB) (n := n) (FU := FU) (FV := FV) U V x A C).trans
    (homRiemannianMetric_inner U V x A C).symm

end Bundle
