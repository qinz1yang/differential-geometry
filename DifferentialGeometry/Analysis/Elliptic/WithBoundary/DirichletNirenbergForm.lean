import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.FluxBounds
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMulDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormChart
import DifferentialGeometry.Analysis.Elliptic.MetricDensity

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal



open Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)


omit [IsManifold I_hs ∞ M] [T2Space M] [CompactSpace M] in
private theorem chartPullback_mul_chartInverse (α : M)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (f : EuStd → ℝ) :
    (fun x => φ x * chartPullback I_hs α f x) =
      chartPullback I_hs α (fun z => φ ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm z)) * f z) := by
  funext x
  by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · rw [chartPullback_apply_of_mem α f hx, chartPullback_apply_of_mem α _ hx,
      ContinuousLinearEquiv.symm_apply_apply]
    have hx' : x ∈ (extChartAt I_hs α).source := by simpa only [extChartAt_source] using hx
    rw [(extChartAt I_hs α).left_inv hx']
  · rw [chartPullback_apply_of_notMem α f hx, chartPullback_apply_of_notMem α _ hx, mul_zero]

private theorem chartInverse_smoothMul_h1ComplDirichletChartPullback_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
    (fun z => H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ w)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω]
      fun z => P z * f z := by
  intro P w
  rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
  filter_upwards [ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q w)),
    chartInverse_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs] with z hz hv
  rw [hz, hv]

private theorem smoothMul_h1ComplDirichletChartPullback_eq
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ∃ hPf : MemWkp 1 2 (fun z => P z * f z) Ω,
      ∃ hPfs : tsupport (fun z => P z * f z) ⊆ Ω,
        smoothMulH1ComplDirichlet q φ (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs) =
          h1ComplDirichletChartPullback q α hΩ hΩc hΩs hPf hPfs := by
  intro P
  let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
  have hPf : MemWkp 1 2 (fun z => P z * f z) Ω :=
    (MemWkp_congr_ae (by norm_num) hΩ
      (chartInverse_smoothMul_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs φ hf hfs)).mp
        (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs (smoothMulH1ComplDirichlet q φ w))
  have hPfs : tsupport (fun z => P z * f z) ⊆ Ω := tsupport_mul_subset_right.trans hfs
  refine ⟨hPf, hPfs, eq_h1ComplDirichletChartPullback_of_coeFn q α hΩ hΩc hΩs hPf hPfs ?_⟩
  rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
  apply (smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q w)).trans
  have hv := h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs
  have heq := chartPullback_mul_chartInverse α φ f
  filter_upwards [hv] with x hx
  rw [hx]
  exact congrFun heq x

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem integral_mul_smoothMul_chartPullback_partial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) {f : EuStd → ℝ} (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω)
    (j : Fin (Module.finrank ℝ EuN)) (F : EuStd → ℝ) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (∫ z in Ω, F z * D j (smoothMulH1ComplDirichlet q φ w) z) =
      ∫ z in Ω, F z * (P z * D j w z + fderiv ℝ P z (EuclideanSpace.single j 1) * f z) := by
  intro P w D
  apply integral_congr_ae
  filter_upwards [dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet q α hΩ hΩc hΩs φ j w,
    chartInverse_h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs] with z hz hv
  rw [hz, hv]

private theorem dirichletWeakFormCompl_smoothMul_chartPullback_eq_chart_partial
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (u : H1ComplDirichlet q) {f : EuStd → ℝ}
    (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => φ ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothMulH1ComplDirichlet q φ w) =
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) *
        D j (smoothMulH1ComplDirichlet q φ w) z) +
        (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * f z)) -
          (∫ z in Ω, ρ z * U z * (a * (P z * f z))) := by
  intro e ρ A B U P D w
  obtain ⟨hPf, hPfs, heq⟩ := smoothMul_h1ComplDirichletChartPullback_eq q α hΩ hΩc hΩs φ hf hfs
  have hi := dirichletWeakFormCompl_apply_h1ComplDirichletChartPullback_eq_integral_chart
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u hPf hPfs
  dsimp only at hi
  rw [← heq] at hi
  exact hi

theorem dirichletWeakFormCompl_smoothMul_h1ComplDirichletChartPullback_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (u : H1ComplDirichlet q) {f : EuStd → ℝ}
    (hf : MemWkp 1 2 f Ω) (hfs : tsupport f ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => φ ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let w := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothMulH1ComplDirichlet q φ w) =
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) *
        (P z * D j w z + fderiv ℝ P z (EuclideanSpace.single j 1) * f z)) +
        (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * f z)) -
          (∫ z in Ω, ρ z * U z * (a * (P z * f z))) := by
  intro e ρ A B U P D w
  have hi := dirichletWeakFormCompl_smoothMul_chartPullback_eq_chart_partial
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol φ u hf hfs
  dsimp only at hi
  rw [hi]
  apply congrArg (fun t : ℝ => -t +
    (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * f z)) -
      (∫ z in Ω, ρ z * U z * (a * (P z * f z))))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_smoothMul_chartPullback_partial q α hΩ hΩc hΩs φ hf hfs j _

private theorem integral_mul_weight_dirichletNirenbergTest_partial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (v : H1ComplDirichlet q)
    (F P b : EuStd → ℝ) :
    let V := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (∫ z in Ω, F z * (P z * D j (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v) z + b z)) =
      ∫ z in Ω, F z * (P z * Sobolev.diffQuot k (-s) (fun y =>
        (η y)^2 * Sobolev.diffQuot k s (D j v) y +
          2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V y) z + b z) := by
  intro V D
  apply integral_congr_ae
  exact (dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded
    q α hΩ hΩc hΩs hη hηc k j s hηs v).mono fun z hz => congrArg (fun t => F z * (P z * t + b z)) hz

theorem dirichletWeakFormCompl_smoothMul_dirichletNirenbergTest_eq_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u v : H1ComplDirichlet q) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => φ ((extChartAt I_hs α).symm (e.symm z))
    let V := fun (z : EuStd) => H1ComplDirichletToLp q v ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let N := standardNirenbergTest k s η V
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v)) =
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) *
        (P z * Sobolev.diffQuot k (-s) (fun y => (η y)^2 * Sobolev.diffQuot k s (D j v) y +
          2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V y) z + fderiv ℝ P z (EuclideanSpace.single j 1) * N z)) +
        (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * N z)) -
          (∫ z in Ω, ρ z * U z * (a * (P z * N z))) := by
  intro e ρ A B U P V D N
  have hV : MemWkp 1 2 V Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v
  have hN : MemWkp 1 2 N Ω :=
    (memWkp_standardNirenbergTest_of_memWkp_local hΩ hV hη hηc k s hηs).mono_set
      (by norm_num) hΩ (subset_univ _)
  have hNs : tsupport N ⊆ Ω := (standardNirenbergTest_tsupport_subset_cthickening k s η V).trans hηs
  have htest : dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v =
      h1ComplDirichletChartPullback q α hΩ hΩc hΩs hN hNs :=
    eq_h1ComplDirichletChartPullback_of_coeFn q α hΩ hΩc hΩs hN hNs
      (dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k s hηs v)
  have hi := dirichletWeakFormCompl_smoothMul_h1ComplDirichletChartPullback_eq_integral_chart
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol φ u hN hNs
  dsimp only at hi
  rw [← htest] at hi
  rw [hi]
  apply congrArg (fun t : ℝ => -t +
    (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * N z)) -
      (∫ z in Ω, ρ z * U z * (a * (P z * N z))))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_weight_dirichletNirenbergTest_partial q α hΩ hΩc hΩs hη hηc k j s hηs v _ P _

open DifferentialGeometry.Analysis.Laplacian.MetricExtension

omit [T2Space M] [CompactSpace M] in
private theorem memLp_chart_smoothMap_partial
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (j : Fin (Module.finrank ℝ EuN)) :
    MemLp (fun z => fderiv ℝ (fun y => φ ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm y))) z (EuclideanSpace.single j 1)) ∞ (volume.restrict Ω) := by
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => φ ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm y))) U := by
    apply (scalarOnE_contDiffOn α φ.contMDiff).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  have hc := (((hP.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (g := fun _ => EuclideanSpace.single j 1) contDiffOn_const).continuousOn).mono hΩs
  exact hc.memLp_top_of_subset_isCompact hΩc hΩ.measurableSet subset_closure

private theorem integral_normalized_dirichlet_nirenberg_flux
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hP : ∀ z ∈ Ω, densityOnEuclid h α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k i j : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u v : H1ComplDirichlet q) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let V := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let A := invGramOnEuclid h α i j
    let C := weightedInvGramOnEuclid h α i j
    let Q := fun z => fderiv ℝ P z (EuclideanSpace.single j 1)
    (-(∫ z in Ω, D i u z * C z * (P z * Sobolev.diffQuot k (-s) (fun y =>
      (η y)^2 * Sobolev.diffQuot k s (D j v) y +
        2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V y) z +
      Q z * standardNirenbergTest k s η V z))) =
      (∫ z, (Sobolev.translate k s A z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s A z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j v) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V z)) +
      ∫ z, (Sobolev.translate k s (fun y => C y * Q y) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (fun y => C y * Q y) z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s V z) := by
  intro P V D A C Q
  have htarget := hΩs.trans (image_mono interior_subset)
  have hA : MemLp A ∞ (volume.restrict Ω) :=
    ((invGramOnEuclid_contDiffOn h α i j).continuousOn.mono htarget).memLp_top_of_subset_isCompact
      hΩc hΩ.measurableSet subset_closure
  have hC : MemLp C ∞ (volume.restrict Ω) :=
    ((weightedInvGramOnEuclid_contDiffOn h α i j).continuousOn.mono htarget).memLp_top_of_subset_isCompact
      hΩc hΩ.measurableSet subset_closure
  have hQ : MemLp Q ∞ (volume.restrict Ω) := memLp_chart_smoothMap_partial α hΩ hΩc hΩs φ j
  have hcu : MemLp (fun z => A z * D i u z) 2 (volume.restrict Ω) := (Lp.memLp _).mul' hA
  have hcqu : MemLp (fun z => (C z * Q z) * D i u z) 2 (volume.restrict Ω) :=
    (Lp.memLp _).mul' (hQ.mul' (r := ∞) hC)
  have hV : MemLp V 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
  apply integral_normalized_multiplier_nirenberg_flux_eq_local hΩ.measurableSet hcu ?_ hcqu hV
    (Lp.memLp (D j v)) hη hηc k j s hηs
  intro z hz
  change (densityOnEuclid h α z * A z) * P z = A z
  calc
    _ = (densityOnEuclid h α z * P z) * A z := by ring
    _ = _ := by rw [hP z hz, one_mul]

private theorem integral_normalized_weight_nirenberg_eq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {ρ P b u v η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hP : ∀ z ∈ Ω, ρ z * P z = 1)
    (hbu : MemLp (fun z => b z * u z) 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) :
    (∫ z in Ω, u z * (b z * ρ z) * (P z * standardNirenbergTest k s η v z)) =
      -∫ z, (Sobolev.translate k s b z * Sobolev.diffQuot k s u z +
        Sobolev.diffQuot k s b z * u z) * ((η z)^2 * Sobolev.diffQuot k s v z) := by
  rw [← integral_weight_mul_standardNirenbergTest_eq_local hΩ hbu hv hη hηc k s hηs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ] with z hz
  calc
    _ = b z * u z * (ρ z * P z) * standardNirenbergTest k s η v z := by ring
    _ = _ := by rw [hP z hz, mul_one]

private theorem integral_normalized_reaction_nirenberg_eq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {ρ P u v η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hP : ∀ z ∈ Ω, ρ z * P z = 1)
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (a : ℝ) (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) :
    (∫ z in Ω, ρ z * u z * (a * (P z * standardNirenbergTest k s η v z))) =
      -(a * ∫ z, Sobolev.diffQuot k s u z * ((η z)^2 * Sobolev.diffQuot k s v z)) := by
  have hi := integral_mul_standardNirenbergTest_eq_local hΩ hu hv hη hηc k s hηs
  calc
    _ = a * ∫ z in Ω, u z * standardNirenbergTest k s η v z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hΩ] with z hz
      calc
        _ = a * (ρ z * P z) * (u z * standardNirenbergTest k s η v z) := by ring
        _ = _ := by rw [hP z hz, mul_one]
    _ = _ := by rw [hi, mul_neg]

omit [T2Space M] [CompactSpace M] in
private theorem memLp_chart_vector_field_coefficient
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ EuN)) :
    MemLp (fun z => chartCoeffOnE (I := I_hs) α X i ((toEuclidean (E := EuN)).symm z))
      ∞ (volume.restrict Ω) := by
  have hm : MapsTo (toEuclidean (E := EuN)).symm (closure Ω) (extChartAt I_hs α).target := by
    rintro z hz
    obtain ⟨y, hy, rfl⟩ := hΩs hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  exact (((chartCoeffOnE_contDiffOn (I := I_hs) α X i).comp
    (toEuclidean (E := EuN)).symm.contDiff.contDiffOn hm).continuousOn).memLp_top_of_subset_isCompact
      hΩc hΩ.measurableSet subset_closure

theorem dirichletWeakFormCompl_smoothMul_dirichletNirenbergTest_eq_shifted_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hP : ∀ z ∈ Ω, densityOnEuclid h α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u v : H1ComplDirichlet q) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => φ ((extChartAt I_hs α).symm (e.symm z))
    let V := fun (z : EuStd) => H1ComplDirichletToLp q v ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let R := fun i j z => (ρ z * A i j z) * fderiv ℝ P z (EuclideanSpace.single j 1)
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v)) =
      (∑ i, ∑ j, ((∫ z, (Sobolev.translate k s (A i j) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (A i j) z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j v) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V z)) +
        ∫ z, (Sobolev.translate k s (R i j) z * Sobolev.diffQuot k s (D i u) z +
          Sobolev.diffQuot k s (R i j) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z))) -
      (∑ i, ∫ z, (Sobolev.translate k s (B i) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (B i) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z)) +
      a * ∫ z, Sobolev.diffQuot k s U z * ((η z)^2 * Sobolev.diffQuot k s V z) := by
  intro e ρ A B U P V D R
  let N := standardNirenbergTest k s η V
  have hi := dirichletWeakFormCompl_smoothMul_dirichletNirenbergTest_eq_integral_chart
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol φ hη hηc k s hηs u v
  dsimp only at hi
  have hV : MemLp V 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
  have hU : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hprincipal :
      -(∑ i, ∑ j, ∫ z in Ω, D i u z * (ρ z * A i j z) *
        (P z * Sobolev.diffQuot k (-s) (fun y => (η y)^2 * Sobolev.diffQuot k s (D j v) y +
          2 * η y * fderiv ℝ η y (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V y) z +
            fderiv ℝ P z (EuclideanSpace.single j 1) * N z)) =
      ∑ i, ∑ j, ((∫ z, (Sobolev.translate k s (A i j) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (A i j) z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j v) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V z)) +
        ∫ z, (Sobolev.translate k s (R i j) z * Sobolev.diffQuot k s (D i u) z +
          Sobolev.diffQuot k s (R i j) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_normalized_dirichlet_nirenberg_flux q h α hΩ hΩc hΩs φ hP hη hηc k i j s hηs u v
  have hdrift : (∑ i, ∫ z in Ω, D i u z * (B i z * ρ z) * (P z * N z)) =
      -(∑ i, ∫ z, (Sobolev.translate k s (B i) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (B i) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hBi : MemLp (fun z => B i z * D i u z) 2 (volume.restrict Ω) :=
      (Lp.memLp _).mul' (memLp_chart_vector_field_coefficient α hΩ hΩc hΩs X i)
    exact integral_normalized_weight_nirenberg_eq hΩ.measurableSet hP hBi hV hη.continuous hηc k s hηs
  have hreaction := integral_normalized_reaction_nirenberg_eq hΩ.measurableSet hP hU hV a
    hη.continuous hηc k s hηs
  change (∫ z in Ω, ρ z * U z * (a * (P z * N z))) = _ at hreaction
  have hadd := congrArg₂ (fun p d : ℝ => p + d) hprincipal hdrift
  have hsub := congrArg₂ (fun p r : ℝ => p - r) hadd hreaction
  simp only [sub_neg_eq_add, ← sub_eq_add_neg] at hsub
  exact hi.trans hsub

theorem dirichletWeakFormCompl_volumeDensity_smoothMul_dirichletNirenbergTest_eq_shifted_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    (h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (X : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯)
    (a Bx : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ Bx)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ h.inner x w w ∧ h.inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (s : ℝ)
    (hηs : Metric.cthickening |s| (tsupport η) ⊆ Ω) (u v : H1ComplDirichlet q) :
    let e := toEuclidean (E := EuN)
    let ρ := fun (z : EuStd) => chartDensityOnE (I := I_hs) h α (e.symm z)
    let A := fun (i j : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    let B := fun (i : Fin (Module.finrank ℝ EuN)) (z : EuStd) => chartCoeffOnE (I := I_hs) α X i (e.symm z)
    let U := fun (z : EuStd) => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z))
    let P := fun (z : EuStd) => (riemannianVolumeDensitySmoothMap h q * φ) ((extChartAt I_hs α).symm (e.symm z))
    let V := fun (z : EuStd) => H1ComplDirichletToLp q v ((extChartAt I_hs α).symm (e.symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let R := fun i j z => (ρ z * A i j z) * fderiv ℝ P z (EuclideanSpace.single j 1)
    dirichletWeakFormCompl h X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol u
      (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap h q * φ)
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k s hηs v)) =
      (∑ i, ∑ j, ((∫ z, (Sobolev.translate k s (A i j) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (A i j) z * D i u z) *
          ((η z)^2 * Sobolev.diffQuot k s (D j v) z +
            2 * η z * fderiv ℝ η z (EuclideanSpace.single j 1) * Sobolev.diffQuot k s V z)) +
        ∫ z, (Sobolev.translate k s (R i j) z * Sobolev.diffQuot k s (D i u) z +
          Sobolev.diffQuot k s (R i j) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z))) -
      (∑ i, ∫ z, (Sobolev.translate k s (B i) z * Sobolev.diffQuot k s (D i u) z +
        Sobolev.diffQuot k s (B i) z * D i u z) * ((η z)^2 * Sobolev.diffQuot k s V z)) +
      a * ∫ z, Sobolev.diffQuot k s U z * ((η z)^2 * Sobolev.diffQuot k s V z) := by
  exact dirichletWeakFormCompl_smoothMul_dirichletNirenbergTest_eq_shifted_integral_chart
    h α hΩ hΩc hΩs X a Bx hX hCg hequiv Cv hCv0 hCvtop hvol
      (riemannianVolumeDensitySmoothMap h q * φ)
      (densityOnEuclid_mul_riemannianVolumeDensity_mul_chartInverse q h α
        (subset_closure.trans (hΩs.trans (image_mono interior_subset))) φ hφ)
      hη hηc k s hηs u v

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
