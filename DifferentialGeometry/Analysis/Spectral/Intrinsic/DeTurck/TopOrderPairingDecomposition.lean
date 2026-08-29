import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniDecomposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovDivergence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.TopOrderPairingAlgebra
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowOrderPairingDecomposition
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral


open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private local instance edgeTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

private local instance edgeTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

private local instance edgeTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

private local instance edgeTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

def ricciPalatiniHalfCoefficient (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g g₁ +
    (1 / 2 : Real) •
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g g₁

def ricciPalatiniZeroOrderFold (g g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  ((deTurckLieEndoArmField (I := I) (M := M) g g₁ g_bg +
      lieCorrectionZeroField (I := I) (M := M) g g₁ g_bg) +
    metricPrincipalDefectCurvCoeff (I := I) g g₁) -
      backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg

def ricciPalatiniTopOrderDecomposition (g g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (C₀ : SmoothCcTensor g 2 2)
    (C₂ : SmoothCcTensor g 4 2) : SmoothCcTensor g 0 2 :=
  (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
      (ricciPalatiniHalfCoefficient (I := I) (M := M) g g₁) W +
    operatorFieldApply (I := I) (M := M) g 2 2 C₀ W +
    operatorFieldApply (I := I) (M := M) g 2 2
      (ricciPalatiniZeroOrderFold (I := I) (M := M) g g₁ g_bg) W +
    operatorFieldApply (I := I) (M := M) g 3 2
      (metricDependentFirstOrderCoefficient (I := I) (M := M) g g₁ g_bg)
      (iteratedCovGrad (I := I) g 0 2 1 W) +
    operatorFieldApply (I := I) (M := M) g 4 2 C₂
      (iteratedCovGrad (I := I) g 0 2 2 W)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem metricPerturbation_zero_bound_at (g : SmoothRiemannianMetric I M) {delta : Real}
    (hdelta : 0 ≤ delta) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0, ccTensorBilinSymm_smul]
  simp only [zero_mul, abs_zero]
  exact mul_nonneg (mul_nonneg hdelta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

omit [CompactSpace M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem metricComparisonEndomorphism_pairing_balance
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    {s : Real} (hs : s ∈ Set.Icc (0 : Real) 1) :
    metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s =
      metricPerturbationPath (I := I) g W 0 hdelta hdeltaZ s := by
  have hs0 : s ∈ metricPerturbationPathDomain (δ := delta) (δ' := 0) :=
    Icc_subset_metricPerturbationPathDomain hdelta_lt (by norm_num) hs
  have hsdelta : s ∈ metricPerturbationPathDomain (δ := delta) (δ' := delta) :=
    Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt hs
  apply riemannianMetric_eq_of_inner
  intro x v w
  change
    (metricPerturbationPath (I := I) g W 0 hdelta
        (zero_metricPerturbation_bound (I := I) (M := M) g) s).inner x v w =
      (metricPerturbationPath (I := I) g W 0 hdelta hdeltaZ s).inner x v w
  rw [metricPerturbationPath_inner_of_mem (I := I) g W 0 hdelta
      (zero_metricPerturbation_bound (I := I) (M := M) g) hs0 x v w,
    metricPerturbationPath_inner_of_mem (I := I) g W 0 hdelta hdeltaZ hsdelta x v w]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_rank0_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

omit [NeZero (Module.finrank Real E)] [TopologicalSpace M] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_cons_sum (_x : M) {n : Nat}
    (Zm : Tensor0SModel (n + 1) Real E) (d : Nat) (t : Fin d → Real)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : Real) • (0 : E)) from (zero_smul Real (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank Real E)] [TopologicalSpace M] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_cons2_sum (_x : M) {n : Nat}
    (Zm : Tensor0SModel (n + 2) Real E) (aa : E) (d : Nat)
    (t : Fin d → Real) (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1
          (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c *
          Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : Real) • (0 : E)) from (zero_smul Real (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_frame_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank Real E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  have : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  have : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))⟩⟩
  set B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent Real B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) =
        c i * (if i = j then (1 : Real) else 0) := by
      intro i
      rw [map_smul, smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : Real) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank Real E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank Real E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : Real) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricComparison_trace_contraction (g gm : SmoothRiemannianMetric I M) (s : Nat) :
    secondMetricCometricDoubleTraceField (I := I) (M := M) g gm s =
      ccOperatorFieldComp (I := I) (M := M) g (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g s)
        (endoSlotZeroCcTensor (I := I) (M := M) g (s + 1)
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) := by
  exact pairTrace_decomposition (I := I) (M := M) g gm s

private lemma edge_sum4_comm
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ p : A × B, ∑ q : C × D, F p.1 p.2 q.1 q.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ q : C × D, ∑ p : A × B, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
          simp only [Fintype.sum_prod_type]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_bitrace_move
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (S Z : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : Real) else 0) :
    (∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
        S (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x) *
          Z (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x)) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        S (metricComparisonEndomorphism (I := I) g gm x (e i))
            (metricComparisonEndomorphism (I := I) g gm x (e j)) * Z (e i) (e j) := by
  classical
  let f : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) gm x a x
  let c : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i a => g.inner x (e i) (f a)
  have hf : ∀ a b, gm.inner x (f a) (f b) = if a = b then (1 : Real) else 0 := by
    intro a b
    exact smoothOrthoFrame_orthonormal_at_center (I := I) gm x a b
  have hraise : ∀ i, metricComparisonEndomorphism (I := I) g gm x (e i) =
      ∑ a, c i a • f a := by
    intro i
    have hrep := orthonormal_tangent_expansion (I := I) (M := M) gm x f hf
      (metricComparisonEndomorphism (I := I) g gm x (e i))
    rw [← hrep]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [gm.symm x (f a) (metricComparisonEndomorphism (I := I) g gm x (e i))]
    rw [metricComparisonEndomorphism_apply]
    rw [inverseMetricSharpFib_inner (I := I) gm x
      (g0FlatCLM (I := I) g x (e i)) (f a)]
    rw [show cotangentToDualLinear (I := I) (x := x)
        (g0FlatCLM (I := I) g x (e i)) (f a) =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x (e i)) (f a) from rfl]
    rw [cotangentToDual_g0FlatCLM]
  have hframe : ∀ a, f a = ∑ i, c i a • e i := by
    intro a
    exact (orthonormal_tangent_expansion (I := I) (M := M) g x e he (f a)).symm
  have hS : ∀ i j,
      S (metricComparisonEndomorphism (I := I) g gm x (e i))
          (metricComparisonEndomorphism (I := I) g gm x (e j)) =
        ∑ a, ∑ b, (c i a * c j b) * S (f a) (f b) := by
    intro i j
    rw [hraise i, map_sum S (fun a => c i a • f a) Finset.univ]
    simp only [map_smul, sum_apply,
      smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hraise j, map_sum (S (f a)) (fun b => c j b • f b) Finset.univ]
    simp only [map_smul,
      smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hZ : ∀ a b, Z (f a) (f b) =
      ∑ i, ∑ j, (c i a * c j b) * Z (e i) (e j) := by
    intro a b
    rw [hframe a, map_sum Z (fun i => c i a • e i) Finset.univ]
    simp only [map_smul, sum_apply,
      smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hframe b, map_sum (Z (e i)) (fun j => c j b • e j) Finset.univ]
    simp only [map_smul,
      smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc
    (∑ a, ∑ b, S (f a) (f b) * Z (f a) (f b)) =
        ∑ a, ∑ b, ∑ i, ∑ j,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hZ a b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) :=
      edge_sum4_comm (fun a b i j =>
        (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)))
    _ = ∑ i, ∑ j,
        S (metricComparisonEndomorphism (I := I) g gm x (e i))
            (metricComparisonEndomorphism (I := I) g gm x (e j)) * Z (e i) (e j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS i j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring

def secondSlotInsertionCoefficient (g : SmoothRiemannianMetric I M)
    (Lambda : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j)
    (operatorFieldApply (I := I) (M := M) g 2 2
      (endoSlotZeroCcTensor (I := I) (M := M) g 1 Lambda)
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S))

def secondSlotMetricComparisonCoefficient (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  secondSlotInsertionCoefficient (I := I) (M := M) g
    (metricComparisonEndomorphismField (I := I) (M := M) g gm) 1
    (secondSlotInsertionCoefficient (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 S)

def fourTensorProductCoefficient (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  operatorFieldApply (I := I) (M := M) g 2 4
    (slotExtendIter (I := I) (M := M) g 0 2 2 B) A

def topOrderPairingAdjointCoefficient (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (sigma : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g sigma.symm
    (fourTensorProductCoefficient (I := I) (M := M) g
      (secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm S) S)

def topOrderPairingCoefficient (g gm : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 6 2
    (secondMetricPairTraceOperator (I := I) (M := M) g gm)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G)))

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderPairingCoefficient_decomposition (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S =
      operatorFieldApply (I := I) (M := M) g 4 2
        (curvatureActionMonomialCoeffField (I := I) (M := M) g gm
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ) G := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  apply ContinuousLinearMap.ext
  intro t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [edge_rank0_decomp (I := I) (M := M) x t]
  simp only [map_smul, Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  congr 1
  rw [topOrderPairingCoefficient]
  rw [secondMetricPairTraceOperator_apply_toModel (I := I) (M := M) g gm
    (domDomCongrSection (I := I) g
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G) x
    ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x)) v]
  rw [show ((show Tensor0SSpace 4 I x →L[Real] Tensor0SSpace 2 I x from
      (curvatureActionMonomialCoeffField (I := I) (M := M) g gm
        (ccTensorUnitValueSection (I := I) (M := M) g S)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ).toSection x)
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x))) =
    curvatureActionMonomialTrace (I := I) (M := M) gm
      (ccTensorUnitValueSection (I := I) (M := M) g S) σ x
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) from rfl]
  rw [curvatureActionMonomialTrace,
    curvatureDecompositionMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg₂ (· * ·) rfl ?_
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)) =
    unitModel (I := I) (M := M) g 4 G x from rfl]
  refine congrArg _ ?_
  funext i
  rw [Equiv.trans_apply]
  generalize σ i = k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem secondSlotInsertionCoefficient_apply (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[Real] E) ∞
      (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))
    (j : Fin 2) (S : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (secondSlotInsertionCoefficient (I := I) (M := M) g Λ j S) x v =
      unitModel (I := I) (M := M) g 2 S x
        (Function.update v j (tangentLinearMapToModel (Λ x) (v j))) := by
  classical
  rw [secondSlotInsertionCoefficient, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) j) S) x from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases j <;> fin_cases k <;> simp [Equiv.swap_apply_def]

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem secondSlotMetricComparisonCoefficient_apply (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm S) x v =
      unitModel (I := I) (M := M) g 2 S x
        (fun k => tangentLinearMapToModel
          (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v k)) := by
  classical
  rw [secondSlotMetricComparisonCoefficient, secondSlotInsertionCoefficient_apply, secondSlotInsertionCoefficient_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma edge_extend_cons
    (g : SmoothRiemannianMetric I M) (r s : Nat)
    (Φ : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : E)
    (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[Real]
            Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s Φ).toSection x) D)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
          Φ.toSection x)
          (tensor0SCurry (I := I) (M := M) (𝕜 := Real) r x D
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0))) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[Real]
      Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s Φ).toSection x) D) =
      slotExtendPointwise (I := I) (M := M) r s x
        (show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
          Φ.toSection x) D from rfl]
  exact slotExtendFib_apply_eval (I := I) (M := M) r s x
    (show Tensor0SSpace r I x →L[Real] Tensor0SSpace s I x from
      Φ.toSection x) D v0 vs

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma edge_extend2_eval (g : SmoothRiemannianMetric I M)
    (B : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 2 B).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g 2 B x ![u 2, u 3] := by
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 2 B).toSection x) D) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtendIter (I := I) (M := M) g 0 2 1 B)).toSection x) D)
        u from rfl]
  have hu : u = Fin.cons (u 0) (Fin.cons (u 1) ![u 2, u 3]) := by
    funext k
    fin_cases k <;> rfl
  rw [hu]
  rw [edge_extend_cons (I := I) (M := M) g 1 3
    (slotExtendIter (I := I) (M := M) g 0 2 1 B) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 1 B).toSection x)
        (tensor0SCurry (I := I) (M := M) (𝕜 := Real) 1 x D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))) =
      ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g 0 2 B).toSection x)
        (tensor0SCurry (I := I) (M := M) (𝕜 := Real) 1 x D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))) from rfl]
  rw [edge_extend_cons (I := I) (M := M) g 0 2 B x
    (tensor0SCurry (I := I) (M := M) (𝕜 := Real) 1 x D
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0))) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0SCurry (I := I) (M := M) (𝕜 := Real) 0 x
      (tensor0SCurry (I := I) (M := M) (𝕜 := Real) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 1))
      with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
      (T := tensor0SCurry (I := I) (M := M) (𝕜 := Real) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
      (v0 := u 1) (vs := fun i : Fin 0 => i.elim0)]
    rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
      (T := D) (v0 := u 0)
      (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))]
    congr 1
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, smul_apply,
    smul_eq_mul]
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem fourTensorProductCoefficient_apply (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (fourTensorProductCoefficient (I := I) (M := M) g A B) x v =
      unitModel (I := I) (M := M) g 2 A x ![v 0, v 1] *
        unitModel (I := I) (M := M) g 2 B x ![v 2, v 3] := by
  rw [unitModel, fourTensorProductCoefficient, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  rw [edge_extend2_eval (I := I) (M := M) g B x]
  rfl

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderPairingAdjointCoefficient_apply (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4))
    (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ) x v =
      unitModel (I := I) (M := M) g 2 S x
          ![tangentLinearMapToModel
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v (σ.symm 0)),
            tangentLinearMapToModel
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v (σ.symm 1))] *
        unitModel (I := I) (M := M) g 2 S x
          ![v (σ.symm 2), v (σ.symm 3)] := by
  rw [topOrderPairingAdjointCoefficient, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply, fourTensorProductCoefficient_apply,
    secondSlotMetricComparisonCoefficient_apply]
  congr 2 ; funext k ; fin_cases k <;> rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderPairingCoefficient_apply (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S) x v =
      ∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 S x
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g 4 G x
            (fun i => (Fin.cons
              (smoothOrthoFrame (I := I) gm x a x : E)
              (Fin.cons (smoothOrthoFrame (I := I) gm x b x : E) v) :
                Fin 4 → E) (σ i)) := by
  rw [topOrderPairingCoefficient_decomposition (I := I) (M := M) g gm S G σ]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (curvatureActionMonomialTrace (I := I) (M := M) gm
        (ccTensorUnitValueSection (I := I) (M := M) g S) σ x
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
          G.toSection x) (unitTensor (I := I) (M := M) x))) v = _
  rw [curvatureActionMonomialTrace,
    curvatureDecompositionMonomialFibFixedFrame_toModel]
  rfl

private def edgeEvalCLM (s : Nat) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[Real] Real :=
  haveI : FiniteDimensional Real (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edgeEvalCLM_apply (s : Nat) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    edgeEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel D v := rfl

private def edgeFeedCLM (s : Nat) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  let split : Fin (s + 2) ≃ Fin 2 ⊕ Fin s :=
    (finCongr (Nat.add_comm s 2)).trans finSumFinEquiv.symm
  let onModel : ContinuousMultilinearMap Real (fun _ : Fin 2 => E) Real :=
    (ContinuousMultilinearMap.apply Real (fun _ : Fin s => E) Real v)
      |>.compContinuousMultilinearMap
        ((ContinuousMultilinearMap.domDomCongr split (Tensor0SSpace.toModel G)).currySum)
  let onTangent : ContinuousMultilinearMap Real
      (fun _ : Fin 2 => TangentSpace I x) Real :=
    onModel.compContinuousLinearMap (fun _ => trivToE (I := I) x x)
  (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).toContinuousLinearMap.comp
    onTangent.curryLeft

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edgeFeedCLM_apply (s : Nat) (x : M)
    (G : Tensor0SSpace (s + 2) I x) (v : Fin s → E)
    (p q : TangentSpace I x) :
    edgeFeedCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel G
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x q) v)) := by
  let split : Fin (s + 2) ≃ Fin 2 ⊕ Fin s :=
    (finCongr (Nat.add_comm s 2)).trans finSumFinEquiv.symm
  let onModel : ContinuousMultilinearMap Real (fun _ : Fin 2 => E) Real :=
    (ContinuousMultilinearMap.apply Real (fun _ : Fin s => E) Real v)
      |>.compContinuousMultilinearMap
        ((ContinuousMultilinearMap.domDomCongr split (Tensor0SSpace.toModel G)).currySum)
  let onTangent : ContinuousMultilinearMap Real
      (fun _ : Fin 2 => TangentSpace I x) Real :=
    onModel.compContinuousLinearMap (fun _ => trivToE (I := I) x x)
  change (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
      (onTangent.curryLeft p)) q =
    Tensor0SSpace.toModel G
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x q) v))
  rw [continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  simp only [onTangent, onModel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply,
    trivToE_self_apply,
    DifferentialGeometry.Integral.Measure.centeredChartTangentEquiv_apply]
  change (ContinuousMultilinearMap.domDomCongr split (Tensor0SSpace.toModel G)).currySum
      (fun i : Fin 2 =>
        @Fin.cons 1 (fun _ : Fin 2 => E)
          (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
          (@Fin.snoc 0 (fun _ : Fin 1 => E) (fun j => j.elim0)
            (tangentSpaceModelContinuousLinearEquiv (I := I) x q)) i) v =
    Tensor0SSpace.toModel G
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x q) v))
  rw [ContinuousMultilinearMap.currySum_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => ?_) j) i
  have hcast :
      Fin.cast (Nat.add_comm s 2) k.succ.succ = Fin.natAdd 2 k := by
    apply Fin.ext
    change k.val + 1 + 1 = 2 + k.val
    omega
  simp only [split, Equiv.trans_apply, finCongr_apply, hcast,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
  rfl

private lemma edge_sum_succ {A R : Type*} [Fintype A] [AddCommMonoid R]
    (s : Nat) (F : (Fin (s + 1) → A) → R) :
    (∑ J : Fin (s + 1) → A, F J) =
      ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
  classical
  calc
    (∑ J : Fin (s + 1) → A, F J) =
        ∑ p : A × (Fin s → A),
          F ((Fin.consEquiv (fun _ : Fin (s + 1) => A)) p) :=
      ((Fin.consEquiv (fun _ : Fin (s + 1) => A)).sum_comp F).symm
    _ = ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
      rw [Fintype.sum_prod_type]
      rfl

private lemma edge_sum2 {A : Type*} [Fintype A] (F : (Fin 2 → A) → Real) :
    (∑ J : Fin 2 → A, F J) = ∑ a : A, ∑ b : A, F ![a, b] := by
  classical
  calc
    (∑ J : Fin 2 → A, F J) =
        ∑ p : A × A, F ((finTwoArrowEquiv A).symm p) :=
      ((finTwoArrowEquiv A).symm.sum_comp F).symm
    _ = ∑ a : A, ∑ b : A, F ![a, b] := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1

private lemma edge_sum4 {A : Type*} [Fintype A] (F : (Fin 4 → A) → Real) :
    (∑ J : Fin 4 → A, F J) =
      ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A, F ![a, b, c, d] := by
  classical
  rw [edge_sum_succ (s := 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [edge_sum_succ (s := 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [edge_sum_succ (s := 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [edge_sum_succ (s := 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · congr 1
  · intro q _ hq
    exact absurd (Subsingleton.elim q (fun i : Fin 0 => i.elim0)) hq
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edge_inner0 (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g.inner x (e a) (e b) = if a = b then (1 : Real) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x (A.toFun x) (B.toFun x) =
      ∑ J : Fin s → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g s A x (fun k => (e (J k) : E)) *
          unitModel (I := I) (M := M) g s B x (fun k => (e (J k) : E)) := by
  classical
  rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  rw [tensorInnerPointwise_eq_sum_componentS_mul
    (I := I) (M := M) g 0 s x e bse rfl hbse horth
    (A.toSection x) (B.toSection x)]
  have hcomp : ∀ (T : SmoothCcTensor g 0 s)
      (K : Fin 0 → Fin (Module.finrank Real E))
      (J : Fin s → Fin (Module.finrank Real E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (T.toSection x) (Module.finrank Real E) e K J =
        unitModel (I := I) (M := M) g s T x
          (fun k => (e (J k) : E)) := by
    intro T K J
    rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s
        (T.toSection x) (Module.finrank Real E) e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          T.toSection x) (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => (e (J k) : E)) from rfl]
    rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
    rfl
  have hK : ∀ F : (Fin 0 → Fin (Module.finrank Real E)) → Real,
      (∑ K : Fin 0 → Fin (Module.finrank Real E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro q _ hq
      exact absurd (Subsingleton.elim q Fin.elim0) hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hK]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hcomp A Fin.elim0 J, hcomp B Fin.elim0 J]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem edgePair_point (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x (S.toFun x)
        ((operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ).toFun x) (G.toFun x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) g x
  let em : Fin (Module.finrank Real E) → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x (e i)
  let fm : Fin (Module.finrank Real E) → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x
      (smoothOrthoFrame (I := I) gm x i x)
  let cm : Fin (Module.finrank Real E) → E := fun i =>
    tangentLinearMapToModel (metricComparisonEndomorphism (I := I) g gm x) (em i)
  rw [edge_inner0 (I := I) (M := M) g 2 S
      (operatorFieldApply (I := I) (M := M) g 2 2
        (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S) x e bse hbse horth,
    edge_inner0 (I := I) (M := M) g 4
      (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ) G x e bse hbse horth,
    edge_sum2]
  have hmove : ∀ i j : Fin (Module.finrank Real E),
      (∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 S x
              (Fin.cons (fm a) (Fin.cons (fm b) ![])) *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons
                (fm a) (Fin.cons (fm b) ![em i, em j]) : Fin 4 → E) (σ k))) =
        (∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 S x
              (Fin.cons (cm a) (Fin.cons (cm b) ![])) *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons (em a)
                (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                (σ k))) := by
    intro i j
    let Sx : Tensor0SSpace 2 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from S.toSection x)
        (unitTensor (I := I) (M := M) x)
    let Gx : Tensor0SSpace 4 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)
    have hm := edge_bitrace_move (I := I) (M := M) g gm x
      (edgeFeedCLM (I := I) (M := M) 0 x Sx ![])
      (edgeFeedCLM (I := I) (M := M) 2 x
        (tensorRank4PermuteCLM (I := I) (M := M) x σ Gx) ![em i, em j])
      e horth
    simpa only [edgeFeedCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply, Sx, Gx, unitModel,
      em, fm, cm, tangentLinearMapToModel_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hm
  calc
    _ = (∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S) x
            ![em i, em j]) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have hv : (fun k : Fin 2 => (e (![i, j] k) : E)) = ![em i, em j] := by
          funext k
          fin_cases k <;> rfl
        rw [hv]
    _ =
      ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 S x
                ![fm a, fm b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons
                  (fm a) (Fin.cons (fm b) ![em i, em j]) : Fin 4 → E) (σ k))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [topOrderPairingCoefficient_apply (I := I) (M := M) g gm S G σ x]
        simp only [fm, tangentSpaceModelContinuousLinearEquiv_apply]
    _ = ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 S x
                ![cm a, cm b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (em a)
                  (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                  (σ k))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        exact congrArg
          (fun r : Real => unitModel (I := I) (M := M) g 2 S x ![em i, em j] * r)
          (hmove i j)
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        (unitModel (I := I) (M := M) g 2 S x
              ![cm a, cm b] *
            unitModel (I := I) (M := M) g 2 S x ![em i, em j]) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => (Fin.cons (em a)
              (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                (σ k)) := by
        rw [show (∑ i, ∑ j,
            unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
              (∑ a, ∑ b,
                unitModel (I := I) (M := M) g 2 S x
                    ![cm a, cm b] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (em a)
                      (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                      (σ k)))) =
            ∑ i, ∑ j, ∑ a, ∑ b,
              unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
                (unitModel (I := I) (M := M) g 2 S x
                    ![cm a, cm b] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (em a)
                      (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                      (σ k))) from by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]]
        rw [edge_sum4_comm (fun i j a b =>
          unitModel (I := I) (M := M) g 2 S x ![em i, em j] *
            (unitModel (I := I) (M := M) g 2 S x
                ![cm a, cm b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (em a)
                  (Fin.cons (em b) ![em i, em j]) : Fin 4 → E)
                  (σ k))))]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ K : Fin 4 → Fin (Module.finrank Real E),
        (unitModel (I := I) (M := M) g 2 S x
              ![cm (K 0), cm (K 1)] *
            unitModel (I := I) (M := M) g 2 S x
              ![em (K 2), em (K 3)]) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => em (K (σ k))) := by
        rw [edge_sum4]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have h0 : cm (![a, b, i, j] 0) = cm a := rfl
        have h1 : cm (![a, b, i, j] 1) = cm b := rfl
        have h2 : em (![a, b, i, j] 2) = em i := rfl
        have h3 : em (![a, b, i, j] 3) = em j := rfl
        have hcomp :
            (fun k => em (![a, b, i, j] (σ k))) =
              fun k => (Fin.cons (em a)
                (Fin.cons (em b) ![em i, em j]) : Fin 4 → E) (σ k) := by
          funext k
          generalize σ k = l
          fin_cases l <;> rfl
        rw [h0, h1, h2, h3, hcomp]
    _ = ∑ J : Fin 4 → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4
            (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ) x
            (fun k => em (J k)) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => em (J k)) := by
        refine Fintype.sum_equiv
          (Equiv.arrowCongr σ.symm
            (Equiv.refl (Fin (Module.finrank Real E))))
          (fun K =>
            (unitModel (I := I) (M := M) g 2 S x
                  ![cm (K 0), cm (K 1)] *
                unitModel (I := I) (M := M) g 2 S x
                  ![em (K 2), em (K 3)]) *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => em (K (σ k))))
          (fun J =>
            unitModel (I := I) (M := M) g 4
                (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ) x
                (fun k => em (J k)) *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => em (J k)))
          (fun K => ?_)
        have heqv :
            (Equiv.arrowCongr σ.symm
              (Equiv.refl (Fin (Module.finrank Real E)))) K =
              (fun k => K (σ k)) := by
          funext k
          simp [Equiv.arrowCongr]
        rw [heqv]
        simp only
        rw [topOrderPairingAdjointCoefficient_apply]
        simp only [Equiv.apply_symm_apply]
        rfl
    _ = _ := by
        simp only [em, tangentSpaceModelContinuousLinearEquiv_apply]

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem topOrderPairing_l2 (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    tensorL2Inner (I := I) (M := M) g 0 2 S.toFun
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ).toFun G.toFun := by
  classical
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact edgePair_point (I := I) (M := M) g gm S G σ x

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem topOrderPairing_inner (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    (⟪S, (operatorFieldApply (I := I) (M := M) g 2 2
        (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) S)⟫_ℝ : Real) =
      ⟪topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S σ, G⟫_ℝ := by
  rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  exact topOrderPairing_l2 (I := I) (M := M) g gm S G σ

def deTurckLieTopOrderPairingFamily (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
    (topOrderPairingCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) (q i)
      + topOrderPairingCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

def deTurckLieTopOrderPairingAdjoint (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 0 4 :=
  s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
    (topOrderPairingAdjointCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T (q i) +
      topOrderPairingAdjointCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem deTurckLieTopOrderPairing_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ q epsilon s) T =
      operatorFieldApply (I := I) (M := M) g 4 2
        (deTurckLieCovariantDerivativeDecompositionC2Family
          (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [deTurckLieTopOrderPairingFamily, deTurckLieCovariantDerivativeDecompositionC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [operatorFieldApplication_smul_left, operatorFieldApplication_add_left]
  rw [topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 0),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 1),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) (q 2),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T)
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

def riemannTopOrderPairingCoefficient (g gm : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) (q : Fin 4 → Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 2 2 :=
  (1 / 2 : Real) •
    (topOrderPairingCoefficient (I := I) (M := M) g gm G (q 0) +
      topOrderPairingCoefficient (I := I) (M := M) g gm G (q 1) -
      topOrderPairingCoefficient (I := I) (M := M) g gm G (q 2) -
      topOrderPairingCoefficient (I := I) (M := M) g gm G (q 3))

def riemannTopOrderPairingAdjoint (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (q : Fin 4 → Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 0 4 :=
  (1 / 2 : Real) •
    (topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S (q 0) +
      topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S (q 1) -
      topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S (q 2) -
      topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S (q 3))

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem riemannTopOrderPairing_apply (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (q : Fin 4 → Equiv.Perm (Fin 4)) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (riemannTopOrderPairingCoefficient (I := I) (M := M) g gm G q) S =
      operatorFieldApply (I := I) (M := M) g 4 2
        (curvatureActionKernelCoeffField (I := I) (M := M) g gm
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S)
          (q 0) (q 1) (q 2) (q 3)) G := by
  rw [riemannTopOrderPairingCoefficient, curvatureActionKernelCoeffField]
  simp only [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, operatorFieldApplication_sub_left]
  rw [topOrderPairingCoefficient_decomposition (I := I) (M := M) g gm S G (q 0),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g gm S G (q 1),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g gm S G (q 2),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g gm S G (q 3)]

def riemannTopOrderPairingFamily (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    SmoothCcTensor g 2 2 :=
  s • ((1 / 2 : Real) •
    (riemannTopOrderPairingCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) qA +
      riemannTopOrderPairingCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) qB))

def riemannTopOrderPairingFamilyAdjoint (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    SmoothCcTensor g 0 4 :=
  s • ((1 / 2 : Real) •
    (riemannTopOrderPairingAdjoint (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T qA +
      riemannTopOrderPairingAdjoint (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T qB))

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
theorem riemannTopOrderPairingFamily_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : Real) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (riemannTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ qA qB s) T =
      operatorFieldApply (I := I) (M := M) g 4 2
        (riemannPalatiniDecompositionC2Family
          (I := I) (M := M) g T hdelta hdeltaZ qA qB s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [riemannTopOrderPairingFamily, riemannPalatiniDecompositionC2Family]
  simp only [operatorFieldApplication_smul_left, operatorFieldApplication_add_left]
  rw [riemannTopOrderPairing_apply (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) qA,
    riemannTopOrderPairing_apply (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T
      (iteratedCovGrad (I := I) g 0 2 2 T) qB]

def ricciDeTurckTopOrderPairingCoefficient (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  (2 : Real) • riemannTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hdelta hdeltaZ q epsilon s

def ricciDeTurckTopOrderPairingAdjoint (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 0 4 :=
  (2 : Real) •
      riemannTopOrderPairingFamilyAdjoint (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
    deTurckLieTopOrderPairingAdjoint (I := I) (M := M) g T hdelta hdeltaZ q epsilon s

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
theorem ricciDeTurckTopOrderPairingCoefficient_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ qA qB q epsilon s) T =
      operatorFieldApply (I := I) (M := M) g 4 2
        ((2 : Real) • riemannPalatiniDecompositionC2Family
            (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
          deTurckLieCovariantDerivativeDecompositionC2Family
            (I := I) (M := M) g T hdelta hdeltaZ q epsilon s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [ricciDeTurckTopOrderPairingCoefficient]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
  rw [riemannTopOrderPairingFamily_apply (I := I) (M := M) g T hdelta hdeltaZ qA qB s,
    deTurckLieTopOrderPairing_apply (I := I) (M := M) g T hdelta hdeltaZ q epsilon s]

omit [BoundarylessManifold I M] in
theorem ricciDeTurckTopOrderPairing_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T)⟫_ℝ : Real) =
      ⟪ricciDeTurckTopOrderPairingAdjoint (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s,
        iteratedCovGrad (I := I) g 0 2 2 T⟫_ℝ := by
  rw [ricciDeTurckTopOrderPairingCoefficient, ricciDeTurckTopOrderPairingAdjoint, riemannTopOrderPairingFamily, riemannTopOrderPairingFamilyAdjoint,
    riemannTopOrderPairingCoefficient, riemannTopOrderPairingCoefficient, riemannTopOrderPairingAdjoint, riemannTopOrderPairingAdjoint,
    deTurckLieTopOrderPairingFamily, deTurckLieTopOrderPairingAdjoint,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp_rw [topOrderPairing_inner (I := I) (M := M) g]

theorem ricciDeTurckTopOrderPairing_green
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    (⟪T, (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T)⟫_ℝ : Real) =
      -⟪covDivergence (I := I) (M := M) g 3
          (ricciDeTurckTopOrderPairingAdjoint (I := I) (M := M) g T hdelta hdeltaZ
            qA qB q epsilon s),
        iteratedCovGrad (I := I) g 0 2 1 T⟫_ℝ := by
  let P : SmoothCcTensor g 0 4 :=
    ricciDeTurckTopOrderPairingAdjoint (I := I) (M := M) g T hdelta hdeltaZ
      qA qB q epsilon s
  let T₁ : SmoothCcTensor g 0 3 := iteratedCovGrad (I := I) g 0 2 1 T
  have hjet : iteratedCovGrad (I := I) g 0 2 2 T =
      covGrad (I := I) (M := M) g 0 3 T₁ := by
    simp only [T₁]
    exact (iteratedCovGrad_succ g 0 2 1 T).symm
  have hgreen :
      (⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_ℝ : Real) =
        -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_ℝ := by
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 3 T₁ P
  calc
    (⟪T, operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ
          qA qB q epsilon s) T⟫_ℝ : Real) =
        ⟪P, iteratedCovGrad (I := I) g 0 2 2 T⟫_ℝ := by
      exact ricciDeTurckTopOrderPairing_inner (I := I) (M := M) g T hdelta hdeltaZ
        qA qB q epsilon s
    _ = ⟪covGrad (I := I) (M := M) g 0 3 T₁, P⟫_ℝ := by
      rw [hjet, real_inner_comm]
    _ = -⟪T₁, covDivergence (I := I) (M := M) g 3 P⟫_ℝ := hgreen
    _ = -⟪covDivergence (I := I) (M := M) g 3 P, T₁⟫_ℝ := by
      rw [real_inner_comm]

theorem exists_ricciDeTurck_top_order_pairing_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B₀ : Real, 0 ≤ B₀ ∧
      ∃ (C₀ : Real → SmoothCcTensor g 2 2)
        (C₂ : Real → SmoothCcTensor g 4 2),
        (∀ s ∈ Set.Icc (0 : Real) 1,
          metricDependentLowOrderAction (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W =
            (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
                (ricciPalatiniHalfCoefficient (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)) W +
              operatorFieldApply (I := I) (M := M) g 2 2 (C₀ s) W +
              operatorFieldApply (I := I) (M := M) g 2 2
                (ricciPalatiniZeroOrderFold (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W +
              operatorFieldApply (I := I) (M := M) g 3 2
                (metricDependentFirstOrderCoefficient (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg)
                (iteratedCovGrad (I := I) g 0 2 1 W) +
              operatorFieldApply (I := I) (M := M) g 4 2 (C₂ s)
                (iteratedCovGrad (I := I) g 0 2 2 W)) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C₀ s).toSection x) ≤ B₀ ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((C₂ s).toSection x) ≤
            2 * (max (8 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta))) 0) ^ 2 +
              2 * (max (3 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta) ^ 2)) 0) ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1,
          (⟪W, (metricDependentLowOrderAction (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W)⟫_ℝ : Real) =
            (-2 : Real) *
                ⟪W, operatorFieldApply (I := I) (M := M) g 2 2
                  (ricciPalatiniHalfCoefficient (I := I) (M := M) g
                    (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)) W⟫_ℝ +
              ⟪W, operatorFieldApply (I := I) (M := M) g 2 2 (C₀ s) W⟫_ℝ +
              ⟪W, operatorFieldApply (I := I) (M := M) g 2 2
                (ricciPalatiniZeroOrderFold (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W⟫_ℝ +
              ⟪W, operatorFieldApply (I := I) (M := M) g 3 2
                (metricDependentFirstOrderCoefficient (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg)
                (iteratedCovGrad (I := I) g 0 2 1 W)⟫_ℝ +
              ⟪W, operatorFieldApply (I := I) (M := M) g 4 2 (C₂ s)
                (iteratedCovGrad (I := I) g 0 2 2 W)⟫_ℝ) := by
  classical
  let a : Nat := 2 * Module.finrank Real E + 10
  let R : Real := ∑ j ∈ Finset.range (a + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j W‖
  have ha : 2 * Module.finrank Real E + 10 ≤ a := by rfl
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg fun j _ => norm_nonneg _
  have hball : ∀ j : Nat, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g 0 2 j W‖ ≤ R := by
    intro j hj
    exact Finset.single_le_sum
      (f := fun k => ‖iteratedCovGrad (I := I) g 0 2 k W‖)
      (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hhalf_lt : (1 / 2 : Real) < 1 := by norm_num
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half hhalf_lt
  let hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta :=
    metricPerturbation_zero_bound_at (I := I) (M := M) g hdelta_nn
  obtain ⟨LambdaR, hLambdaR, KR, hKR, qA, qB, hq, hRmain⟩ :=
    exists_riemannPalatini_decomposition_identity_data (I := I) (M := M)
      g a ha hR hhalf_lt
  obtain ⟨LambdaD, hLambdaD, KD, hKD, q, epsilon, hepsilon, hDmain⟩ :=
    exists_deTurckLieCovariantDerivativeArm_decomposition_identity_data (I := I) (M := M)
      g g_bg a ha hR hhalf_lt
  obtain ⟨C0R, hjR, hidR, hsupR, henvR⟩ :=
    hRmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨C0D, hjD, hidD, hsupD, henvD⟩ :=
    hDmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨K2D, hK2D, hDcap⟩ :=
    exists_deTurckLieCovariantDerivativeDecompositionC2Family_cap_l2JetWindow
      (I := I) (M := M) g a ha hR hhalf_lt q epsilon hepsilon
  obtain ⟨hj2D, hsup2D, henv2D⟩ :=
    hDcap W hdelta_half hdelta hdeltaZ hball
  have hsup2R := riemannPalatiniDecompositionC2Family_riemannianFiberNormSq_le
    (I := I) (M := M) g W hdelta_lt hdelta_half hdelta hdeltaZ qA qB hq
  let C₀ : Real → SmoothCcTensor g 2 2 := fun s => C0R s + C0D s
  let C₂ : Real → SmoothCcTensor g 4 2 := fun s =>
    (2 : Real) •
        riemannPalatiniDecompositionC2Family (I := I) (M := M) g W hdelta hdeltaZ qA qB s +
      deTurckLieCovariantDerivativeDecompositionC2Family
        (I := I) (M := M) g W hdelta hdeltaZ q epsilon s
  have hnormal : ∀ s ∈ Set.Icc (0 : Real) 1,
      metricDependentLowOrderAction (I := I) (M := M) g
          (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W =
        (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
            (ricciPalatiniHalfCoefficient (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)) W +
          operatorFieldApply (I := I) (M := M) g 2 2 (C₀ s) W +
          operatorFieldApply (I := I) (M := M) g 2 2
            (ricciPalatiniZeroOrderFold (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W +
          operatorFieldApply (I := I) (M := M) g 3 2
            (metricDependentFirstOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg)
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          operatorFieldApply (I := I) (M := M) g 4 2 (C₂ s)
            (iteratedCovGrad (I := I) g 0 2 2 W) := by
    intro s hs
    have hmetric := metricComparisonEndomorphism_pairing_balance (I := I) (M := M) g W hdelta_lt hdelta hdeltaZ hs
    have hriem := hidR s hs
    have hlie := hidD s hs
    simp only [iteratedCovGrad_zero] at hriem hlie
    rw [hmetric]
    have hriemInsert :
        (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
            (linearizedRicciConnectionDifferenceOrder0CoeffField
              (I := I) (M := M) g
              (metricPerturbationPath (I := I) g W 0 hdelta hdeltaZ s)) W =
          (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
              (ricciPalatiniHalfCoefficient (I := I) (M := M) g
                (metricPerturbationPath (I := I) g W 0 hdelta hdeltaZ s)) W +
            (operatorFieldApply (I := I) (M := M) g 2 2 (C0R s) W +
              operatorFieldApply (I := I) (M := M) g 4 2
                ((2 : Real) • riemannPalatiniDecompositionC2Family
                  (I := I) (M := M) g W hdelta hdeltaZ qA qB s)
                (iteratedCovGrad (I := I) g 0 2 2 W)) := by
      symm
      rw [← hriem]
      simp only [ricciPalatiniHalfCoefficient, operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
      module
    simp only [metricDependentLowOrderAction, firstOrderCoefficientAction, metricDependentZeroOrderCoefficient,
      deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left]
    rw [hriemInsert, hlie]
    simp only [ricciPalatiniZeroOrderFold, C₀, C₂,
      operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left]
    module
  have hBsq : 0 ≤ 2 * LambdaR ^ 2 + 2 * LambdaD ^ 2 := by positivity
  refine ⟨Real.sqrt (2 * LambdaR ^ 2 + 2 * LambdaD ^ 2), Real.sqrt_nonneg _,
    C₀, C₂, ?_, ?_, ?_, ?_⟩
  · exact hnormal
  · intro s hs x
    dsimp only [C₀]
    change riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        ((C0R s).toSection x + (C0D s).toSection x) ≤ _
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 2 2 x ((C0R s).toSection x) ((C0D s).toSection x)
    have hR0 := hsupR s hs x
    have hD0 := hsupD s hs x
    rw [Real.sq_sqrt hBsq]
    linarith
  · intro s hs x
    dsimp only [C₂]
    change riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (((2 : Real) • riemannPalatiniDecompositionC2Family
            (I := I) (M := M) g W hdelta hdeltaZ qA qB s).toSection x +
          (deTurckLieCovariantDerivativeDecompositionC2Family
            (I := I) (M := M) g W hdelta hdeltaZ q epsilon s).toSection x) ≤ _
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
      (((2 : Real) •
        riemannPalatiniDecompositionC2Family
          (I := I) (M := M) g W hdelta hdeltaZ qA qB s).toSection x)
      ((deTurckLieCovariantDerivativeDecompositionC2Family
        (I := I) (M := M) g W hdelta hdeltaZ q epsilon s).toSection x)
    have hR2 := hsup2R s hs x
    have hD2 := hsup2D s hs x
    linarith
  · intro s hs
    have hid := hnormal s hs
    rw [hid]
    simp only [inner_add_right, real_inner_smul_right]

theorem exists_ricciDeTurck_top_order_pairing_lipschitz_bound
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B₀ : Real, 0 ≤ B₀ ∧
      ∃ (C₀ : Real → SmoothCcTensor g 2 2)
        (C₂ : Real → SmoothCcTensor g 4 2),
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C₀ s).toSection x) ≤ B₀ ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((C₂ s).toSection x) ≤
            2 * (max (8 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta))) 0) ^ 2 +
              2 * (max (3 * deTurckArmFibreConst (Module.finrank Real E) *
                (delta / (1 - delta) ^ 2)) 0) ^ 2) ∧
        ∀ (x : M) (v w : TangentSpace I x) {s : Real},
          s ∈ Set.Ioo (0 : Real) 1 →
          DeTurckCoefficients.rhsSumSlope (I := I) g g_bg W 0
              (lt_of_le_of_lt hdelta_half (by norm_num : (1 / 2 : Real) < 1)) hdelta
              (show (0 : Real) < 1 by norm_num)
              (zero_metricPerturbation_bound (I := I) (M := M) g) x v w s =
            unitModel (I := I) (M := M) g 2
              ((rawTensorConnLapSmooth (I := I) g 0 2 W +
                  deTurckPrincipalCometricArm (I := I) (M := M) g
                    (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) W) +
                (backgroundLowOrderAction (I := I) (M := M) g g_bg W +
                  ricciPalatiniTopOrderDecomposition (I := I) (M := M) g
                    (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W
                    (C₀ s) (C₂ s))) x ![v, w] := by
  obtain ⟨B₀, hB₀, C₀, C₂, hquad, hC₀, hC₂, hpair⟩ :=
    exists_ricciDeTurck_top_order_pairing_decomposition (I := I) (M := M) g g_bg W hWsymm hdelta_nn hdelta_half hdelta
  refine ⟨B₀, hB₀, C₀, C₂, hC₀, hC₂, ?_⟩
  intro x v w s hs
  have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hslope := ricciDeTurckRhsSlope_decomposition (I := I) (M := M) g g_bg W hWsymm
    (lt_of_le_of_lt hdelta_half (by norm_num : (1 / 2 : Real) < 1)) hdelta x v w hs
  rw [hslope, hquad s hscc]
  rfl

end Spectral
end Analysis
end DifferentialGeometry

end
