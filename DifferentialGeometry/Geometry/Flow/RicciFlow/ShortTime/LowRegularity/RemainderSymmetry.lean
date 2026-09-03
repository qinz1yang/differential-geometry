import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SymmetryPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SmoothBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.Basic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.SectionRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor_ext_bilin (g : SmoothRiemannianMetric I M)
    {S S' : SmoothCcTensor g 0 2}
    (h : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g S x u w = ccTensorBilin (I := I) g S' x u w) :
    S = S' := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have key : ∀ W : SmoothCcTensor g 0 2,
      unitModel (I := I) (M := M) g 2 W x v =
        ccTensorBilin (I := I) g W x (v 0) (v 1) := by
    intro W
    rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x (v 0) (v 1)]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [key S, key S']
  exact h x (v 0) (v 1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem bilin_ddc_swap (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) b u w =
      ccTensorBilin (I := I) g T b w u := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) b u w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g T b w u,
    domDomCongrSection_unitModel (I := I) g (Equiv.swap (0 : Fin 2) 1) T b,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ddc_swap_swap (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) = T := by
  refine ccTensor_ext_bilin (I := I) (M := M) g (fun x u w => ?_)
  rw [bilin_ddc_swap (I := I) (M := M) g, bilin_ddc_swap (I := I) (M := M) g]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ddc_swap_sub (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) (A - B) =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A -
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B := by
  refine ccTensor_ext_bilin (I := I) (M := M) g (fun x u w => ?_)
  simp only [bilin_ddc_swap (I := I) (M := M) g,
    ccTensorBilin_sub (I := I) (M := M) g]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_of_swap (g₀ : SmoothRiemannianMetric I M) {X : SmoothCcTensor g₀ 0 2}
    (h : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X = X) :
    symmS (I := I) (M := M) g₀ X = X := by
  simp only [symmS, ccTensor02Symm, h, ← two_smul ℝ X, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem swap_symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (symmS (I := I) (M := M) g₀ T) =
      symmS (I := I) (M := M) g₀ T := by
  refine ccTensor_ext_bilin (I := I) (M := M) g₀ (fun x u w => ?_)
  rw [bilin_ddc_swap (I := I) (M := M) g₀]
  simp only [ccTensorBilin_symmS (I := I) (M := M) g₀]
  exact ccTensorBilinSymm_symm (I := I) g₀ T x w u

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_idem (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T) =
      symmS (I := I) (M := M) g₀ T :=
  symmS_of_swap (I := I) (M := M) g₀ (swap_symmS (I := I) (M := M) g₀ T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem swap_of_symmS (g₀ : SmoothRiemannianMetric I M) {X : SmoothCcTensor g₀ 0 2}
    (h : symmS (I := I) (M := M) g₀ X = X) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X = X := by
  conv_lhs => rw [← h]
  rw [swap_symmS (I := I) (M := M) g₀, h]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem bilin_symm_of_symmS (g₀ : SmoothRiemannianMetric I M)
    {X : SmoothCcTensor g₀ 0 2} (h : symmS (I := I) (M := M) g₀ X = X)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ X x v w = ccTensorBilin (I := I) g₀ X x w v := by
  conv_lhs => rw [← h]
  conv_rhs => rw [← h]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ X x v w,
    ccTensorBilin_symmS (I := I) (M := M) g₀ X x w v,
    ccTensorBilinSymm_symm (I := I) g₀ X x v w]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem swap_deTurckRHSTerm (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ) x]
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 := unitModel_of_deTurckRHSSection_realize (I := I) (M := M) g₀ g_bg T
    hδ_lt hδ (deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x
    (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
  have h2 := unitModel_of_deTurckRHSSection_realize (I := I) (M := M) g₀ g_bg T
    hδ_lt hδ (deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v
  rw [h1, h2]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact deTurckRicciRHS_symm (I := I) g_bg
    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 1) (v 0)

omit [SigmaCompactSpace M] in
private theorem smoothRem_eq_term_sub (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSTermG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

omit [SigmaCompactSpace M] in
theorem swap_smoothRem (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T = T) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ := by
  rw [smoothRem_eq_term_sub (I := I) (M := M) g₀ g_bg T hδ_lt hδ,
    ddc_swap_sub (I := I) (M := M) g₀,
    swap_deTurckRHSTerm (I := I) (M := M) g₀ g_bg T hδ_lt hδ,
    ← rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T,
    hT]

omit [SigmaCompactSpace M] in
theorem symmS_smoothRem (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T) :
    symmS (I := I) (M := M) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ :=
  symmS_of_swap (I := I) (M := M) g₀
    (swap_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ
      (swap_of_symmS (I := I) (M := M) g₀ hT))

omit [SigmaCompactSpace M] in
theorem symmS_remSymmS (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ) :
    symmS (I := I) (M := M) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (symmS (I := I) (M := M) g₀ T) hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (symmS (I := I) (M := M) g₀ T) hδ_lt hδ :=
  symmS_smoothRem (I := I) (M := M) g₀ g_bg _ hδ_lt hδ
    (symmS_idem (I := I) (M := M) g₀ T)

omit [SigmaCompactSpace M] in
theorem bilin_smoothRem_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) x v w =
      ccTensorBilin (I := I) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) x w v :=
  bilin_symm_of_symmS (I := I) (M := M) g₀
    (symmS_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ hT) x v w

theorem smoothN_eq_embed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) := by
  ext i
  rfl

theorem symmHs_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (hσ : (0 : ℝ) ≤ (a : ℝ)) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T) :
    symmHs (I := I) (M := M) g₀ hσ
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  rw [smoothN_eq_embed (I := I) (M := M) g₀ g_bg a T hδ_lt hδ]
  exact symmHs_smoothCc_eq_self (I := I) (M := M) g₀ hσ _
    (symmS_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ hT)

theorem symmHs_deTurckRemainderOnSmoothCore (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    symmHs (I := I) (M := M) g₀ hσ
        (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal x) =
      deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal x :=
  symmHs_smoothN (I := I) (M := M) g₀ g_bg 1 hσ
    (symmS (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))
    (symmS_idem (I := I) (M := M) g₀ (coreRep g₀ x))

theorem symmHs_deTurckRemainderOnLowerState (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (u : lowerState (I := I) (M := M) g₀ 1 R) :
    symmHs (I := I) (M := M) g₀ hσ
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal u) =
      deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal u := by
  set C : Set (lowerState (I := I) (M := M) g₀ 1 R) :=
    {w | symmHs (I := I) (M := M) g₀ hσ
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal w) =
      deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal w} with hC_def
  have hclosed : IsClosed C :=
    isClosed_eq ((symmHs (I := I) (M := M) g₀ hσ).continuous.comp hcont) hcont
  have hsub : smoothCore (I := I) (M := M) g₀ R ⊆ C := by
    intro w hw
    have hx := deTurckRemainderOnLowerState_on_smoothCore (I := I) (M := M) g₀ g_bg hR hδ hreal hcore ⟨w, hw⟩
    change symmHs (I := I) (M := M) g₀ hσ
        (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal w) =
      deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal w
    rw [hx]
    exact symmHs_deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal hσ ⟨w, hw⟩
  have hCuniv : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (smoothCore_dense (I := I) (M := M) g₀ hR).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hu : u ∈ C := by rw [hCuniv]; trivial
  exact hu

theorem deTurck_remainder_forcing_symmetric_ae (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ hσ (gforce t) = gforce t := by
  filter_upwards [hforce] with t ht
  rw [ht]
  exact symmHs_deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal hcont hcore hσ (u t)

theorem duhamel_solution_of_deTurck_remainder_symmetric_ae (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (ha : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)) (h2 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (hT : 0 < T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ h2
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t) =
        maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t :=
  duhamel_solution_symmetric_ae (I := I) (M := M) g₀ ha h2 hT gforce
    (deTurck_remainder_forcing_symmetric_ae (I := I) (M := M) g₀ g_bg hR hδ hreal hcont hcore ha u
      gforce hforce)

theorem symmHs_congr (g : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a = b)
    (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b)
    (u : TensorHs (I := I) (M := M) g 0 2 a) :
    symmHs (I := I) (M := M) g hb
        (tensorHsCongr (I := I) (M := M) g 0 2 hab u) =
      tensorHsCongr (I := I) (M := M) g 0 2 hab
        (symmHs (I := I) (M := M) g ha u) := by
  cases hab
  rfl

theorem duhamel_solution_of_deTurck_remainder_symmetric_h3_ae (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (ha : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)) (h2 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (h3 : (0 : ℝ) ≤ (3 : ℝ)) (hex : ((1 : ℕ) : ℝ) + 2 = (3 : ℝ))
    (hT : 0 < T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ h3
          (tensorHsCongr (I := I) (M := M) g₀ 0 2 hex
            (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce t)) =
        tensorHsCongr (I := I) (M := M) g₀ 0 2 hex
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce t) := by
  filter_upwards [duhamel_solution_of_deTurck_remainder_symmetric_ae (I := I) (M := M) g₀ g_bg hR hδ hreal
    hcont hcore ha h2 hT u gforce hforce] with t ht
  rw [symmHs_congr (I := I) (M := M) g₀ hex h2 h3, ht]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
