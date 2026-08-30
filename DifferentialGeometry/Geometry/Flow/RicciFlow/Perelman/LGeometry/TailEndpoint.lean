import DifferentialGeometry.Geometry.Comparison.Variation.VariationFieldSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.NegativeDirectionLeft
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.TailFamilySpan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.PiecewiseNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.CurvatureBoundedMinimizer

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lTailLine_smooth
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 B : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K)) :
    ContMDiffOn 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s))
          (lVelocity (I := I)
            (fun u : Real ↦ alpha (A0 + u • B, s)) 0) :
          TangentBundle I M)) K := by
  let f : Real → Real → M := fun u s ↦ alpha (A0 + u • B, s)
  have hf : ∀ s ∈ K, ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I ∞
      (fun p : Real × Real ↦ f p.1 p.2) (0, s) := by
    intro s hs
    have hparam : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real))
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun p : Real × Real ↦ (A0 + p.1 • B, p.2)) (0, s) :=
      ((contMDiff_const.add
        (contMDiff_fst.smul contMDiff_const)).prodMk
          contMDiff_snd).contMDiffAt
    have halphaAt : ContMDiffAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s) :=
      (halpha (A0, s) ⟨hA0V, hs⟩).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hs⟩)
    have hcomp := halphaAt.comp_of_eq hparam (by
      simp only [zero_smul, add_zero])
    rw [show (alpha ∘ fun p : Real × Real ↦ (A0 + p.1 • B, p.2)) =
      (fun p : Real × Real ↦ alpha (A0 + p.1 • B, p.2)) by rfl] at hcomp
    exact hcomp
  have hsmooth := varField_smoothOn (I := I) f hf
  have heq : (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s))
          (lVelocity (I := I)
            (fun u : Real ↦ alpha (A0 + u • B, s)) 0) :
          TangentBundle I M)) =
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f 0 s)
          (mfderiv 𝓘(Real, Real) I (fun u : Real ↦ f u s) 0 (1 : Real)) :
          TangentBundle I M)) := by
    funext s
    dsimp only [f, lVelocity]
    rw [zero_smul, add_zero]
  rw [heq]
  exact hsmooth

end

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem tailEnd_injective
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    {gamma : Real → M} {x : M} {Z : TangentSpace I x}
    {s0 b : Real} (hs00 : 0 < s0) (hs0b : s0 < b)
    (hgeo : IsLRegCurveOn S T gamma (uIcc (0 : Real) b) x Z)
    (hmin : ∀ delta : Real → M,
      ContMDiff 𝓘(Real, Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (h0K : 0 ∈ K) (hs0K : s0 ∈ K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hcurves : ∀ A ∈ V,
      alpha (A, s0) = gamma s0 ∧
        lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
        ∀ r ∈ K,
          T - r ^ 2 ∈ D.regular ∧
            MDifferentiableAt 𝓘(Real, Real) I
              (fun q ↦ alpha (A, q)) r ∧
            DifferentiableAt Real
              (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
            covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                (fun q ↦ alpha (A, q))
                (fun q : Real ↦
                  lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
              lRegAccel S T r (alpha (A, r))
                (lVelocity (I := I) (fun q ↦ alpha (A, q)) r))
    (hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] gamma) :
    Function.Injective
      (mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0) := by
  rw [injective_iff_map_eq_zero]
  intro B hB
  change E at B
  by_contra hBne
  let beta : Real → M := fun s ↦ alpha (A0, s)
  let Y : (s : Real) → TangentSpace I (beta s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ alpha (A0 + u • B, s)) 0
  have hsegK : Icc (0 : Real) b ⊆ K :=
    hKconn.ordConnected.out h0K hbK
  have hlineSmooth : ContMDiffOn 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (beta s) (Y s) : TangentBundle I M)) K := by
    simpa only [beta, Y] using
      lTailLine_smooth (I := I) hVopen hA0V hKopen halpha
  have hlineJac := lTailLine_jacobi (I := I) (B := B) S T (gamma s0)
    hVopen hA0V hKopen halpha
    (fun A hA ↦ (hcurves A hA).1)
    (fun A hA r hr ↦ (hcurves A hA).2.2 r hr |>.2.2.2)
  have hJac : IsLRegJacobi S T beta Y K := by
    simpa only [beta, Y] using hlineJac.1
  have hYs0 : Y s0 = 0 := by
    have h := congrArg
      (fun v : TangentSpace I (alpha (A0 + 0 • B, s0)) ↦ (v : E)) hlineJac.2
    change (lVelocity (I := I) (fun u : Real ↦
      alpha (A0 + u • B, s0)) 0 : E) = 0 at h
    exact h
  have halphaB : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, b) :=
    (halpha (A0, b) ⟨hA0V, hbK⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hbK⟩)
  have hYb : Y b = 0 := by
    have hline := lTailLine_deriv (I := I) A0 B b halphaB
    simpa only [Y, hline] using hB
  have halphaS0 : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, s0) :=
    (halpha (A0, s0) ⟨hA0V, hs0K⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hs0K⟩)
  have hDY : covDerivAlong (I := I) (S.base.metric (T - s0 ^ 2))
      beta Y s0 = B := by
    simpa only [beta, Y] using lTailLine_dstart (I := I)
      (S.base.metric (T - s0 ^ 2)) (gamma s0)
      hVopen hA0V halphaS0
      (fun A hA ↦ (hcurves A hA).1)
      (fun A hA ↦ (hcurves A hA).2.1)
  have hDYne : covDerivAlong (I := I) (S.base.metric (T - s0 ^ 2))
      beta Y s0 ≠ 0 := by
    rw [hDY]
    exact hBne
  obtain ⟨rho, a, d, ha0, hbd, _hrho, hrhoEq, _hrhoDeriv,
      _hrhoRange, hpairSmooth, _hpairEq⟩ :=
    exists_lTail_germ (I := I) hKopen (show 0 < b from hs00.trans hs0b)
      hsegK hlineSmooth
  let gammaG : Real → M := fun s ↦ beta (rho s)
  let Yg : (s : Real) → TangentSpace I (gammaG s) := fun s ↦ Y (rho s)
  have hsegad : Icc (0 : Real) b ⊆ Ioo a d := by
    intro s hs
    exact ⟨ha0.trans_le hs.1, hs.2.trans_lt hbd⟩
  have hrhoGerm : ∀ s ∈ Icc (0 : Real) b, rho =ᶠ[nhds s] id := by
    intro s hs
    have hsad := hsegad hs
    filter_upwards [Ioo_mem_nhds hsad.1 hsad.2] with r hr
    exact hrhoEq ⟨hr.1.le, hr.2.le⟩
  have hGBGerm : ∀ s ∈ Icc (0 : Real) b,
      gammaG =ᶠ[nhds s] beta := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    simp only [gammaG, id_eq, hr]
  have hYgGerm : ∀ s ∈ Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Yg r : E) = (Y r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (Y (rho r) : E) = (Y r : E)
    exact congrArg (fun q : Real ↦ (Y q : E)) (by
      simpa only [id_eq] using hr)
  have hGGerm : ∀ s ∈ Icc (0 : Real) b,
      gammaG =ᶠ[nhds s] gamma := by
    intro s hs
    exact (hGBGerm s hs).trans (hcenter s hs)
  have hGYSmooth : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Yg s) : TangentBundle I M)) := by
    simpa only [gammaG, Yg, beta, Y] using hpairSmooth
  have hGSmooth : ContMDiff 𝓘(Real, Real) I ∞ gammaG := by
    intro s
    exact (Bundle.contMDiffAt_totalSpace.mp hGYSmooth.contMDiffAt).1
  have hb0 : 0 < b := hs00.trans hs0b
  have hgeoG : IsLRegCurveOn S T gammaG (uIcc (0 : Real) b) x Z := by
    have h0Icc : (0 : Real) ∈ Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
    have h0germ := hGGerm 0 h0Icc
    refine ⟨(h0germ.self_of_nhds).trans hgeo.1, ?_, ?_⟩
    · have hvel0 : lVelocity (I := I) gammaG 0 =
          lVelocity (I := I) gamma 0 := by
        unfold lVelocity
        rw [h0germ.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
        rfl
      exact hvel0.trans hgeo.2.1
    · intro s hs
      have hsIcc : s ∈ Icc (0 : Real) b := by
        simpa only [uIcc_of_le hb0.le] using hs
      exact lRegData_congr S T s (hGGerm s hsIcc) (hgeo.2.2 s hs)
  have hminG : ∀ delta : Real → M,
      ContMDiff 𝓘(Real, Real) I 1 delta →
      delta 0 = gammaG 0 → delta b = gammaG b →
      lRegAction S T gammaG 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    have hG0 := (hGGerm 0 ⟨le_rfl, hb0.le⟩).self_of_nhds
    have hGb := (hGGerm b ⟨hb0.le, le_rfl⟩).self_of_nhds
    have hraw := hmin delta hdelta (hd0.trans hG0) (hdb.trans hGb)
    have haction : lRegAction S T gammaG 0 b =
        lRegAction S T gamma 0 b := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) b := by
        simpa only [uIoo_of_le hb0.le] using hs
      exact (hGGerm s ⟨hs'.1.le, hs'.2.le⟩).self_of_nhds
    rw [haction]
    exact hraw
  let P : TangentSpace I (beta s0) :=
    covDerivAlong (I := I) (S.base.metric (T - s0 ^ 2)) beta Y s0
  obtain ⟨W, hWsmooth, hW0, hWb, hWc⟩ :=
    exists_lTest (I := I) gammaG hGSmooth s0 b P
  have hreg0s : ∀ s ∈ uIcc (0 : Real) s0,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs' : s ∈ Icc (0 : Real) s0 := by
      simpa only [uIcc_of_le hs00.le] using hs
    have hsb : s ∈ uIcc (0 : Real) b := by
      rw [uIcc_of_le hb0.le]
      exact ⟨hs'.1, hs'.2.trans hs0b.le⟩
    exact (hgeoG.2.2 s hsb).1
  have hregs0b : ∀ s ∈ uIcc s0 b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs' : s ∈ Icc s0 b := by
      simpa only [uIcc_of_le hs0b.le] using hs
    have hsb : s ∈ uIcc (0 : Real) b := by
      rw [uIcc_of_le hb0.le]
      exact ⟨hs00.le.trans hs'.1, hs'.2⟩
    exact (hgeoG.2.2 s hsb).1
  have hYg2 := hGYSmooth.of_le (by decide :
    (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hW2 := hWsmooth.of_le (by decide :
    (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hYYgInt := lRegIndex_int (I := I) S hS T s0 b gammaG Yg Yg
    hYg2 hYg2 hregs0b
  have hYWgInt := lRegIndex_int (I := I) S hS T s0 b gammaG Yg W
    hYg2 hW2 hregs0b
  have hWW0s := lRegIndex_int (I := I) S hS T 0 s0 gammaG W W
    hW2 hW2 hreg0s
  have hWWs0b := lRegIndex_int (I := I) S hS T s0 b gammaG W W
    hW2 hW2 hregs0b
  have hBetaGerm : ∀ s ∈ Ioo s0 b, beta =ᶠ[nhds s] gammaG := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hGBGerm s ⟨hs00.le.trans hs.1.le, hs.2.le⟩)
  have hYGerm : ∀ s ∈ Ioo s0 b,
      ∀ᶠ r in nhds s, (Y r : E) = (Yg r : E) := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hYgGerm s ⟨hs00.le.trans hs.1.le, hs.2.le⟩)
  have hWGerm : ∀ s ∈ Ioo s0 b,
      ∀ᶠ r in nhds s, (W r : E) = (W r : E) :=
    fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl
  have hYYInt : IntervalIntegrable (lRegIndexInt S T beta Y Y)
      MeasureTheory.volume s0 b :=
    (lIndexInt_int_iff (I := I) S T Y Y Yg Yg s0 b hs0b.le
      hBetaGerm hYGerm hYGerm).2 hYYgInt
  have hYWInt : IntervalIntegrable (lRegIndexInt S T beta Y W)
      MeasureTheory.volume s0 b :=
    (lIndexInt_int_iff (I := I) S T Y W Yg W s0 b hs0b.le
      hBetaGerm hYGerm hWGerm).2 hYWgInt
  have hbetaMdiff : ∀ s ∈ uIcc s0 b, ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I beta r := by
    intro s hs
    have hs' : s ∈ Icc s0 b := by
      simpa only [uIcc_of_le hs0b.le] using hs
    filter_upwards [hKopen.mem_nhds (hsegK
      ⟨hs00.le.trans hs'.1, hs'.2⟩)] with r hr
    exact (hcurves A0 hA0V).2.2 r hr |>.2.1
  have hA : ∀ s ∈ uIcc s0 b, DifferentiableAt Real
      (chartRepAt (I := I) beta
        (fun r ↦ lVelocity (I := I) beta r) s) s := by
    intro s hs
    have hs' : s ∈ Icc s0 b := by
      simpa only [uIcc_of_le hs0b.le] using hs
    simpa only [beta] using
      ((hcurves A0 hA0V).2.2 s (hsegK
        ⟨hs00.le.trans hs'.1, hs'.2⟩)).2.2.1
  have hJacTail : IsLRegJacobi S T beta Y (uIcc s0 b) :=
    fun s hs ↦ hJac s (by
      have hs' : s ∈ Icc s0 b := by
        simpa only [uIcc_of_le hs0b.le] using hs
      exact hsegK ⟨hs00.le.trans hs'.1, hs'.2⟩)
  have hYdiff : ∀ s ∈ uIcc s0 b,
      DifferentiableAt Real (chartRepAt (I := I) beta Y s) s :=
    fun s hs ↦ (hJacTail s hs).2.1
  have hWdiff : ∀ s ∈ uIcc s0 b,
      DifferentiableAt Real (chartRepAt (I := I) beta W s) s := by
    intro s hs
    have hs' : s ∈ Icc s0 b := by
      simpa only [uIcc_of_le hs0b.le] using hs
    have hrep :=
      DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
        (I := I) W W (hGBGerm s
          ⟨hs00.le.trans hs'.1, hs'.2⟩).symm
          (Eventually.of_forall fun _ ↦ rfl)
    exact hrep.differentiableAt_iff.mpr
      (chartRep_diff (I := I) gammaG W hWsmooth s)
  have hYY : lRegIndex S T beta Y Y s0 b = 0 := by
    have hgreen := lRegIndex_jacobi (I := I) S hS T beta Y Y s0 b
      hregs0b hbetaMdiff hA hJacTail hYdiff hYYInt
    rw [hgreen, hYs0, hYb]
    simp
  have hYW : lRegIndex S T beta Y W s0 b < 0 :=
    lIndex_cross_neg (I := I) S hS T beta Y W s0 b hs00 hs0b
      hregs0b hbetaMdiff hA hJacTail hWdiff hYWInt hWb
      (by
        change (W s0 : E) = (s0 * (b - s0)) • (P : E)
        change W s0 = (s0 * (b - s0)) • (P : E) at hWc
        exact hWc)
      (by simpa only [P] using hDYne)
  have hBetaUGerm : ∀ s ∈ uIoo s0 b, beta =ᶠ[nhds s] gammaG := by
    intro s hs
    exact hBetaGerm s (by
      simpa only [uIoo_of_le hs0b.le] using hs)
  have hYUGerm : ∀ s ∈ uIoo s0 b,
      ∀ᶠ r in nhds s, (Y r : E) = (Yg r : E) := by
    intro s hs
    exact hYGerm s (by
      simpa only [uIoo_of_le hs0b.le] using hs)
  have hWUGerm : ∀ s ∈ uIoo s0 b,
      ∀ᶠ r in nhds s, (W r : E) = (W r : E) :=
    fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl
  have hYYeq : lRegIndex S T beta Y Y s0 b =
      lRegIndex S T gammaG Yg Yg s0 b := by
    apply lIndex_germ_congr (I := I) S T Y Y Yg Yg
    · exact hBetaUGerm
    · exact hYUGerm
    · exact hYUGerm
  have hYWeq : lRegIndex S T beta Y W s0 b =
      lRegIndex S T gammaG Yg W s0 b := by
    apply lIndex_germ_congr (I := I) S T Y W Yg W
    · exact hBetaUGerm
    · exact hYUGerm
    · exact hWUGerm
  have hYgdiff : ∀ s ∈ uIcc s0 b,
      DifferentiableAt Real (chartRepAt (I := I) gammaG Yg s) s :=
    fun s _ ↦ chartRep_diff (I := I) gammaG Yg hGYSmooth s
  have hWgdiff : ∀ s ∈ uIcc s0 b,
      DifferentiableAt Real (chartRepAt (I := I) gammaG W s) s :=
    fun s _ ↦ chartRep_diff (I := I) gammaG W hWsmooth s
  obtain ⟨k, hk⟩ := exists_lSplit_left (I := I) S T gammaG Yg W
    0 s0 b hYgdiff hWgdiff hYYgInt hYWgInt hWW0s hWWs0b
    (hYYeq ▸ hYY) (hYWeq ▸ hYW)
  let Y0 : Real → E := fun s ↦ k • W s
  let YgE : Real → E := fun s ↦ Yg s
  let Y1 : Real → E := fun s ↦ YgE s + k • W s
  have hkW : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Y0 s) : TangentBundle I M)) := by
    have h := (contMDiff_const (c := k)).smul_bundle hWsmooth
    change ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Y0 s) : TangentBundle I M)) at h
    exact h
  have hY1smooth : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Y1 s) : TangentBundle I M)) := by
    have h := hGYSmooth.add_bundle hkW
    change ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Y1 s) : TangentBundle I M)) at h
    exact h
  have hYgS0 : Yg s0 = 0 := by
    have hgerm := hYgGerm s0 ⟨hs00.le, hs0b.le⟩
    rw [show Yg s0 = Y s0 from hgerm.self_of_nhds]
    exact hYs0
  have hYgB : Yg b = 0 := by
    have hgerm := hYgGerm b ⟨hb0.le, le_rfl⟩
    rw [show Yg b = Y b from hgerm.self_of_nhds]
    exact hYb
  have hYgES0 : YgE s0 = 0 := hYgS0
  have hYgEB : YgE b = 0 := hYgB
  have hY00 : Y0 0 = 0 := by
    simp only [Y0, hW0, smul_zero]
  have hY1b : Y1 b = 0 := by
    change YgE b + k • W b = 0
    rw [hYgEB, hWb, smul_zero, add_zero]
  have hnode : Y0 s0 = Y1 s0 := by
    change k • W s0 = YgE s0 + k • W s0
    rw [hYgES0, zero_add]
  have hnonneg := lIndex_sum_nonneg (E := E) (I := I) S hS T gammaG
    0 s0 b hs00 hs0b x Z hgeoG hminG Y0 Y1
    (hkW.of_le (by decide :
      (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    (hY1smooth.of_le (by decide :
      (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    hY00 hY1b hnode
  have hk' : lRegIndex S T gammaG Y0 Y0 0 s0 +
      lRegIndex S T gammaG Y1 Y1 s0 b < 0 := by
    change lRegIndex S T gammaG Y0 Y0 0 s0 +
      lRegIndex S T gammaG Y1 Y1 s0 b < 0 at hk
    exact hk
  exact not_lt_of_ge hnonneg hk'

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem exists_lTail_inj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : Real) (x : M)
    {Z : TangentSpace I x} {tau s0 : Real}
    (hmin : (Z, tau) ∈ lMinDomain (E := E) (I := I) S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (hs00 : 0 < s0) (hs0b : s0 < Real.sqrt tau) :
    let gamma : Real → M := lRegCurve S T x Z
    let b : Real := Real.sqrt tau
    let x0 : M := gamma s0
    let A0 : TangentSpace I x0 := lVelocity (I := I) gamma s0
    ∃ V : Set E, IsOpen V ∧ A0 ∈ V ∧
      ∃ K : Set Real, IsOpen K ∧ IsPreconnected K ∧
        0 ∈ K ∧ s0 ∈ K ∧ b ∈ K ∧
        ∃ alpha : E × Real → M,
          ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha
              (V ×ˢ K) ∧
            (∀ A ∈ V,
              alpha (A, s0) = x0 ∧
                lVelocity (I := I) (fun r ↦ alpha (A, r)) s0 = A ∧
                ∀ r ∈ K,
                  T - r ^ 2 ∈ D.regular ∧
                    MDifferentiableAt 𝓘(Real, Real) I
                      (fun q ↦ alpha (A, q)) r ∧
                    DifferentiableAt Real
                      (chartRepAt (I := I) (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r) r ∧
                    covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
                        (fun q ↦ alpha (A, q))
                        (fun q : Real ↦
                          lVelocity (I := I) (fun z ↦ alpha (A, z)) q) r =
                      lRegAccel S T r (alpha (A, r))
                        (lVelocity (I := I) (fun q ↦ alpha (A, q)) r)) ∧
            Function.Injective
              (mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0) := by
  dsimp only
  let gamma : Real → M := lRegCurve S T x Z
  let b : Real := Real.sqrt tau
  let x0 : M := gamma s0
  let A0 : TangentSpace I x0 := lVelocity (I := I) gamma s0
  have htauPos : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb0 : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htauPos
  have hbdom : b ∈ lRegDomain S T x Z := by
    have hpos : (Z, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z tau).1 hmin).1
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hpos).2.2
  let J : Set Real := lRegDomain S T x Z
  have hJopen : IsOpen J := by
    simpa only [J] using lRegDomain_isOpen S T x Z
  have hJconn : IsPreconnected J := by
    simpa only [J] using lRegDomain_preconn S T x Z
  have h0J : 0 ∈ J := by
    simpa only [J] using lRegDomain_seg S T x Z hbdom le_rfl hb0.le
  have hs0J : s0 ∈ J := by
    simpa only [J] using lRegDomain_seg S T x Z hbdom hs00.le hs0b.le
  have hbJ : b ∈ J := by
    simpa only [J] using hbdom
  have hgamma : ∀ r ∈ J,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I gamma r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r =
          lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r) := by
    intro r hr
    have hrdom : r ∈ lRegDomain S T x Z := by
      simpa only [J] using hr
    obtain ⟨K, hKopen, hKconn, h0K, hrK, hchosen⟩ :=
      lRegChosen_spec S T x Z hrdom
    have heqOn : Set.EqOn gamma (lRegChosen S T x Z hrdom) K := by
      simpa only [gamma] using
        lRegCurve_eqOn S hS T hKopen hKconn h0K hchosen
    have heq : gamma =ᶠ[nhds r] lRegChosen S T x Z hrdom :=
      heqOn.eventuallyEq_of_mem (hKopen.mem_nhds hrK)
    exact lRegData_congr S T r heq (hchosen.2.2 r hrK)
  obtain ⟨V, hVopen, hA0V, Ktime, hKopen, hKconn, h0K, hs0K, hbK,
      alpha, halpha, hcurves⟩ :=
    lTailFamily_span S hS T hJopen hJconn h0J hs0J hbJ rfl rfl hgamma
  have hcenterEq : Set.EqOn (fun r ↦ alpha (A0, r)) gamma (Ktime ∩ J) :=
    lRegSol_eqOn S hS T hKopen hKconn hs0K hJopen hJconn hs0J
      (hcurves A0 hA0V).2.2 hgamma
      (by simpa only [x0] using (hcurves A0 hA0V).1)
      (by simpa only [A0] using (hcurves A0 hA0V).2.1)
  have hsegK : Icc (0 : Real) b ⊆ Ktime :=
    hKconn.ordConnected.out h0K hbK
  have hsegJ : Icc (0 : Real) b ⊆ J :=
    hJconn.ordConnected.out h0J hbJ
  have hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] gamma := by
    intro s hs
    exact hcenterEq.eventuallyEq_of_mem
      ((hKopen.inter hJopen).mem_nhds ⟨hsegK hs, hsegJ hs⟩)
  have hgeo : IsLRegCurveOn S T gamma (uIcc (0 : Real) b) x Z := by
    simpa only [gamma] using lRegCurve_isReg (I := I) S hS T x Z hb0 hbdom
  have hminGamma : ∀ delta : Real → M,
      ContMDiff 𝓘(Real, Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    simpa only [gamma, b] using
      lMinVec_min_rm (I := I) S hS K T x hmin hreg hRm
        delta hdelta hd0 hdb
  have hinj := tailEnd_injective (I := I) S hS T hs00 hs0b hgeo hminGamma
    hVopen hA0V hKopen hKconn h0K hs0K hbK halpha hcurves hcenter
  exact ⟨V, hVopen, hA0V, Ktime, hKopen, hKconn, h0K, hs0K, hbK,
    alpha, halpha, hcurves, hinj⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
