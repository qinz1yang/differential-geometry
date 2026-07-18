import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type} [Fintype Idx]
variable {u : Set M}




def RealizedMetricFamilyOn.toRealizedMetricFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s)) :
    RealizedMetricFamily (I := I) (M := M) Real where
  metric := G.metric
  connection := G.connection
  metricCompatible := fun t => (hLC t).1

@[simp] theorem RealizedMetricFamilyOn.toRealizedMetricFamily_metric
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (s : Real) :
    (G.toRealizedMetricFamily hLC).metric s = G.metric s := rfl

@[simp] theorem RealizedMetricFamilyOn.toRealizedMetricFamily_connection
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (s : Real) :
    (G.toRealizedMetricFamily hLC).connection s = G.connection s := rfl




def connectionPairingTimeDeriv
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j l : Idx) : Real :=
  deriv
    (fun s : Real =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x)))
    base




private theorem matrixDet_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Mx : Real → Matrix ι ι Real) (x : Real)
    (h : ∀ i j, DifferentiableAt Real (fun s => Mx s i j) x) :
    DifferentiableAt Real (fun s => (Mx s).det) x := by
  have e : (fun s => (Mx s).det)
      = (∑ σ : Equiv.Perm ι, fun s => Equiv.Perm.sign σ • ∏ i, Mx s (σ i) i) := by
    funext s; simp only [Matrix.det_apply, Finset.sum_apply]
  rw [e]
  refine DifferentiableAt.sum (fun σ _ => ?_)
  have hp : DifferentiableAt Real (fun s => ∏ i, Mx s (σ i) i) x := by
    have e2 : (fun s => ∏ i : ι, Mx s (σ i) i) = (∏ i : ι, fun s => Mx s (σ i) i) := by
      funext s; simp only [Finset.prod_apply]
    rw [e2]; exact DifferentiableAt.finset_prod (fun i _ => h (σ i) i)
  exact hp.const_smul _

private theorem matrixAdjugate_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Mx : Real → Matrix ι ι Real) (x : Real)
    (a b : ι) (h : ∀ i j, DifferentiableAt Real (fun s => Mx s i j) x) :
    DifferentiableAt Real (fun s => (Mx s).adjugate a b) x := by
  have e : (fun s => (Mx s).adjugate a b)
      = (fun s => ((Mx s).updateRow b (Pi.single a 1)).det) := by
    funext s; rw [Matrix.adjugate_apply]
  rw [e]; apply matrixDet_differentiableAt; intro i j
  by_cases hib : i = b
  · subst hib; simp only [Matrix.updateRow_self]; exact differentiableAt_const _
  · simp only [Matrix.updateRow_ne hib]; exact h i j

private theorem matrixInvEntry_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Mx : Real → Matrix ι ι Real)
    (x : Real) (a b : ι) (h : ∀ i j, DifferentiableAt Real (fun s => Mx s i j) x)
    (hdet : (Mx x).det ≠ 0) :
    DifferentiableAt Real (fun s => (Mx s)⁻¹ a b) x := by
  have e : (fun s => (Mx s)⁻¹ a b)
      = (fun s => (Ring.inverse (Mx s).det) * (Mx s).adjugate a b) := by
    funext s; rw [Matrix.inv_def]; simp [Matrix.smul_apply, smul_eq_mul]
  rw [e]
  have hinv : DifferentiableAt Real (fun s => Ring.inverse (Mx s).det) x := by
    have e2 : (fun s => Ring.inverse (Mx s).det) = (fun s => ((Mx s).det)⁻¹) := by
      funext s; rw [Ring.inverse_eq_inv]
    rw [e2]; exact (matrixDet_differentiableAt Mx x h).inv hdet
  exact hinv.mul (matrixAdjugate_differentiableAt Mx x a b h)

private theorem metricExtDtOn_posit
    [I.Boundaryless]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D G)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (frameSmooth : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (base : Real)
    (hbase : D.regular ∈ nhds base) :
    metricExtDtOn (I := I) (G.toRealizedMetricFamily hLC) frame base u
      (fun y a b =>
        deriv (fun s => (G.metric s).inner y (frame a y) (frame b y)) base) := by
  have hbaseR : base ∈ D.regular := mem_of_mem_nhds hbase
  refine metricExtDt_of_fixedBaseRegular (I := I) (G.toRealizedMetricFamily hLC) frame base u
    (fun y a b => deriv (fun s => (G.metric s).inner y (frame a y) (frame b y)) base) ?_
  intro a b
  have hbig :
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) (Set.univ : Set Real) D.regular u
        (fun s y => (G.metric s).inner y (frame a y) (frame b y))
        (fun t y => deriv (fun s => (G.metric s).inner y (frame a y) (frame b y)) t) := by
    refine fixedBaseOnRegSmooth hu D.regular_isOpen ?_ ?_ ?_
    · intro t _ht
      exact Filter.univ_mem
    · intro t ht x hx
      have hcomp := hsmooth.frameCompSmooth (Idx := Idx) frame frameSmooth a b
      have hmem : (t, x) ∈ D.regular ×ˢ u := ⟨ht, hx⟩
      have hn : D.regular ×ˢ u ∈ nhds (t, x) :=
        (D.regular_isOpen.prod hu).mem_nhds hmem
      exact (hcomp.contMDiffAt hn).of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
    · intro t ht x hx
      have hcd : ContDiffOn Real ∞
          (fun s => (G.metric s).inner x (frame a x) (frame b x)) D.regular :=
        hsmooth.coeff x (frame a x) (frame b x)
      have hda : DifferentiableAt Real
          (fun s => (G.metric s).inner x (frame a x) (frame b x)) t :=
        (hcd.contDiffAt (D.regular_isOpen.mem_nhds ht)).differentiableAt (by norm_num)
      exact hda.hasDerivAt.hasDerivWithinAt
  intro t ht x hx V
  have htb : t = base := ht
  subst htb
  exact hbig t hbaseR x hx V

theorem lowerPairDeriv_of_metricFamilySmoothOn
    [I.Boundaryless]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D G)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (frameSmooth : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (base : Real)
    (hbase : D.regular ∈ nhds base) :
    lowerPairDerivOn (I := I) (G.toRealizedMetricFamily hLC) frame base u
      (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base) := by
  classical
  set G' := G.toRealizedMetricFamily hLC with hG'
  have hbaseR : base ∈ D.regular := mem_of_mem_nhds hbase
  have hframe1 : IsLocalFrameOn I E 1 frame u :=
    { linearIndependent := fun {x} hx => frameSmooth.linearIndependent hx
      generating := fun {x} hx => frameSmooth.generating hx
      contMDiffOn := fun i => (frameSmooth.contMDiffOn i).of_le (by exact_mod_cast le_top) }
  set metricDot : M → Idx → Idx → Real :=
    fun y a b => deriv (fun s => (G.metric s).inner y (frame a y) (frame b y)) base with hmd
  have hMV : metricVarOn (I := I) G' frame base u metricDot := by
    intro x hx a b
    have hcd : ContDiffOn Real ∞
        (fun t => (G.metric t).inner x (frame a x) (frame b x)) D.regular :=
      hsmooth.coeff x (frame a x) (frame b x)
    have hda : DifferentiableAt Real
        (fun s => (G.metric s).inner x (frame a x) (frame b x)) base :=
      (hcd.contDiffAt hbase).differentiableAt (by norm_num)
    exact hda.hasDerivAt
  have hExt : metricExtDtOn (I := I) G' frame base u metricDot :=
    metricExtDtOn_posit (I := I) G hLC hsmooth frame frameSmooth hu base hbase
  have hMCV : metricCovVarOn (I := I) G' frame base u
      (dotCovAt (I := I) (G'.connection base) frame hframe1 metricDot) :=
    metricCovVar_ext (I := I) G' frame hframe1 base metricDot hMV hExt
  have hQ : ∀ x : M, x ∈ u → ∀ i j l : Idx,
      DifferentiableAt Real (fun s => connDiffLow (I := I) G' frame s base s x i j l) base := by
    intro x hx i j l
    have hA1 : DifferentiableAt Real
        (fun s => metricCovAtBase (I := I) G' frame base s x i j l) base :=
      (hMCV x hx i j l).differentiableAt
    have hA2 : DifferentiableAt Real
        (fun s => metricCovAtBase (I := I) G' frame base s x j i l) base :=
      (hMCV x hx j i l).differentiableAt
    have hA3 : DifferentiableAt Real
        (fun s => metricCovAtBase (I := I) G' frame base s x l i j) base :=
      (hMCV x hx l i j).differentiableAt
    have hsum : DifferentiableAt Real (fun s =>
        metricCovAtBase (I := I) G' frame base s x i j l +
          metricCovAtBase (I := I) G' frame base s x j i l -
            metricCovAtBase (I := I) G' frame base s x l i j) base := (hA1.add hA2).sub hA3
    have heq : (fun s => 2 * connDiffLow (I := I) G' frame s base s x i j l) =ᶠ[nhds base]
        (fun s => metricCovAtBase (I := I) G' frame base s x i j l +
          metricCovAtBase (I := I) G' frame base s x j i l -
            metricCovAtBase (I := I) G' frame base s x l i j) :=
      Filter.Eventually.of_forall
        (fun s => finiteDiffKoszul (I := I) G' hLC frame hframe1 hu hx base s i j l)
    have h2Q : DifferentiableAt Real
        (fun s => 2 * connDiffLow (I := I) G' frame s base s x i j l) base :=
      hsum.congr_of_eventuallyEq heq
    have hrw : (fun s => connDiffLow (I := I) G' frame s base s x i j l)
        = (fun s => (2 * connDiffLow (I := I) G' frame s base s x i j l) / 2) := by
      funext s; ring
    rw [hrw]; exact h2Q.div_const 2
  intro x hx i j l
  set V : Real → TangentSpace I x :=
    fun s => (G'.connection s (frame j) x) (frame i x) with hVdef
  set cf : Idx → Real → Real := fun k s => hframe1.coeff k x (V s) with hcfdef
  set A : Real → Matrix Idx Idx Real :=
    fun s => Matrix.of (fun a b => (G'.metric s).inner x (frame b x) (frame a x)) with hAdef
  have hAentry : ∀ a b : Idx, DifferentiableAt Real (fun s => A s a b) base := by
    intro a b; exact (hMV x hx b a).differentiableAt
  have hdet : (A base).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    set w : TangentSpace I x := ∑ b : Idx, v b • frame b x with hwdef
    have hpair : ∀ a : Idx, (G'.metric base).inner x w (frame a x) = 0 := by
      intro a
      have hmul : (A base *ᵥ v) a = 0 := by rw [hAv]; rfl
      have hexp : (G'.metric base).inner x w (frame a x)
          = ∑ b : Idx, v b * (G'.metric base).inner x (frame b x) (frame a x) := by
        rw [hwdef]
        simp [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hmul' : (A base *ᵥ v) a
          = ∑ b : Idx, v b * (G'.metric base).inner x (frame b x) (frame a x) := by
        simp [Matrix.mulVec, dotProduct, hAdef, mul_comm]
      rw [hexp, ← hmul', hmul]
    have hww : (G'.metric base).inner x w w = 0 := by
      have hexpand : (G'.metric base).inner x w w
          = ∑ a : Idx, v a * (G'.metric base).inner x w (frame a x) := by
        nth_rewrite 2 [show (w : TangentSpace I x) = ∑ a : Idx, v a • frame a x from hwdef]
        simp [map_sum, map_smul, smul_eq_mul]
      rw [hexpand]; simp [hpair]
    have hw0 : w = 0 := by
      by_contra hwne
      exact lt_irrefl (0 : Real) (hww ▸ (G'.metric base).pos x w hwne)
    have hv0 : v = 0 := by
      funext b
      exact (Fintype.linearIndependent_iff.1 (frameSmooth.linearIndependent hx)) v hw0 b
    exact hv hv0
  set gsub : Idx → Real → Real := fun k s => cf k s - cf k base with hgsubdef
  have hrel : ∀ s : Real, ∀ l' : Idx,
      connDiffLow (I := I) G' frame s base s x i j l' = (A s *ᵥ (fun k => gsub k s)) l' := by
    intro s l'
    have hE := connDiffLow_eq_sum_gammaSub (I := I) G' frame hframe1 hx s base s i j l'
    rw [hE]
    simp only [Matrix.mulVec, dotProduct, hAdef, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hchi :
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G'.connection s) frame hframe1 x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G'.connection base) frame hframe1 x i j k)
          = gsub k s := rfl
    rw [hchi]; ring
  have hcontdet : ContinuousAt (fun s => (A s).det) base :=
    (matrixDet_differentiableAt A base hAentry).continuousAt
  have hcfdiff : ∀ k : Idx, DifferentiableAt Real (fun s => cf k s) base := by
    intro k
    have hev : (fun s => gsub k s) =ᶠ[nhds base]
        (fun s => ∑ l' : Idx,
          (A s)⁻¹ k l' * connDiffLow (I := I) G' frame s base s x i j l') := by
      filter_upwards [hcontdet.eventually_ne hdet] with s hs
      have hunit : IsUnit (A s).det := isUnit_iff_ne_zero.2 hs
      have hginv : (fun k' => gsub k' s)
          = (A s)⁻¹ *ᵥ (fun l' => connDiffLow (I := I) G' frame s base s x i j l') := by
        have hQ' : (fun l' => connDiffLow (I := I) G' frame s base s x i j l')
            = A s *ᵥ (fun k' => gsub k' s) := by
          funext l'; exact hrel s l'
        rw [hQ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
      have hcomp : gsub k s
          = ((A s)⁻¹ *ᵥ (fun l' => connDiffLow (I := I) G' frame s base s x i j l')) k := by
        rw [← hginv]
      rw [hcomp]
      simp [Matrix.mulVec, dotProduct]
    have hRHS : DifferentiableAt Real
        (fun s => ∑ l' : Idx,
          (A s)⁻¹ k l' * connDiffLow (I := I) G' frame s base s x i j l') base := by
      have he : (fun s => ∑ l' : Idx,
            (A s)⁻¹ k l' * connDiffLow (I := I) G' frame s base s x i j l')
          = (∑ l' : Idx,
            fun s => (A s)⁻¹ k l' * connDiffLow (I := I) G' frame s base s x i j l') := by
        funext s; simp only [Finset.sum_apply]
      rw [he]
      refine DifferentiableAt.sum (fun l' _ => ?_)
      exact (matrixInvEntry_differentiableAt A base k l' hAentry hdet).mul (hQ x hx i j l')
    have hgsubdiff : DifferentiableAt Real (fun s => gsub k s) base :=
      hRHS.congr_of_eventuallyEq hev
    have hcfeq : (fun s => cf k s) = (fun s => gsub k s + cf k base) := by
      funext s; rw [hgsubdef]; ring
    rw [hcfeq]; exact hgsubdiff.add_const _
  have hfl : (fun s => (G'.metric base).inner x (frame l x) (V s))
      = (fun s => ∑ k : Idx, cf k s * (G'.metric base).inner x (frame l x) (frame k x)) := by
    funext s
    have hVexp : V s = ∑ k : Idx, cf k s • frame k x := by
      have hsr := hframe1.coeff_sum_eq (fun y => (G'.connection s (frame j) y) (frame i y)) hx
      simpa [hcfdef, hVdef] using hsr
    rw [hVexp]
    simp [map_sum, map_smul, smul_eq_mul]
  have hfldiff : DifferentiableAt Real
      (fun s => (G'.metric base).inner x (frame l x) (V s)) base := by
    rw [hfl]
    have he2 : (fun s => ∑ k : Idx, cf k s * (G'.metric base).inner x (frame l x) (frame k x))
        = (∑ k : Idx, fun s => cf k s * (G'.metric base).inner x (frame l x) (frame k x)) := by
      funext s; simp only [Finset.sum_apply]
    rw [he2]
    refine DifferentiableAt.sum (fun k _ => ?_)
    exact (hcfdiff k).mul_const _
  exact hfldiff.hasDerivAt




theorem gammaDerivOn_of_metricFamilySmoothOn [DecidableEq Idx]
    [I.Boundaryless]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D G)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (frameSmooth : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (base : Real)
    (hbase : D.regular ∈ nhds base)
    (hinv :
      InverseMetricComponentsInFrame (I := I)
        ((G.toRealizedMetricFamily hLC).metric base) gInv frame) :
    gammaDerivOn (I := I) (G.toRealizedMetricFamily hLC) frame hframe base u
      (fun x k i j =>
        gammaFromLower gInv
          (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base)
          x i j k) :=
  gammaDerivOfLower (I := I) (G.toRealizedMetricFamily hLC) gInv frame hframe base
    (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base) hinv
    (lowerPairDeriv_of_metricFamilySmoothOn (I := I) G hLC hsmooth frame frameSmooth hu base
      hbase)




theorem metricCovVarOn_of_ricciFlow
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (ricComp : M -> Idx -> Idx -> Real)
    (hflow :
      metricVarOn (I := I) G frame base u
        (fun x a b => (-2 : Real) * ricComp x a b))
    (hExt :
      metricExtDtOn (I := I) G frame base u
        (fun x a b => (-2 : Real) * ricComp x a b)) :
    metricCovVarOn (I := I) G frame base u
      (dotCovAt (I := I) (G.connection base) frame hframe
        (fun x a b => (-2 : Real) * ricComp x a b)) :=
  metricCovVar_ext (I := I) G frame hframe base
    (fun x a b => (-2 : Real) * ricComp x a b) hflow hExt

end DifferentialGeometry.Integral.Connection
