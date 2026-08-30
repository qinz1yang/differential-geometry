import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Tail.LaplacianBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.TraceIntegral

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

variable [CompactSpace M] in
theorem redLength_lap_K
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) ((s / Real.sqrt tau) • P i s) :
          TangentBundle I M)) Ω)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / Real.sqrt tau) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegCurve S T x Z s)
          (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau)) :
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) ≤
      (Module.finrank Real E : Real) / (2 * tau) -
        S.scalar (T - tau) (lExp S T x Z tau) -
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) := by
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hb_sq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hZinj : Z ∈ lInjDomain S T x tau := hZ
  rcases hZ with ⟨sigma, hsigma, hmin⟩
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  have hONb : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegCurve S T x Z b)
          (P i b) (P j b) = if i = j then 1 else 0 := by
    intro i j
    rw [hb_sq]
    change (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = _
    exact hON i j
  have hIintb : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 b := by
    simpa only [b] using hIint
  have htrace := lTraceInt_eq (I := I) S hS T x Z hb hbdom P
    (by simpa only [b] using hP)
    (by simpa only [b] using hDP) hONb hIintb
  have hlap := redLength_lap_le (I := I) S hS T x htau hZinj P
    hΩ hΩseg hW hP hDP hON hIint hRint
  calc
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) ≤
      (Module.finrank Real E : Real) / (2 * tau) +
        (1 / b) *
          ∫ s in (0 : Real)..b,
            ((s / b) ^ 2 * ∑ i : Fin (Module.finrank Real E),
                lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s) -
              (2 * s ^ 2 / b ^ 2) *
                S.scalar (T - s ^ 2) (lRegCurve S T x Z s) := by
        simpa only [b] using hlap
    _ = (Module.finrank Real E : Real) / (2 * tau) -
        S.scalar (T - tau) (lExp S T x Z tau) -
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) := by
      rw [htrace]
      simp only [b, hb_sq, lExp]
      field_simp [hb.ne']
      ring

private noncomputable def tailFieldCast
     {alpha beta : Real → M} (Y : ∀ s, TangentSpace I (alpha s)) :
     ∀ s, TangentSpace I (beta s) := by
  exact fun s ↦ (Y s : E)

variable [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lTail_lap_K
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (ha0 : 0 < a) (hab : a < b)
    (x : M) (Z : TangentSpace I x)
    (hbdom : b ∈ lRegDomain S T x Z)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = lRegCurve S T x Z 0 →
      delta b = lRegCurve S T x Z b →
      lRegAction S T (lRegCurve S T x Z) 0 b ≤
        lRegAction S T delta 0 b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (h0K : 0 ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real))
        I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ K,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] lRegCurve S T x Z)
    (hinj : Function.Injective fun B : E ↦
      mfderiv (modelWithCornersSelf Real E) I
        (fun A : E ↦ alpha (A, b)) A0 B)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (alpha (A0, s)))
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hOmegaSeg : Icc (0 : Real) b ⊆ Omega)
    (hPsm : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s)) (P i s) : TangentBundle I M)) Omega)
    (hDP : ∀ i s, s ∈ Icc a b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A0, r)) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (alpha (A0, s)) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
          (P i b) (P j b) = if i = j then 1 else 0) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let branch : M → Real := fun y ↦
      lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2))
        branch (alpha (A0, b)) ≤
      (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - b ^ 2) (alpha (A0, b)) -
        lKTail S T (fun s ↦ alpha (A0, s)) a b / (b - a) ^ 2 := by
  classical
  dsimp only
  let beta : Real → M := fun s ↦ alpha (A0, s)
  let gamma : Real → M := lRegCurve S T x Z
  let c : Real → Real := fun s ↦ (s - a) / (b - a)
  let Pc : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (gamma s) := fun i ↦
    tailFieldCast (I := I) (beta := gamma) (P i)
  have hb0 : 0 < b := ha0.trans hab
  have hsegK : Icc (0 : Real) b ⊆ K :=
    hKconn.ordConnected.out h0K hbK
  have hregIcc : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg (A0, s) ⟨hA0V, hsegK ⟨ha0.le.trans hs.1, hs.2⟩⟩
  have hcurve (s : Real) (hs : s ∈ Icc a b) :
      beta =ᶠ[nhds s] gamma :=
    hcenter s ⟨ha0.le.trans hs.1, hs.2⟩
  have hPcGerm (i : Fin (Module.finrank Real E)) (s : Real)
      (hs : s ∈ Icc a b) :
      ∀ᶠ r in nhds s, (P i r : E) = (Pc i r : E) := by
    refine Filter.Eventually.of_forall (fun r ↦ ?_)
    rfl
  have hPdiff (i : Fin (Module.finrank Real E)) (s : Real)
      (hs : s ∈ Icc a b) :
      DifferentiableAt Real (chartRepAt (I := I) beta (P i) s) s := by
    apply chartRep_diff_at
    exact (((hPsm i s (hOmegaSeg ⟨ha0.le.trans hs.1,
      hs.2⟩)).contMDiffAt
        (hOmega.mem_nhds (hOmegaSeg ⟨ha0.le.trans hs.1,
          hs.2⟩))).of_le (by decide :
            (2 : WithTop ℕ∞) ≤ (8 : WithTop ℕ∞)))
  have hPcanDiff (i : Fin (Module.finrank Real E)) (s : Real)
      (hs : s ∈ Icc a b) :
      DifferentiableAt Real (chartRepAt (I := I) gamma (Pc i) s) s := by
    exact (DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := I) (P i) (Pc i)
      (hcurve s hs) (hPcGerm i s hs)).differentiableAt_iff.mp (hPdiff i s hs)
  have hDPcan (i : Fin (Module.finrank Real E)) (s : Real)
      (hs : s ∈ Icc a b) :
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma (Pc i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (gamma s) (Pc i s) := by
    have hc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I)
      (S.base.metric (T - s ^ 2)) (P i) (Pc i)
      (hcurve s hs) (hPcGerm i s hs)
    have hbase := (hcurve s hs).self_of_nhds
    have hfield := (hPcGerm i s hs).self_of_nhds
    have hfield' : P i s = Pc i s := hfield
    change (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        gamma (Pc i) s : E) =
      ((-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
        (gamma s) (Pc i s) : E)
    rw [← hc]
    calc
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          beta (P i) s : E) =
        ((-2 * s) • ricciSharp (I := I)
          (S.base.metric (T - s ^ 2)) (beta s) (P i s) : E) :=
        congrArg (fun v : TangentSpace I (beta s) ↦ (v : E)) (hDP i s hs)
      _ = _ := by rw [hbase, hfield']
  have hONcan : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (gamma b)
          (Pc i b) (Pc j b) = if i = j then 1 else 0 := by
    intro i j
    have hsb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
    have hbase := (hcurve b hsb).self_of_nhds
    have hi := (hPcGerm i b hsb).self_of_nhds
    have hj := (hPcGerm j b hsb).self_of_nhds
    have hi' : P i b = Pc i b := hi
    have hj' : P j b = Pc j b := hj
    rw [← hbase, ← hi', ← hj']
    exact hON i j
  have hPtwo (i : Fin (Module.finrank Real E)) :
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 2
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta s) (P i s) : TangentBundle I M)) Omega :=
    (hPsm i).of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (8 : WithTop ℕ∞))
  have hraw (i : Fin (Module.finrank Real E)) :
      IntervalIntegrable (lRegIndexInt S T beta (P i) (P i))
        MeasureTheory.volume a b := by
    have hsegOmega : uIcc a b ⊆ Omega := by
      intro s hs
      have hs' : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab.le] using hs
      exact hOmegaSeg ⟨ha0.le.trans hs'.1, hs'.2⟩
    exact lRegIndex_intOn S hS T a b beta (P i) (P i) hOmega hsegOmega
      (hPtwo i) (hPtwo i) (by
        intro s hs
        exact hregIcc s (by simpa only [uIcc_of_le hab.le] using hs))
  have hrawCan (i : Fin (Module.finrank Real E)) :
      IntervalIntegrable (lRegIndexInt S T gamma (Pc i) (Pc i))
        MeasureTheory.volume a b := by
    apply (lIndexInt_int_iff (I := I) S T (P i) (P i) (Pc i) (Pc i)
      a b hab.le
      (fun s hs ↦ hcurve s ⟨hs.1.le, hs.2.le⟩)
      (fun s hs ↦ hPcGerm i s ⟨hs.1.le, hs.2.le⟩)
      (fun s hs ↦ hPcGerm i s ⟨hs.1.le, hs.2.le⟩)).mp
    exact hraw i
  have hIintCan (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦ c s ^ 2 * lRegIndexInt S T gamma (Pc i) (Pc i) s)
      MeasureTheory.volume a b :=
    (hrawCan i).continuousOn_mul
      (((continuous_id.sub continuous_const).div_const (b - a)).pow 2).continuousOn
  have hRintBeta (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦ (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (beta s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume a b := by
    let L := Icc a b
    have hsec : Continuous (L.domRestrict fun u : Real ↦
        (TotalSpace.mk' E (beta u) (P i u) : TangentBundle I M)) := by
      simpa only [L, beta] using
        ((hPsm i).continuousOn.mono (fun s hs ↦
          hOmegaSeg ⟨ha0.le.trans hs.1, hs.2⟩)).domRestrict
    have hbase : Continuous (fun u : L ↦ beta u) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).comp hsec
    have htime : Continuous (fun u : L ↦ T - (u : Real) ^ 2) :=
      continuous_const.sub (continuous_subtype_val.pow 2)
    have heval := hS.ricciCont.eval_continuous
      (P := L) htime (fun u ↦ D.regular_subset (hregIcc u u.2)) hbase
      (v := fun k u ↦ vec2 (P i u) (P i u) k) (by
        intro k
        fin_cases k
        · change Continuous (fun u : L ↦
            (TotalSpace.mk' E (beta u) (P i u) : TangentBundle I M))
          exact hsec
        · change Continuous (fun u : L ↦
            (TotalSpace.mk' E (beta u) (P i u) : TangentBundle I M))
          exact hsec)
    have hric : ContinuousOn
        (fun s : Real ↦ S.ricciAt (T - s ^ 2) (beta s)
          (vec2 (P i s) (P i s))) L := by
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : L.domRestrict (fun s : Real ↦
          S.ricciAt (T - s ^ 2) (beta s) (vec2 (P i s) (P i s))) =
          fun u : L ↦ S.ricciAt (T - (u : Real) ^ 2) (beta u)
            (vec2 (P i u) (P i u)) := by
        funext u
        rfl
      rw [heq]
      simpa only [L, SolutionOn.ricci, SolutionFamily.ricci_apply,
        SolutionOn.ricciAt, SolutionFamily.ricciAt] using heval
    have hc : Continuous
        (fun s : Real ↦ 2 * s * (s - a) / (b - a) ^ 2) :=
      ((continuous_const.mul continuous_id).mul
        (continuous_id.sub continuous_const)).div_const _
    exact (hc.continuousOn.mul hric).intervalIntegrable_of_Icc hab.le
  have hRintCan (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦ (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (gamma s) (vec2 (Pc i s) (Pc i s)))
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_congr (f := fun s : Real ↦
      (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (gamma s) (vec2 (Pc i s) (Pc i s)))
      (g := fun s : Real ↦
      (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (beta s) (vec2 (P i s) (P i s))) (by
        intro s hs
        have hsIoc : s ∈ Ioc a b := by
          simpa only [uIoc_of_le hab.le] using hs
        have hs' : s ∈ Icc a b := ⟨hsIoc.1.le, hsIoc.2⟩
        have hbase := (hcurve s hs').self_of_nhds
        have hfield := (hPcGerm i s hs').self_of_nhds
        have hfield' : P i s = Pc i s := hfield
        change (2 * s * (s - a) / (b - a) ^ 2) *
            S.ricciAt (T - s ^ 2) (gamma s) (vec2 (Pc i s) (Pc i s)) =
          (2 * s * (s - a) / (b - a) ^ 2) *
            S.ricciAt (T - s ^ 2) (beta s) (vec2 (P i s) (P i s))
        rw [← hbase, ← hfield'])]
    exact hRintBeta i
  have htrace := lIndex_trace_pos (I := I) S hS T gamma Pc a b hab
    (by
      intro s hs
      exact lRegDomain_reg S T x Z
        (lRegDomain_seg S T x Z hbdom (ha0.le.trans hs.1) hs.2))
    (by
      intro s hs
      have hs' : s ∈ uIcc (0 : Real) b := by
        simpa only [uIcc_of_le hb0.le] using
          (show s ∈ Icc (0 : Real) b from ⟨ha0.le.trans hs.1, hs.2⟩)
      exact (lRegCurve_isReg (I := I) S hS T x Z hb0 hbdom).2.2 s hs' |>.2.1)
    hPcanDiff hDPcan hONcan
    (by simpa only [c] using hIintCan) hRintCan
  have htraceInt := lTraceInt_pos (I := I) S hS T x Z ha0 hab hbdom Pc
    hPcanDiff hDPcan hONcan (by simpa only [c] using hIintCan)
  have hW (i : Fin (Module.finrank Real E)) :
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta s) (c s • P i s) : TangentBundle I M)) Omega := by
    intro s hs
    apply ContMDiffAt.contMDiffWithinAt
    have hsec := (hPsm i s hs).contMDiffAt (hOmega.mem_nhds hs)
    have hc : ContMDiffAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) 8 c s :=
      ((contMDiff_id.sub contMDiff_const).div_const (b - a)).contMDiffAt
    rw [Bundle.contMDiffAt_totalSpace] at hsec ⊢
    refine ⟨hsec.1, ?_⟩
    let e := trivializationAt E (TangentSpace I) (beta s)
    apply (hc.smul hsec.2).congr_of_eventuallyEq
    have he : ∀ᶠ r in nhds s, beta r ∈ e.baseSet := by
      apply hsec.1.continuousAt
      exact e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (beta s))
    filter_upwards [he] with r hr
    change (e ⟨beta r, c r • P i r⟩).2 = c r • (e ⟨beta r, P i r⟩).2
    exact (e.linear Real hr).map_smul (c r) (P i r)
  have hgeo : IsLRegCurveOn S T gamma (uIcc (0 : Real) b) x Z := by
    simpa only [gamma] using lRegCurve_isReg (I := I) S hS T x Z hb0 hbdom
  have hlap := lTail_lap_le (I := I) S hS T a b ha0 hab hgeo
    (by simpa only [gamma] using hmin) hVopen hA0V hKopen hKconn h0K hbK
    hstart halpha hreg hEuler (by simpa only [beta, gamma] using hcenter)
    hinj P hOmega hOmegaSeg (by simpa only [beta, c] using hW) hON
  have hsum :
      (∑ i : Fin (Module.finrank Real E),
        lRegIndex S T beta (fun s ↦ c s • P i s)
          (fun s ↦ c s • P i s) a b) =
      ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T gamma (fun s ↦ c s • Pc i s)
          (fun s ↦ c s • Pc i s) a b := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    apply lIndex_germ_congr (I := I) S T _ _ _ _ a b
    · intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [uIoo_of_le hab.le] using hs
      exact hcurve s ⟨hs'.1.le, hs'.2.le⟩
    · intro s hs
      have hs' : s ∈ Icc a b := by
        have hs'' : s ∈ Ioo a b := by simpa only [uIoo_of_le hab.le] using hs
        exact ⟨hs''.1.le, hs''.2.le⟩
      filter_upwards [hPcGerm i s hs'] with r hr
      change c r • (P i r : E) = c r • (Pc i r : E)
      rw [hr]
      rfl
    · intro s hs
      have hs' : s ∈ Icc a b := by
        have hs'' : s ∈ Ioo a b := by simpa only [uIoo_of_le hab.le] using hs
        exact ⟨hs''.1.le, hs''.2.le⟩
      filter_upwards [hPcGerm i s hs'] with r hr
      change c r • (P i r : E) = c r • (Pc i r : E)
      rw [hr]
      rfl
  have hbaseB : beta b = gamma b :=
    (hcenter b ⟨hb0.le, le_rfl⟩).self_of_nhds
  have hK : lKTail S T beta a b = lKTail S T gamma a b := by
    unfold lKTail
    apply congrArg (fun q : Real ↦ 2 * q)
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hs
    have heq := hcurve s hs'
    have hvel : lVelocity (I := I) beta s =
        lVelocity (I := I) gamma s := by
      unfold lVelocity
      rw [heq.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
      rfl
    have hpt := heq.self_of_nhds
    unfold lHamSq
    dsimp only
    rw [hpt] at hvel ⊢
    rw [hvel]
  have hbaseB' : alpha (A0, b) = lRegCurve S T x Z b := by
    simpa only [beta, gamma] using hbaseB
  have hK' : lKTail S T beta a b =
      lKTail S T (lRegCurve S T x Z) a b := by
    simpa only [gamma] using hK
  calc
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2))
        (fun y ↦ lRegAction S T
          (fun s ↦ alpha
            ((lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse y, s))
          a b) (alpha (A0, b)) ≤
      2 * ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T beta (fun s ↦ c s • P i s)
          (fun s ↦ c s • P i s) a b := by
      simpa only [beta, c] using hlap
    _ = 2 * ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T gamma (fun s ↦ c s • Pc i s)
          (fun s ↦ c s • Pc i s) a b := by rw [hsum]
    _ = (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - b ^ 2) (alpha (A0, b)) -
        lKTail S T beta a b / (b - a) ^ 2 := by
      rw [htrace, htraceInt]
      rw [← hbaseB']
      rw [← hK']
      simp only [beta]
      field_simp [sub_ne_zero.mpr hab.ne']
      ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
