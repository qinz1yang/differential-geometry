import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FrameExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.Joint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Analysis.ODE.Flow.BundleLinearODE
import DifferentialGeometry.Bundle.Equiv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem exists_uhlenbeck_endomorphism_after
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hEpos : 0 < Module.finrank Real E)
    {s : Real} (hs : 0 < s) (hsT : s < T) :
    ∃ Phi : Real → ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x,
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M =>
          (⟨p.2, Phi p.1 p.2⟩ : TotalSpace (E →L[Real] E)
            (fun x : M => TangentSpace I x →L[Real] TangentSpace I x)))
        (Ioo 0 (T - s) ×ˢ (univ : Set M)) ∧
      (∀ r ∈ Icc 0 (T - s), ∀ x : M, Function.Bijective (Phi r x)) ∧
      (∀ r ∈ Icc 0 (T - s), ∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric (r + s)).inner x (Phi r x v) (Phi r x w) =
          (S.family.metric s).inner x v w) ∧
      ∀ r ∈ Ico 0 (T - s), ∀ x : M, ∀ v : TangentSpace I x,
        HasDerivWithinAt (fun q : Real => Phi q x v)
          (ricciSharp (I := I) (S.family.metric (r + s)) x (Phi r x v))
          (Ici 0) r := by
  let _ : NeZero (Module.finrank Real E) := ⟨Nat.ne_of_gt hEpos⟩
  let width : Real := T - s
  have hwidth : 0 < width := by
    dsimp [width]
    linarith
  let D0 : RealTimeInterval := RealTimeInterval.closed 0 width hwidth.le
  let Sshift := S.timeShift s
  let S0 := Sshift.timeRestrict D0
  have hSshift : IsSolutionOn (I := I) Sshift := isSolutionOn_timeShift hS s
  have hcarrier : D0.carrier ⊆
      ((RealTimeInterval.closed 0 T hT.le).timeShift s).carrier := by
    intro r hr
    change r + s ∈ Icc 0 T
    change r ∈ Icc 0 width at hr
    dsimp [width] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hregular : D0.regular ⊆
      ((RealTimeInterval.closed 0 T hT.le).timeShift s).regular := by
    intro r hr
    change r + s ∈ Ioo 0 T
    change r ∈ Ioo 0 width at hr
    dsimp [width] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hS0 : IsSolutionOn (I := I) S0 :=
    isSolutionOn_timeRestrict (I := I) hSshift hcarrier hregular
  let basisAt : ∀ x : M,
      Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    fun _ => Module.finBasis Real E
  let iota : MatrixComp M (Fin (Module.finrank Real E)) :=
    solutionUhlenbeckIota hwidth S0 hS0 basisAt
  let Phi0 : Real → ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x :=
    fun r x => uhlenbeckEndomorphismAt (basisAt x) iota r
  let A : Real → ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x :=
    fun r x => ricciSharp (I := I) (S0.family.metric r) x
  have hspec := solutionUhlenbeckIota_spec
    (I := I) (M := M) hwidth S0 hS0 basisAt
  have hiota0 : ∀ x : M, ∀ a k : Fin (Module.finrank Real E),
      iota 0 x a k = if a = k then 1 else 0 := by
    simpa only [iota] using hspec.1
  have hiotaCont : ∀ x : M,
      ContinuousOn (fun r : Real => iota r x) (Icc 0 width) := by
    simpa only [iota] using hspec.2.1
  have hiotaForward : ∀ r : Real, r ∈ Ico 0 width → ∀ x : M,
      ∀ a k : Fin (Module.finrank Real E),
        HasDerivWithinAt (fun q : Real => iota q x a k)
          (∑ l : Fin (Module.finrank Real E),
            uhlenbeckRupOfSolution (I := I) S0
                (solutionInverseMetricComponents S0 basisAt)
                (fun a x => basisAt x a) r x l k * iota r x a l)
          (Ici 0) r := by
    simpa only [iota] using hspec.2.2.1
  have hgram : ∀ r : Real, r ∈ Icc 0 width → ∀ x : M,
      ∀ a b : Fin (Module.finrank Real E),
        movingFrameGramInFrame
            (metricCompInFrame (I := I) S0 (fun a x => basisAt x a))
            iota r x a b =
          movingFrameGramInFrame
            (metricCompInFrame (I := I) S0 (fun a x => basisAt x a))
            iota 0 x a b := by
    simpa only [iota] using hspec.2.2.2.2
  have hAshift := ricciSharp_family_contMDiffOn
    (I := I) (M := M) Sshift hSshift
  have hA : ContMDiffOn (𝓘(Real, Real).prod I)
      (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun p : Real × M =>
        (⟨p.2, A p.1 p.2⟩ : TotalSpace (E →L[Real] E)
          (fun x : M => TangentSpace I x →L[Real] TangentSpace I x)))
      (Ioo (-s) width ×ˢ (univ : Set M)) := by
    have hsub : Ioo (-s) width ×ˢ (univ : Set M) ⊆
        ((RealTimeInterval.closed 0 T hT.le).timeShift s).regular ×ˢ
          (univ : Set M) := by
      intro p hp
      refine ⟨?_, hp.2⟩
      change p.1 + s ∈ Ioo 0 T
      dsimp [width] at hp
      constructor <;> linarith [hp.1.1, hp.1.2]
    simpa [A, S0, Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
      SolutionOn.family, SolutionFamily.timeShift] using hAshift.mono hsub
  have hPhi0 : ∀ x : M,
      Phi0 0 x = ContinuousLinearMap.id Real (TangentSpace I x) := by
    intro x
    exact uhlenbeckEndomorphism_eq_id_of_identity_components
      (basisAt x) iota (hiota0 x)
  have hPhiCont : ∀ x : M, ∀ v : TangentSpace I x,
      ContinuousOn (fun r : Real => Phi0 r x v) (Icc 0 width) := by
    intro x v
    exact uhlenbeckEndomorphism_continuousOn
      (basisAt x) iota (hiotaCont x) v
  have hPhiDeriv : ∀ x : M, ∀ v : TangentSpace I x,
      ∀ r ∈ Ico 0 width,
        HasDerivWithinAt (fun q : Real => Phi0 q x v)
          (A r x (Phi0 r x v)) (Ici 0) r := by
    intro x v r hr
    exact uhlenbeckEndomorphism_hasDerivWithinAt_right
      hwidth S0 (solutionInverseMetricComponents S0 basisAt) basisAt iota
      (fun q y i j => solutionInverseMetricComponents_mul_metric
        (I := I) (M := M) S0 basisAt q y i j)
      (fun q y i j => solutionInverseMetricComponents_symm
        (I := I) (M := M) S0 basisAt q y i j)
      hiotaForward hr x v
  have hzero : (0 : Real) ∈ Ioo (-s) width := by
    exact ⟨by linarith, hwidth⟩
  have hPhiSmooth : ContMDiffOn (𝓘(Real, Real).prod I)
      (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun p : Real × M =>
        (⟨p.2, Phi0 p.1 p.2⟩ : TotalSpace (E →L[Real] E)
          (fun x : M => TangentSpace I x →L[Real] TangentSpace I x)))
      (Ioo 0 width ×ˢ (univ : Set M)) :=
    fiberwise_linear_ode_solution_contMDiffOn_right
      hzero A Phi0 hA hPhi0 hPhiCont hPhiDeriv
  have hPhiBij : ∀ r ∈ Icc 0 width, ∀ x : M,
      Function.Bijective (Phi0 r x) := by
    intro r hr x
    exact uhlenbeckEndomorphism_invertible
      hwidth S0 basisAt iota hiota0 hgram hr x
  refine ⟨Phi0, ?_, ?_, ?_, ?_⟩
  · simpa only [width] using hPhiSmooth
  · simpa only [width] using hPhiBij
  · intro r hr x v w
    have hiso := uhlenbeckEndomorphism_isometry
      (I := I) (M := M) hwidth S0 basisAt iota hiota0
        hgram (by simpa only [width] using hr) x v w
    simpa [S0, Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
      SolutionOn.family, SolutionFamily.timeShift] using hiso
  · intro r hr x v
    simpa [A, S0, Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
      SolutionOn.family, SolutionFamily.timeShift] using
        hPhiDeriv x v r (by simpa only [width] using hr)

omit [SigmaCompactSpace M] in
theorem exists_uhlenbeck_tangent_bundle_isometry_family_of_pos_finrank
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hEpos : 0 < Module.finrank Real E)
    {s : Real} (hs : 0 < s) (hsT : s < T) :
    ∃ Phi : Real → ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x,
      ContMDiffOn (𝓘(Real, Real).prod I) (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : Real × M =>
          (⟨p.2, Phi p.1 p.2⟩ : TotalSpace (E →L[Real] E)
            (fun x : M => TangentSpace I x →L[Real] TangentSpace I x)))
        (Ioo s T ×ˢ (univ : Set M)) ∧
      (∀ r ∈ Icc s T, ∀ x : M, Function.Bijective (Phi r x)) ∧
      (∀ r ∈ Icc s T, ∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric r).inner x (Phi r x v) (Phi r x w) =
          (S.family.metric s).inner x v w) ∧
      ∀ r ∈ Ico s T, ∀ x : M, ∀ v : TangentSpace I x,
        @HasDerivWithinAt Real _ (TangentSpace I x)
          (Tensor0SBundle.tangentSpaceNormedAddCommGroup x).toAddCommGroup
          (Tensor0SBundle.tangentSpaceNormedSpace x).toModule
          (@UniformSpace.toTopologicalSpace (TangentSpace I x)
            (@PseudoMetricSpace.toUniformSpace (TangentSpace I x)
              (@MetricSpace.toPseudoMetricSpace (TangentSpace I x)
                (Tensor0SBundle.tangentSpaceNormedAddCommGroup x).toMetricSpace)))
          _ (fun q : Real => Phi q x v)
          (ricciSharp (I := I) (S.family.metric r) x (Phi r x v))
          (Ici s) r := by
  obtain ⟨Phi0, hPhiSmooth, hPhiBij, hPhiIso, hPhiDeriv⟩ :=
    exists_uhlenbeck_endomorphism_after
      (I := I) (M := M) hT S hS hEpos hs hsT
  let Phi : Real → ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x :=
    fun r x => Phi0 (r - s) x
  refine ⟨Phi, ?_, ?_, ?_, ?_⟩
  · have hshift : ContMDiff (𝓘(Real, Real).prod I)
        (𝓘(Real, Real).prod I) ∞
        (fun p : Real × M => (p.1 - s, p.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    have hmaps : Set.MapsTo (fun p : Real × M => (p.1 - s, p.2))
        (Ioo s T ×ˢ (univ : Set M))
        (Ioo 0 (T - s) ×ˢ (univ : Set M)) := by
      intro p hp
      exact ⟨⟨sub_pos.mpr hp.1.1, sub_lt_sub_right hp.1.2 s⟩, hp.2⟩
    exact (hPhiSmooth.comp hshift.contMDiffOn hmaps).congr fun p hp => rfl
  · intro r hr x
    exact hPhiBij (r - s) ⟨sub_nonneg.mpr hr.1, sub_le_sub_right hr.2 s⟩ x
  · intro r hr x v w
    simpa only [Phi, sub_add_cancel] using
      hPhiIso (r - s) ⟨sub_nonneg.mpr hr.1, sub_le_sub_right hr.2 s⟩ x v w
  · intro r hr x v
    have hq : r - s ∈ Ico 0 (T - s) :=
      ⟨sub_nonneg.mpr hr.1, sub_lt_sub_right hr.2 s⟩
    have hraw := hPhiDeriv (r - s) hq x v
    have hshift : HasDerivWithinAt (fun q : Real => q - s) 1 (Ici s) r :=
      ((hasDerivAt_id r).sub_const s).hasDerivWithinAt
    have hcomp := hraw.scomp r hshift
      (fun q hq => sub_nonneg.mpr hq)
    simpa only [Phi, Function.comp_def, one_smul, sub_add_cancel] using hcomp

omit [SigmaCompactSpace M] in
theorem exists_uhlenbeck_tangent_bundle_isometry
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {s t : Real} (hs : 0 < s) (hst : s < t) (htT : t < T) :
    ∃ phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x,
      ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, phi p.1 p.2⟩ : TangentBundle I M)) ∧
      ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, (phi p.1).symm p.2⟩ : TangentBundle I M)) ∧
      ∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric t).inner x (phi x v) (phi x w) =
          (S.family.metric s).inner x v w := by
  by_cases hdim : Module.finrank Real E = 0
  · let phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x :=
      fun x => LinearEquiv.refl Real (TangentSpace I x)
    have hphiSmooth : ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, phi p.1 p.2⟩ : TangentBundle I M)) := by
      exact (contMDiff_id : ContMDiff (I.prod 𝓘(Real, E))
        (I.prod 𝓘(Real, E)) ∞
        (_root_.id : TangentBundle I M → TangentBundle I M)).congr
          (fun p => by cases p; rfl)
    have hphiInvSmooth : ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, (phi p.1).symm p.2⟩ : TangentBundle I M)) := by
      exact (contMDiff_id : ContMDiff (I.prod 𝓘(Real, E))
        (I.prod 𝓘(Real, E)) ∞
        (_root_.id : TangentBundle I M → TangentBundle I M)).congr
          (fun p => by cases p; rfl)
    refine ⟨phi, hphiSmooth, hphiInvSmooth, ?_⟩
    intro x v w
    have hv : v = 0 :=
      (finrank_zero_iff_forall_zero.mp
        (show Module.finrank Real (TangentSpace I x) = 0 by exact hdim)) v
    have hw : w = 0 :=
      (finrank_zero_iff_forall_zero.mp
        (show Module.finrank Real (TangentSpace I x) = 0 by exact hdim)) w
    simp [hv, hw]
  have hEpos : 0 < Module.finrank Real E := Nat.pos_of_ne_zero hdim
  obtain ⟨PhiFamily, hPhiJoint, hPhiBijFamily, hPhiIsoFamily, _⟩ :=
    exists_uhlenbeck_endomorphism_after
      (I := I) (M := M) hT S hS hEpos hs (lt_trans hst htT)
  let target : Real := t - s
  have htarget : target ∈ Ioo 0 (T - s) := by
    dsimp [target]
    constructor <;> linarith
  let Phi : ∀ x : M, TangentSpace I x →L[Real] TangentSpace I x :=
    fun x => PhiFamily target x
  have hPhiBij : ∀ x : M, Function.Bijective (Phi x) := by
    intro x
    exact hPhiBijFamily target ⟨le_of_lt htarget.1, le_of_lt htarget.2⟩ x
  have hPhiSection : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x : M =>
        (⟨x, Phi x⟩ : TotalSpace (E →L[Real] E)
          (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) := by
    have hpair : ContMDiff I (𝓘(Real, Real).prod I) ∞
        (fun x : M => (target, x)) :=
      contMDiff_const.prodMk contMDiff_id
    have hcomp := hPhiJoint.comp_contMDiff hpair
      (fun x => ⟨htarget, mem_univ x⟩)
    exact hcomp.congr fun x => rfl
  let phi : ∀ x : M, TangentSpace I x ≃ₗ[Real] TangentSpace I x :=
    fun x => LinearEquiv.ofBijective (Phi x).toLinearMap (hPhiBij x)
  have hphiSmooth : ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
      (fun p : TangentBundle I M =>
        (⟨p.1, phi p.1 p.2⟩ : TangentBundle I M)) := by
    change ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
      (fun p : TangentBundle I M =>
        (⟨p.1, Phi p.1 p.2⟩ : TangentBundle I M))
    have hsection : ContMDiff (I.prod 𝓘(Real, E))
        (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun p : TangentBundle I M =>
          (⟨p.1, Phi p.1⟩ : TotalSpace (E →L[Real] E)
            (fun x : M => TangentSpace I x →L[Real] TangentSpace I x))) :=
      hPhiSection.comp (contMDiff_proj (TangentSpace I))
    exact hsection.clm_bundle_apply contMDiff_id
  let total : TangentBundle I M → TangentBundle I M :=
    fun p => ⟨p.1, Phi p.1 p.2⟩
  have htotalBij : Function.Bijective total := by
    constructor
    · rintro ⟨x, v⟩ ⟨y, w⟩ h
      have hxy : x = y := congrArg TotalSpace.proj h
      subst y
      have hvw : Phi x v = Phi x w := TotalSpace.mk_inj.mp h
      exact TotalSpace.mk_inj.mpr ((hPhiBij x).1 hvw)
    · rintro ⟨x, v⟩
      obtain ⟨w, hw⟩ := (hPhiBij x).2 v
      exact ⟨⟨x, w⟩, TotalSpace.mk_inj.mpr hw⟩
  let hom := ContMDiffVectorBundleHom.ofFiberwiseLinearMap
    (𝕜 := Real) (IB := I) (n := (∞ : WithTop ℕ∞)) (F₁ := E) (F₂ := E)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (_root_.id : M → M) (fun x => (Phi x).toLinearMap) hphiSmooth
  have hhomBij : Function.Bijective hom.toFun := by
    change Function.Bijective
      (fun p : TangentBundle I M =>
        (⟨p.1, Phi p.1 p.2⟩ : TangentBundle I M))
    exact htotalBij
  let e := hom.toContMDiffVectorBundleEquivId rfl hhomBij
  have hinv := e.toDiffeomorph.contMDiff_invFun
  have hphiInvSmooth : ContMDiff (I.prod 𝓘(Real, E)) (I.prod 𝓘(Real, E)) ∞
      (fun p : TangentBundle I M =>
        (⟨p.1, (phi p.1).symm p.2⟩ : TangentBundle I M)) := by
    have heq : (fun p : TangentBundle I M =>
        (⟨p.1, (phi p.1).symm p.2⟩ : TangentBundle I M)) =
        e.toDiffeomorph.symm := by
      funext p
      apply e.toDiffeomorph.toEquiv.eq_symm_apply.mpr
      obtain ⟨x, v⟩ := p
      change (⟨x, Phi x ((phi x).symm v)⟩ : TangentBundle I M) = ⟨x, v⟩
      exact TotalSpace.mk_inj.mpr ((phi x).apply_symm_apply v)
    rw [heq]
    exact hinv
  refine ⟨phi, hphiSmooth, hphiInvSmooth, ?_⟩
  intro x v w
  change (S.family.metric t).inner x (Phi x v) (Phi x w) =
    (S.family.metric s).inner x v w
  simpa only [Phi, target, sub_add_cancel] using
    hPhiIsoFamily target ⟨le_of_lt htarget.1, le_of_lt htarget.2⟩ x v w

end DifferentialGeometry.PDE.RicciFlow
