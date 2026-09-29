import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.Action
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem hasMFDerivAt_lRegularizedAction_endpointBranch_at
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegularizedAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B)
    (y : M)
    (hySource : y ∈
      (Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
        hVopen hA0V hbK halpha hinj).localInverse.source)
    (hyV : (Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
      hVopen hA0V hbK halpha hinj).localInverse y ∈ V) :
    HasMFDerivAt I 𝓘(Real, Real)
      (fun q : M ↦ lRegularizedAction S T
        (fun s ↦ alpha
          ((Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
            hVopen hA0V hbK halpha hinj).localInverse q, s))
        a b) y
      ((S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I)
          (fun s : Real ↦ alpha
            ((Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
              hVopen hA0V hbK halpha hinj).localInverse y, s))
          b)) := by
  let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
    hVopen hA0V hbK halpha hinj
  let A : E := hloc.localInverse y
  let endMap : E → M := fun B ↦ alpha (B, b)
  let act : E → Real := fun B ↦
    lRegularizedAction S T (fun s ↦ alpha (B, s)) a b
  let flat : TangentSpace I (alpha (A, b)) →L[Real] Real :=
    (S.base.metric (T - b ^ 2)).inner (alpha (A, b))
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)
  have hright : endMap A = y := hloc.localInverse_right_inv hySource
  have hstartA : ∀ B ∈ V, alpha (B, a) = alpha (A, a) := by
    intro B hBV
    exact (hstart B hBV).trans (hstart A hyV).symm
  have hjoint := hasFDerivAt_lRegularizedAction_family_endpoint
    S hS T a b hab hVopen hyV hKopen
    hKconn haK hbK hstartA halpha hreg (hEuler A hyV)
  have hins : HasFDerivAt (fun B : E ↦ (B, b))
      ((1 : E →L[Real] E).prod (0 : E →L[Real] Real)) A :=
    hasFDerivAt_prodMk_left A b
  have hact : HasFDerivAt act
      (flat.comp (mfderiv 𝓘(Real, E) I endMap A)) A := by
    have h := hjoint.comp A hins
    change HasFDerivAt act _ A at h
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro B
    change flat (mfderiv 𝓘(Real, E) I endMap A B) +
        lRegularizedLagrangian S T (fun s : Real ↦ alpha (A, s)) b * 0 =
      flat (mfderiv 𝓘(Real, E) I endMap A B)
    ring
  have hInv : MDifferentiableAt I 𝓘(Real, E) hloc.localInverse y :=
    (hloc.contMDiffOn_localInverse y hySource).contMDiffAt
      (hloc.localInverse_open_source.mem_nhds hySource) |>.mdifferentiableAt (by simp)
  have hEnd : MDifferentiableAt 𝓘(Real, E) I endMap A := by
    have hpair : ContMDiffAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun B : E ↦ (B, b)) A :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact ((halpha (A, b) ⟨hyV, hbK⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hyV, hbK⟩)).comp A hpair
        |>.mdifferentiableAt (by simp)
  have hcomp := hact.hasMFDerivAt.comp y hInv.hasMFDerivAt
  have hEq : (endMap ∘ hloc.localInverse) =ᶠ[nhds y] id := by
    exact Filter.eventuallyEq_of_mem
      (hloc.localInverse_open_source.mem_nhds hySource)
      (fun q hq ↦ hloc.localInverse_right_inv hq)
  have hchain := mfderiv_comp y hEnd hInv
  have hcancel :
      (mfderiv 𝓘(Real, E) I endMap A).comp
          (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
        (1 : TangentSpace I y →L[Real] TangentSpace I y) := by
    have hd := hEq.mfderiv_eq (I := I) (I' := I)
    have hc := hchain.symm.trans hd
    change (mfderiv 𝓘(Real, E) I endMap A).comp
        (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
      mfderiv I I id y at hc
    rw [mfderiv_id] at hc
    exact hc
  have hderiv :
      (flat.comp (mfderiv 𝓘(Real, E) I endMap A)).comp
          (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
        (S.base.metric (T - b ^ 2)).inner y
          (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b) := by
    apply ContinuousLinearMap.ext
    intro Y
    have hc := congrArg
      (fun L : TangentSpace I y →L[Real] TangentSpace I y ↦ L Y) hcancel
    change flat
        (mfderiv 𝓘(Real, E) I endMap A
          (mfderiv I 𝓘(Real, E) hloc.localInverse y Y)) =
      (S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b) Y
    change (S.base.metric (T - b ^ 2)).inner (alpha (A, b))
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)
        (mfderiv 𝓘(Real, E) I endMap A
          (mfderiv I 𝓘(Real, E) hloc.localInverse y Y)) = _
    change mfderiv 𝓘(Real, E) I endMap A
        (mfderiv I 𝓘(Real, E) hloc.localInverse y Y) = Y at hc
    change alpha (A, b) = y at hright
    rw [hright]
    exact congrArg
      ((S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)) hc
  have hout := hcomp.congr_mfderiv hderiv
  change HasMFDerivAt I 𝓘(Real, Real)
    (act ∘ hloc.localInverse) y
    ((S.base.metric (T - b ^ 2)).inner y
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)) at hout
  change HasMFDerivAt I 𝓘(Real, Real)
    (act ∘ hloc.localInverse) y
    ((S.base.metric (T - b ^ 2)).inner y
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b))
  exact hout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_gradient_lRegularizedAction_endpointBranch
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegularizedAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
      hVopen hA0V hbK halpha hinj
    let branch : M → Real := fun y ↦
      lRegularizedAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    ∃ U : Set M, IsOpen U ∧ alpha (A0, b) ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ branch U ∧
      (∀ y ∈ U, y ∈ hloc.localInverse.source) ∧
      (∀ y ∈ U, hloc.localInverse y ∈ V) ∧
      ∀ y ∈ U, gradientFun (I := I) (S.base.metric (T - b ^ 2))
        branch y = lVelocity (I := I)
          (fun s : Real ↦ alpha (hloc.localInverse y, s)) b := by
  dsimp only
  obtain ⟨W, hWopen, hA0W, hWV, hact⟩ :=
    exists_contDiffOn_lRegularizedAction_family
      S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hreg
  let hloc := Coordinates.isLocalDiffeomorphAt_slice_of_mfderiv_injective
    hVopen hA0V hbK halpha hinj
  let branch : M → Real := fun y ↦
    lRegularizedAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
  let U : Set M := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' W
  have hUopen : IsOpen U :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hWopen
  have hinv : hloc.localInverse (alpha (A0, b)) = A0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : alpha (A0, b) ∈ U := by
    refine ⟨hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (alpha (A0, b)) ∈ W
    rw [hinv]
    exact hA0W
  have hactM : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun A : E ↦ lRegularizedAction S T (fun s ↦ alpha (A, s)) a b) W :=
    contMDiffOn_iff_contDiffOn.mpr hact
  have hbranch : ContMDiffOn I 𝓘(Real, Real) ∞ branch U := by
    have hcomp := hactM.comp
      (hloc.contMDiffOn_localInverse.mono inter_subset_left)
      (fun _ hy ↦ hy.2)
    change ContMDiffOn I 𝓘(Real, Real) ∞
      ((fun A : E ↦ lRegularizedAction S T (fun s ↦ alpha (A, s)) a b) ∘
        hloc.localInverse) U
    exact hcomp
  refine ⟨U, hUopen, hyU, hbranch, (fun _ hy ↦ hy.1),
    (fun _ hy ↦ hWV hy.2), ?_⟩
  intro y hy
  apply gradientFun_eq_of_flat
  have hmfd := hasMFDerivAt_lRegularizedAction_endpointBranch_at
    S hS T a b hab hVopen hA0V hKopen
    hKconn haK hbK hstart halpha hreg hEuler hinj y hy.1 (hWV hy.2)
  ext Y
  have hd := congrArg (fun L : TangentSpace I y →L[Real]
    TangentSpace 𝓘(Real, Real) (branch y) ↦ L Y) hmfd.mfderiv
  change mvfderiv (I := I) branch y Y = _
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  have hd' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)) hd
  let velocity : TangentSpace I y :=
    lVelocity (I := I) (fun s : Real ↦ alpha (hloc.localInverse y, s)) b
  have hcast :
      ((S.base.metric (T - b ^ 2)).inner y velocity) Y =
        (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)).symm
          (metricFlatEquiv (I := I) (S.base.metric (T - b ^ 2)) y velocity Y) := by
    rfl
  calc
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y))
        (((S.base.metric (T - b ^ 2)).inner y velocity) Y) := hd'
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y))
        ((NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)).symm
          (metricFlatEquiv (I := I) (S.base.metric (T - b ^ 2)) y velocity Y)) :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)) hcast
    _ = _ := ContinuousLinearEquiv.apply_symm_apply _ _

end DifferentialGeometry.PDE.RicciFlow.Perelman
