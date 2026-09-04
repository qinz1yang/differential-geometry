import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LaplacianBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.RicciEndomorphism

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [InnerProductSpace Real E]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem basis_eq_gON
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∃ basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      ∀ i, basis i = e i := by
  classical
  let cd : InnerProductSpace.Core Real (TangentSpace I x) :=
    g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x ↦ cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded Real
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let : InnerProductSpace Real (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, NeZero.pos _⟩⟩
  have hon : Orthonormal Real e := by
    rw [orthonormal_iff_ite]
    intro i j
    change g.inner x (e i) (e j) = _
    exact hON i j
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) := basisOfOrthonormalOfCardEqFinrank hon hcard
  refine ⟨basis, fun i ↦ ?_⟩
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hon hcard) i

omit [InnerProductSpace Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem sum_diag_eq_trace
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (B : Tensor0SSpace 2 I x) :
    ∑ i, B (vec2 (e i) (e i)) = metricTracePair0SAt (I := I) g B := by
  classical
  obtain ⟨basis, hbasis⟩ := basis_eq_gON (I := I) g x e hON
  have hONbasis : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    exact hON i j
  have hinv := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hONbasis
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank Real E))) hinv]
  simp [identityInvMetric, diagonalInvMetric, hbasis]

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
private theorem sum_ricciSharp_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, g.inner x (ricciSharp (I := I) g x (e i))
        (ricciSharp (I := I) g x (e i)) =
      normSq0S (I := I) g x 2 (metricRicci (I := I) (M := M) g x) := by
  classical
  obtain ⟨basis, hbasis⟩ := basis_eq_gON (I := I) g x e hON
  have hONbasis : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    exact hON i j
  have hinv := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hONbasis
  rw [normSq0S_identity_eq_sum_sq (I := I) g x 2 basis hinv]
  rw [sum_fin_two_fun]
  apply Finset.sum_congr rfl
  intro i _
  rw [g_inner_eq_orthonormal_parseval_sum (I := I) g x
    (ricciSharp (I := I) g x (e i)) (ricciSharp (I := I) g x (e i)) e hON]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_ricciSharp (I := I) g x (e i) (e j),
    inner_ricciSharp_right (I := I) g x (e i) (e j)]
  simp only [component0S_apply, hbasis, metricRicci_apply]
  have hslots : (fun a : Fin 2 => e (if a = 0 then i else j)) =
      vec2 (e i) (e j) := by
    funext a
    fin_cases a <;> rfl
  rw [hslots, metricRicciAt_apply_eq_ricciTensor]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem sum_rm04_diag
    (g : SmoothRiemannianMetric I M) (x : M) (A : TangentSpace I x)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, metricRm04 (I := I) (M := M) g x (vec4 (e i) A A (e i)) =
      metricRicci (I := I) (M := M) g x (vec2 A A) := by
  classical
  obtain ⟨Asec, hAsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A
  rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x A A e hON]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨Esec, hEsec⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (e i)
  have hRm :=
    (metricCurvData (I := I) (M := M) g).rm04Realizes Esec Asec Asec Esec x
  have hop := riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (x := x)
    Esec.contMDiff Asec.contMDiff Asec.contMDiff
  rw [hEsec, hAsec] at hRm hop
  change (metricCurvData (I := I) (M := M) g).rm04 x
      (vec4 (e i) A A (e i)) = _
  rw [hRm, hop]
  exact g.symm x _ _

omit [InnerProductSpace Real E] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem sum_hessian_diag
    (g : SmoothRiemannianMetric I M) (x : M) (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, hessianSec (I := I) (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g)
        f hf x (vec2 (e i) (e i)) =
      laplacian (I := I) (LeviCivita (I := I) g) g f x := by
  have hmc : IsMetricCompatibleGen (I := I) (LeviCivita (I := I) g) g := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hreal := scalarLap_smooth (I := I) (M := M)
    (LeviCivita (I := I) g)
    (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g)
    g hmc f hf (x := x)
  exact (sum_diag_eq_trace (I := I) g x e hON
    (hessianSec (I := I) (LeviCivita (I := I) g)
      (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) f hf x)).trans
    (ScalarLaplacianRealizesTraceAt.eq_trace
      (I := I) (LeviCivita (I := I) g) g f _ hreal).symm

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
private theorem totalNabla_ricci_apply
    (g : SmoothRiemannianMetric I M)
    (X V W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
        (metricRicci (I := I) (M := M) g) x (vec3 (X x) (V x) (W x)) =
      nablaRicci (I := I) g X V W x := by
  have htotal := totalNabla0SFun_apply_section (𝕜 := Real) (I := I) 2
    (LeviCivita (I := I) g) X (metricRicci (I := I) (M := M) g) x
    (vec2 (V x) (W x))
  have hslots : Fin.cons (X x) (vec2 (V x) (W x)) =
      vec3 (X x) (V x) (W x) := by
    funext i
    fin_cases i <;> rfl
  rw [← hslots, htotal]
  rw [nabla0S_two_apply (I := I) (LeviCivita (I := I) g) X V W
    (metricRicci (I := I) (M := M) g) x]
  unfold nablaRicci
  have hfun :
      (fun p : M => metricRicci (I := I) (M := M) g p
        (vec2 (V p) (W p))) =
      (fun p : M => ricciTensor (I := I) g p (V p) (W p)) := by
    funext p
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  rw [hfun]
  simp only [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
private theorem sum_nablaRicci_first
    (g : SmoothRiemannianMetric I M) (x : M) (A : TangentSpace I x)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
        (metricRicci (I := I) (M := M) g) x (vec3 A (e i) (e i)) =
      nablaScalar (I := I) g
        (ContMDiffSection.exists_eq_at
          (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose x := by
  classical
  let X := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose
  have hX : X x = A := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose_spec
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
    (metricRicci (I := I) (M := M) g) x
  let Q : Tensor0SSpace 2 I x := tensor0SCurry (I := I) 2 x dRic A
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i ↦ smoothOrthoFrame (I := I) g x i x
  have hBON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 :=
    fun i j ↦ smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have htrace := (sum_diag_eq_trace (I := I) g x e hON Q).trans
    (sum_diag_eq_trace (I := I) g x B hBON Q).symm
  have hQ (v : TangentSpace I x) : Q (vec2 v v) = dRic (vec3 A v v) := by
    change (tensor0SCurry (I := I) 2 x dRic A) (vec2 v v) = _
    rw [tensor0S_curry_apply_cons]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [Finset.sum_congr rfl (fun i _ ↦ hQ (e i)),
    Finset.sum_congr rfl (fun i _ ↦ hQ (B i))] at htrace
  rw [htrace]
  rw [nablaScalar_eq_frame_trace_nablaRicci (I := I) g]
  apply Finset.sum_congr rfl
  intro i _
  let Bi : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨smoothOrthoFrame (I := I) g x i,
      smoothOrthoFrame_smooth (I := I) g x i⟩
  simpa only [hX, Bi, B, ContMDiffSection.coeFn_mk] using
    (totalNabla_ricci_apply (I := I) g X Bi Bi x)

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
private theorem sum_nablaRicci_div
    (g : SmoothRiemannianMetric I M) (x : M) (A : TangentSpace I x)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
        (metricRicci (I := I) (M := M) g) x (vec3 (e i) (e i) A) =
      (1 / 2 : Real) * nablaScalar (I := I) g
        (ContMDiffSection.exists_eq_at
          (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose x := by
  classical
  let X := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose
  have hX : X x = A := (ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose_spec
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
    (metricRicci (I := I) (M := M) g) x
  let dRic' : Tensor0SSpace 3 I x := dRic.domDomCongr (Equiv.swap 0 2)
  let Q : Tensor0SSpace 2 I x := tensor0SCurry (I := I) 2 x dRic' A
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i ↦ smoothOrthoFrame (I := I) g x i x
  have hBON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 :=
    fun i j ↦ smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have htrace := (sum_diag_eq_trace (I := I) g x e hON Q).trans
    (sum_diag_eq_trace (I := I) g x B hBON Q).symm
  have hQ (v : TangentSpace I x) : Q (vec2 v v) = dRic (vec3 v v A) := by
    change (tensor0SCurry (I := I) 2 x dRic' A) (vec2 v v) = _
    rw [tensor0S_curry_apply_cons]
    change dRic.domDomCongr (Equiv.swap 0 2) _ = _
    rw [Tensor0SSpace.domDomCongr_apply]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [Finset.sum_congr rfl (fun i _ ↦ hQ (e i)),
    Finset.sum_congr rfl (fun i _ ↦ hQ (B i))] at htrace
  rw [htrace]
  rw [← contracted_second_bianchi (I := I) g X.contMDiff]
  apply Finset.sum_congr rfl
  intro i _
  let Bi : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨smoothOrthoFrame (I := I) g x i,
      smoothOrthoFrame_smooth (I := I) g x i⟩
  simpa only [hX, Bi, B, ContMDiffSection.coeFn_mk] using
    (totalNabla_ricci_apply (I := I) g Bi Bi X x)

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lRegIndexIntegrand_trace
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ r, TangentSpace I (alpha r))
    (s : Real)
    (hDP : ∀ i,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (alpha s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0) :
    ∑ i : Fin (Module.finrank Real E),
        lRegIndexIntegrand S T alpha (P i) (P i) s =
      2 * s ^ 2 * ricciNorm (I := I) S (T - s ^ 2) (alpha s) -
        (1 / 2 : Real) * S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) +
        s ^ 2 * laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric (T - s ^ 2)))
          (S.base.metric (T - s ^ 2)) (S.scalar (T - s ^ 2)) (alpha s) := by
  classical
  let t := T - s ^ 2
  let g := S.base.metric t
  let x := alpha s
  let A := lVelocity (I := I) alpha s
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I) 2
    (S.base.connection t) (S.ricci t) x
  have hD :
      ∑ i, g.inner x
          (covDerivAlong (I := I) g alpha (P i) s)
          (covDerivAlong (I := I) g alpha (P i) s) =
        4 * s ^ 2 * ricciNorm (I := I) S t x := by
    simp_rw [g, t, x, hDP]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hsharp :
        ∑ i, (S.base.metric (T - s ^ 2)).inner (alpha s)
            (ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P i s))
            (ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P i s)) =
          ricciNorm (I := I) S (T - s ^ 2) (alpha s) := by
      simpa only [g, t, x, ricciNorm, SolutionOn.family, SolutionOn.ricci,
        SolutionFamily.ricci] using
        (sum_ricciSharp_sq (I := I) g x (fun i ↦ P i s) hON)
    rw [hsharp]
    ring
  have hRm :
      ∑ i, S.base.rm04 t x (vec4 (P i s) A A (P i s)) =
        S.ricciAt t x (vec2 A A) := by
    change ∑ i, metricRm04 (I := I) (M := M) g x
        (vec4 (P i s) A A (P i s)) =
      metricRicciAt (I := I) (M := M) g x (vec2 A A)
    simpa only [metricRicci_apply] using
      (sum_rm04_diag (I := I) g x A (fun i ↦ P i s) hON)
  have hHess :
      ∑ i, hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g) (S.scalar t)
          (scalarSmoothOfSol (I := I) S t) x (vec2 (P i s) (P i s)) =
        laplacian (I := I) (LeviCivita (I := I) g) g (S.scalar t) x := by
    change ∑ i, hessianSec (I := I) (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t) x
        (vec2 (P i s) (P i s)) =
      laplacian (I := I) (LeviCivita (I := I) g) g (S.scalar t) x
    exact sum_hessian_diag (I := I) g x (S.scalar t)
      (scalarSmoothOfSol (I := I) S t) (fun i ↦ P i s) hON
  have hFirst :
      ∑ i, dRic (vec3 A (P i s) (P i s)) =
        nablaScalar (I := I) g
          (ContMDiffSection.exists_eq_at
            (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose x := by
    change ∑ i, totalNabla0SFun (𝕜 := Real) (I := I) 2
        (LeviCivita (I := I) g) (metricRicci (I := I) (M := M) g) x
        (vec3 A (P i s) (P i s)) = _
    exact sum_nablaRicci_first (I := I) g x A (fun i ↦ P i s) hON
  have hDiv :
      ∑ i, dRic (vec3 (P i s) (P i s) A) =
        (1 / 2 : Real) * nablaScalar (I := I) g
          (ContMDiffSection.exists_eq_at
            (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose x := by
    change ∑ i, totalNabla0SFun (𝕜 := Real) (I := I) 2
        (LeviCivita (I := I) g) (metricRicci (I := I) (M := M) g) x
        (vec3 (P i s) (P i s) A) = _
    exact sum_nablaRicci_div (I := I) g x A (fun i ↦ P i s) hON
  have hSymm (i : Fin (Module.finrank Real E)) :
      dRic (vec3 (P i s) A (P i s)) = dRic (vec3 (P i s) (P i s) A) := by
    change totalNabla0SFun (𝕜 := Real) (I := I) 2
        (LeviCivita (I := I) g) (metricRicci (I := I) (M := M) g) x
          (vec3 (P i s) A (P i s)) =
      totalNabla0SFun (𝕜 := Real) (I := I) 2
        (LeviCivita (I := I) g) (metricRicci (I := I) (M := M) g) x
          (vec3 (P i s) (P i s) A)
    exact metricNablaSymm (I := I) (M := M) g x (P i s) A (P i s)
  have hMid :
      (∑ i, dRic (vec3 (P i s) A (P i s))) =
        ∑ i, dRic (vec3 (P i s) (P i s) A) := by
    exact Finset.sum_congr rfl (fun i _ ↦ hSymm i)
  have hDeriv :
      (∑ i, dRic (vec3 A (P i s) (P i s))) -
          (∑ i, dRic (vec3 (P i s) A (P i s))) -
          (∑ i, dRic (vec3 (P i s) A (P i s))) = 0 := by
    rw [hMid]
    rw [hFirst, hDiv]
    ring
  change
    ∑ i, ((1 / 2 : Real) *
          (g.inner x (covDerivAlong (I := I) g alpha (P i) s)
              (covDerivAlong (I := I) g alpha (P i) s) -
            S.base.rm04 t x (vec4 (P i s) A A (P i s))) +
        s ^ 2 * hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g) (S.scalar t)
          (scalarSmoothOfSol (I := I) S t) x (vec2 (P i s) (P i s)) +
        s * (dRic (vec3 A (P i s) (P i s)) -
          dRic (vec3 (P i s) A (P i s)) -
          dRic (vec3 (P i s) A (P i s)))) =
      2 * s ^ 2 * ricciNorm (I := I) S t x -
        (1 / 2 : Real) * S.ricciAt t x (vec2 A A) +
        s ^ 2 * laplacian (I := I) (LeviCivita (I := I) g) g (S.scalar t) x
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hD, hRm, hHess, hDeriv]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
