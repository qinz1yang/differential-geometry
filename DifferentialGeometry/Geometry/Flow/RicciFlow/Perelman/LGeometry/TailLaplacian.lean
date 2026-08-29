import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.TailHessian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem tail_basis_of_on
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
  let nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let ips : InnerProductSpace Real (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, NeZero.pos _⟩⟩
  have hinner : ∀ u v : TangentSpace I x,
      (inner Real u v : Real) = g.inner x u v := fun _ _ ↦ rfl
  have hon : Orthonormal Real e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner (e i) (e j)]
    exact hON i j
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hon hcard
  refine ⟨basis, fun i ↦ ?_⟩
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hon hcard) i

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lTail_lap_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (ha0 : 0 < a) (hab : a < b)
    {gamma : Real → M} {x : M} {Z : TangentSpace I x}
    (hgeo : IsLRegCurveOn S T gamma (uIcc (0 : Real) b) x Z)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (h0K : 0 ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ K,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] gamma)
    (hinj : Function.Injective fun B : E ↦
      mfderiv (modelWithCornersSelf Real E) I
        (fun A : E ↦ alpha (A, b)) A0 B)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (alpha (A0, s)))
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hOmegaSeg : Icc (0 : Real) b ⊆ Omega)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real)
      I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s)) (((s - a) / (b - a)) • P i s) :
            TangentBundle I M)) Omega)
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
          (P i b) (P j b) = if i = j then 1 else 0) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let beta : Real → M := fun s ↦ alpha (A0, s)
    let branch : M → Real := fun y ↦
      lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2))
        branch (alpha (A0, b)) ≤
      2 * ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T beta (fun s ↦ ((s - a) / (b - a)) • P i s)
          (fun s ↦ ((s - a) / (b - a)) • P i s) a b := by
  classical
  dsimp only
  let beta : Real → M := fun s ↦ alpha (A0, s)
  let y : M := beta b
  let g : SmoothRiemannianMetric I M := S.base.metric (T - b ^ 2)
  let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let branch : M → Real := fun q ↦
    lRegAction S T (fun s ↦ alpha (hloc.localInverse q, s)) a b
  let W : Fin (Module.finrank Real E) →
      (s : Real) → TangentSpace I (beta s) := fun i s ↦
    ((s - a) / (b - a)) • P i s
  have hb0 : 0 < b := ha0.trans hab
  have hsegK : Icc (0 : Real) b ⊆ K :=
    hKconn.ordConnected.out h0K hbK
  have haK : a ∈ K := hsegK ⟨ha0.le, hab.le⟩
  obtain ⟨basis, hbasis⟩ :=
    tail_basis_of_on (I := I) g y (fun i ↦ P i b) (by
      simpa only [g, y, beta] using hON)
  have hONbasis : ∀ i j,
      g.inner y (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    simpa only [g, y, beta] using hON i j
  obtain ⟨U, hUopen, hyU, F, hFsmooth, hFeq⟩ :=
    lTailBranch_smooth S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hreg hinj
  have hsmooth : ContMDiffOn I (modelWithCornersSelf Real Real) ∞
      branch U := by
    exact hFsmooth.congr (fun q hq ↦ (hFeq q hq).symm)
  have hlap :
      laplacian (I := I) (LeviCivita (I := I) g) g branch y =
        ∑ i : Fin (Module.finrank Real E),
          hessFun (I := I) g branch y (P i b) (P i b) := by
    have hlap0 := lap_eq_hess_on (I := I) g hUopen hsmooth hyU
    have htrace :
        metricTracePair0SAt (I := I) g
            (hessTensorAt (I := I) g branch y) =
          ∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) g branch y (P i b) (P i b) := by
      rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (fun i j ↦ if i = j then (1 : Real) else 0)
        (metricInverseInBasis_of_orthonormal (I := I) g basis hONbasis)
        (hessTensorAt (I := I) g branch y)]
      simp only [hessTensorAt_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hbasis i]
      · intro j _ hji
        rw [if_neg (fun hij ↦ hji hij.symm), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    exact hlap0.trans htrace
  have hfield (i : Fin (Module.finrank Real E)) :
      hessFun (I := I) g branch y (P i b) (P i b) ≤
        2 * lRegIndex S T beta (W i) (W i) a b := by
    have hWa : W i a = 0 := by
      simp only [W, sub_self, zero_div, zero_smul]
    have hWb : W i b = P i b := by
      change ((b - a) / (b - a)) • P i b = P i b
      rw [div_self (sub_ne_zero.mpr hab.ne'), one_smul]
    simpa only [g, branch, y, beta, hloc, W] using
      lTail_hess_le S hS T a b ha0 hab hgeo hmin hVopen hA0V hKopen
        hKconn h0K hbK hstart halpha hreg hEuler hcenter hinj
        (P i b) (W i) hOmega hOmegaSeg (by
          simpa only [W, beta] using hW i) hWa hWb
  rw [show S.base.metric (T - b ^ 2) = g from rfl,
    show alpha (A0, b) = y from rfl, hlap]
  calc
    (∑ i : Fin (Module.finrank Real E),
        hessFun (I := I) g branch y (P i b) (P i b)) ≤
        ∑ i : Fin (Module.finrank Real E),
          2 * lRegIndex S T beta (W i) (W i) a b :=
      Finset.sum_le_sum fun i _ ↦ hfield i
    _ = 2 * ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T beta (W i) (W i) a b := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T beta
          (fun s ↦ ((s - a) / (b - a)) • P i s)
          (fun s ↦ ((s - a) / (b - a)) • P i s) a b := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
