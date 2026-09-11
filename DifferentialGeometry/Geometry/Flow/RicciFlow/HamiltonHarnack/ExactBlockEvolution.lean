import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.PreSquareEvolution
import DifferentialGeometry.Geometry.Operator.Laplacian.TensorInner

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private theorem sum_fin_three_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 3 -> A) -> B) :
    (∑ slots : Fin 3 -> A, F slots) =
      ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 2]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tensor0SBundle.sum_fin_succ_fun 1]
  apply Finset.sum_congr rfl
  intro b _
  rw [Tensor0SBundle.sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem sum_fin_two_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 2 -> A) -> B) :
    (∑ slots : Fin 2 -> A, F slots) = ∑ a, ∑ b, F ![a, b] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 1]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tensor0SBundle.sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem sum_fin_four_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 4 -> A) -> B) :
    (∑ slots : Fin 4 -> A, F slots) =
      ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 3]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_fin_three_fun]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rfl

private theorem hamiltonBlockRawKProduct_eq_inner0S
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : N} (g : SmoothRiemannianMetric I N)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (K LK : Tensor0SSpace 4 I x) (DK : Tensor0SSpace 5 I x)
    (DU : Tensor0SSpace 3 I x) (U : Tensor0SSpace 2 I x) :
    hamiltonBlockRawKProduct
        (fun a b c d => K (vec4 (basis a) (basis b) (basis c) (basis d)))
        (fun a b c d => LK (vec4 (basis a) (basis b) (basis c) (basis d)))
        (fun e a b c d =>
          DK (vec5 (basis e) (basis a) (basis b) (basis c) (basis d)))
        (fun e a b => DU (vec3 (basis e) (basis a) (basis b)))
        (fun a b => U (vec2 (basis a) (basis b))) =
      inner0S (I := I) g x 4 LK (U.product U) -
        4 * ∑ e : Idx, inner0S (I := I) g x 4
          (tensor0SCurry (I := I) (M := N) 4 x DK (basis e))
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product U) -
        2 * ∑ e : Idx, inner0S (I := I) g x 4 K
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product
            (tensor0SCurry (I := I) (M := N) 2 x DU (basis e))) := by
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hvec4 (a b c d : Idx) :
      (fun i => basis (![a, b, c, d] i)) =
        vec4 (basis a) (basis b) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have hcons4 (e a b c d : Idx) :
      Fin.cons (basis e) (fun i => basis (![a, b, c, d] i)) =
        vec5 (basis e) (basis a) (basis b) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have happly4 (A : Tensor0SSpace 4 I x) (a b c d : Idx) :
      A (fun i => basis (![a, b, c, d] i)) =
        A (vec4 (basis a) (basis b) (basis c) (basis d)) :=
    congrArg A (hvec4 a b c d)
  have happlyCons4 (A : Tensor0SSpace 5 I x) (e a b c d : Idx) :
      A (Fin.cons (basis e) (fun i => basis (![a, b, c, d] i))) =
        A (vec5 (basis e) (basis a) (basis b) (basis c) (basis d)) :=
    congrArg A (hcons4 e a b c d)
  have hUU (a b c d : Idx) :
      (U.product U) (vec4 (basis a) (basis b) (basis c) (basis d)) =
        U (vec2 (basis a) (basis b)) * U (vec2 (basis c) (basis d)) := by
    rw [Tensor0SSpace.product_apply]
    congr 1 <;> apply congrArg U <;> funext i <;> fin_cases i <;> rfl
  have hDUU (e a b c d : Idx) :
      ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product U)
          (vec4 (basis a) (basis b) (basis c) (basis d)) =
        DU (vec3 (basis e) (basis a) (basis b)) *
          U (vec2 (basis c) (basis d)) := by
    rw [Tensor0SSpace.product_apply, tensor0S_curry_apply_cons]
    congr 1
    · apply congrArg DU
      funext i
      fin_cases i <;> rfl
    · apply congrArg U
      funext i
      fin_cases i <;> rfl
  have hKDU (e a b c d : Idx) :
      ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product
          (tensor0SCurry (I := I) (M := N) 2 x DU (basis e)))
          (vec4 (basis a) (basis b) (basis c) (basis d)) =
        DU (vec3 (basis e) (basis a) (basis b)) *
          DU (vec3 (basis e) (basis c) (basis d)) := by
    rw [Tensor0SSpace.product_apply, tensor0S_curry_apply_cons,
      tensor0S_curry_apply_cons]
    congr 1 <;> apply congrArg DU <;> funext i <;> fin_cases i <;> rfl
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 4 basis hinv]
  simp_rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 4 basis hinv]
  rw [sum_fin_four_fun]
  simp_rw [sum_fin_four_fun]
  unfold hamiltonBlockRawKProduct
  simp only [component0S_apply, tensor0S_curry_apply_cons]
  simp_rw [happly4, happlyCons4]
  simp_rw [hUU, hDUU, hKDU]
  ring_nf

private theorem hamiltonBlockRawPProduct_eq_inner0S
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : N} (g : SmoothRiemannianMetric I N)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (P LP : Tensor0SSpace 3 I x) (DP : Tensor0SSpace 4 I x)
    (DU : Tensor0SSpace 3 I x) (LW W : Tensor0SSpace 1 I x)
    (U : Tensor0SSpace 2 I x) :
    hamiltonBlockRawPProduct
        (fun a b c => P (vec3 (basis a) (basis b) (basis c)))
        (fun a b c => LP (vec3 (basis a) (basis b) (basis c)))
        (fun e a b c => DP (vec4 (basis e) (basis a) (basis b) (basis c)))
        (fun e a b => DU (vec3 (basis e) (basis a) (basis b)))
        (fun a => LW (fun _ => basis a))
        (fun a b => U (vec2 (basis a) (basis b)))
        (fun a => W (fun _ => basis a)) =
      2 * inner0S (I := I) g x 3 LP (U.product W) +
        2 * inner0S (I := I) g x 3 P (U.product LW) -
        4 * ∑ e : Idx, inner0S (I := I) g x 3
          (tensor0SCurry (I := I) (M := N) 3 x DP (basis e))
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product W) := by
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hvec3 (a b c : Idx) :
      (fun i => basis (![a, b, c] i)) =
        vec3 (basis a) (basis b) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have hcons3 (e a b c : Idx) :
      Fin.cons (basis e) (fun i => basis (![a, b, c] i)) =
        vec4 (basis e) (basis a) (basis b) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have happly3 (A : Tensor0SSpace 3 I x) (a b c : Idx) :
      A (fun i => basis (![a, b, c] i)) =
        A (vec3 (basis a) (basis b) (basis c)) :=
    congrArg A (hvec3 a b c)
  have happlyCons3 (A : Tensor0SSpace 4 I x) (e a b c : Idx) :
      A (Fin.cons (basis e) (fun i => basis (![a, b, c] i))) =
        A (vec4 (basis e) (basis a) (basis b) (basis c)) :=
    congrArg A (hcons3 e a b c)
  have hUW (a b c : Idx) :
      (U.product W) (vec3 (basis a) (basis b) (basis c)) =
        U (vec2 (basis a) (basis b)) * W (fun _ => basis c) := by
    rw [Tensor0SSpace.product_apply]
    congr 1
    · apply congrArg U
      funext i
      fin_cases i <;> rfl
    · apply congrArg W
      funext i
      fin_cases i
      rfl
  have hULW (a b c : Idx) :
      (U.product LW) (vec3 (basis a) (basis b) (basis c)) =
        U (vec2 (basis a) (basis b)) * LW (fun _ => basis c) := by
    rw [Tensor0SSpace.product_apply]
    congr 1
    · apply congrArg U
      funext i
      fin_cases i <;> rfl
    · apply congrArg LW
      funext i
      fin_cases i
      rfl
  have hDUW (e a b c : Idx) :
      ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product W)
          (vec3 (basis a) (basis b) (basis c)) =
        DU (vec3 (basis e) (basis a) (basis b)) * W (fun _ => basis c) := by
    rw [Tensor0SSpace.product_apply, tensor0S_curry_apply_cons]
    congr 1
    · apply congrArg DU
      funext i
      fin_cases i <;> rfl
    · apply congrArg W
      funext i
      fin_cases i
      rfl
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 3 basis hinv]
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 3 basis hinv]
  simp_rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 3 basis hinv]
  rw [sum_fin_three_fun, sum_fin_three_fun]
  simp_rw [sum_fin_three_fun]
  unfold hamiltonBlockRawPProduct
  simp only [component0S_apply, tensor0S_curry_apply_cons]
  simp_rw [happly3, happlyCons3]
  simp_rw [hUW, hULW, hDUW]
  ring_nf

private theorem hamiltonBlockRawMProduct_eq_inner0S
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : N} (g : SmoothRiemannianMetric I N)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (M LM : Tensor0SSpace 2 I x) (LW W : Tensor0SSpace 1 I x) :
    hamiltonBlockRawMProduct
        (fun a b => M (vec2 (basis a) (basis b)))
        (fun a b => LM (vec2 (basis a) (basis b)))
        (fun a => LW (fun _ => basis a))
        (fun a => W (fun _ => basis a)) =
      inner0S (I := I) g x 2 LM (W.product W) +
        2 * inner0S (I := I) g x 2 M (LW.product W) := by
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hvec2 (a b : Idx) :
      (fun i => basis (![a, b] i)) = vec2 (basis a) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have happly2 (A : Tensor0SSpace 2 I x) (a b : Idx) :
      A (fun i => basis (![a, b] i)) = A (vec2 (basis a) (basis b)) :=
    congrArg A (hvec2 a b)
  have hWW (a b : Idx) :
      (W.product W) (vec2 (basis a) (basis b)) =
        W (fun _ => basis a) * W (fun _ => basis b) := by
    rw [Tensor0SSpace.product_apply]
    congr 1 <;> apply congrArg W <;> funext i <;> fin_cases i <;> rfl
  have hLWW (a b : Idx) :
      (LW.product W) (vec2 (basis a) (basis b)) =
        LW (fun _ => basis a) * W (fun _ => basis b) := by
    rw [Tensor0SSpace.product_apply]
    congr 1
    · apply congrArg LW
      funext i
      fin_cases i
      rfl
    · apply congrArg W
      funext i
      fin_cases i
      rfl
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 2 basis hinv]
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 2 basis hinv]
  rw [sum_fin_two_fun, sum_fin_two_fun]
  unfold hamiltonBlockRawMProduct
  simp only [component0S_apply]
  simp_rw [happly2]
  simp_rw [hWW, hLWW]
  ring_nf

theorem hamiltonBlockRawProduct_eq_inner0S
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : N} (g : SmoothRiemannianMetric I N)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : forall i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (K LK : Tensor0SSpace 4 I x)
    (P LP : Tensor0SSpace 3 I x)
    (M LM : Tensor0SSpace 2 I x)
    (DK : Tensor0SSpace 5 I x) (DP : Tensor0SSpace 4 I x)
    (DU : Tensor0SSpace 3 I x) (LW W : Tensor0SSpace 1 I x)
    (U : Tensor0SSpace 2 I x) :
    hamiltonBlockRawProduct
        (fun a b c d => K (vec4 (basis a) (basis b) (basis c) (basis d)))
        (fun a b c => P (vec3 (basis a) (basis b) (basis c)))
        (fun a b => M (vec2 (basis a) (basis b)))
        (fun a b c d => LK (vec4 (basis a) (basis b) (basis c) (basis d)))
        (fun a b c => LP (vec3 (basis a) (basis b) (basis c)))
        (fun a b => LM (vec2 (basis a) (basis b)))
        (fun e a b c d =>
          DK (vec5 (basis e) (basis a) (basis b) (basis c) (basis d)))
        (fun e a b c => DP (vec4 (basis e) (basis a) (basis b) (basis c)))
        (fun e a b => DU (vec3 (basis e) (basis a) (basis b)))
        (fun a => LW (fun _ => basis a))
        (fun a b => U (vec2 (basis a) (basis b)))
        (fun a => W (fun _ => basis a)) =
      inner0S (I := I) g x 4 LK (U.product U) +
        2 * inner0S (I := I) g x 3 LP (U.product W) +
        2 * inner0S (I := I) g x 3 P (U.product LW) -
        4 * ∑ e : Idx, inner0S (I := I) g x 3
          (tensor0SCurry (I := I) (M := N) 3 x DP (basis e))
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product W) +
        inner0S (I := I) g x 2 LM (W.product W) +
        2 * inner0S (I := I) g x 2 M (LW.product W) -
        4 * ∑ e : Idx, inner0S (I := I) g x 4
          (tensor0SCurry (I := I) (M := N) 4 x DK (basis e))
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product U) -
        2 * ∑ e : Idx, inner0S (I := I) g x 4 K
          ((tensor0SCurry (I := I) (M := N) 2 x DU (basis e)).product
            (tensor0SCurry (I := I) (M := N) 2 x DU (basis e))) := by
  rw [hamiltonBlockRawProduct_eq_split]
  rw [hamiltonBlockRawKProduct_eq_inner0S g basis horth]
  rw [hamiltonBlockRawPProduct_eq_inner0S g basis horth]
  rw [hamiltonBlockRawMProduct_eq_inner0S g basis horth]
  ring_nf

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem hamiltonBlock_heat_product_eq_pre_square
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaM : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hNablaPSkew : forall e a b c, nablaP e a b c = -nablaP e b a c)
    (hM : forall a b,
      hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) b a)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockHeatProduct
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b))
        (fun a b c d => hamiltonRmReactionComponent R a b d c)
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
          (fun a b => ∑ e, nablaP e e a b))
        (fun e a b c d => nablaR e a b d c) nablaP nablaM
        (hamiltonTestJetDU clock Ric (fun a b => if a = b then 1 else 0) W)
        (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W =
      hamiltonBlockPreSquare
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b)) U W := by
  rw [hamiltonBlock_heat_product_eq_raw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) hM]
  exact hamiltonBlockRawProduct_eq_pre_square clock R Ric nablaR nablaRic nablaP U W
    hRm hNablaRm hRic hNablaRic hTrace hContract hNablaPSkew hU

theorem hamiltonBlock_heat_product_eq_j_add_sigma_square
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaM : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hNablaPSkew : forall e a b c, nablaP e a b c = -nablaP e b a c)
    (hM : forall a b,
      hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) b a)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockHeatProduct
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b))
        (fun a b c d => hamiltonRmReactionComponent R a b d c)
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
          (fun a b => ∑ e, nablaP e e a b))
        (fun e a b c d => nablaR e a b d c) nablaP nablaM
        (hamiltonTestJetDU clock Ric (fun a b => if a = b then 1 else 0) W)
        (fun _ => 0) (fun _ _ => 0)
        (fun a => (1 / clock.elapsed) * W a) U W =
      hamiltonBlockJ
          (fun a b c d => R a b d c)
          (hamiltonPComponent nablaRic)
          (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b)) U W +
        hamiltonBlockSigmaSquare
          (fun a b c d => R a b d c) (hamiltonPComponent nablaRic) U W := by
  rw [hamiltonBlock_heat_product_eq_pre_square clock R Ric nablaR nablaRic nablaP
    nablaM U W hRm hNablaRm hRic hNablaRic hTrace hContract hNablaPSkew hM hU]
  exact hamiltonBlock_pre_square_eq_j_add_sigma_square _ _ _ U W

end DifferentialGeometry.PDE.RicciFlow
