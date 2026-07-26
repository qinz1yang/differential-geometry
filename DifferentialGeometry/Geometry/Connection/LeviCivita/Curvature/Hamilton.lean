import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.DifferentiatedSecondBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureActionLower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff BigOperators

/-!
# Static Hamilton curvature identity

This file derives the fixed-metric covariant-derivative identity underlying the
arbitrary-dimensional Hamilton evolution equation for lowered Riemann
curvature.  The first layer is pure slot algebra; the geometric layer supplies
canonical Levi-Civita Bianchi, symmetry, trace, and Ricci-identity producers.
-/

/-- Six Hessian contractions reduce to the rough trace and five derivative
commutators using only the Riemann symmetries and differentiated second
Bianchi identity. -/
theorem hessian_comm_eq
    {V : Type*} (N : V -> V -> V -> V -> V -> V -> Real)
    (hOut : forall u v a b c d,
      N u v a b c d = -N u v a b d c)
    (hIn : forall u v a b c d,
      N u v b a c d = -N u v a b c d)
    (hPair : forall u v a b c d,
      N u v a b c d = N u v c d a b)
    (hBianchi : forall v a x y z w,
      N v a x y z w + N v x y a z w + N v y a x z w = 0)
    (a b c d i : V) :
    -N a b i c d i - N a c i b d i + N a d i b c i +
          N b a i c d i + N b c i a d i - N b d i a c i =
      N i i a b c d +
        (N a b c i d i - N b a c i d i) +
        (N a i b c d i - N i a b c d i) -
        (N a i b d c i - N i a b d c i) -
        (N b i a c d i - N i b a c d i) +
        (N b i a d c i - N i b a d c i) := by
  linear_combination
    -(hBianchi a b c i d i) +
      (hBianchi a b d i c i) +
      (hBianchi b a c i d i) -
      (hBianchi b a d i c i) +
      (hBianchi i a b c d i) +
      (hBianchi i a b d i c) -
      (hBianchi i c d i a b) -
      (hIn a b c i d i) +
      (hPair a b c i d i) +
      (hIn b a c i d i) -
      (hPair b a c i d i) -
      (hOut i a b d c i) -
      (hIn i b a c d i) +
      (hOut i b a d c i) -
      (hIn i b a d i c) -
      (hPair i c a b d i) -
      (hPair i d a b i c) -
      (hPair i i a b c d)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

private theorem cons_vec4_eq_vec5 {x : M}
    (A B C D F : TangentSpace I x) :
    Fin.cons A (vec4 (I := I) B C D F) = vec5 (I := I) A B C D F := by
  funext q
  fin_cases q <;> rfl

private def rmActionTerm
    {V : Type*} (R : V -> V -> V -> V -> Real)
    (P U W A B C D : V) : Real :=
  -(R P B C D * R U W A P +
    R A P C D * R U W B P +
    R A B P D * R U W C P +
    R A B C P * R U W D P)

private def rmAction4
    {V Idx : Type*} [Fintype Idx]
    (R : V -> V -> V -> V -> Real) (basis : Idx -> V)
    (U W A B C D : V) : Real :=
  -∑ p : Idx, (
    R (basis p) B C D * R U W A (basis p) +
    R A (basis p) C D * R U W B (basis p) +
    R A B (basis p) D * R U W C (basis p) +
    R A B C (basis p) * R U W D (basis p))

/-- The arbitrary-dimensional quadratic reaction in Hamilton's evolution of
the lowered Riemann tensor, written in a finite orthonormal frame. -/
def hamiltonRmReact {Idx : Type*} [Fintype Idx]
    (R : (Fin 4 -> Idx) -> Real) (m : Fin 4 -> Idx) : Real :=
  -2 * (∑ e : Idx, ∑ f : Idx,
      R ![m 0, e, m 1, f] * R ![m 2, e, m 3, f])
    + 2 * (∑ e : Idx, ∑ f : Idx,
      R ![m 0, e, m 1, f] * R ![m 3, e, m 2, f])
    + -2 * (∑ e : Idx, ∑ f : Idx,
      R ![m 0, e, m 2, f] * R ![m 1, e, m 3, f])
    + 2 * (∑ e : Idx, ∑ f : Idx,
      R ![m 0, e, m 3, f] * R ![m 1, e, m 2, f])
    + (∑ e : Idx, ∑ f : Idx,
      R ![m 0, e, f, e] * R ![f, m 1, m 2, m 3])
    + (∑ e : Idx, ∑ f : Idx,
      R ![m 1, e, f, e] * R ![m 0, f, m 2, m 3])
    + (∑ e : Idx, ∑ f : Idx,
      R ![m 2, e, f, e] * R ![m 0, m 1, f, m 3])
    + (∑ e : Idx, ∑ f : Idx,
      R ![m 3, e, f, e] * R ![m 0, m 1, m 2, f])

private theorem action_term_eq
    {V : Type*} (R : V -> V -> V -> V -> Real)
    (hOut : ∀ a b c d, R a b c d = -R a b d c)
    (hIn : ∀ a b c d, R b a c d = -R a b c d)
    (hPair : ∀ a b c d, R a b c d = R c d a b)
    (hFirst : ∀ a b c d,
      R a b c d + R b c a d + R c a b d = 0)
    (a b c d i p : V) :
    rmActionTerm R p a b c i d i +
        rmActionTerm R p a i b c d i -
        rmActionTerm R p a i b d c i -
        rmActionTerm R p b i a c d i +
        rmActionTerm R p b i a d c i =
      -2 * (R a i b p * R c i d p) +
        2 * (R a i b p * R d i c p) -
        2 * (R a i c p * R b i d p) +
        2 * (R a i d p * R b i c p) +
        R a i p i * R p b c d +
        R b i p i * R a p c d +
        R c i p i * R a b p d -
        R d i p i * R a b c p +
        2 * R a p b i * R c i d p -
        2 * R a i b p * R c p d i := by
  have hSplit (x y z w : V) :
      R x y z w = R x z y w - R x w y z := by
    linarith [hFirst x z y w, hPair z y x w,
      hOut x w z y, hIn x y z w]
  have h1 : R a b c p = R a c b p - R a p b c := hSplit a b c p
  have h2 : R a b d p = R a d b p - R a p b d := hSplit a b d p
  have h3 : R a b i p = R a i b p - R a p b i := hSplit a b i p
  have h4 : R a b p d = -R a d b p + R a p b d := by
    linarith [hSplit a b p d]
  have h5 : R a c d p = R a d c p - R a p c d := hSplit a c d p
  have h6 : R a c p i = -R a i c p + R a p c i := by
    linarith [hSplit a c p i]
  have h7 : R a d p i = -R a i d p + R a p d i := by
    linarith [hSplit a d p i]
  have h8 : R b c d p = R b d c p - R b p c d := hSplit b c d p
  have h9 : R b c p i = -R b i c p + R b p c i := by
    linarith [hSplit b c p i]
  have h10 : R b d p i = -R b i d p + R b p d i := by
    linarith [hSplit b d p i]
  have h11 : R a i p i = -R a i i p := hOut a i p i
  have h12 : R b i a p = R a p b i := hPair b i a p
  have h13 : R b i p i = -R b i i p := hOut b i p i
  have h14 : R c i p i = -R c i i p := hOut c i p i
  have h15 : R d i c p = R c p d i := hPair d i c p
  have h16 : R d i p i = -R d i i p := hOut d i p i
  have h17 : R p b c d = -R b p c d := hIn b p c d
  have h18 : R p c d i = -R c p d i := hIn c p d i
  have h19 : R p d c i = -R c i d p := by
    calc
      R p d c i = R c i p d := hPair p d c i
      _ = -R c i d p := hOut c i p d
  have h20 : R p i d i = -R d i i p := by
    calc
      R p i d i = R d i p i := hPair p i d i
      _ = -R d i i p := hOut d i p i
  simp only [rmActionTerm]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  ring

private theorem five_actions_eq
    {V Idx : Type*} [Fintype Idx]
    (R : V -> V -> V -> V -> Real) (basis : Idx -> V)
    (hOut : ∀ a b c d, R a b c d = -R a b d c)
    (hIn : ∀ a b c d, R b a c d = -R a b c d)
    (hPair : ∀ a b c d, R a b c d = R c d a b)
    (hFirst : ∀ a b c d,
      R a b c d + R b c a d + R c a b d = 0)
    (a b c d : V) :
    (∑ i : Idx, (
        rmAction4 R basis a b c (basis i) d (basis i) +
        rmAction4 R basis a (basis i) b c d (basis i) -
        rmAction4 R basis a (basis i) b d c (basis i) -
        rmAction4 R basis b (basis i) a c d (basis i) +
        rmAction4 R basis b (basis i) a d c (basis i))) =
      -2 * (∑ i : Idx, ∑ p : Idx,
        R a (basis i) b (basis p) * R c (basis i) d (basis p)) +
      2 * (∑ i : Idx, ∑ p : Idx,
        R a (basis i) b (basis p) * R d (basis i) c (basis p)) -
      2 * (∑ i : Idx, ∑ p : Idx,
        R a (basis i) c (basis p) * R b (basis i) d (basis p)) +
      2 * (∑ i : Idx, ∑ p : Idx,
        R a (basis i) d (basis p) * R b (basis i) c (basis p)) +
      (∑ i : Idx, ∑ p : Idx,
        R a (basis i) (basis p) (basis i) * R (basis p) b c d) +
      (∑ i : Idx, ∑ p : Idx,
        R b (basis i) (basis p) (basis i) * R a (basis p) c d) +
      (∑ i : Idx, ∑ p : Idx,
        R c (basis i) (basis p) (basis i) * R a b (basis p) d) -
      (∑ i : Idx, ∑ p : Idx,
        R d (basis i) (basis p) (basis i) * R a b c (basis p)) := by
  have hlocal (i p : Idx) := action_term_eq R hOut hIn hPair hFirst
    a b c d (basis i) (basis p)
  have hswap2 :
      (∑ i : Idx, ∑ p : Idx,
        2 * R a (basis p) b (basis i) * R c (basis i) d (basis p)) =
      ∑ i : Idx, ∑ p : Idx,
        2 * R a (basis i) b (basis p) * R c (basis p) d (basis i) := by
    rw [Finset.sum_comm]
  calc
    _ = ∑ i : Idx, ∑ p : Idx, (
        rmActionTerm R (basis p) a b c (basis i) d (basis i) +
        rmActionTerm R (basis p) a (basis i) b c d (basis i) -
        rmActionTerm R (basis p) a (basis i) b d c (basis i) -
        rmActionTerm R (basis p) b (basis i) a c d (basis i) +
        rmActionTerm R (basis p) b (basis i) a d c (basis i)) := by
      simp only [rmAction4, rmActionTerm, Finset.sum_neg_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ i : Idx, ∑ p : Idx, (
        -2 * (R a (basis i) b (basis p) * R c (basis i) d (basis p)) +
        2 * (R a (basis i) b (basis p) * R d (basis i) c (basis p)) -
        2 * (R a (basis i) c (basis p) * R b (basis i) d (basis p)) +
        2 * (R a (basis i) d (basis p) * R b (basis i) c (basis p)) +
        R a (basis i) (basis p) (basis i) * R (basis p) b c d +
        R b (basis i) (basis p) (basis i) * R a (basis p) c d +
        R c (basis i) (basis p) (basis i) * R a b (basis p) d -
        R d (basis i) (basis p) (basis i) * R a b c (basis p) +
        2 * R a (basis p) b (basis i) * R c (basis i) d (basis p) -
        2 * R a (basis i) b (basis p) * R c (basis p) d (basis i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_congr rfl fun p _ => hlocal i p
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [hswap2]
      ring

private theorem curvatureAction_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (U W A B C D : TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13 Rm04 U W
        (vec4 (I := I) A B C D) =
      rmAction4
        (fun P Q R S => Rm04 (vec4 (I := I) P Q R S)) basis
        U W A B C D := by
  classical
  rw [curvatureAction0SAt_eq_rm04 (I := I) g basis
    (identityInvMetric (Idx := Idx)) hinv Rm13 Rm04 hLower]
  have hdelta (slots : Fin 4 -> TangentSpace I x) (q : Fin 4) (p : Idx) :
      (∑ r : Idx, identityInvMetric p r *
        Rm04 (Function.update slots q (basis r))) =
        Rm04 (Function.update slots q (basis p)) := by
    rw [Finset.sum_eq_single p]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro r _ hr
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hr h.symm),
        zero_mul]
    · intro h
      exact absurd (Finset.mem_univ p) h
  simp_rw [hdelta]
  rw [Fin.sum_univ_four]
  have hupdate0 (P : TangentSpace I x) :
      Function.update (vec4 (I := I) A B C D) 0 P =
        vec4 (I := I) P B C D := by
    funext q
    fin_cases q <;> simp [Function.update, vec4]
  have hupdate1 (P : TangentSpace I x) :
      Function.update (vec4 (I := I) A B C D) 1 P =
        vec4 (I := I) A P C D := by
    funext q
    fin_cases q <;> simp [Function.update, vec4]
  have hupdate2 (P : TangentSpace I x) :
      Function.update (vec4 (I := I) A B C D) 2 P =
        vec4 (I := I) A B P D := by
    funext q
    fin_cases q <;> simp [Function.update, vec4]
  have hupdate3 (P : TangentSpace I x) :
      Function.update (vec4 (I := I) A B C D) 3 P =
        vec4 (I := I) A B C P := by
    funext q
    fin_cases q <;> simp [Function.update, vec4]
  simp_rw [hupdate0, hupdate1, hupdate2, hupdate3]
  have hvec0 : vec4 (I := I) A B C D 0 = A := by rfl
  have hvec1 : vec4 (I := I) A B C D 1 = B := by rfl
  have hvec2 : vec4 (I := I) A B C D 2 = C := by rfl
  have hvec3 : vec4 (I := I) A B C D 3 = D := by rfl
  simp_rw [hvec0, hvec1, hvec2, hvec3]
  simp [rmAction4, Finset.sum_add_distrib]

private theorem canRmActionSum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (A B C D : TangentSpace I x) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm13 : Tensor13Section (I := I) (M := M) :=
      CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    (∑ i : Idx, (
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
          (vec4 (I := I) C (basis i) D (basis i)) +
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
          (vec4 (I := I) B C D (basis i)) -
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
          (vec4 (I := I) B D C (basis i)) -
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
          (vec4 (I := I) A C D (basis i)) +
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
          (vec4 (I := I) A D C (basis i)))) =
      -2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) A (basis i) B (basis p)) *
          Rm04 x (vec4 (I := I) C (basis i) D (basis p))) +
      2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) A (basis i) B (basis p)) *
          Rm04 x (vec4 (I := I) D (basis i) C (basis p))) -
      2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) A (basis i) C (basis p)) *
          Rm04 x (vec4 (I := I) B (basis i) D (basis p))) +
      2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) A (basis i) D (basis p)) *
          Rm04 x (vec4 (I := I) B (basis i) C (basis p))) +
      (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) A (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) (basis p) B C D)) +
      (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) B (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) A (basis p) C D)) +
      (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) C (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) A B (basis p) D)) -
      (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) D (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) A B C (basis p))) := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let R := fun P Q S T : TangentSpace I x =>
    Rm04 x (vec4 (I := I) P Q S T)
  have hRm13 : Rm13RealizesConnection (I := I) cov Rm13 := by
    simpa [Rm13] using
      (rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov))
  have hRm04 : Rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04] using
      (rm04Section_realizes (I := I) (M := M) g (cov := cov) (hcov := hcov))
  have hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) :=
    rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x
  have hOut : ∀ P Q S T, R P Q S T = -R P Q T S := by
    simpa [R] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (x := x))
  have hIn : ∀ P Q S T, R Q P S T = -R P Q S T := by
    simpa [R] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (x := x))
  have hPair : ∀ P Q S T, R P Q S T = R S T P Q := by
    simpa [R] using
      (rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (x := x))
  have hFirst : ∀ P Q S T,
      R P Q S T + R Q S P T + R S P Q T = 0 := by
    simpa [R] using
      (firstBianchiAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (x := x))
  have hAlg := five_actions_eq R basis hOut hIn hPair hFirst A B C D
  have hActions : ∀ i : Idx,
      curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
            (vec4 (I := I) C (basis i) D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B C D (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B D C (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A C D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A D C (basis i)) =
        rmAction4 R basis A B C (basis i) D (basis i) +
          rmAction4 R basis A (basis i) B C D (basis i) -
          rmAction4 R basis A (basis i) B D C (basis i) -
          rmAction4 R basis B (basis i) A C D (basis i) +
          rmAction4 R basis B (basis i) A D C (basis i) := by
    intro i
    rw [curvatureAction_basis (I := I) g basis hinv Rm13 (Rm04 x) hLower,
      curvatureAction_basis (I := I) g basis hinv Rm13 (Rm04 x) hLower,
      curvatureAction_basis (I := I) g basis hinv Rm13 (Rm04 x) hLower,
      curvatureAction_basis (I := I) g basis hinv Rm13 (Rm04 x) hLower,
      curvatureAction_basis (I := I) g basis hinv Rm13 (Rm04 x) hLower]
  dsimp only
  rw [Finset.sum_congr rfl fun i _ => hActions i]
  simpa [cov, hcov, Rm13, Rm04, R] using hAlg

private theorem canRic_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (a b : Idx) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    Ric x (vec2 (I := I) (basis a) (basis b)) =
      ∑ i : Idx,
        Rm04 x (vec4 (I := I) (basis i) (basis a) (basis b) (basis i)) := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  have hRm13 : Rm13RealizesConnection (I := I) cov Rm13 := by
    simpa [Rm13] using
      (rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov))
  have hRm04 : Rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04] using
      (rm04Section_realizes (I := I) (M := M) g (cov := cov) (hcov := hcov))
  have hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) :=
    rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x
  have hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13 := by
    intro y
    simp [Ric, Rm13,
      (CovariantDerivative.ricciSection_eq_trace
        (I := I) (M := M) cov hcov y)]
  have hInvSym : ∀ i j : Idx,
      identityInvMetric i j = identityInvMetric j i := by
    intro i j
    simp [identityInvMetric, diagonalInvMetric, eq_comm]
  have hTrace := ricciFirstTraceAt_of_rm13_section
    (I := I) g basis (identityInvMetric (Idx := Idx)) hinv
    Ric Rm13 Rm04 hRic13 hLower hInvSym
  have h := hTrace a b
  simpa [cov, hcov, Rm04, Ric, identityInvMetric, diagonalInvMetric] using h

private theorem canRawLowering
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (a b c d : Idx) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    (-2 * (∑ p : Idx,
        Ric x (vec2 (I := I) (basis d) (basis p)) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))) =
      2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) (basis d) (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p)))) := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  have hRm04 : Rm04RealizesConnection (I := I) g cov Rm04 := by
    simpa [Rm04] using
      (rm04Section_realizes (I := I) (M := M) g (cov := cov) (hcov := hcov))
  have hIn := rm04InputSkewAt_of_leviCivita_realizes
    (I := I) g Rm04 hRm04 (x := x)
  have hRic (p : Idx) :
      Ric x (vec2 (I := I) (basis d) (basis p)) =
        ∑ i : Idx,
          Rm04 x (vec4 (I := I) (basis i) (basis d) (basis p) (basis i)) := by
    simpa [cov, hcov, Rm04, Ric] using
      canRic_basis (I := I) (M := M) g basis hinv d p
  have hTrace (p : Idx) :
      (∑ i : Idx,
        Rm04 x (vec4 (I := I) (basis d) (basis i) (basis p) (basis i))) =
        -Ric x (vec2 (I := I) (basis d) (basis p)) := by
    calc
      _ = ∑ i : Idx,
          -Rm04 x (vec4 (I := I) (basis i) (basis d) (basis p) (basis i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact hIn (basis i) (basis d) (basis p) (basis i)
      _ = -(∑ i : Idx,
          Rm04 x (vec4 (I := I) (basis i) (basis d) (basis p) (basis i))) := by
            rw [Finset.sum_neg_distrib]
      _ = -Ric x (vec2 (I := I) (basis d) (basis p)) := by
            rw [hRic p]
  change
    (-2 * (∑ p : Idx,
        Ric x (vec2 (I := I) (basis d) (basis p)) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))) =
      2 * (∑ i : Idx, ∑ p : Idx,
        Rm04 x (vec4 (I := I) (basis d) (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))))
  calc
    _ = 2 * (∑ p : Idx,
        (-Ric x (vec2 (I := I) (basis d) (basis p))) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))) := by
          simp only [neg_mul, Finset.sum_neg_distrib]
          ring
    _ = 2 * (∑ p : Idx,
        (∑ i : Idx,
          Rm04 x (vec4 (I := I) (basis d) (basis i) (basis p) (basis i))) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))) := by
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hTrace p]
    _ = 2 * (∑ p : Idx, ∑ i : Idx,
        Rm04 x (vec4 (I := I) (basis d) (basis i) (basis p) (basis i)) *
          Rm04 x (vec4 (I := I) (basis a) (basis b) (basis c) (basis p))) := by
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]

/-- Canonical Levi-Civita `nabla^2 Rm04` satisfies the covariant-tensor Ricci
identity, so every derivative commutator is the curvature action on `Rm04`. -/
theorem canRmRicci
    (g : SmoothRiemannianMetric I M) {x : M} :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm13 : Tensor13Section (I := I) (M := M) :=
      CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let nablaRm04 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov hcov Rm04)
    let nabla2Rm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov nablaRm04 x
    Tensor0SRicciIdentityAt (I := I) Rm13 (Rm04 x) nabla2Rm04 := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let nablaRm04 :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        4 cov hcov Rm04)
  let nabla2Rm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 cov nablaRm04 x
  apply tensor0S_ricciIdentity_of_leviCivita
    (I := I) g Rm13 Rm04 nablaRm04 (Rm04 x) (nablaRm04 x) nabla2Rm04
  · simpa [Rm13] using
      (rm13Section_realizes (I := I) (M := M) (cov := cov) (hcov := hcov))
  · rfl
  · rfl
  · constructor
    · intro y X slots
      exact (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 4 cov Rm04 _) X y slots
    · intro X slots
      exact totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov X nablaRm04 x slots

/-- The six second-Ricci-derivative terms in the lowered-Riemann variation
equal one rough-trace summand plus five curvature actions.  This is the static,
pointwise Hamilton commutator identity before summing an orthonormal basis. -/
theorem canRmHessComm
    (g : SmoothRiemannianMetric I M) {x : M}
    (A B C D V : TangentSpace I x) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm13 : Tensor13Section (I := I) (M := M) :=
      CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let nablaRm04 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov hcov Rm04)
    let nabla2Rm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov nablaRm04 x
    let N := fun U W X Y Z Q : TangentSpace I x =>
      nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
    (-N A B V C D V - N A C V B D V + N A D V B C V +
          N B A V C D V + N B C V A D V - N B D V A C V =
      N V V A B C D +
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
          (vec4 (I := I) C V D V) +
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A V
          (vec4 (I := I) B C D V) -
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) A V
          (vec4 (I := I) B D C V) -
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) B V
          (vec4 (I := I) A C D V) +
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) B V
          (vec4 (I := I) A D C V)) := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let nablaRm04 :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        4 cov hcov Rm04)
  let nabla2Rm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 cov nablaRm04 x
  let N := fun U W X Y Z Q : TangentSpace I x =>
    nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
  have hSymm := canRm2Symm (I := I) (M := M) g (x := x)
  have hBianchi := canRmSecond_nabla (I := I) (M := M) g (x := x)
  have hRicci := canRmRicci (I := I) (M := M) g (x := x)
  dsimp [cov, hcov, Rm13, Rm04, nablaRm04, nabla2Rm04] at hSymm hRicci
  have hOut : forall U W X Y Z Q : TangentSpace I x,
      N U W X Y Z Q = -N U W X Y Q Z := by
    intro U W X Y Z Q
    simpa [N] using hSymm.1 U W X Y Z Q
  have hIn : forall U W X Y Z Q : TangentSpace I x,
      N U W Y X Z Q = -N U W X Y Z Q := by
    intro U W X Y Z Q
    simpa [N] using hSymm.2.1 U W X Y Z Q
  have hPair : forall U W X Y Z Q : TangentSpace I x,
      N U W X Y Z Q = N U W Z Q X Y := by
    intro U W X Y Z Q
    simpa [N] using hSymm.2.2 U W X Y Z Q
  have hB : forall U W X Y Z Q : TangentSpace I x,
      N U W X Y Z Q + N U X Y W Z Q + N U Y W X Z Q = 0 := by
    intro U W X Y Z Q
    simpa [cov, hcov, Rm04, nablaRm04, nabla2Rm04, N] using
      hBianchi U W X Y Z Q
  have hAlg := hessian_comm_eq N hOut hIn hPair hB A B C D V
  have comm_eq (U W X Y Z Q : TangentSpace I x) :
      N U W X Y Z Q - N W U X Y Z Q =
        curvatureAction0SAt (I := I) Rm13 (Rm04 x) U W
          (vec4 (I := I) X Y Z Q) := by
    have h := hRicci U W (vec4 (I := I) X Y Z Q)
    rw [metricTraceInput_eq_finCons, cons_vec4_eq_vec5,
      metricTraceInput_eq_finCons, cons_vec4_eq_vec5] at h
    simpa [N] using h
  rw [comm_eq A B C V D V, comm_eq A V B C D V,
    comm_eq A V B D C V, comm_eq B V A C D V,
    comm_eq B V A D C V] at hAlg
  simpa [cov, hcov, Rm13, Rm04, nablaRm04, nabla2Rm04, N] using hAlg

/-- In a basis whose inverse metric is the identity matrix, the six canonical
`nabla^2 Ric` terms in the lowered-Riemann variation are the basis trace of the
rough Hessian and the five curvature-action terms from `canRmHessComm`. -/
theorem canRicHessSum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (A B C D : TangentSpace I x) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm13 : Tensor13Section (I := I) (M := M) :=
      CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let nablaRm04 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov hcov Rm04)
    let nabla2Rm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov nablaRm04 x
    let nablaRic :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov Ric)
    let nabla2Ric :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaRic x
    let N := fun U W X Y Z Q : TangentSpace I x =>
      nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
    (-nabla2Ric (vec4 (I := I) A B C D) -
          nabla2Ric (vec4 (I := I) A C B D) +
          nabla2Ric (vec4 (I := I) A D B C) +
          nabla2Ric (vec4 (I := I) B A C D) +
          nabla2Ric (vec4 (I := I) B C A D) -
          nabla2Ric (vec4 (I := I) B D A C) =
      ∑ i : Idx, (
        N (basis i) (basis i) A B C D +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
            (vec4 (I := I) C (basis i) D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B C D (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B D C (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A C D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A D C (basis i)))) := by
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRm04 :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        4 cov hcov Rm04)
  let nabla2Rm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 cov nablaRm04 x
  let nablaRic :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov Ric)
  let nabla2Ric :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaRic x
  let N := fun U W X Y Z Q : TangentSpace I x =>
    nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
  have trace_eq (U W X Y : TangentSpace I x) :
      nabla2Ric (vec4 (I := I) U W X Y) =
        ∑ i : Idx, N U W (basis i) X Y (basis i) := by
    have h := canNabla2RicTrace (I := I) (M := M) g basis
      (identityInvMetric (Idx := Idx)) hinv U W X Y
    simpa [cov, hcov, Rm04, Ric, nablaRm04, nabla2Rm04, nablaRic,
      nabla2Ric, N, identityInvMetric, diagonalInvMetric] using h
  have hsum :
      (∑ i : Idx, (-N A B (basis i) C D (basis i) -
          N A C (basis i) B D (basis i) + N A D (basis i) B C (basis i) +
          N B A (basis i) C D (basis i) + N B C (basis i) A D (basis i) -
          N B D (basis i) A C (basis i))) =
        ∑ i : Idx, (N (basis i) (basis i) A B C D +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
            (vec4 (I := I) C (basis i) D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B C D (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B D C (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A C D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A D C (basis i))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa [cov, hcov, Rm13, Rm04, nablaRm04, nabla2Rm04, N] using
      canRmHessComm (I := I) (M := M) g A B C D (basis i)
  dsimp only
  rw [trace_eq A B C D, trace_eq A C B D, trace_eq A D B C,
    trace_eq B A C D, trace_eq B C A D, trace_eq B D A C]
  rw [← hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]

/-- Hamilton's fixed-metric identity for the canonical lowered Riemann tensor:
the six second-Ricci derivatives and the metric-lowering variation equal the
rough Hessian trace plus the explicit arbitrary-dimensional quadratic
reaction. -/
theorem hamiltonRm04Id
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Idx)))
    (m : Fin 4 -> Idx) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    let Ric : Tensor02Section (I := I) (M := M) :=
      CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
    let nablaRm04 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov hcov Rm04)
    let nabla2Rm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov nablaRm04 x
    let nablaRic :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov Ric)
    let nabla2Ric :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaRic x
    let N := fun U W X Y Z Q : TangentSpace I x =>
      nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
    let Rcomp := fun q : Fin 4 -> Idx =>
      Rm04 x (vec4 (I := I) (basis (q 0)) (basis (q 1))
        (basis (q 2)) (basis (q 3)))
    (-nabla2Ric (vec4 (I := I) (basis (m 0)) (basis (m 1))
          (basis (m 2)) (basis (m 3))) -
        nabla2Ric (vec4 (I := I) (basis (m 0)) (basis (m 2))
          (basis (m 1)) (basis (m 3))) +
        nabla2Ric (vec4 (I := I) (basis (m 0)) (basis (m 3))
          (basis (m 1)) (basis (m 2))) +
        nabla2Ric (vec4 (I := I) (basis (m 1)) (basis (m 0))
          (basis (m 2)) (basis (m 3))) +
        nabla2Ric (vec4 (I := I) (basis (m 1)) (basis (m 2))
          (basis (m 0)) (basis (m 3))) -
        nabla2Ric (vec4 (I := I) (basis (m 1)) (basis (m 3))
          (basis (m 0)) (basis (m 2))) -
        2 * (∑ p : Idx,
          Ric x (vec2 (I := I) (basis (m 3)) (basis p)) *
            Rm04 x (vec4 (I := I) (basis (m 0)) (basis (m 1))
              (basis (m 2)) (basis p))) =
      (∑ i : Idx,
        N (basis i) (basis i) (basis (m 0)) (basis (m 1))
          (basis (m 2)) (basis (m 3))) +
        hamiltonRmReact Rcomp m) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm13 : Tensor13Section (I := I) (M := M) :=
    CovariantDerivative.rm13Section (I := I) (M := M) cov hcov
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let Ric : Tensor02Section (I := I) (M := M) :=
    CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRm04 :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04 (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        4 cov hcov Rm04)
  let nabla2Rm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 cov nablaRm04 x
  let nablaRic :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov Ric)
  let nabla2Ric :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaRic x
  let N := fun U W X Y Z Q : TangentSpace I x =>
    nabla2Rm04 (Fin.cons U (vec5 (I := I) W X Y Z Q))
  let A := basis (m 0)
  let B := basis (m 1)
  let C := basis (m 2)
  let D := basis (m 3)
  let Rcomp := fun q : Fin 4 -> Idx =>
    Rm04 x (vec4 (I := I) (basis (q 0)) (basis (q 1))
      (basis (q 2)) (basis (q 3)))
  let action := fun i : Idx =>
    curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
        (vec4 (I := I) C (basis i) D (basis i)) +
      curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
        (vec4 (I := I) B C D (basis i)) -
      curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
        (vec4 (I := I) B D C (basis i)) -
      curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
        (vec4 (I := I) A C D (basis i)) +
      curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
        (vec4 (I := I) A D C (basis i))
  have hHess0 := canRicHessSum (I := I) (M := M) g basis hinv A B C D
  have hHess :
      (-nabla2Ric (vec4 (I := I) A B C D) -
          nabla2Ric (vec4 (I := I) A C B D) +
          nabla2Ric (vec4 (I := I) A D B C) +
          nabla2Ric (vec4 (I := I) B A C D) +
          nabla2Ric (vec4 (I := I) B C A D) -
          nabla2Ric (vec4 (I := I) B D A C)) =
        ∑ i : Idx, (N (basis i) (basis i) A B C D + action i) := by
    calc
      _ = ∑ i : Idx, (N (basis i) (basis i) A B C D +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A B
            (vec4 (I := I) C (basis i) D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B C D (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) A (basis i)
            (vec4 (I := I) B D C (basis i)) -
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A C D (basis i)) +
          curvatureAction0SAt (I := I) Rm13 (Rm04 x) B (basis i)
            (vec4 (I := I) A D C (basis i))) := by
            simpa [cov, hcov, Rm13, Rm04, Ric, nablaRm04, nabla2Rm04,
              nablaRic, nabla2Ric, N] using hHess0
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [action]
        ring
  have hAct0 := canRmActionSum (I := I) (M := M) g basis hinv A B C D
  have hAct :
      (∑ i : Idx, action i) =
        -2 * (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) A (basis i) B (basis p)) *
            Rm04 x (vec4 (I := I) C (basis i) D (basis p))) +
        2 * (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) A (basis i) B (basis p)) *
            Rm04 x (vec4 (I := I) D (basis i) C (basis p))) -
        2 * (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) A (basis i) C (basis p)) *
            Rm04 x (vec4 (I := I) B (basis i) D (basis p))) +
        2 * (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) A (basis i) D (basis p)) *
            Rm04 x (vec4 (I := I) B (basis i) C (basis p))) +
        (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) A (basis i) (basis p) (basis i)) *
            Rm04 x (vec4 (I := I) (basis p) B C D)) +
        (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) B (basis i) (basis p) (basis i)) *
            Rm04 x (vec4 (I := I) A (basis p) C D)) +
        (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) C (basis i) (basis p) (basis i)) *
            Rm04 x (vec4 (I := I) A B (basis p) D)) -
        (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) D (basis i) (basis p) (basis i)) *
            Rm04 x (vec4 (I := I) A B C (basis p))) := by
    simpa [cov, hcov, Rm13, Rm04, action] using hAct0
  have hRaw0 := canRawLowering (I := I) (M := M) g basis hinv
    (m 0) (m 1) (m 2) (m 3)
  have hRaw :
      -2 * (∑ p : Idx,
          Ric x (vec2 (I := I) D (basis p)) *
            Rm04 x (vec4 (I := I) A B C (basis p))) =
        2 * (∑ i : Idx, ∑ p : Idx,
          Rm04 x (vec4 (I := I) D (basis i) (basis p) (basis i)) *
            Rm04 x (vec4 (I := I) A B C (basis p))) := by
    simpa [cov, hcov, Rm04, Ric, A, B, C, D] using hRaw0
  change
    (-nabla2Ric (vec4 (I := I) A B C D) -
        nabla2Ric (vec4 (I := I) A C B D) +
        nabla2Ric (vec4 (I := I) A D B C) +
        nabla2Ric (vec4 (I := I) B A C D) +
        nabla2Ric (vec4 (I := I) B C A D) -
        nabla2Ric (vec4 (I := I) B D A C) -
        2 * (∑ p : Idx,
          Ric x (vec2 (I := I) D (basis p)) *
            Rm04 x (vec4 (I := I) A B C (basis p)))) =
      (∑ i : Idx, N (basis i) (basis i) A B C D) +
        hamiltonRmReact Rcomp m
  rw [hHess, Finset.sum_add_distrib, hAct]
  simp [hamiltonRmReact, Rcomp, A, B, C, D]
  linear_combination hRaw

end DifferentialGeometry.Integral.Connection
