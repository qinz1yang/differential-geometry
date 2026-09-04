import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.InverseMetric
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section FixedFrame

open DifferentialGeometry.Dim3Reaction

open scoped Matrix

variable {x : M}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private lemma fixedFrame_sum_repr
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (e : Fin 3 → TangentSpace I x)
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (i : Fin 3) :
    e i = ∑ j : Fin 3, P j i • f j := by
  rw [← f.sum_repr (e i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hP i j]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private lemma fixedFrame_coord_eq
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (e : Fin 3 → TangentSpace I x)
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (i j : Fin 3) :
    f.coord j (e i) = P j i := by
  simp [← hP i j]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
private lemma fixedFrame_metricComp_eq_sum
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (i j : Fin 3) :
    (S.base.metric t).inner x (e i) (e j) =
      ∑ a : Fin 3, P a i * P a j := by
  classical
  rw [fixedFrame_sum_repr f e P hP i, fixedFrame_sum_repr f e P hP j]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc
    (∑ b : Fin 3, P b j * (P a i * (S.base.metric t).inner x (f a) (f b)))
        = ∑ b : Fin 3, P a i * (P b j * (S.base.metric t).inner x (f a) (f b)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
    _ = P a i * (∑ b : Fin 3, P b j * (S.base.metric t).inner x (f a) (f b)) := by
          rw [Finset.mul_sum]
    _ = P a i * P a j := by
          have hsum : (∑ b : Fin 3, P b j * (S.base.metric t).inner x (f a) (f b)) = P a j := by
            rw [Finset.sum_eq_single a]
            · rw [horth a a]
              simp [kd]
            · intro b _hb hba
              rw [horth a b]
              simp [kd, Ne.symm hba]
            · intro ha
              exact absurd (Finset.mem_univ a) ha
          rw [hsum]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
private lemma fixedFrame_ginvP_eq_kd
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (gInvAt : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (hginv : ∀ i j : Fin 3, (∑ k : Fin 3, gInvAt i k * (S.base.metric t).inner x (e k) (e j)) = kd i j)
    (E G : Fin 3) :
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, P E e0 * gInvAt e0 g0 * P G g0) = kd E G := by
  classical
  let Pm : Matrix (Fin 3) (Fin 3) ℝ := fun a i => P a i
  let Gm : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (S.base.metric t).inner x (e i) (e j)
  let Gi : Matrix (Fin 3) (Fin 3) ℝ := gInvAt
  have hg : Gm = Matrix.transpose Pm * Pm := by
    ext i j
    simp only [Gm, Pm]
    exact fixedFrame_metricComp_eq_sum (I := I) (M := M) S t e f P hP horth i j
  have hgi : Gi * Gm = 1 := by
    ext i j
    change (∑ k : Fin 3, gInvAt i k * (S.base.metric t).inner x (e k) (e j)) =
      if i = j then 1 else 0
    simpa only [kd] using hginv i j
  have h1 : (Gi * Matrix.transpose Pm) * Pm = 1 := by
    calc
      (Gi * Matrix.transpose Pm) * Pm = Gi * (Matrix.transpose Pm * Pm) := by rw [Matrix.mul_assoc]
      _ = Gi * Gm := by rw [hg]
      _ = 1 := hgi
  have h2 : Pm * (Gi * Matrix.transpose Pm) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (R := ℝ) (m := Fin 3) (n := Fin 3) rfl).mp h1
  calc
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, P E e0 * gInvAt e0 g0 * P G g0)
        = ∑ e0 : Fin 3, P E e0 * (∑ g0 : Fin 3, gInvAt e0 g0 * P G g0) := by
          refine Finset.sum_congr rfl fun e0 _ => ?_
          calc
            (∑ g0 : Fin 3, P E e0 * gInvAt e0 g0 * P G g0)
                = ∑ g0 : Fin 3, P E e0 * (gInvAt e0 g0 * P G g0) := by
                  refine Finset.sum_congr rfl fun g0 _ => ?_
                  ring
            _ = P E e0 * (∑ g0 : Fin 3, gInvAt e0 g0 * P G g0) := by
                  rw [Finset.mul_sum]
    _ = (Pm * (Gi * Matrix.transpose Pm)) E G := by
          change
            (∑ e0 : Fin 3, P E e0 * (∑ g0 : Fin 3, gInvAt e0 g0 * P G g0)) =
              ∑ e0 : Fin 3, P E e0 * (∑ g0 : Fin 3, gInvAt e0 g0 * P G g0)
          rfl
    _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) E G := congrFun (congrFun h2 E) G
    _ = kd E G := by
          rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
lemma rm04Comp_ortho_eq_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (I0 : Fin 4 → Fin 3) :
    S.base.rm04 t x (fun p : Fin 4 => f (I0 p)) =
      rm (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (f i) (f j)))
        (I0 0) (I0 1) (I0 2) (I0 3) := by
  classical
  have horth' : OrthonormalBasisAt (I := I) (S.base.metric t) x f := by
    intro i j
    simpa [OrthonormalBasisAt, delta3, kd] using horth i j
  have hvec : (fun p : Fin 4 => f (I0 p)) =
      vec4 (I := I) (f (I0 0)) (f (I0 1)) (f (I0 2)) (f (I0 3)) := by
    funext p
    fin_cases p <;> rfl
  rw [hvec]
  have hkn := solution_rm04_kn_field (I := I) S t x hdim (f (I0 0)) (f (I0 1))
    (f (I0 2)) (f (I0 3))
  have hsc : S.scalar t x =
      sc (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (f i) (f j))) := by
    have h := scalar_eq_trace_ortho (I := I) S t x horth'
    unfold sc
    rw [h]
  rw [hkn]
  unfold rm
  simp only [horth, hsc, kd]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma rm04Comp_expand
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (a e0 b f0 : Fin 3) :
    S.base.rm04 t x (vec4 (I := I) (e a) (e e0) (e b) (e f0)) =
      ∑ J : Fin 4 → Fin 3,
        S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          (∏ p : Fin 4, P (J p) (slots4 a e0 b f0 p)) := by
  classical
  have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.base.rm04 t x)
    (vec4 (I := I) (e a) (e e0) (e b) (e f0))
  rw [hsum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show component0S (I := I) f (S.base.rm04 t x) J =
      S.base.rm04 t x (fun p : Fin 4 => f (J p)) by rfl]
  congr 1
  have hvec : (vec4 (I := I) (e a) (e e0) (e b) (e f0)) =
      fun p : Fin 4 => e (slots4 a e0 b f0 p) := by
    funext p
    fin_cases p <;> rfl
  rw [hvec]
  apply Finset.prod_congr rfl
  intro p _
  exact fixedFrame_coord_eq f e P hP (slots4 a e0 b f0 p) (J p)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma rm04Comp_expand_gen
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (H : Fin 4 → Fin 3) :
    S.base.rm04 t x (fun p : Fin 4 => e (H p)) =
      ∑ J : Fin 4 → Fin 3,
        S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          (∏ p : Fin 4, P (J p) (H p)) := by
  classical
  have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.base.rm04 t x)
    (fun p : Fin 4 => e (H p))
  rw [hsum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show component0S (I := I) f (S.base.rm04 t x) J =
      S.base.rm04 t x (fun p : Fin 4 => f (J p)) by rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact fixedFrame_coord_eq f e P hP (H p) (J p)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private def fin4SlotsEquiv : (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private lemma sum_fin_four_fun {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 → Fin 3) → α) :
    (∑ I0 : Fin 4 → Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [fin4SlotsEquiv, slots4]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private lemma sum3_kd_collapse (a : Fin 3) (X : Fin 3 → ℝ) :
    (∑ j : Fin 3, X j * kd a j) = X a := by
  rw [Finset.sum_eq_single a]
  · simp [kd]
  · intro j _hj hja
    simp [kd, Ne.symm hja]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma sum4_fix_two
    (J : Fin 4 → Fin 3) (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ K : Fin 4 → Fin 3, F K * kd (J 1) (K 1) * kd (J 3) (K 3)) =
      ∑ E : Fin 3, ∑ F0 : Fin 3, F (slots4 E (J 1) F0 (J 3)) := by
  classical
  rw [sum_fin_four_fun (fun K : Fin 4 → Fin 3 =>
    F K * kd (J 1) (K 1) * kd (J 3) (K 3))]
  simp only [slots4, Fin.isValue, Fin.reduceEq, reduceIte]
  have hre : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) * kd (J 1) j * kd (J 3) l) =
      ∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) * kd (J 3) l) * kd (J 1) j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hre]
  have hcol1 : (∑ i : Fin 3, ∑ j : Fin 3, (∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) * kd (J 3) l) * kd (J 1) j) =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, F (slots4 i (J 1) k l) * kd (J 3) l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sum3_kd_collapse (J 1) (fun j : Fin 3 => ∑ k : Fin 3, ∑ l : Fin 3,
      F (slots4 i j k l) * kd (J 3) l)
  rw [hcol1]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum3_kd_collapse (J 3) (fun l : Fin 3 => F (slots4 i (J 1) k l))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma roughLapRm04_fixedFrame_pullback
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (a b c d : Fin 3) :
    metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
        (vec4 (I := I) (e a) (e b) (e c) (e d)) =
      ∑ I0 : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
          tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f
            (identityInvMetric (Idx := Fin 3)) (nablaKRm04Field (I := I) S t 2 x))
            (fun i => f i) I0 := by
  classical
  let Tt : Tensor0SSpace 4 I x :=
    metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
      (nablaKRm04Field (I := I) S t 2 x)
  have hinv : MetricInverseInBasis (I := I) (S.base.metric t) x f
      (identityInvMetric (Idx := Fin 3)) := by
    exact DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (S.base.metric t) f horth
  have hconv : metricTraceFirstTwo0SAt (I := I) (S.base.metric t)
      (nablaKRm04Field (I := I) S t 2 x) (vec4 (I := I) (e a) (e b) (e c) (e d)) =
      Tt (vec4 (I := I) (e a) (e b) (e c) (e d)) := by
    rw [metricTrace0S2TensorInBasis_apply (I := I) f (identityInvMetric (Idx := Fin 3))
      (nablaKRm04Field (I := I) S t 2 x) (vec4 (I := I) (e a) (e b) (e c) (e d))]
    exact (metricTrace0S2InBasis_eq_metricTrace (I := I) (S.base.metric t) f
      (identityInvMetric (Idx := Fin 3)) hinv (nablaKRm04Field (I := I) S t 2 x)
      (vec4 (I := I) (e a) (e b) (e c) (e d))).symm
  have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f Tt
    (vec4 (I := I) (e a) (e b) (e c) (e d))
  rw [hconv, hsum]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  rw [show component0S (I := I) f Tt I0 = Tt (fun p : Fin 4 => f (I0 p)) by rfl]
  rw [mul_comm (∏ p : Fin 4, P (I0 p) (slots4 a b c d p))]
  congr 1
  have hvec : (vec4 (I := I) (e a) (e b) (e c) (e d)) =
      fun p : Fin 4 => e (slots4 a b c d p) := by
    funext p
    fin_cases p <;> rfl
  rw [hvec]
  apply Finset.prod_congr rfl
  intro p _
  exact fixedFrame_coord_eq f e P hP (slots4 a b c d p) (I0 p)

private lemma sum6_reorder
    (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Fin 4 → Fin 3) → (Fin 4 → Fin 3) → ℝ) :
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        ∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3, F e0 g0 f0 r0 J K) =
      (∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3,
        ∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3, F e0 g0 f0 r0 J K) := by
  classical
  conv_lhs =>
    enter [2]; intro e0; enter [2]; intro g0; enter [2]; intro f0; enter [2]; intro r0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro e0; enter [2]; intro g0; enter [2]; intro f0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro e0; enter [2]; intro g0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro e0
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro K; enter [2]; intro e0; enter [2]; intro g0; enter [2]; intro f0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro K; enter [2]; intro e0; enter [2]; intro g0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro K; enter [2]; intro e0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro K
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]

private lemma sum5_reorder
    (F : Fin 3 → Fin 3 → (Fin 4 → Fin 3) → Fin 3 → Fin 3 → ℝ) :
    (∑ p : Fin 3, ∑ q : Fin 3, ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3, ∑ J' : Fin 3,
        F p q J A J') =
      (∑ A : Fin 3, ∑ J' : Fin 3, ∑ J : Fin 4 → Fin 3,
        ∑ p : Fin 3, ∑ q : Fin 3, F p q J A J') := by
  classical
  conv_lhs =>
    enter [2]; intro p
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro J; enter [2]; intro p
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro J
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro J; enter [2]; intro A; enter [2]; intro p
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro J; enter [2]; intro A
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro A
    rw [Finset.sum_comm]

private lemma sum_relabel_slot
    (F : (Fin 4 → Fin 3) → Fin 3 → ℝ) (s : Fin 4) :
    (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3, F (fun a => if a = s then p0 else I0 a) (I0 s)) =
      ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3, F J A := by
  classical
  calc
    (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3, F (fun a => if a = s then p0 else I0 a) (I0 s))
        = ∑ p : (Fin 4 → Fin 3) × Fin 3, F (fun a => if a = s then p.2 else p.1 a) (p.1 s) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin 4 → Fin 3) × Fin 3, F p.1 p.2 := by
          let e : ((Fin 4 → Fin 3) × Fin 3) ≃ ((Fin 4 → Fin 3) × Fin 3) := {
            toFun := fun p : (Fin 4 → Fin 3) × Fin 3 =>
              (fun a : Fin 4 => if a = s then p.2 else p.1 a, p.1 s)
            invFun := fun p : (Fin 4 → Fin 3) × Fin 3 =>
              (fun a : Fin 4 => if a = s then p.2 else p.1 a, p.1 s)
            left_inv := by
              intro p
              rcases p with ⟨J, A⟩
              apply Prod.ext
              · funext a
                by_cases h : a = s <;> simp [h]
              · simp
            right_inv := by
              intro p
              rcases p with ⟨J, A⟩
              apply Prod.ext
              · funext a
                by_cases h : a = s <;> simp [h]
              · simp
          }
          exact Fintype.sum_equiv e
            (fun p => F (fun a => if a = s then p.2 else p.1 a) (p.1 s))
            (fun p => F p.1 p.2)
            (by intro p; rfl)
    _ = ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3, F J A := by
          rw [Fintype.sum_prod_type]

private lemma sum_comp_perm
    (σ : Equiv.Perm (Fin 4)) (F : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, F (fun p : Fin 4 => J (σ p))) = ∑ J : Fin 4 → Fin 3, F J := by
  classical
  let e : (Fin 4 → Fin 3) ≃ (Fin 4 → Fin 3) := {
    toFun := fun J : Fin 4 → Fin 3 => fun p : Fin 4 => J (σ p)
    invFun := fun J : Fin 4 → Fin 3 => fun p : Fin 4 => J (σ.symm p)
    left_inv := by
      intro J
      funext p
      simp
    right_inv := by
      intro J
      funext p
      simp
  }
  exact Fintype.sum_equiv e (fun J => F (fun p : Fin 4 => J (σ p))) (fun J => F J)
    (by intro J; rfl)

private lemma sum6_relabel
    (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ j0 : Fin 3, ∑ j1 : Fin 3, ∑ j2 : Fin 3, ∑ j3 : Fin 3,
        ∑ E : Fin 3, ∑ F0 : Fin 3, F j0 j1 j2 j3 E F0) =
      (∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
        ∑ E : Fin 3, ∑ F0 : Fin 3, F A E B F0 C D) := by
  classical
  conv_lhs =>
    enter [2]; intro j0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro j1
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro E; enter [2]; intro j1
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro E
    rw [Finset.sum_comm]

private lemma sum22_const_mul (H : Fin 3 → Fin 3 → ℝ) (c : ℝ) :
    (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0 * c) =
      (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) * c := by
  classical
  calc
    (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0 * c)
        = ∑ f0 : Fin 3, ∑ r0 : Fin 3, c * H f0 r0 := by
          refine Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
          ring
    _ = ∑ f0 : Fin 3, c * (∑ r0 : Fin 3, H f0 r0) := by
          refine Finset.sum_congr rfl fun f0 _ => ?_
          rw [← Finset.mul_sum]
    _ = c * (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) := by
          rw [← Finset.mul_sum]
    _ = (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) * c := by
          rw [mul_comm]

private lemma sum22_mul (G : Fin 3 → Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) :
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3, G e0 g0 * H f0 r0) =
      (∑ e0 : Fin 3, ∑ g0 : Fin 3, G e0 g0) *
        (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) := by
  classical
  calc
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3, G e0 g0 * H f0 r0)
        = ∑ e0 : Fin 3, ∑ g0 : Fin 3, G e0 g0 * (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) := by
          refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f0 _ => ?_
          rw [Finset.mul_sum]
    _ = (∑ e0 : Fin 3, ∑ g0 : Fin 3, G e0 g0) *
          (∑ f0 : Fin 3, ∑ r0 : Fin 3, H f0 r0) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun e0 _ => ?_
          rw [Finset.sum_mul]

private lemma sum6_relabel2
    (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ j0 : Fin 3, ∑ j1 : Fin 3, ∑ j2 : Fin 3, ∑ j3 : Fin 3,
        ∑ E : Fin 3, ∑ F0 : Fin 3, F j0 j1 j2 j3 E F0) =
      (∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
        ∑ E : Fin 3, ∑ F1 : Fin 3, F A E B F1 C D) := by
  classical
  conv_lhs =>
    enter [2]; intro j0
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro j1
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro E; enter [2]; intro j1
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro j0; enter [2]; intro j2; enter [2]; intro E
    rw [Finset.sum_comm]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma uhlenbeckPair_ginv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (gInvAt : Fin 3 → Fin 3 → ℝ)
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (hginv : ∀ i j : Fin 3, (∑ k : Fin 3, gInvAt i k * (S.base.metric t).inner x (e k) (e j)) = kd i j)
    (a b c d : Fin 3) :
    (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        gInvAt e0 g0 * gInvAt f0 r0 *
          S.base.rm04 t x (vec4 (I := I) (e a) (e e0) (e b) (e f0)) *
          S.base.rm04 t x (vec4 (I := I) (e c) (e g0) (e d) (e r0))) =
      ∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
        ∑ E : Fin 3, ∑ F : Fin 3,
          P A a * P B b * P C c * P D d *
            S.base.rm04 t x (vec4 (I := I) (f A) (f E) (f B) (f F)) *
            S.base.rm04 t x (vec4 (I := I) (f C) (f E) (f D) (f F)) := by
  classical
  let X : (Fin 4 → Fin 3) → Fin 3 → Fin 3 → ℝ := fun J e0 f0 =>
    S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
      (∏ p : Fin 4, P (J p) (slots4 a e0 b f0 p))
  let Y : (Fin 4 → Fin 3) → Fin 3 → Fin 3 → ℝ := fun K g0 r0 =>
    S.base.rm04 t x (fun p : Fin 4 => f (K p)) *
      (∏ p : Fin 4, P (K p) (slots4 c g0 d r0 p))
  have hX : ∀ e0 f0 : Fin 3,
      S.base.rm04 t x (vec4 (I := I) (e a) (e e0) (e b) (e f0)) =
        ∑ J : Fin 4 → Fin 3, X J e0 f0 := by
    intro e0 f0
    exact rm04Comp_expand (I := I) S t e f P hP a e0 b f0
  have hY : ∀ g0 r0 : Fin 3,
      S.base.rm04 t x (vec4 (I := I) (e c) (e g0) (e d) (e r0)) =
        ∑ K : Fin 4 → Fin 3, Y K g0 r0 := by
    intro g0 r0
    exact rm04Comp_expand (I := I) S t e f P hP c g0 d r0
  rw [show (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        gInvAt e0 g0 * gInvAt f0 r0 *
          S.base.rm04 t x (vec4 (I := I) (e a) (e e0) (e b) (e f0)) *
          S.base.rm04 t x (vec4 (I := I) (e c) (e g0) (e d) (e r0))) =
      (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        gInvAt e0 g0 * gInvAt f0 r0 *
          (∑ J : Fin 4 → Fin 3, X J e0 f0) * (∑ K : Fin 4 → Fin 3, Y K g0 r0)) from by
    refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
      Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
    rw [hX e0 f0, hY g0 r0]]
  have hdist : (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        gInvAt e0 g0 * gInvAt f0 r0 *
          (∑ J : Fin 4 → Fin 3, X J e0 f0) * (∑ K : Fin 4 → Fin 3, Y K g0 r0)) =
      (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
        ∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3,
          gInvAt e0 g0 * gInvAt f0 r0 * X J e0 f0 * Y K g0 r0) := by
    refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
      Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
    conv_lhs =>
      enter [1]
      rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    conv_lhs =>
      enter [2]
      intro J
      rw [Finset.mul_sum]
  rw [hdist]
  rw [sum6_reorder (fun e0 g0 f0 r0 J K =>
    gInvAt e0 g0 * gInvAt f0 r0 * X J e0 f0 * Y K g0 r0)]
  have hXprod : ∀ (J : Fin 4 → Fin 3) (e0 f0 : Fin 3),
      (∏ p : Fin 4, P (J p) (slots4 a e0 b f0 p)) =
        P (J 0) a * P (J 1) e0 * P (J 2) b * P (J 3) f0 := by
    intro J e0 f0
    simp [Fin.prod_univ_four, slots4]
  have hYprod : ∀ (K : Fin 4 → Fin 3) (g0 r0 : Fin 3),
      (∏ p : Fin 4, P (K p) (slots4 c g0 d r0 p)) =
        P (K 0) c * P (K 1) g0 * P (K 2) d * P (K 3) r0 := by
    intro K g0 r0
    simp [Fin.prod_univ_four, slots4]
  have hcontr : (∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3,
        ∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
          gInvAt e0 g0 * gInvAt f0 r0 * X J e0 f0 * Y K g0 r0) =
      (∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3,
        kd (J 1) (K 1) * kd (J 3) (K 3) *
          S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          S.base.rm04 t x (fun p : Fin 4 => f (K p)) *
          P (J 0) a * P (J 2) b * P (K 0) c * P (K 2) d) := by
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ => ?_
    let A : ℝ := S.base.rm04 t x (fun p : Fin 4 => f (J p)) * P (J 0) a * P (J 2) b
    let B : ℝ := S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d
    calc
      (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
          gInvAt e0 g0 * gInvAt f0 r0 * X J e0 f0 * Y K g0 r0)
          = ∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
              (gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0) *
                (gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0) * A * B := by
            simp only [X, Y, A, B]
            refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
              Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
            rw [hXprod J e0 f0, hYprod K g0 r0]
            ring
      _ = (∑ e0 : Fin 3, ∑ g0 : Fin 3, gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0) *
            (∑ f0 : Fin 3, ∑ r0 : Fin 3, gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0) * A * B := by
            have hsum : (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
                (gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0) *
                  (gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0) * A * B) =
                (∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
                  (gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0) *
                    (gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0 * A * B)) := by
              refine Finset.sum_congr rfl fun e0 _ => Finset.sum_congr rfl fun g0 _ =>
                Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
              ring
            rw [hsum]
            rw [sum22_mul (fun e0 g0 => gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0)
              (fun f0 r0 => gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0 * A * B)]
            have hsum2 : (∑ f0 : Fin 3, ∑ r0 : Fin 3,
                gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0 * A * B) =
                (∑ f0 : Fin 3, ∑ r0 : Fin 3,
                  gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0 * (A * B)) := by
              refine Finset.sum_congr rfl fun f0 _ => Finset.sum_congr rfl fun r0 _ => ?_
              ring
            rw [hsum2]
            rw [sum22_const_mul (fun f0 r0 => gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0) (A * B)]
            ring
      _ = kd (J 1) (K 1) * kd (J 3) (K 3) * A * B := by
            have h1 : (∑ e0 : Fin 3, ∑ g0 : Fin 3,
                gInvAt e0 g0 * P (J 1) e0 * P (K 1) g0) = kd (J 1) (K 1) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (fixedFrame_ginvP_eq_kd (I := I) (M := M) S t e f P gInvAt hP horth hginv
                  (J 1) (K 1))
            have h2 : (∑ f0 : Fin 3, ∑ r0 : Fin 3,
                gInvAt f0 r0 * P (J 3) f0 * P (K 3) r0) = kd (J 3) (K 3) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (fixedFrame_ginvP_eq_kd (I := I) (M := M) S t e f P gInvAt hP horth hginv
                  (J 3) (K 3))
            rw [h1, h2]
    simp only [A, B]
    ring
  rw [hcontr]
  have hvec2 : ∀ (w x y z : Fin 3),
      (fun p : Fin 4 => f (slots4 w x y z p)) = vec4 (I := I) (f w) (f x) (f y) (f z) := by
    intro w x y z
    funext p
    fin_cases p <;> simp [slots4, vec4]
  have hvecJ : ∀ J : Fin 4 → Fin 3,
      S.base.rm04 t x (fun p : Fin 4 => f (J p)) =
        S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) := by
    intro J
    congr 1
    funext p
    fin_cases p <;> simp [vec4]
  have hcollK : ∀ J : Fin 4 → Fin 3,
      (∑ K : Fin 4 → Fin 3,
        kd (J 1) (K 1) * kd (J 3) (K 3) *
          S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d) =
        ∑ E : Fin 3, ∑ F0 : Fin 3,
          S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
            P E c * P F0 d := by
    intro J
    have h := sum4_fix_two (J := J) (F := fun K : Fin 4 → Fin 3 =>
      S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d)
    calc
      (∑ K : Fin 4 → Fin 3,
        kd (J 1) (K 1) * kd (J 3) (K 3) *
          S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d)
          = ∑ K : Fin 4 → Fin 3,
              (S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d) *
                kd (J 1) (K 1) * kd (J 3) (K 3) := by
            refine Finset.sum_congr rfl fun K _ => ?_
            ring
      _ = ∑ E : Fin 3, ∑ F0 : Fin 3,
            (S.base.rm04 t x (fun p : Fin 4 => f (slots4 E (J 1) F0 (J 3) p)) *
              P (slots4 E (J 1) F0 (J 3) 0) c * P (slots4 E (J 1) F0 (J 3) 2) d) := h
      _ = ∑ E : Fin 3, ∑ F0 : Fin 3,
            S.base.rm04 t x (fun p : Fin 4 => f (slots4 E (J 1) F0 (J 3) p)) *
              P E c * P F0 d := by
            refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F0 _ => ?_
            simp only [slots4, Fin.isValue, Fin.reduceEq, reduceIte]
      _ = ∑ E : Fin 3, ∑ F0 : Fin 3,
            S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
              P E c * P F0 d := by
            refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F0 _ => ?_
            rw [hvec2 E (J 1) F0 (J 3)]
  have hcoll : (∑ J : Fin 4 → Fin 3, ∑ K : Fin 4 → Fin 3,
        kd (J 1) (K 1) * kd (J 3) (K 3) *
          S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          S.base.rm04 t x (fun p : Fin 4 => f (K p)) *
          P (J 0) a * P (J 2) b * P (K 0) c * P (K 2) d) =
      (∑ J : Fin 4 → Fin 3,
        S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) *
          P (J 0) a * P (J 2) b *
          (∑ E : Fin 3, ∑ F0 : Fin 3,
            S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
            P E c * P F0 d)) := by
    refine Finset.sum_congr rfl fun J _ => ?_
    calc
      (∑ K : Fin 4 → Fin 3,
        kd (J 1) (K 1) * kd (J 3) (K 3) *
          S.base.rm04 t x (fun p : Fin 4 => f (J p)) *
          S.base.rm04 t x (fun p : Fin 4 => f (K p)) *
          P (J 0) a * P (J 2) b * P (K 0) c * P (K 2) d)
          = ∑ K : Fin 4 → Fin 3,
              (S.base.rm04 t x (fun p : Fin 4 => f (J p)) * P (J 0) a * P (J 2) b) *
                (kd (J 1) (K 1) * kd (J 3) (K 3) *
                  S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d) := by
            refine Finset.sum_congr rfl fun K _ => ?_
            ring
      _ = (S.base.rm04 t x (fun p : Fin 4 => f (J p)) * P (J 0) a * P (J 2) b) *
            (∑ K : Fin 4 → Fin 3,
              kd (J 1) (K 1) * kd (J 3) (K 3) *
                S.base.rm04 t x (fun p : Fin 4 => f (K p)) * P (K 0) c * P (K 2) d) := by
            rw [Finset.mul_sum]
      _ = S.base.rm04 t x (fun p : Fin 4 => f (J p)) * P (J 0) a * P (J 2) b *
            (∑ E : Fin 3, ∑ F0 : Fin 3,
              S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
              P E c * P F0 d) := by
            rw [hcollK J]
      _ = S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) *
            P (J 0) a * P (J 2) b *
            (∑ E : Fin 3, ∑ F0 : Fin 3,
              S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
              P E c * P F0 d) := by
            rw [hvecJ J]
  rw [hcoll]
  have hc : (∑ J : Fin 4 → Fin 3,
        S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) *
          P (J 0) a * P (J 2) b *
          (∑ E : Fin 3, ∑ F0 : Fin 3,
            S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) *
            P E c * P F0 d)) =
      (∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
        ∑ E : Fin 3, ∑ F : Fin 3,
          P A a * P B b * P C c * P D d *
            S.base.rm04 t x (vec4 (I := I) (f A) (f E) (f B) (f F)) *
            S.base.rm04 t x (vec4 (I := I) (f C) (f E) (f D) (f F))) := by
    rw [sum_fin_four_fun (fun J : Fin 4 → Fin 3 =>
      S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) *
        P (J 0) a * P (J 2) b *
        (∑ E : Fin 3, ∑ F0 : Fin 3,
          S.base.rm04 t x (vec4 (I := I) (f E) (f (J 1)) (f F0) (f (J 3))) * P E c * P F0 d))]
    calc
      (∑ j0 : Fin 3, ∑ j1 : Fin 3, ∑ j2 : Fin 3, ∑ j3 : Fin 3,
          S.base.rm04 t x (vec4 (I := I) (f (slots4 j0 j1 j2 j3 0)) (f (slots4 j0 j1 j2 j3 1))
            (f (slots4 j0 j1 j2 j3 2)) (f (slots4 j0 j1 j2 j3 3))) *
          P (slots4 j0 j1 j2 j3 0) a * P (slots4 j0 j1 j2 j3 2) b *
          (∑ E : Fin 3, ∑ F0 : Fin 3,
            S.base.rm04 t x (vec4 (I := I) (f E) (f (slots4 j0 j1 j2 j3 1)) (f F0)
              (f (slots4 j0 j1 j2 j3 3))) * P E c * P F0 d))
          = ∑ j0 : Fin 3, ∑ j1 : Fin 3, ∑ j2 : Fin 3, ∑ j3 : Fin 3,
              S.base.rm04 t x (vec4 (I := I) (f j0) (f j1) (f j2) (f j3)) *
                P j0 a * P j2 b *
                (∑ E : Fin 3, ∑ F0 : Fin 3,
                  S.base.rm04 t x (vec4 (I := I) (f E) (f j1) (f F0) (f j3)) * P E c * P F0 d) := by
            simp only [slots4, Fin.isValue, Fin.reduceEq, reduceIte]
      _ = ∑ j0 : Fin 3, ∑ j1 : Fin 3, ∑ j2 : Fin 3, ∑ j3 : Fin 3,
            ∑ E : Fin 3, ∑ F0 : Fin 3,
              S.base.rm04 t x (vec4 (I := I) (f j0) (f j1) (f j2) (f j3)) *
                P j0 a * P j2 b *
                S.base.rm04 t x (vec4 (I := I) (f E) (f j1) (f F0) (f j3)) * P E c * P F0 d := by
            refine Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ =>
              Finset.sum_congr rfl fun j2 _ => Finset.sum_congr rfl fun j3 _ => ?_
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F0 _ => ?_
            ring
      _ = ∑ j0 : Fin 3, ∑ j2 : Fin 3, ∑ E : Fin 3, ∑ F0 : Fin 3,
            ∑ j1 : Fin 3, ∑ j3 : Fin 3,
              S.base.rm04 t x (vec4 (I := I) (f j0) (f j1) (f j2) (f j3)) *
                P j0 a * P j2 b *
                S.base.rm04 t x (vec4 (I := I) (f E) (f j1) (f F0) (f j3)) * P E c * P F0 d := by
            rw [sum6_relabel2 (fun j0 j1 j2 j3 E F0 =>
              S.base.rm04 t x (vec4 (I := I) (f j0) (f j1) (f j2) (f j3)) *
                P j0 a * P j2 b *
                S.base.rm04 t x (vec4 (I := I) (f E) (f j1) (f F0) (f j3)) * P E c * P F0 d)]
      _ = ∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
            ∑ E : Fin 3, ∑ F : Fin 3,
              P A a * P B b * P C c * P D d *
                S.base.rm04 t x (vec4 (I := I) (f A) (f E) (f B) (f F)) *
                S.base.rm04 t x (vec4 (I := I) (f C) (f E) (f D) (f F)) := by
            refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
              Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ =>
                Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F _ => ?_
            ring
  rw [hc]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
lemma uhlenbeckBTensorInFrame_fixedFrame_pullback
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (gInv : MatrixComp M (Fin 3))
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (hginv : ∀ i j : Fin 3, (∑ k : Fin 3, gInv (t : Real) x i k * (S.base.metric t).inner x (e k) (e j)) = kd i j)
    (a b c d : Fin 3) :
    uhlenbeckBTensorInFrame gInv
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) t x a b c d =
      ∑ I0 : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
          Bt (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (f i) (f j)))
            (I0 0) (I0 1) (I0 2) (I0 3) := by
  classical
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (f i) (f j))
  have hrm : ∀ (u v w z : Fin 3),
      S.base.rm04 t x (vec4 (I := I) (f u) (f v) (f w) (f z)) = rm Rf u v w z := by
    intro u v w z
    have h := rm04Comp_ortho_eq_rm (I := I) S t hdim f horth (slots4 u v w z)
    calc
      S.base.rm04 t x (vec4 (I := I) (f u) (f v) (f w) (f z))
          = S.base.rm04 t x (fun p : Fin 4 => f (slots4 u v w z p)) := by
            congr 1
            funext p
            fin_cases p <;> simp [slots4, vec4]
      _ = rm Rf u v w z := by
            simpa [Rf, slots4, Fin.isValue, Fin.reduceEq, reduceIte] using h
  have hB : ∀ I0 : Fin 4 → Fin 3,
      Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) =
        ∑ E : Fin 3, ∑ F : Fin 3,
          S.base.rm04 t x (vec4 (I := I) (f (I0 0)) (f E) (f (I0 1)) (f F)) *
          S.base.rm04 t x (vec4 (I := I) (f (I0 2)) (f E) (f (I0 3)) (f F)) := by
    intro I0
    unfold Bt
    refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F _ => ?_
    rw [hrm (I0 0) E (I0 1) F, hrm (I0 2) E (I0 3) F]
  calc
    uhlenbeckBTensorInFrame gInv
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => e a)) t x a b c d
        = ∑ e0 : Fin 3, ∑ g0 : Fin 3, ∑ f0 : Fin 3, ∑ r0 : Fin 3,
            gInv (t : Real) x e0 g0 * gInv (t : Real) x f0 r0 *
              S.base.rm04 t x (vec4 (I := I) (e a) (e e0) (e b) (e f0)) *
              S.base.rm04 t x (vec4 (I := I) (e c) (e g0) (e d) (e r0)) := by
          simp only [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp]
    _ = ∑ A : Fin 3, ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3,
          ∑ E : Fin 3, ∑ F : Fin 3,
            P A a * P B b * P C c * P D d *
              S.base.rm04 t x (vec4 (I := I) (f A) (f E) (f B) (f F)) *
              S.base.rm04 t x (vec4 (I := I) (f C) (f E) (f D) (f F)) :=
          uhlenbeckPair_ginv (I := I) S t e f P (fun i j => gInv (t : Real) x i j) hP horth hginv a b c d
    _ = ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            Bt Rf (I0 0) (I0 1) (I0 2) (I0 3) := by
          rw [sum_fin_four_fun (fun I0 : Fin 4 → Fin 3 =>
            (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) * Bt Rf (I0 0) (I0 1) (I0 2) (I0 3))]
          refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
            Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => ?_
          rw [hB (slots4 A B C D)]
          simp only [slots4, Fin.isValue, Fin.reduceEq, reduceIte, Fin.prod_univ_four]
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun F _ => ?_
          ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma riemann04RicciDriftInFrame_fixedFrame_pullback
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (e : Fin 3 → TangentSpace I x)
    (f : Module.Basis (Fin 3) Real (TangentSpace I x))
    (P : Fin 3 → Fin 3 → ℝ)
    (gInv : MatrixComp M (Fin 3))
    (hP : ∀ i j : Fin 3, P j i = f.repr (e i) j)
    (horth : ∀ i j : Fin 3, (S.base.metric t).inner x (f i) (f j) = kd i j)
    (hginv : ∀ i j : Fin 3, (∑ k : Fin 3, gInv (t : Real) x i k * (S.base.metric t).inner x (e k) (e j)) = kd i j)
    (a b c d : Fin 3) :
    riemann04RicciDriftInFrame
        (solutionRicciOneUpInFrame (I := I) S gInv (fun a _ => e a))
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) t x a b c d =
      ∑ I0 : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
          drift (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (f i) (f j)))
            (I0 0) (I0 1) (I0 2) (I0 3) := by
  classical
  let Rf : Fin 3 → Fin 3 → ℝ := fun i j => S.ricciAt t x (vec2 (I := I) (f i) (f j))
  have hrm : ∀ (u v w z : Fin 3),
      S.base.rm04 t x (vec4 (I := I) (f u) (f v) (f w) (f z)) = rm Rf u v w z := by
    intro u v w z
    have h := rm04Comp_ortho_eq_rm (I := I) S t hdim f horth (slots4 u v w z)
    calc
      S.base.rm04 t x (vec4 (I := I) (f u) (f v) (f w) (f z))
          = S.base.rm04 t x (fun p : Fin 4 => f (slots4 u v w z p)) := by
            congr 1
            funext p
            fin_cases p <;> simp [slots4, vec4]
      _ = rm Rf u v w z := by
            simpa [Rf, slots4, Fin.isValue, Fin.reduceEq, reduceIte] using h
  have hRexp : ∀ (i j : Fin 3),
      S.ricciAt t x (vec2 (I := I) (e i) (e j)) =
        ∑ A : Fin 3, ∑ J : Fin 3, P A i * P J j * Rf A J := by
    intro i j
    have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.ricciAt t x)
      (vec2 (I := I) (e i) (e j))
    rw [hsum]
    rw [sum_fin_two_fun (fun slots : Fin 2 → Fin 3 =>
      component0S (I := I) f (S.ricciAt t x) slots *
        ∏ a : Fin 2, f.coord (slots a) ((vec2 (I := I) (e i) (e j)) a))]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
    simp only [component0S]
    have hc : (fun a : Fin 2 => f (if a = 0 then A else J)) =
        vec2 (I := I) (f A) (f J) := by
      funext a
      fin_cases a <;> simp [vec2]
    rw [hc]
    have hc2 : (vec2 (I := I) (e i) (e j)) = fun a : Fin 2 => e (if a = 0 then i else j) := by
      funext a
      fin_cases a <;> simp [vec2]
    rw [hc2]
    rw [Fin.prod_univ_two]
    simp only [Fin.isValue, Fin.reduceEq, reduceIte]
    rw [fixedFrame_coord_eq f e P hP i A]
    rw [fixedFrame_coord_eq f e P hP j J]
    ring
  have hRexp1 : ∀ (i : Fin 3) (E : Fin 3),
      S.ricciAt t x (vec2 (I := I) (e i) (f E)) = ∑ A : Fin 3, P A i * Rf A E := by
    intro i E
    have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.ricciAt t x)
      (vec2 (I := I) (e i) (f E))
    rw [hsum]
    rw [sum_fin_two_fun (fun slots : Fin 2 → Fin 3 =>
      component0S (I := I) f (S.ricciAt t x) slots *
        ∏ a : Fin 2, f.coord (slots a) ((vec2 (I := I) (e i) (f E)) a))]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_eq_single E]
    · simp only [component0S]
      rw [show (fun a : Fin 2 => f (if a = 0 then A else E)) =
          vec2 (I := I) (f A) (f E) by
        funext a
        fin_cases a <;> simp [vec2]]
      rw [show (vec2 (I := I) (e i) (f E)) = fun a : Fin 2 => if a = 0 then e i else f E by
          funext a
          fin_cases a <;> simp [vec2]]
      rw [Fin.prod_univ_two]
      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
      rw [fixedFrame_coord_eq f e P hP i A]
      have hcoord : f.coord E (f E) = (1 : ℝ) := by
        simp [f.coord_apply]
      rw [hcoord]
      ring
    · intro J _hJ hJE
      simp only [component0S]
      rw [show (fun a : Fin 2 => f (if a = 0 then A else J)) =
          vec2 (I := I) (f A) (f J) by
        funext a
        fin_cases a <;> simp [vec2]]
      rw [show (vec2 (I := I) (e i) (f E)) = fun a : Fin 2 => if a = 0 then e i else f E by
          funext a
          fin_cases a <;> simp [vec2]]
      rw [Fin.prod_univ_two]
      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
      rw [fixedFrame_coord_eq f e P hP i A]
      have hcoord2 : f.coord J (f E) = 0 := by
        simp [f.coord_apply, Ne.symm hJE]
      rw [hcoord2]
      ring
    · intro hE
      exact absurd (Finset.mem_univ E) hE
  have hRm3 : ∀ (E v w z : Fin 3),
      S.base.rm04 t x (vec4 (I := I) (f E) (e v) (e w) (e z)) =
        ∑ B : Fin 3, ∑ C : Fin 3, ∑ D : Fin 3, P B v * P C w * P D z *
          S.base.rm04 t x (vec4 (I := I) (f E) (f B) (f C) (f D)) := by
    intro E v w z
    have hsum := tensor0S_apply_eq_sum (𝕜 := ℝ) (I := I) f (S.base.rm04 t x)
      (vec4 (I := I) (f E) (e v) (e w) (e z))
    rw [hsum]
    rw [sum_fin_four_fun (fun I0 : Fin 4 → Fin 3 =>
      component0S (I := I) f (S.base.rm04 t x) I0 *
        ∏ a : Fin 4, f.coord (I0 a) ((vec4 (I := I) (f E) (e v) (e w) (e z)) a))]
    have hcol : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          component0S (I := I) f (S.base.rm04 t x) (slots4 i j k l) *
            ∏ a : Fin 4, f.coord (slots4 i j k l a) ((vec4 (I := I) (f E) (e v) (e w) (e z)) a)) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          component0S (I := I) f (S.base.rm04 t x) (slots4 E j k l) *
            ∏ a : Fin 4, f.coord (slots4 E j k l a) ((vec4 (I := I) (f E) (e v) (e w) (e z)) a) := by
      rw [Finset.sum_eq_single E]
      · intro J _hJ hJE
        simp only [Fin.prod_univ_four]
        simp only [slots4, vec4, Fin.isValue, Fin.reduceEq, reduceIte]
        have hcoord2 : f.coord J (f E) = 0 := by
          simp [f.coord_apply, Ne.symm hJE]
        rw [hcoord2]
        simp
      · intro hE
        exact absurd (Finset.mem_univ E) hE
    rw [hcol]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ =>
      Finset.sum_congr rfl fun D _ => ?_
    simp only [component0S]
    rw [show (fun a : Fin 4 => f (slots4 E B C D a)) =
        vec4 (I := I) (f E) (f B) (f C) (f D) by
      funext a
      fin_cases a <;> simp [slots4, vec4]]
    rw [Fin.prod_univ_four]
    simp only [slots4, vec4, Fin.isValue, Fin.reduceEq, reduceIte]
    have hcoord : f.coord E (f E) = (1 : ℝ) := by
      simp [f.coord_apply]
    rw [hcoord]
    rw [fixedFrame_coord_eq f e P hP v B]
    rw [fixedFrame_coord_eq f e P hP w C]
    rw [fixedFrame_coord_eq f e P hP z D]
    ring
  have hpairS : ∀ (u : Fin 3) (G : Fin 4 → Fin 3) (s : Fin 4),
      (∑ p : Fin 3, ∑ q : Fin 3,
          gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e u) (e q)) *
            S.base.rm04 t x (fun a : Fin 4 => e (if a = s then p else G a))) =
        ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
          P A u * Rf A (J s) * S.base.rm04 t x (fun a : Fin 4 => f (J a)) *
            (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
    intro u G s
    classical
    let Rm_f : (Fin 4 → Fin 3) → ℝ := fun J =>
      S.base.rm04 t x (fun a : Fin 4 => f (J a))
    have hgen : ∀ p : Fin 3,
        S.base.rm04 t x (fun a : Fin 4 => e (if a = s then p else G a)) =
          ∑ J : Fin 4 → Fin 3, Rm_f J * (∏ a : Fin 4, P (J a) (if a = s then p else G a)) := by
      intro p
      simpa [Rm_f] using rm04Comp_expand_gen (I := I) S t e f P hP (fun a : Fin 4 => if a = s then p else G a)
    have hprod : ∀ p : Fin 3, ∀ J : Fin 4 → Fin 3,
        (∏ a : Fin 4, P (J a) (if a = s then p else G a)) =
          P (J s) p * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
      intro p J
      fin_cases s <;> simp [Fin.prod_univ_four] <;> ring
    have hcontr : ∀ (J' : Fin 3) (J : Fin 4 → Fin 3),
        (∑ p : Fin 3, ∑ q : Fin 3, gInv (t : Real) x p q * P J' q * P (J s) p) =
          kd (J s) J' := by
      intro J' J
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (fixedFrame_ginvP_eq_kd (I := I) (M := M) S t e f P (fun i j => gInv (t : Real) x i j) hP horth hginv
          (J s) J')
    calc
      (∑ p : Fin 3, ∑ q : Fin 3,
          gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e u) (e q)) *
            S.base.rm04 t x (fun a : Fin 4 => e (if a = s then p else G a)))
          = ∑ p : Fin 3, ∑ q : Fin 3,
              gInv (t : Real) x p q * (∑ A : Fin 3, ∑ J' : Fin 3, P A u * P J' q * Rf A J') *
                (∑ J : Fin 4 → Fin 3, Rm_f J * (∏ a : Fin 4, P (J a) (if a = s then p else G a))) := by
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
            rw [hRexp u q, hgen p]
      _ = ∑ A : Fin 3, ∑ J' : Fin 3, ∑ J : Fin 4 → Fin 3,
            P A u * Rf A J' * Rm_f J *
              (∑ p : Fin 3, ∑ q : Fin 3, gInv (t : Real) x p q * P J' q * P (J s) p) *
                (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
            conv_lhs =>
              simp only [Finset.mul_sum, Finset.sum_mul]
            rw [show (∑ p : Fin 3, ∑ q : Fin 3, ∑ J : Fin 4 → Fin 3,
                  ∑ A : Fin 3, ∑ J' : Fin 3,
                    gInv (t : Real) x p q * (P A u * P J' q * Rf A J') *
                      (Rm_f J * (∏ a : Fin 4, P (J a) (if a = s then p else G a)))) =
                (∑ p : Fin 3, ∑ q : Fin 3, ∑ J : Fin 4 → Fin 3,
                  ∑ A : Fin 3, ∑ J' : Fin 3,
                    gInv (t : Real) x p q * (P A u * P J' q * Rf A J') *
                      (Rm_f J * (P (J s) p * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))))) from by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
                Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun A _ =>
                  Finset.sum_congr rfl fun J' _ => ?_
              rw [hprod p J]]
            rw [sum5_reorder (fun p q J A J' =>
              gInv (t : Real) x p q * (P A u * P J' q * Rf A J') * (Rm_f J * (P (J s) p *
                (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)))))]
            refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J' _ =>
              Finset.sum_congr rfl fun J _ => ?_
            rw [show (∑ p : Fin 3, ∑ q : Fin 3,
                  gInv (t : Real) x p q * (P A u * P J' q * Rf A J') *
                    (Rm_f J * (P (J s) p * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))))) =
                (∑ p : Fin 3, ∑ q : Fin 3,
                  (gInv (t : Real) x p q * P J' q * P (J s) p) *
                    (P A u * Rf A J' * Rm_f J * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)))) by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
              ring]
            rw [show (∑ p : Fin 3, ∑ q : Fin 3,
                  (gInv (t : Real) x p q * P J' q * P (J s) p) *
                    (P A u * Rf A J' * Rm_f J * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)))) =
                (∑ p : Fin 3, ∑ q : Fin 3, gInv (t : Real) x p q * P J' q * P (J s) p) *
                  (P A u * Rf A J' * Rm_f J * (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))) by
              simp only [Finset.sum_mul]]
            ring
      _ = ∑ A : Fin 3, ∑ J' : Fin 3, ∑ J : Fin 4 → Fin 3,
            P A u * Rf A J' * Rm_f J * kd (J s) J' *
              (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
            refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J' _ =>
              Finset.sum_congr rfl fun J _ => ?_
            rw [hcontr J' J]
      _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
            P A u * Rf A (J s) * Rm_f J *
              (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
            rw [show (∑ A : Fin 3, ∑ J' : Fin 3, ∑ J : Fin 4 → Fin 3,
                  P A u * Rf A J' * Rm_f J * kd (J s) J' *
                    (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))) =
                (∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                  ∑ J' : Fin 3, P A u * Rf A J' * Rm_f J * kd (J s) J' *
                    (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))) from by
              conv_lhs =>
                enter [2]; intro A
                rw [Finset.sum_comm]]
            refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
            rw [show (∑ J' : Fin 3, P A u * Rf A J' * Rm_f J * kd (J s) J' *
                  (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))) =
                (∑ J' : Fin 3, (P A u * Rf A J' * Rm_f J *
                  (∏ a : Fin 4, if a = s then 1 else P (J a) (G a))) * kd (J s) J') by
              refine Finset.sum_congr rfl fun J' _ => ?_
              ring]
            rw [sum3_kd_collapse (J s) (fun J' : Fin 3 => P A u * Rf A J' * Rm_f J *
              (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)))]
      _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
            P A u * Rf A (J s) * S.base.rm04 t x (fun a : Fin 4 => f (J a)) *
              (∏ a : Fin 4, if a = s then 1 else P (J a) (G a)) := by
            simp only [Rm_f]
  calc
    riemann04RicciDriftInFrame
        (solutionRicciOneUpInFrame (I := I) S gInv (fun a _ => e a))
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) t x a b c d
        = (∑ p : Fin 3, ∑ q : Fin 3,
            gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e a) (e q)) *
              S.base.rm04 t x (vec4 (I := I) (e p) (e b) (e c) (e d))) +
          (∑ p : Fin 3, ∑ q : Fin 3,
            gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e b) (e q)) *
              S.base.rm04 t x (vec4 (I := I) (e a) (e p) (e c) (e d))) +
          (∑ p : Fin 3, ∑ q : Fin 3,
            gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e c) (e q)) *
              S.base.rm04 t x (vec4 (I := I) (e a) (e b) (e p) (e d))) +
          (∑ p : Fin 3, ∑ q : Fin 3,
            gInv (t : Real) x p q * S.ricciAt t x (vec2 (I := I) (e d) (e q)) *
              S.base.rm04 t x (vec4 (I := I) (e a) (e b) (e c) (e p))) := by
            simp only [riemann04RicciDriftInFrame, solutionRicciOneUpInFrame, ricciOneUpCompInFrame,
              ricciCompInFrame, solutionRm04CompInFrame, rm04Comp]
            conv_lhs =>
              simp only [Finset.sum_mul]
    _ = (∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
          P A a * Rf A (J 0) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
            (∏ a0 : Fin 4, if a0 = 0 then 1 else P (J a0) (slots4 a b c d a0))) +
        (∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
          P A b * Rf A (J 1) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
            (∏ a0 : Fin 4, if a0 = 1 then 1 else P (J a0) (slots4 a b c d a0))) +
        (∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
          P A c * Rf A (J 2) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
            (∏ a0 : Fin 4, if a0 = 2 then 1 else P (J a0) (slots4 a b c d a0))) +
        (∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
          P A d * Rf A (J 3) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
            (∏ a0 : Fin 4, if a0 = 3 then 1 else P (J a0) (slots4 a b c d a0))) := by
            have hvec0 : ∀ p : Fin 3,
                vec4 (I := I) (e p) (e b) (e c) (e d) =
                  (fun a0 : Fin 4 => e (if a0 = 0 then p else slots4 a b c d a0)) := by
              intro p
              funext a0
              fin_cases a0 <;> simp [slots4, vec4]
            have hvec1 : ∀ p : Fin 3,
                vec4 (I := I) (e a) (e p) (e c) (e d) =
                  (fun a0 : Fin 4 => e (if a0 = 1 then p else slots4 a b c d a0)) := by
              intro p
              funext a0
              fin_cases a0 <;> simp [slots4, vec4]
            have hvec2 : ∀ p : Fin 3,
                vec4 (I := I) (e a) (e b) (e p) (e d) =
                  (fun a0 : Fin 4 => e (if a0 = 2 then p else slots4 a b c d a0)) := by
              intro p
              funext a0
              fin_cases a0 <;> simp [slots4, vec4]
            have hvec3 : ∀ p : Fin 3,
                vec4 (I := I) (e a) (e b) (e c) (e p) =
                  (fun a0 : Fin 4 => e (if a0 = 3 then p else slots4 a b c d a0)) := by
              intro p
              funext a0
              fin_cases a0 <;> simp [slots4, vec4]
            conv_lhs =>
              simp only [hvec0, hvec1, hvec2, hvec3]
            rw [hpairS a (fun a0 => slots4 a b c d a0) 0,
              hpairS b (fun a0 => slots4 a b c d a0) 1,
              hpairS c (fun a0 => slots4 a b c d a0) 2,
              hpairS d (fun a0 => slots4 a b c d a0) 3]
    _ = ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            drift (fun i j : Fin 3 => S.ricciAt t x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3) := by
            have hrmf : ∀ J : Fin 4 → Fin 3,
                S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) =
                  rm Rf (J 0) (J 1) (J 2) (J 3) := by
              intro J
              calc
                S.base.rm04 t x (fun a0 : Fin 4 => f (J a0))
                    = S.base.rm04 t x (vec4 (I := I) (f (J 0)) (f (J 1)) (f (J 2)) (f (J 3))) := by
                      congr 1
                      funext a0
                      fin_cases a0 <;> simp [vec4]
                _ = rm Rf (J 0) (J 1) (J 2) (J 3) := hrm (J 0) (J 1) (J 2) (J 3)
            have hd0 : (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                    Rf (I0 0) p0 * rm Rf p0 (I0 1) (I0 2) (I0 3)) =
                ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                  P A a * Rf A (J 0) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                    (∏ a0 : Fin 4, if a0 = 0 then 1 else P (J a0) (slots4 a b c d a0)) := by
              calc
                (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                    (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                      Rf (I0 0) p0 * rm Rf p0 (I0 1) (I0 2) (I0 3))
                    = ∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                        P (I0 0) a * P (I0 1) b * P (I0 2) c * P (I0 3) d *
                          Rf (I0 0) p0 * rm Rf p0 (I0 1) (I0 2) (I0 3) := by
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3,
                      P A a * P (J 1) b * P (J 2) c * P (J 3) d *
                        Rf A (J 0) * rm Rf (J 0) (J 1) (J 2) (J 3) := by
                      rw [← sum_relabel_slot (fun J A =>
                        P A a * P (J 1) b * P (J 2) c * P (J 3) d *
                          Rf A (J 0) * rm Rf (J 0) (J 1) (J 2) (J 3)) 0]
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
                _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                      P A a * Rf A (J 0) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                        (∏ a0 : Fin 4, if a0 = 0 then 1 else P (J a0) (slots4 a b c d a0)) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
                      rw [hrmf J]
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
            have hd1 : (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                    Rf (I0 1) p0 * rm Rf (I0 0) p0 (I0 2) (I0 3)) =
                ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                  P A b * Rf A (J 1) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                    (∏ a0 : Fin 4, if a0 = 1 then 1 else P (J a0) (slots4 a b c d a0)) := by
              calc
                (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                    (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                      Rf (I0 1) p0 * rm Rf (I0 0) p0 (I0 2) (I0 3))
                    = ∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                        P (I0 0) a * P (I0 1) b * P (I0 2) c * P (I0 3) d *
                          Rf (I0 1) p0 * rm Rf (I0 0) p0 (I0 2) (I0 3) := by
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3,
                      P A b * P (J 0) a * P (J 2) c * P (J 3) d *
                        Rf A (J 1) * rm Rf (J 0) (J 1) (J 2) (J 3) := by
                      rw [← sum_relabel_slot (fun J A =>
                        P A b * P (J 0) a * P (J 2) c * P (J 3) d *
                          Rf A (J 1) * rm Rf (J 0) (J 1) (J 2) (J 3)) 1]
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
                _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                      P A b * Rf A (J 1) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                        (∏ a0 : Fin 4, if a0 = 1 then 1 else P (J a0) (slots4 a b c d a0)) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
                      rw [hrmf J]
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
            have hd2 : (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                    Rf (I0 2) p0 * rm Rf (I0 0) (I0 1) p0 (I0 3)) =
                ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                  P A c * Rf A (J 2) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                    (∏ a0 : Fin 4, if a0 = 2 then 1 else P (J a0) (slots4 a b c d a0)) := by
              calc
                (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                    (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                      Rf (I0 2) p0 * rm Rf (I0 0) (I0 1) p0 (I0 3))
                    = ∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                        P (I0 0) a * P (I0 1) b * P (I0 2) c * P (I0 3) d *
                          Rf (I0 2) p0 * rm Rf (I0 0) (I0 1) p0 (I0 3) := by
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3,
                      P A c * P (J 0) a * P (J 1) b * P (J 3) d *
                        Rf A (J 2) * rm Rf (J 0) (J 1) (J 2) (J 3) := by
                      rw [← sum_relabel_slot (fun J A =>
                        P A c * P (J 0) a * P (J 1) b * P (J 3) d *
                          Rf A (J 2) * rm Rf (J 0) (J 1) (J 2) (J 3)) 2]
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
                _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                      P A c * Rf A (J 2) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                        (∏ a0 : Fin 4, if a0 = 2 then 1 else P (J a0) (slots4 a b c d a0)) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
                      rw [hrmf J]
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
            have hd3 : (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                  (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                    Rf (I0 3) p0 * rm Rf (I0 0) (I0 1) (I0 2) p0) =
                ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                  P A d * Rf A (J 3) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                    (∏ a0 : Fin 4, if a0 = 3 then 1 else P (J a0) (slots4 a b c d a0)) := by
              calc
                (∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                    (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                      Rf (I0 3) p0 * rm Rf (I0 0) (I0 1) (I0 2) p0)
                    = ∑ I0 : Fin 4 → Fin 3, ∑ p0 : Fin 3,
                        P (I0 0) a * P (I0 1) b * P (I0 2) c * P (I0 3) d *
                          Rf (I0 3) p0 * rm Rf (I0 0) (I0 1) (I0 2) p0 := by
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                _ = ∑ J : Fin 4 → Fin 3, ∑ A : Fin 3,
                      P A d * P (J 0) a * P (J 1) b * P (J 2) c *
                        Rf A (J 3) * rm Rf (J 0) (J 1) (J 2) (J 3) := by
                      rw [← sum_relabel_slot (fun J A =>
                        P A d * P (J 0) a * P (J 1) b * P (J 2) c *
                          Rf A (J 3) * rm Rf (J 0) (J 1) (J 2) (J 3)) 3]
                      refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun p0 _ => ?_
                      simp only [Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
                _ = ∑ A : Fin 3, ∑ J : Fin 4 → Fin 3,
                      P A d * Rf A (J 3) * S.base.rm04 t x (fun a0 : Fin 4 => f (J a0)) *
                        (∏ a0 : Fin 4, if a0 = 3 then 1 else P (J a0) (slots4 a b c d a0)) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun J _ => ?_
                      rw [hrmf J]
                      simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
                      ring
            conv_rhs =>
              simp only [drift]
              simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
              simp only [← mul_assoc]
            rw [hd0, hd1, hd2, hd3]

end FixedFrame

open DifferentialGeometry.Dim3Reaction

private lemma sum_lin_comb (w A B1 B2 B3 B4 D : (Fin 4 → Fin 3) → ℝ) :
    (∑ J : Fin 4 → Fin 3, w J * A J)
        - 2 * ((∑ J : Fin 4 → Fin 3, w J * B1 J) - (∑ J : Fin 4 → Fin 3, w J * B2 J)
            + (∑ J : Fin 4 → Fin 3, w J * B3 J) - (∑ J : Fin 4 → Fin 3, w J * B4 J))
        - (∑ J : Fin 4 → Fin 3, w J * D J)
      = (∑ J : Fin 4 → Fin 3,
          w J * (A J + (-2 * (B1 J - B2 J + B3 J - B4 J) - D J))) := by
  rw [show (∑ J : Fin 4 → Fin 3,
        w J * (A J + (-2 * (B1 J - B2 J + B3 J - B4 J) - D J))) =
      (∑ J : Fin 4 → Fin 3,
        (w J * A J + w J * (-2 * (B1 J - B2 J + B3 J - B4 J)) - w J * D J)) by
    refine Finset.sum_congr rfl fun J _ => ?_
    ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ J : Fin 4 → Fin 3, w J * (-2 * (B1 J - B2 J + B3 J - B4 J))) =
      (∑ J : Fin 4 → Fin 3, -2 * (w J * (B1 J - B2 J + B3 J - B4 J))) by
    refine Finset.sum_congr rfl fun J _ => ?_
    ring]
  rw [← Finset.mul_sum]
  rw [show (∑ J : Fin 4 → Fin 3, w J * (B1 J - B2 J + B3 J - B4 J)) =
      (∑ J : Fin 4 → Fin 3, w J * B1 J) - (∑ J : Fin 4 → Fin 3, w J * B2 J)
        + (∑ J : Fin 4 → Fin 3, w J * B3 J) - (∑ J : Fin 4 → Fin 3, w J * B4 J) by
    rw [show (∑ J : Fin 4 → Fin 3,
          w J * (B1 J - B2 J + B3 J - B4 J)) =
        (∑ J : Fin 4 → Fin 3,
          (w J * B1 J - w J * B2 J + w J * B3 J - w J * B4 J)) by
      refine Finset.sum_congr rfl fun J _ => ?_
      ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem solutionRm04CompInFrame_fixed_frame_evolution
    (T : ℝ) (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x)) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := RealTimeInterval.closed 0 T hT.le)
      (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
      (fun t x a b c d =>
        metricTraceFirstTwo0SAt (I := I) (S.base.metric t) (nablaKRm04Field (I := I) S t 2 x)
          (vec4 (I := I) (basisAt x a) (basisAt x b) (basisAt x c) (basisAt x d)))
      (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
        (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)))
      (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
        (fun a x => basisAt x a)) := by
  classical
  intro t x a b c d
  let D : RealTimeInterval := RealTimeInterval.closed 0 T hT.le
  rcases exists_orthonormalBasisAt (I := I) (S.base.metric (t : ℝ)) x (hdim x) with ⟨f, hf⟩
  let e : Fin 3 → TangentSpace I x := fun i => basisAt x i
  let P : Fin 3 → Fin 3 → ℝ := fun j i => f.repr (e i) j
  have hP : ∀ i j : Fin 3, P j i = f.repr (e i) j := by
    intro i j
    rfl
  have horth : ∀ i j : Fin 3, (S.base.metric (t : ℝ)).inner x (f i) (f j) = kd i j := by
    intro i j
    simpa [kd, delta3] using hf i j
  let gInvAt : Fin 3 → Fin 3 → ℝ := fun i j =>
    solutionInverseMetricComponents S basisAt (t : ℝ) x i j
  have hginv : ∀ i j : Fin 3,
      (∑ k : Fin 3, gInvAt i k * (S.base.metric (t : ℝ)).inner x (e k) (e j)) = kd i j := by
    intro i j
    have h := solutionInverseMetricComponents_mul_metric (I := I) (M := M) S basisAt (t : ℝ) x i j
    simpa [gInvAt, e, metricCompInFrame, kd] using h
  have hbase : ∀ I0 : Fin 4 → Fin 3,
      HasDerivWithinAt
        (fun r : ℝ => S.base.rm04 r x (fun p : Fin 4 => f (I0 p)))
        (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
            (fun i => f i) I0 +
          (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 3) (I0 2) +
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 2) (I0 1) (I0 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 3) (I0 1) (I0 2)) -
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3)))
        (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    intro I0
    have h := riemann_component_evolution_in_orthonormal_frame_of_solution
      (I := I) (M := M) S hS t hdim x f horth I0
    simpa [kd] using h
  have hfun : (fun r : ℝ => S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d))) =
      fun r : ℝ => ∑ J : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)) := by
    funext r
    have hgen := rm04Comp_expand_gen (I := I) S r e f P hP (slots4 a b c d)
    calc
      S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d))
          = S.base.rm04 r x (fun p : Fin 4 => e (slots4 a b c d p)) := by
            congr 1
            funext p
            fin_cases p <;> simp [slots4, vec4]
      _ = ∑ J : Fin 4 → Fin 3,
            (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hgen
  have hmain : HasDerivWithinAt
      (fun r : ℝ => ∑ J : Fin 4 → Fin 3,
        (∏ p : Fin 4, P (J p) (slots4 a b c d p)) * S.base.rm04 r x (fun p : Fin 4 => f (J p)))
      (∑ J : Fin 4 → Fin 3, (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
        (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
            (fun i => f i) J +
          (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 1) (J 2) (J 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 1) (J 3) (J 2) +
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 2) (J 1) (J 3) -
                Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (J 0) (J 3) (J 1) (J 2)) -
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 1) (J 2) (J 3))))
      (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    refine HasDerivWithinAt.fun_sum ?_
    intro J _hJ
    exact (hbase J).const_mul (∏ p : Fin 4, P (J p) (slots4 a b c d p))
  have hfin : HasDerivWithinAt
      (fun r : ℝ => solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)
        r x a b c d)
      (metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d)
      (RealTimeInterval.closed 0 T hT.le).carrier (t : ℝ) := by
    have hT1 := roughLapRm04_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) e f P hP horth a b c d
    have hT2 := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b c d
    have hT3 := riemann04RicciDriftInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b c d
    let σ23 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 2 then 3 else if p = 3 then 2 else p
      invFun := fun p => if p = 2 then 3 else if p = 3 then 2 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ23_0 : σ23 0 = 0 := by decide
    have hσ23_1 : σ23 1 = 1 := by decide
    have hσ23_2 : σ23 2 = 3 := by decide
    have hσ23_3 : σ23 3 = 2 := by decide
    have hB0 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b c d =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3) := by
      have hA : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b c d =
          uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b c d := by
        simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
      exact hA.trans hT2
    have hdrift : riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (I0 0) (I0 1) (I0 2) (I0 3) := by
      have hA : riemann04RicciDriftInFrame
            (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
              (fun a x => basisAt x a))
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
            (t : ℝ) x a b c d =
          riemann04RicciDriftInFrame
            (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
              (fun a _ => e a))
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a))
            (t : ℝ) x a b c d := by
        unfold riemann04RicciDriftInFrame
        congr 1
      exact hA.trans hT3
    have hlap : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) =
        ∑ I0 : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
              (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0 := by
      exact hT1.trans rfl
    have hT2b := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a b d c
    have hA1 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b d c := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB1 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 1) (J 3) (J 2) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a b d c
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a b d c := hA1
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2b
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ23 p)) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ23 0)) (J (σ23 1)) (J (σ23 2)) (J (σ23 3)) := by
              rw [← sum_comp_perm σ23 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a b d c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 3) (J 2) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ23_0, hσ23_1, hσ23_2, hσ23_3]
              ring
    let σ12 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 1 then 2 else if p = 2 then 1 else p
      invFun := fun p => if p = 1 then 2 else if p = 2 then 1 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ12_0 : σ12 0 = 0 := by decide
    have hσ12_1 : σ12 1 = 2 := by decide
    have hσ12_2 : σ12 2 = 1 := by decide
    have hσ12_3 : σ12 3 = 3 := by decide
    let σ13 : Equiv.Perm (Fin 4) := {
      toFun := fun p => if p = 1 then 3 else if p = 2 then 1 else if p = 3 then 2 else p
      invFun := fun p => if p = 2 then 3 else if p = 3 then 1 else if p = 1 then 2 else p
      left_inv := by intro p; fin_cases p <;> simp
      right_inv := by intro p; fin_cases p <;> simp
    }
    have hσ13_0 : σ13 0 = 0 := by decide
    have hσ13_1 : σ13 1 = 3 := by decide
    have hσ13_2 : σ13 2 = 1 := by decide
    have hσ13_3 : σ13 3 = 2 := by decide
    have hT2c := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a c b d
    have hA2 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a c b d := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB2 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 2) (J 1) (J 3) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a c b d
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a c b d := hA2
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2c
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ12 p)) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ12 0)) (J (σ12 1)) (J (σ12 2)) (J (σ12 3)) := by
              rw [← sum_comp_perm σ12 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a c b d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 2) (J 1) (J 3) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ12_0, hσ12_1, hσ12_2, hσ12_3]
              ring
    have hT2d := uhlenbeckBTensorInFrame_fixedFrame_pullback (I := I) (M := M) S (t : ℝ) (hdim x) e f P
      (solutionInverseMetricComponents S basisAt) hP horth hginv a d b c
    have hA3 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c =
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a d b c := by
      simp [uhlenbeckBTensorInFrame, solutionRm04CompInFrame, rm04Comp, e]
    have hB3 : uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c =
        ∑ J : Fin 4 → Fin 3,
          (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
            Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
              (J 0) (J 3) (J 1) (J 2) := by
      calc
        uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
            (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a)) (t : ℝ) x a d b c
            = uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a _ => e a)) (t : ℝ) x a d b c := hA3
        _ = ∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) := hT2d
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J (σ13 p)) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J (σ13 0)) (J (σ13 1)) (J (σ13 2)) (J (σ13 3)) := by
              rw [← sum_comp_perm σ13 (fun J =>
                (∏ p : Fin 4, P (J p) (slots4 a d b c p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 1) (J 2) (J 3))]
        _ = ∑ J : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (J p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (J 0) (J 3) (J 1) (J 2) := by
              refine Finset.sum_congr rfl fun J _ => ?_
              simp only [Fin.prod_univ_four, slots4, Fin.isValue, Fin.reduceEq, reduceIte]
              rw [hσ13_0, hσ13_1, hσ13_2, hσ13_3]
              ring
    have hRHS : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d
        = (∑ I0 : Fin 4 → Fin 3,
            (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
              tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0)
          - 2 * ((∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3))
              - (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 3) (I0 2))
              + (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 2) (I0 1) (I0 3))
              - (∑ I0 : Fin 4 → Fin 3,
                (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 3) (I0 1) (I0 2)))
          - (∑ I0 : Fin 4 → Fin 3,
              (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
                drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3)) := by
      rw [hlap, hB0, hB1, hB2, hB3, hdrift]
    have hEq : metricTraceFirstTwo0SAt (I := I) (S.base.metric (t : ℝ)) (nablaKRm04Field (I := I) S (t : ℝ) 2 x)
          (vec4 (I := I) (e a) (e b) (e c) (e d)) -
        2 * (uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b c d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a b d c +
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a c b d -
            uhlenbeckBTensorInFrame (solutionInverseMetricComponents S basisAt)
              (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
              (t : ℝ) x a d b c) -
        riemann04RicciDriftInFrame
          (solutionRicciOneUpInFrame (I := I) S (solutionInverseMetricComponents S basisAt)
            (fun a x => basisAt x a))
          (solutionRm04CompInFrame (I := I) S.base.rm04 (fun a x => basisAt x a))
          (t : ℝ) x a b c d
        = ∑ I0 : Fin 4 → Fin 3, (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
            (tensor0SComponent (I := I)
                (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
                (fun i => f i) I0 +
              (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 1) (I0 2) (I0 3) -
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 1) (I0 3) (I0 2) +
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 2) (I0 1) (I0 3) -
                    Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                      (I0 0) (I0 3) (I0 1) (I0 2)) -
                drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                  (I0 0) (I0 1) (I0 2) (I0 3))) := by
      rw [hRHS]
      rw [sum_lin_comb (fun I0 : Fin 4 → Fin 3 => ∏ p : Fin 4, P (I0 p) (slots4 a b c d p))
          (fun I0 => tensor0SComponent (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
            (nablaKRm04Field (I := I) S (t : ℝ) 2 x)) (fun i => f i) I0)
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 2) (I0 3))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 3) (I0 2))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 2) (I0 1) (I0 3))
          (fun I0 => Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 3) (I0 1) (I0 2))
          (fun I0 => drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j))) (I0 0) (I0 1) (I0 2) (I0 3))]
    have hdev : HasDerivWithinAt
        (fun r : ℝ => S.base.rm04 r x (vec4 (I := I) (e a) (e b) (e c) (e d)))
        (∑ I0 : Fin 4 → Fin 3, (∏ p : Fin 4, P (I0 p) (slots4 a b c d p)) *
          (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) f (identityInvMetric (Idx := Fin 3))
                (nablaKRm04Field (I := I) S (t : ℝ) 2 x))
              (fun i => f i) I0 +
            (-2 * (Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 2) (I0 3) -
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 1) (I0 3) (I0 2) +
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 2) (I0 1) (I0 3) -
                  Bt (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                    (I0 0) (I0 3) (I0 1) (I0 2)) -
              drift (fun i j : Fin 3 => S.ricciAt (t : ℝ) x (vec2 (I := I) (f i) (f j)))
                (I0 0) (I0 1) (I0 2) (I0 3)))) D.carrier (t : ℝ) := by
      rw [hfun]
      exact hmain
    simpa [hEq, e, solutionRm04CompInFrame, rm04Comp] using hdev
  exact hfin

end DifferentialGeometry.PDE.RicciFlow
