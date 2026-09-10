import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TailRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.TimeRecursion
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.VariationInvariant

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology Bundle BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec3_update_zero {y : M} (p q r z : TangentSpace I y) :
    Function.update (vec3 (I := I) p q r) 0 z = vec3 (I := I) z q r := by
  funext a
  fin_cases a <;> simp [vec3, Function.update]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec3_update_one {y : M} (p q r z : TangentSpace I y) :
    Function.update (vec3 (I := I) p q r) 1 z = vec3 (I := I) p z r := by
  funext a
  fin_cases a <;> simp [vec3, Function.update]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem vec3_update_two {y : M} (p q r z : TangentSpace I y) :
    Function.update (vec3 (I := I) p q r) 2 z = vec3 (I := I) p q z := by
  funext a
  fin_cases a <;> simp [vec3, Function.update]



omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem inner_eq_sum_repr {Idx : Type} [Fintype Idx] {x : M}
    (g : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    g.inner x X Y = ∑ m, bas.repr X m * g.inner x (bas m) Y := by
  classical
  have hX : (∑ m, bas.repr X m • bas m) = X := bas.sum_repr X
  calc g.inner x X Y = g.inner x (∑ m, bas.repr X m • bas m) Y := by rw [hX]
    _ = ∑ m, bas.repr X m * g.inner x (bas m) Y := by
        rw [map_sum]
        simp

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem inner_eq_sum_repr_right {Idx : Type} [Fintype Idx] {x : M}
    (g : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    g.inner x X Y = ∑ m, bas.repr Y m * g.inner x X (bas m) := by
  classical
  rw [g.symm x X Y, inner_eq_sum_repr (I := I) g bas Y X]
  exact Finset.sum_congr rfl fun m _ => by rw [g.symm x (bas m) X]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem repr_eq_inner_of_orthonormal {Idx : Type} [Finite Idx]
    [DecidableEq Idx] {x : M}
    (g : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ k l, g.inner x (bas k) (bas l) = if k = l then (1 : Real) else 0)
    (X : TangentSpace I x) (l : Idx) :
    bas.repr X l = g.inner x X (bas l) := by
  classical
  have := Fintype.ofFinite Idx
  rw [inner_eq_sum_repr (I := I) g bas X (bas l)]
  simp [hON]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem clm2_eq_sum_repr {Idx : Type} [Fintype Idx] {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (u w : TangentSpace I x) :
    A u w = ∑ j, ∑ i, (bas.repr u j * bas.repr w i) • A (bas j) (bas i) := by
  classical
  have hu : (∑ j, bas.repr u j • bas j) = u := bas.sum_repr u
  have hw : (∑ i, bas.repr w i • bas i) = w := bas.sum_repr w
  have h1 : A u = ∑ j, bas.repr u j • A (bas j) := by
    calc A u = A (∑ j, bas.repr u j • bas j) := by rw [hu]
      _ = ∑ j, bas.repr u j • A (bas j) := by rw [map_sum]; simp
  have h2 : ∀ j : Idx, A (bas j) w = ∑ i, bas.repr w i • A (bas j) (bas i) := by
    intro j
    calc A (bas j) w = A (bas j) (∑ i, bas.repr w i • bas i) := by rw [hw]
      _ = ∑ i, bas.repr w i • A (bas j) (bas i) := by rw [map_sum]; simp
  calc A u w = (∑ j, bas.repr u j • A (bas j)) w := by rw [h1]
    _ = ∑ j, bas.repr u j • A (bas j) w := by
        simp
    _ = ∑ j, ∑ i, (bas.repr u j * bas.repr w i) • A (bas j) (bas i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h2 j, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem inner_sum2_left {Idx : Type} [Fintype Idx] {x : M}
    (g : SmoothRiemannianMetric I M) (c : Idx → Idx → Real)
    (W : Idx → Idx → TangentSpace I x) (P : TangentSpace I x) :
    g.inner x (∑ j, ∑ i, c j i • W j i) P = ∑ j, ∑ i, c j i * g.inner x (W j i) P := by
  classical
  have h1 : g.inner x (∑ j, ∑ i, c j i • W j i)
      = ∑ j, ∑ i, c j i • g.inner x (W j i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  rw [h1]
  simp

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem exists_metricOrthonormalBasis
    (g : SmoothRiemannianMetric I M) (y : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I y))) Real
        (TangentSpace I y),
      ∀ i j, g.inner y (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let Dat := (tangentMetricDataGen (I := I) g y).metric
  let _ : InnerProductSpace.Core Real (TangentSpace I y) := Dat.toCore
  let _ : NormedAddCommGroup (TangentSpace I y) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I y) _ _ _ Dat.toCore
  let _ : InnerProductSpace Real (TangentSpace I y) :=
    @InnerProductSpace.ofCore Real (TangentSpace I y) _ _ _ Dat.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I y)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = Dat.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner Dat (ob i) (ob j)
  change g.inner y (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricDataGen.inner_eq_gen
    (tangentMetricDataGen (I := I) g y) (ob.toBasis i) (ob.toBasis j)]
  change Dat.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

private theorem abs_le_two_mul_sum_of_absorb {Idx : Type} [Fintype Idx]
    (alpha beta : Idx → Real) (dd : Idx → Idx → Real)
    (hsplit : ∀ l, alpha l = beta l + ∑ m, alpha m * dd m l)
    (hclose : (∑ m, ∑ l, |dd m l|) ≤ 1 / 2) (k : Idx) :
    |alpha k| ≤ 2 * ∑ l, |beta l| := by
  classical
  set Phi : Real := ∑ l, |beta l| with hPhi
  have hPhi0 : 0 ≤ Phi := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : Real := ∑ l, alpha l * alpha l with hn
  have hn0 : 0 ≤ n := by
    rw [hn]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  set q : Real := Real.sqrt n with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = n := Real.mul_self_sqrt hn0
  have habs : ∀ l, |alpha l| ≤ q := by
    intro l
    have hle : alpha l * alpha l ≤ n := by
      rw [hn]
      exact Finset.single_le_sum (f := fun m => alpha m * alpha m)
        (fun m _ => mul_self_nonneg _) (Finset.mem_univ l)
    have h2 : |alpha l| * |alpha l| ≤ n := by
      rw [abs_mul_abs_self]
      exact hle
    nlinarith [abs_nonneg (alpha l), hq0, hqq]
  have hkey : n = (∑ l, alpha l * beta l) + ∑ l, ∑ m, alpha l * (alpha m * dd m l) := by
    rw [hn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    calc alpha l * alpha l = alpha l * (beta l + ∑ m, alpha m * dd m l) := by
          rw [← hsplit l]
      _ = alpha l * beta l + ∑ m, alpha l * (alpha m * dd m l) := by
          rw [mul_add, Finset.mul_sum]
  have hb1 : |∑ l, alpha l * beta l| ≤ q * Phi := by
    calc |∑ l, alpha l * beta l| ≤ ∑ l, |alpha l * beta l| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, q * |beta l| := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (habs l) (abs_nonneg _)
      _ = q * Phi := by rw [hPhi, Finset.mul_sum]
  have hb2 : |∑ l, ∑ m, alpha l * (alpha m * dd m l)| ≤ n * (1 / 2) := by
    have hstep : |∑ l, ∑ m, alpha l * (alpha m * dd m l)| ≤
        ∑ l, ∑ m, n * |dd m l| := by
      calc |∑ l, ∑ m, alpha l * (alpha m * dd m l)|
          ≤ ∑ l, |∑ m, alpha l * (alpha m * dd m l)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, ∑ m, n * |dd m l| := by
            refine Finset.sum_le_sum fun l _ => ?_
            calc |∑ m, alpha l * (alpha m * dd m l)|
                ≤ ∑ m, |alpha l * (alpha m * dd m l)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ m, n * |dd m l| := by
                  refine Finset.sum_le_sum fun m _ => ?_
                  rw [abs_mul, abs_mul]
                  have hpos : 0 ≤ |alpha m| * |dd m l| :=
                    mul_nonneg (abs_nonneg _) (abs_nonneg _)
                  have hm : |alpha m| * |dd m l| ≤ q * |dd m l| :=
                    mul_le_mul_of_nonneg_right (habs m) (abs_nonneg _)
                  calc |alpha l| * (|alpha m| * |dd m l|)
                      ≤ q * (|alpha m| * |dd m l|) :=
                        mul_le_mul_of_nonneg_right (habs l) hpos
                    _ ≤ q * (q * |dd m l|) := mul_le_mul_of_nonneg_left hm hq0
                    _ = n * |dd m l| := by rw [← mul_assoc, hqq]
    have hsum : (∑ l, ∑ m, n * |dd m l|) = n * ∑ m, ∑ l, |dd m l| := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
    refine hstep.trans ?_
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hclose hn0
  have hfinal : n ≤ q * Phi + n * (1 / 2) := by
    have h := abs_le.mp hb1
    have h' := abs_le.mp hb2
    rw [hkey]
    linarith [h.2, h'.2]
  have hqle : q ≤ 2 * Phi := by
    rcases eq_or_lt_of_le hq0 with hz | hpos
    · nlinarith [hPhi0]
    · nlinarith [hqq, hpos]
  exact (habs k).trans hqle

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
private theorem abs_inner_le_of_gram_close {Idx : Type} [Fintype Idx]
    [DecidableEq Idx] {x : M}
    (gs gr : SmoothRiemannianMetric I M)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ k l, gs.inner x (bas k) (bas l) = if k = l then (1 : Real) else 0)
    (hclose : (∑ k, ∑ m, |gs.inner x (bas k) (bas m) - gr.inner x (bas k) (bas m)|)
      ≤ 1 / 2)
    (X : TangentSpace I x) (k : Idx) :
    |gs.inner x X (bas k)| ≤ 2 * ∑ l, |gr.inner x X (bas l)| := by
  classical
  have hrep : ∀ l, bas.repr X l = gs.inner x X (bas l) :=
    fun l => repr_eq_inner_of_orthonormal (I := I) gs bas hON X l
  have hsplit : ∀ l, gs.inner x X (bas l) =
      gr.inner x X (bas l) +
        ∑ m, gs.inner x X (bas m) *
          (gs.inner x (bas m) (bas l) - gr.inner x (bas m) (bas l)) := by
    intro l
    have h1 : gs.inner x X (bas l) =
        ∑ m, gs.inner x X (bas m) * gs.inner x (bas m) (bas l) := by
      rw [inner_eq_sum_repr (I := I) gs bas X (bas l)]
      exact Finset.sum_congr rfl fun m _ => by rw [hrep m]
    have h2 : gr.inner x X (bas l) =
        ∑ m, gs.inner x X (bas m) * gr.inner x (bas m) (bas l) := by
      rw [inner_eq_sum_repr (I := I) gr bas X (bas l)]
      exact Finset.sum_congr rfl fun m _ => by rw [hrep m]
    have h3 : (∑ m, gs.inner x X (bas m) *
          (gs.inner x (bas m) (bas l) - gr.inner x (bas m) (bas l))) =
        (∑ m, gs.inner x X (bas m) * gs.inner x (bas m) (bas l)) -
          ∑ m, gs.inner x X (bas m) * gr.inner x (bas m) (bas l) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h3, ← h1, ← h2]
    ring
  exact abs_le_two_mul_sum_of_absorb (fun l => gs.inner x X (bas l))
    (fun l => gr.inner x X (bas l))
    (fun a b => gs.inner x (bas a) (bas b) - gr.inner x (bas a) (bas b))
    hsplit hclose k



private theorem hasDerivWithinAt_zero_of_vanishing_product
    {K : Set Real} {s : Real} {a c : Real → Real} {c' : Real}
    (ha0 : a s = 0) (hc0 : c s = 0)
    (ha : Tendsto a (nhdsWithin s K) (nhds 0))
    (hc : HasDerivWithinAt c c' K s) :
    HasDerivWithinAt (fun r : Real => a r * c r) 0 K s := by
  have hslope : Tendsto (slope c s) (nhdsWithin s (K \ {s})) (nhds c') :=
    hasDerivWithinAt_iff_tendsto_slope.mp hc
  have ha' : Tendsto a (nhdsWithin s (K \ {s})) (nhds 0) :=
    ha.mono_left (nhdsWithin_mono s Set.sdiff_subset)
  have hmul : Tendsto (fun r : Real => a r * slope c s r)
      (nhdsWithin s (K \ {s})) (nhds (0 * c')) := ha'.mul hslope
  rw [zero_mul] at hmul
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine hmul.congr fun r => ?_
  rw [slope_def_field, slope_def_field, ha0, hc0]
  ring



omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem hasDerivWithinAt_initialMetric_pairing
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K : Set Real} {s : Real} {x : M}
    (V : Real → TangentSpace I x) (hV0 : V s = 0)
    (Z : TangentSpace I x)
    (hF : ∀ P : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (S.base.metric r).inner x (V r) P)
        ((S.base.metric s).inner x Z P) K s)
    (hgram : ∀ P Q : TangentSpace I x,
      DifferentiableWithinAt Real
        (fun r : Real => (S.base.metric r).inner x P Q) K s)
    (v : TangentSpace I x) :
    HasDerivWithinAt (fun r : Real => (S.base.metric 0).inner x (V r) v)
      ((S.base.metric 0).inner x Z v) K s := by
  classical
  obtain ⟨bas, hON⟩ := exists_metricOrthonormalBasis (I := I) (S.base.metric s) x
  set mu : Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun l => (S.base.metric 0).inner x (bas l) v with hmu
  have hkey : ∀ W : TangentSpace I x,
      (S.base.metric 0).inner x W v =
        ∑ l, mu l * (S.base.metric s).inner x W (bas l) := by
    intro W
    rw [inner_eq_sum_repr (I := I) (S.base.metric 0) bas W v]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [repr_eq_inner_of_orthonormal (I := I) (S.base.metric s) bas hON W l, hmu]
    ring
  set alpha : Real → Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun r k => (S.base.metric s).inner x (V r) (bas k) with halpha
  set dd : Real → Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun r a b => (S.base.metric s).inner x (bas a) (bas b) -
      (S.base.metric r).inner x (bas a) (bas b) with hdd
  set gam : Real → Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun r k => ∑ l, mu l * dd r k l with hgam
  have hdecomp : ∀ r : Real,
      (S.base.metric 0).inner x (V r) v =
        (∑ l, mu l * (S.base.metric r).inner x (V r) (bas l)) +
          ∑ k, alpha r k * gam r k := by
    intro r
    have hexp : ∀ l,
        (S.base.metric s).inner x (V r) (bas l) -
            (S.base.metric r).inner x (V r) (bas l) =
          ∑ k, alpha r k * dd r k l := by
      intro l
      have h1 := inner_eq_sum_repr (I := I) (S.base.metric s) bas (V r) (bas l)
      have h2 := inner_eq_sum_repr (I := I) (S.base.metric r) bas (V r) (bas l)
      have hrep : ∀ k, bas.repr (V r) k = alpha r k := fun k =>
        repr_eq_inner_of_orthonormal (I := I) (S.base.metric s) bas hON (V r) k
      rw [h1, h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hrep k, hdd]
      ring
    have hswap : (∑ l, mu l * ∑ k, alpha r k * dd r k l) =
        ∑ k, alpha r k * gam r k := by
      have h1 : (∑ l, mu l * ∑ k, alpha r k * dd r k l)
          = ∑ l, ∑ k, mu l * (alpha r k * dd r k l) :=
        Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hgam, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hkey (V r), ← hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_add, ← hexp l]
    ring
  have halpha0 : ∀ k, alpha s k = 0 := by
    intro k
    simp only [halpha, hV0]
    simp
  have hgam0 : ∀ k, gam s k = 0 := by
    intro k
    simp only [hgam, hdd]
    simp
  have hddDiff : ∀ a b, DifferentiableWithinAt Real (fun r : Real => dd r a b) K s := by
    intro a b
    simp only [hdd]
    exact (differentiableWithinAt_const _).sub (hgram (bas a) (bas b))
  have hgamDiff : ∀ k, DifferentiableWithinAt Real (fun r : Real => gam r k) K s := by
    intro k
    have hfun : (∑ l ∈ (Finset.univ :
          Finset (Fin (Module.finrank Real (TangentSpace I x)))),
          fun r : Real => mu l * dd r k l)
        = fun r : Real => ∑ l, mu l * dd r k l := by
      funext r
      simp
    have h := DifferentiableWithinAt.sum (u := (Finset.univ :
      Finset (Fin (Module.finrank Real (TangentSpace I x)))))
      (fun l _ => (hddDiff k l).const_mul (mu l))
    rw [hfun] at h
    simpa only [hgam] using h
  have hddZero : ∀ a b, dd s a b = 0 := by
    intro a b
    simp only [hdd]
    simp
  have halphaTend : ∀ k, Tendsto (fun r : Real => alpha r k) (nhdsWithin s K) (nhds 0) := by
    intro k
    have hddTend : ∀ a b, Tendsto (fun r : Real => |dd r a b|) (nhdsWithin s K) (nhds 0) := by
      intro a b
      have hc : Tendsto (fun r : Real => dd r a b) (nhdsWithin s K) (nhds (dd s a b)) :=
        (hddDiff a b).continuousWithinAt
      rw [hddZero a b] at hc
      simpa using hc.abs
    have hGapTend : Tendsto (fun r : Real => ∑ a, ∑ b, |dd r a b|)
        (nhdsWithin s K) (nhds 0) := by
      have h1 : ∀ a, Tendsto (fun r : Real => ∑ b, |dd r a b|)
          (nhdsWithin s K) (nhds 0) := by
        intro a
        have h := tendsto_finsetSum (Finset.univ) (fun b (_ : b ∈ Finset.univ) => hddTend a b)
        simpa using h
      have h := tendsto_finsetSum (Finset.univ) (fun a (_ : a ∈ Finset.univ) => h1 a)
      simpa using h
    have hnb : ∀ᶠ y : Real in nhds (0 : Real), y ≤ 1 / 2 := by
      filter_upwards [gt_mem_nhds (show (0 : Real) < 1 / 2 by norm_num)] with y hy
      exact le_of_lt hy
    have hev : ∀ᶠ r in nhdsWithin s K, (∑ a, ∑ b, |dd r a b|) ≤ 1 / 2 :=
      hGapTend.eventually hnb
    have hPsiTend : Tendsto
        (fun r : Real => 2 * ∑ l, |(S.base.metric r).inner x (V r) (bas l)|)
        (nhdsWithin s K) (nhds 0) := by
      have hcont : ∀ l, Tendsto
          (fun r : Real => |(S.base.metric r).inner x (V r) (bas l)|)
          (nhdsWithin s K) (nhds 0) := by
        intro l
        have hc : Tendsto (fun r : Real => (S.base.metric r).inner x (V r) (bas l))
            (nhdsWithin s K) (nhds ((S.base.metric s).inner x (V s) (bas l))) :=
          (hF (bas l)).continuousWithinAt
        rw [hV0] at hc
        simpa using hc.abs
      have h := tendsto_finsetSum (Finset.univ) (fun l (_ : l ∈ Finset.univ) => hcont l)
      have h2 : Tendsto (fun r : Real => ∑ l, |(S.base.metric r).inner x (V r) (bas l)|)
          (nhdsWithin s K) (nhds 0) := by simpa using h
      simpa using h2.const_mul (2 : Real)
    refine squeeze_zero_norm' ?_ hPsiTend
    filter_upwards [hev] with r hr
    have hbound := abs_inner_le_of_gram_close (I := I) (S.base.metric s)
      (S.base.metric r) bas hON (by simpa [hdd] using hr) (V r) k
    simpa only [halpha, Real.norm_eq_abs] using hbound
  have hH1 : HasDerivWithinAt
      (fun r : Real => ∑ l, mu l * (S.base.metric r).inner x (V r) (bas l))
      (∑ l, mu l * (S.base.metric s).inner x Z (bas l)) K s := by
    have hfun : (∑ l ∈ (Finset.univ :
          Finset (Fin (Module.finrank Real (TangentSpace I x)))),
          fun r : Real => mu l * (S.base.metric r).inner x (V r) (bas l))
        = fun r : Real => ∑ l, mu l * (S.base.metric r).inner x (V r) (bas l) := by
      funext r
      simp
    have h := HasDerivWithinAt.sum (u := (Finset.univ :
      Finset (Fin (Module.finrank Real (TangentSpace I x)))))
      (fun l _ => (hF (bas l)).const_mul (mu l))
    rwa [hfun] at h
  have hH2 : HasDerivWithinAt (fun r : Real => ∑ k, alpha r k * gam r k) 0 K s := by
    have hterm : ∀ k, HasDerivWithinAt (fun r : Real => alpha r k * gam r k) 0 K s := by
      intro k
      exact hasDerivWithinAt_zero_of_vanishing_product (halpha0 k) (hgam0 k)
        (halphaTend k) (hgamDiff k).hasDerivWithinAt
    have hfun : (∑ k ∈ (Finset.univ :
          Finset (Fin (Module.finrank Real (TangentSpace I x)))),
          fun r : Real => alpha r k * gam r k)
        = fun r : Real => ∑ k, alpha r k * gam r k := by
      funext r
      simp
    have h := HasDerivWithinAt.sum (u := (Finset.univ :
      Finset (Fin (Module.finrank Real (TangentSpace I x)))))
      (fun k _ => hterm k)
    rw [hfun] at h
    simpa using h
  have hsum := hH1.add hH2
  have hval : (∑ l, mu l * (S.base.metric s).inner x Z (bas l)) + 0
      = (S.base.metric 0).inner x Z v := by
    rw [add_zero, ← hkey Z]
  exact (hsum.congr (fun r _ => hdecomp r) (hdecomp s)).congr_deriv hval


private theorem hasDerivWithinAt_finsum {J : Type} [Fintype J]
    {K : Set Real} {s : Real} (f : J → Real → Real) (f' : J → Real)
    (h : ∀ i, HasDerivWithinAt (f i) (f' i) K s) :
    HasDerivWithinAt (fun r : Real => ∑ i, f i r) (∑ i, f' i) K s := by
  classical
  have hfun : (∑ i ∈ (Finset.univ : Finset J), f i) = fun r : Real => ∑ i, f i r := by
    funext r
    simp
  have hh := HasDerivWithinAt.sum (u := (Finset.univ : Finset J)) (fun i _ => h i)
  rwa [hfun] at hh


private theorem sum3_neg_sub_add {Idx : Type} [Fintype Idx]
    (F G Hh : Idx → Idx → Idx → Real) :
    (∑ j, ∑ i, ∑ l, (-(F j i l) - G j i l + Hh j i l))
      = -(∑ j, ∑ i, ∑ l, F j i l) - (∑ j, ∑ i, ∑ l, G j i l)
        + ∑ j, ∑ i, ∑ l, Hh j i l := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]



omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor3_expand_slot0 {Idx : Type} [Fintype Idx] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (A B C : TangentSpace I x) :
    T (vec3 (I := I) A B C) = ∑ i, bas.repr A i * T (vec3 (I := I) (bas i) B C) := by
  classical
  have h0 : Function.update (vec3 (I := I) A B C) 0 (∑ i, bas.repr A i • bas i)
      = vec3 (I := I) A B C := by
    rw [bas.sum_repr A, vec3_update_zero]
  have hms : T (Function.update (vec3 (I := I) A B C) 0 (∑ i, bas.repr A i • bas i))
      = ∑ i, T (Function.update (vec3 (I := I) A B C) 0 (bas.repr A i • bas i)) :=
    T.toMultilinearMap.map_update_sum Finset.univ 0
      (fun i => bas.repr A i • bas i) (vec3 (I := I) A B C)
  rw [← h0, hms]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [T.map_update_smul, vec3_update_zero]
  simp

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor3_expand_slot1 {Idx : Type} [Fintype Idx] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (A B C : TangentSpace I x) :
    T (vec3 (I := I) A B C) = ∑ i, bas.repr B i * T (vec3 (I := I) A (bas i) C) := by
  classical
  have h0 : Function.update (vec3 (I := I) A B C) 1 (∑ i, bas.repr B i • bas i)
      = vec3 (I := I) A B C := by
    rw [bas.sum_repr B, vec3_update_one]
  have hms : T (Function.update (vec3 (I := I) A B C) 1 (∑ i, bas.repr B i • bas i))
      = ∑ i, T (Function.update (vec3 (I := I) A B C) 1 (bas.repr B i • bas i)) :=
    T.toMultilinearMap.map_update_sum Finset.univ 1
      (fun i => bas.repr B i • bas i) (vec3 (I := I) A B C)
  rw [← h0, hms]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [T.map_update_smul, vec3_update_one]
  simp

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor3_expand_slot2 {Idx : Type} [Fintype Idx] {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (bas : Module.Basis Idx Real (TangentSpace I x))
    (A B C : TangentSpace I x) :
    T (vec3 (I := I) A B C) = ∑ i, bas.repr C i * T (vec3 (I := I) A B (bas i)) := by
  classical
  have h0 : Function.update (vec3 (I := I) A B C) 2 (∑ i, bas.repr C i • bas i)
      = vec3 (I := I) A B C := by
    rw [bas.sum_repr C, vec3_update_two]
  have hms : T (Function.update (vec3 (I := I) A B C) 2 (∑ i, bas.repr C i • bas i))
      = ∑ i, T (Function.update (vec3 (I := I) A B C) 2 (bas.repr C i • bas i)) :=
    T.toMultilinearMap.map_update_sum Finset.univ 2
      (fun i => bas.repr C i • bas i) (vec3 (I := I) A B C)
  rw [← h0, hms]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [T.map_update_smul, vec3_update_two]
  simp



omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hasDerivWithinAt_connectionDifference_pairing
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {K : Set Real} (hK : K ⊆ D.carrier) {s : Real} (hs : s ∈ D.regular)
    (x : M) (u w v : TangentSpace I x) :
    HasDerivWithinAt
      (fun r : Real => (S.base.metric 0).inner x
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric r))
          (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
      ((S.base.metric 0).inner x (connectionVariationSpeed (I := I) S s x u w) v)
      K s := by
  classical
  set ee := trivializationAt E (TangentSpace I : M → Type _) x with hee
  set fb := Module.finBasis Real E with hfb
  set frame := ee.localFrame fb with hfrdef
  have hxe : x ∈ ee.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  have hUopen : IsOpen ee.baseSet := ee.open_baseSet
  have hframeTop : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame ee.baseSet :=
    Bundle.Trivialization.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) ee fb
  have hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame ee.baseSet :=
    { linearIndependent := hframeTop.linearIndependent
      generating := hframeTop.generating
      contMDiffOn := fun i =>
        (hframeTop.contMDiffOn i).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞) }
  set bas := hframe.toBasisAt hxe with hbasdef
  have hbasval : ∀ i, bas i = frame i x := fun i => hframe.toBasisAt_coe hxe i
  have hSmooth : ∀ a b : Fin (Module.finrank Real E), ∀ t, t ∈ D.regular →
      ∀ y : M, y ∈ ee.baseSet →
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M =>
          (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, y) := by
    intro a b t ht y hy
    have hcomp := hS.smoothMetric.frameCompSmooth
      (Idx := Fin (Module.finrank Real E)) frame hframeTop a b
    have hn : D.regular ×ˢ ee.baseSet ∈ nhds ((t, y) : Real × M) :=
      (D.regular_isOpen.prod hUopen).mem_nhds ⟨ht, hy⟩
    exact (hcomp.contMDiffAt hn).of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hFdiff : ∀ a b : Fin (Module.finrank Real E), ∀ r, r ∈ D.carrier →
      ∀ y : M, y ∈ ee.baseSet →
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => (S.family.metric r).inner z (frame a z) (frame b z)) y := by
    intro a b r _hr y hy
    obtain ⟨sec, hsec⟩ := hframeTop.exists_contMDiffSection_eqOn_nhd hUopen hy
    refine (metricInner_mdiffAt (I := I) (S.family.metric r)
      (sec a).contMDiff (sec b).contMDiff y).congr_of_eventuallyEq ?_
    filter_upwards [hsec] with z hz
    rw [hz a, hz b]
  have hFtdiff : ∀ a b : Fin (Module.finrank Real E), ∀ t, t ∈ D.regular →
      ∀ y : M, y ∈ ee.baseSet →
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => ricciCompInFrame (I := I) S frame t z a b) y := by
    intro a b t _ht y hy
    obtain ⟨sec, hsec⟩ := hframeTop.exists_contMDiffSection_eqOn_nhd hUopen hy
    have hscalar : ContMDiff I 𝓘(Real, Real) ∞
        (fun z : M => ricciTensor (I := I) (S.base.metric t) z (sec a z) (sec b z)) :=
      ricciTensor_pairing_contMDiff (I := I) (S.base.metric t)
        (sec a).contMDiff (sec b).contMDiff
    refine ((hscalar y).congr_of_eventuallyEq ?_).mdifferentiableAt (by simp)
    filter_upwards [hsec] with z hz
    rw [hz a, hz b]
    simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := I)
        (S.base.metric t) z (frame a z) (frame b z)
  have hmcd := metricCovDerivDeriv_of_solution (I := I) S hS frame hSmooth hFdiff hFtdiff
  have hvar := variableMetricConnectionDiffDerivative_of_metricCovDeriv (I := I) S frame
    hframe hUopen
    (fun t y d a b => (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame t y d a b)
    (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b)
    hmcd
    (metricCovDerivDerivativeIsRicciFlowInFrame_neg_two (M := M)
      (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b))
  have hnab : ∀ d a b : Fin (Module.finrank Real E),
      ricciCovDerivCompInFrame (I := I) S frame s x d a b
        = nablaRicci (I := I) S s x (vec3 (I := I) (bas d) (bas a) (bas b)) := by
    intro d a b
    rw [hbasval d, hbasval a, hbasval b,
      ← nablaRicReal_frame (I := I) S s frame hframe hUopen hxe d a b]
    rfl
  set Diff : Real →
      (TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :=
    fun r => CovariantDerivative.difference (LeviCivita (I := I) (S.base.metric r))
      (LeviCivita (I := I) (S.base.metric 0)) x with hDiff
  set V : Real → TangentSpace I x := fun r => Diff r u w - Diff s u w with hV
  have hV0 : V s = 0 := by simp [hV]
  have hbridge : ∀ (r : Real) (i j : Fin (Module.finrank Real E)),
      connectionDiffVectorInFrame (I := I) S frame s r x i j
        = Diff r (bas j) (bas i) - Diff s (bas j) (bas i) := by
    intro r i j
    have hfj : MDiffAt (T% (frame j)) x :=
      (hframe.contMDiffAt hUopen hxe j).mdifferentiableAt one_ne_zero
    have h1 := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply (I := I)
      (S.base.metric r) (S.base.metric 0) hfj (frame i x)
    have h2 := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply (I := I)
      (S.base.metric s) (S.base.metric 0) hfj (frame i x)
    simp only [DifferentialGeometry.PDE.DeTurck.connectionDifference] at h1 h2
    simp only [hDiff, hbasval]
    rw [h1, h2]
    simp only [connectionDiffVectorInFrame, SolutionOn.family_connection]
    abel
  have hVsum : ∀ r : Real, V r = ∑ j, ∑ i,
      (bas.repr u j * bas.repr w i) •
        connectionDiffVectorInFrame (I := I) S frame s r x i j := by
    intro r
    calc V r = Diff r u w - Diff s u w := by simp only [hV]
      _ = (∑ j, ∑ i, (bas.repr u j * bas.repr w i) • Diff r (bas j) (bas i))
            - ∑ j, ∑ i, (bas.repr u j * bas.repr w i) • Diff s (bas j) (bas i) := by
          rw [← clm2_eq_sum_repr (I := I) (Diff r) bas u w,
            ← clm2_eq_sum_repr (I := I) (Diff s) bas u w]
      _ = ∑ j, ∑ i, (bas.repr u j * bas.repr w i) •
            connectionDiffVectorInFrame (I := I) S frame s r x i j := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← smul_sub, ← hbridge r i j]
  have hFall : ∀ P : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (S.base.metric r).inner x (V r) P)
        ((S.base.metric s).inner x (connectionVariationSpeed (I := I) S s x u w) P)
        D.carrier s := by
    intro P
    have hfunval : ∀ r : Real, (S.base.metric r).inner x (V r) P
        = ∑ j, ∑ i, ∑ l,
            (bas.repr u j * bas.repr w i * bas.repr P l) *
              connectionDiffLoweredInFrame (I := I) S frame r s r x i j l := by
      intro r
      rw [hVsum r, inner_sum2_left (I := I) (S.base.metric r)
        (fun j i => bas.repr u j * bas.repr w i)
        (fun j i => connectionDiffVectorInFrame (I := I) S frame s r x i j) P]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_eq_sum_repr_right (I := I) (S.base.metric r) bas
        (connectionDiffVectorInFrame (I := I) S frame s r x i j) P, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hl : (S.base.metric r).inner x
            (connectionDiffVectorInFrame (I := I) S frame s r x i j) (bas l)
          = connectionDiffLoweredInFrame (I := I) S frame r s r x i j l := by
        rw [hbasval l]
        rfl
      rw [hl]
      ring
    have hd := hasDerivWithinAt_finsum
      (fun j r => ∑ i, ∑ l,
        (bas.repr u j * bas.repr w i * bas.repr P l) *
          connectionDiffLoweredInFrame (I := I) S frame r s r x i j l)
      (fun j => ∑ i, ∑ l,
        (bas.repr u j * bas.repr w i * bas.repr P l) *
          christoffelVariationLoweredRHSInFrame
            (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b)
            s x i j l)
      (fun j => hasDerivWithinAt_finsum _ _ (fun i =>
        hasDerivWithinAt_finsum _ _ (fun l =>
          (hvar ⟨s, hs⟩ x hxe i j l).const_mul
            (bas.repr u j * bas.repr w i * bas.repr P l))))
    have hkoszul : (S.base.metric s).inner x
          (connectionVariationSpeed (I := I) S s x u w) P
        = -(nablaRicci (I := I) S s x (vec3 (I := I) u w P))
            - nablaRicci (I := I) S s x (vec3 (I := I) w u P)
            + nablaRicci (I := I) S s x (vec3 (I := I) P u w) :=
      inner_metricSharp (I := I) (S.base.metric s) x
        (koszulRicciCovector (I := I) (nablaRicci (I := I) S s x) u w) P
    have hT1 : (∑ j, ∑ i, ∑ l,
          (bas.repr u j * bas.repr w i * bas.repr P l) *
            nablaRicci (I := I) S s x (vec3 (I := I) (bas i) (bas j) (bas l)))
        = nablaRicci (I := I) S s x (vec3 (I := I) w u P) := by
      rw [tensor3_expand_slot1 (I := I) (nablaRicci (I := I) S s x) bas w u P]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tensor3_expand_slot0 (I := I) (nablaRicci (I := I) S s x) bas w (bas j) P,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensor3_expand_slot2 (I := I) (nablaRicci (I := I) S s x) bas
        (bas i) (bas j) P, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hT2 : (∑ j, ∑ i, ∑ l,
          (bas.repr u j * bas.repr w i * bas.repr P l) *
            nablaRicci (I := I) S s x (vec3 (I := I) (bas j) (bas i) (bas l)))
        = nablaRicci (I := I) S s x (vec3 (I := I) u w P) := by
      rw [tensor3_expand_slot0 (I := I) (nablaRicci (I := I) S s x) bas u w P]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tensor3_expand_slot1 (I := I) (nablaRicci (I := I) S s x) bas (bas j) w P,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensor3_expand_slot2 (I := I) (nablaRicci (I := I) S s x) bas
        (bas j) (bas i) P, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hT3 : (∑ j, ∑ i, ∑ l,
          (bas.repr u j * bas.repr w i * bas.repr P l) *
            nablaRicci (I := I) S s x (vec3 (I := I) (bas l) (bas i) (bas j)))
        = nablaRicci (I := I) S s x (vec3 (I := I) P u w) := by
      have hsymm : nablaRicci (I := I) S s x (vec3 (I := I) P w u)
          = nablaRicci (I := I) S s x (vec3 (I := I) P u w) :=
        metricNablaRic_last_two_symm (I := I) (S.base.metric s) x P w u
      rw [← hsymm, tensor3_expand_slot2 (I := I) (nablaRicci (I := I) S s x) bas P w u]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tensor3_expand_slot1 (I := I) (nablaRicci (I := I) S s x) bas P w (bas j),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensor3_expand_slot0 (I := I) (nablaRicci (I := I) S s x) bas
        P (bas i) (bas j), Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hvalue : (∑ j, ∑ i, ∑ l,
          (bas.repr u j * bas.repr w i * bas.repr P l) *
            christoffelVariationLoweredRHSInFrame
              (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b)
              s x i j l)
        = (S.base.metric s).inner x
            (connectionVariationSpeed (I := I) S s x u w) P := by
      have hterm : ∀ j i l : Fin (Module.finrank Real E),
          christoffelVariationLoweredRHSInFrame
              (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b)
              s x i j l
            = -(nablaRicci (I := I) S s x (vec3 (I := I) (bas i) (bas j) (bas l)))
              - nablaRicci (I := I) S s x (vec3 (I := I) (bas j) (bas i) (bas l))
              + nablaRicci (I := I) S s x (vec3 (I := I) (bas l) (bas i) (bas j)) := by
        intro j i l
        simp only [christoffelVariationLoweredRHSInFrame, hnab]
      calc (∑ j, ∑ i, ∑ l,
              (bas.repr u j * bas.repr w i * bas.repr P l) *
                christoffelVariationLoweredRHSInFrame
                  (fun t y d a b => ricciCovDerivCompInFrame (I := I) S frame t y d a b)
                  s x i j l)
          = ∑ j, ∑ i, ∑ l,
              (-((bas.repr u j * bas.repr w i * bas.repr P l) *
                    nablaRicci (I := I) S s x (vec3 (I := I) (bas i) (bas j) (bas l)))
                - (bas.repr u j * bas.repr w i * bas.repr P l) *
                    nablaRicci (I := I) S s x (vec3 (I := I) (bas j) (bas i) (bas l))
                + (bas.repr u j * bas.repr w i * bas.repr P l) *
                    nablaRicci (I := I) S s x (vec3 (I := I) (bas l) (bas i) (bas j))) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun l _ => ?_
            rw [hterm j i l]
            ring
        _ = -(∑ j, ∑ i, ∑ l,
                (bas.repr u j * bas.repr w i * bas.repr P l) *
                  nablaRicci (I := I) S s x (vec3 (I := I) (bas i) (bas j) (bas l)))
              - (∑ j, ∑ i, ∑ l,
                (bas.repr u j * bas.repr w i * bas.repr P l) *
                  nablaRicci (I := I) S s x (vec3 (I := I) (bas j) (bas i) (bas l)))
              + ∑ j, ∑ i, ∑ l,
                (bas.repr u j * bas.repr w i * bas.repr P l) *
                  nablaRicci (I := I) S s x (vec3 (I := I) (bas l) (bas i) (bas j)) :=
            sum3_neg_sub_add _ _ _
        _ = (S.base.metric s).inner x
              (connectionVariationSpeed (I := I) S s x u w) P := by
            rw [hT1, hT2, hT3, hkoszul]
            ring
    rw [← hvalue]
    exact hd.congr (fun r _ => hfunval r) (hfunval s)
  have hgram : ∀ P Q : TangentSpace I x,
      DifferentiableWithinAt Real
        (fun r : Real => (S.base.metric r).inner x P Q) D.carrier s :=
    fun P Q => (metric_derivWithin_eq_neg_two_ricci (I := I) S hS ⟨s, hs⟩ x P
      Q).differentiableWithinAt
  have hmain := hasDerivWithinAt_initialMetric_pairing (I := I) S V hV0
    (connectionVariationSpeed (I := I) S s x u w) hFall hgram v
  have hshift := hmain.add_const ((S.base.metric 0).inner x (Diff s u w) v)
  have hfinal : HasDerivWithinAt
      (fun r : Real => (S.base.metric 0).inner x (Diff r u w) v)
      ((S.base.metric 0).inner x (connectionVariationSpeed (I := I) S s x u w) v)
      D.carrier s := by
    refine hshift.congr (fun r _ => ?_) ?_
    · simp [hV]
    · simp [hV]
  exact hfinal.mono hK



omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem connectionDifferenceTimeDerivativeOn_connectionVariationSpeed
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {T : Real}
    (hregular : Set.Icc (0 : Real) T ⊆ D.regular) :
    ConnectionDifferenceTimeDerivativeOn (I := I) S T
      (connectionVariationSpeed (I := I) S) := by
  intro s hsmem x u w v
  exact hasDerivWithinAt_connectionDifference_pairing (I := I) S hS
    (hregular.trans D.regular_subset) (hregular hsmem) x u w v

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hasDerivWithinAt_connectionDifference_pairing_of_mem_Ioc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {T : Real}
    (hcarrier : Set.Icc (0 : Real) T ⊆ D.carrier)
    (hregular : Set.Ioc (0 : Real) T ⊆ D.regular)
    {s : Real} (hs : s ∈ Set.Ioc (0 : Real) T)
    (x : M) (u w v : TangentSpace I x) :
    HasDerivWithinAt
      (fun r : Real => (S.base.metric 0).inner x
        (CovariantDerivative.difference
          (LeviCivita (I := I) (S.base.metric r))
          (LeviCivita (I := I) (S.base.metric 0)) x u w) v)
      ((S.base.metric 0).inner x (connectionVariationSpeed (I := I) S s x u w) v)
      (Set.Icc (0 : Real) T) s :=
  hasDerivWithinAt_connectionDifference_pairing (I := I) S hS hcarrier
    (hregular hs) x u w v

def ConnectionVariationSpeedTimeContinuousOn
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Z : Real → (y : M) → TangentSpace I y → TangentSpace I y → TangentSpace I y) :
    Prop :=
  ∀ x : M, ∀ u w v : TangentSpace I x,
    ContinuousOn (fun s : Real => (S.base.metric 0).inner x (Z s x u w) v)
      (Set.Icc (0 : Real) T)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem connectionDifferenceTimeIntegralOn_connectionVariationSpeed
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {T : Real}
    (hregular : Set.Icc (0 : Real) T ⊆ D.regular)
    (hcont : ConnectionVariationSpeedTimeContinuousOn (I := I) S T
      (connectionVariationSpeed (I := I) S)) :
    ConnectionDifferenceTimeIntegralOn (I := I) S T
      (connectionVariationSpeed (I := I) S) :=
  connectionDifferenceTimeIntegralOn_of_hasDerivWithinAt (I := I) S
    (connectionDifferenceTimeDerivativeOn_connectionVariationSpeed
      (I := I) S hS hregular) hcont

end DifferentialGeometry.PDE.RicciFlow
