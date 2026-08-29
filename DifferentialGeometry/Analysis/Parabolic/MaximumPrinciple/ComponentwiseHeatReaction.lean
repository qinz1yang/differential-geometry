import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

universe u uE uH uι

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {ι : Type uι} [Fintype ι]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [Fintype ι] in
private lemma contMDiff_finsetSum_real
    {n : WithTop ℕ∞} {s : Finset ι} {f : ι → M → ℝ}
    (hs : ∀ i ∈ s, ContMDiff I 𝓘(Real, Real) n (f i)) :
    ContMDiff I 𝓘(Real, Real) n (fun x : M => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (contMDiff_const : ContMDiff I 𝓘(Real, Real) n (fun _ : M => (0 : ℝ)))
  | insert i s hi ih =>
      have hsum : ContMDiff I 𝓘(Real, Real) n (fun x : M => ∑ j ∈ s, f j x) :=
        ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      have hi' : ContMDiff I 𝓘(Real, Real) n (f i) := hs i (Finset.mem_insert_self i s)
      have hadd := hi'.add hsum
      change ContMDiff I 𝓘(Real, Real) n (fun x : M => f i x + ∑ j ∈ s, f j x) at hadd
      simpa only [Finset.sum_insert hi] using hadd

omit [CompleteSpace E] [Fintype ι] in
private lemma laplacianAt_finset_sum_real
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {t : Real} {s : Finset ι} {f : ι → M → ℝ}
    (hsmooth : ∀ i ∈ s, ContMDiff I 𝓘(Real, Real) ∞ (f i)) :
    laplacianAt (I := I) G t (fun x : M => ∑ i ∈ s, f i x) =
      fun x : M => ∑ i ∈ s, laplacianAt (I := I) G t (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext x
      simp only [Finset.sum_empty]
      change laplacian (I := I) (G.connection t) (G.metric t) (fun _ : M => (0 : ℝ)) x = 0
      exact laplacian_const (I := I) (G.connection t) (G.metric t) (0 : ℝ) x
  | insert i s hi ih =>
      have hsmooth_i : ContMDiff I 𝓘(Real, Real) ∞ (f i) :=
        hsmooth i (Finset.mem_insert_self i s)
      have hsmooth_s : ∀ j ∈ s, ContMDiff I 𝓘(Real, Real) ∞ (f j) :=
        fun j hj => hsmooth j (Finset.mem_insert_of_mem hj)
      have hsum_smooth : ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => ∑ j ∈ s, f j x) :=
        contMDiff_finsetSum_real hsmooth_s
      have hsum_lap := ih hsmooth_s
      funext x
      have hlap_add := laplacianAt_add (I := I) G (t := t)
        (f := f i) (h := fun x : M => ∑ j ∈ s, f j x) (x := x)
        (hsmooth_i.mdifferentiable (by simp))
        (hsum_smooth.mdifferentiable (by simp))
        (gradientFun_mdiffAt (I := I) (G.metric t) hsmooth_i x)
        (gradientFun_mdiffAt (I := I) (G.metric t) hsum_smooth x)
      have hsum_insert : (fun x : M => ∑ j ∈ insert i s, f j x) =
          fun x : M => f i x + ∑ j ∈ s, f j x := by
        funext y
        simp [Finset.sum_insert hi]
      rw [hsum_insert]
      rw [hlap_add]
      rw [hsum_lap]
      simp [Finset.sum_insert hi]

omit [CompleteSpace E] in
theorem innerProductHeatReactionOn_of_componentwise
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (u : Real → M → EuclideanSpace ℝ ι)
    (reaction : Real → M → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hjoint : ContinuousOn (fun q : Real × M => u q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hsmooth : ∀ i : ι, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => u t x i))
    (heq : ∀ i : ι, ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => u s x i)
        (laplacianAt (I := I) G t (fun y : M => u t y i) x + reaction t x (u t x) i) t) :
    IsInnerProductHeatReactionOn (D := D) (G := G)
      (F := EuclideanSpace ℝ ι) reaction u := by
  refine ⟨hjoint, ?_, ?_⟩
  · intro y t ht
    have hsum : (fun x : M => inner ℝ (u t x) y) =
        fun x : M => ∑ i : ι, y i * u t x i := by
      funext x
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl ?_
      intro i hi
      change y i * u t x i = y i * u t x i
      rfl
    change ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => inner ℝ (u t x) y)
    rw [hsum]
    apply contMDiff_finsetSum_real
    intro i hi
    exact (contMDiff_const.mul (hsmooth i t ht))
  · intro y t ht x
    have hsum_fun : (fun s : Real => inner ℝ (u s x) y) =
        fun s : Real => ∑ i : ι, y i * u s x i := by
      funext s
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl ?_
      intro i hi
      change y i * u s x i = y i * u s x i
      rfl
    change HasDerivAt (fun s : Real => inner ℝ (u s x) y)
      (laplacianAt (I := I) G t (fun x : M => inner ℝ (u t x) y) x +
        inner ℝ (reaction t x (u t x)) y) t
    rw [hsum_fun]
    have hderivs : ∀ i : ι, i ∈ Finset.univ → HasDerivAt (fun s : Real => y i * u s x i)
        (y i * (laplacianAt (I := I) G t (fun y : M => u t y i) x + reaction t x (u t x) i)) t := by
      intro i hi
      exact (heq i t ht x).const_mul (y i)
    have hsum_deriv := HasDerivAt.fun_sum (u := Finset.univ) hderivs
    have htarget :
        (∑ i : ι, y i * (laplacianAt (I := I) G t (fun y : M => u t y i) x + reaction t x (u t x) i)) =
          laplacianAt (I := I) G t (fun x : M => inner ℝ (u t x) y) x +
            inner ℝ (reaction t x (u t x)) y := by
      have hlap_sum : laplacianAt (I := I) G t (fun x : M => ∑ i : ι, y i * u t x i) x =
          ∑ i : ι, y i * laplacianAt (I := I) G t (fun y : M => u t y i) x := by
        have hsum_smooth : ∀ i : ι, i ∈ Finset.univ →
            ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => y i * u t x i) := by
          intro i hi
          exact (contMDiff_const.mul (hsmooth i t (D.regular_subset ht)))
        have hlap := congrFun (laplacianAt_finset_sum_real (t := t) G (s := Finset.univ)
          (f := fun (i : ι) (x : M) => y i * u t x i) hsum_smooth) x
        have hsmul : ∀ i : ι, laplacianAt (I := I) G t (fun x : M => y i * u t x i) x =
            y i * laplacianAt (I := I) G t (fun y : M => u t y i) x := by
          intro i
          have hmdiff : ∀ z : M, MDifferentiableAt I 𝓘(Real, Real) (fun x : M => u t x i) z :=
            (hsmooth i t (D.regular_subset ht)).mdifferentiable (by simp)
          have hgrad : MDiffAt (T% fun y : M =>
              gradientFun (I := I) (G.metric t) (fun x : M => u t x i) y) x :=
            gradientFun_mdiffAt (I := I) (G.metric t) (hsmooth i t (D.regular_subset ht)) x
          have hsmul := laplacianAt_smul (I := I) G (t := t) (a := y i)
            (f := fun x : M => u t x i) (x := x) hmdiff hgrad
          have hfun : (y i) • (fun x : M => u t x i) =
              (fun x : M => y i * u t x i) := by
            funext z
            exact smul_eq_mul (y i) (u t z i)
          rw [hfun] at hsmul
          exact hsmul
        calc
          laplacianAt (I := I) G t (fun x : M => ∑ i : ι, y i * u t x i) x
              = ∑ i : ι, laplacianAt (I := I) G t (fun x : M => y i * u t x i) x := hlap
          _ = ∑ i : ι, y i * laplacianAt (I := I) G t (fun y : M => u t y i) x := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hsmul i
      have hsum_eq : (fun x : M => ∑ i : ι, y i * u t x i) =
          fun x : M => inner ℝ (u t x) y := by
        funext z
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        change y i * u t z i = y i * u t z i
        rfl
      rw [← hsum_eq]
      rw [hlap_sum]
      have hinner : inner ℝ (reaction t x (u t x)) y = ∑ i : ι, y i * reaction t x (u t x) i := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        change y i * reaction t x (u t x) i = y i * reaction t x (u t x) i
        rfl
      rw [hinner]
      simp [Finset.sum_add_distrib, mul_add]
    rw [htarget] at hsum_deriv
    exact hsum_deriv

end DifferentialGeometry.Analysis.Parabolic

end
