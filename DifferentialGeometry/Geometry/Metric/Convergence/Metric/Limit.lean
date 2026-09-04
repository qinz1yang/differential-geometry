import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.ComponentSubsequence

import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open Filter Topology
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metric_ext_inner
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (h : forall x : M, g₁.inner x = g₂.inner x) :
    g₁ = g₂ := by
  cases g₁; cases g₂
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x; exact h x

omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricInnerApply_diff_le
    (A B gRef : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |A.inner x v w - B.inner x v w|
      <= (Module.finrank Real (TangentSpace I x) : Real)
          * metricDerivNorm (I := I) 0 A B gRef x
          * (gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w) := by
  classical
  set n : Real := (Module.finrank Real (TangentSpace I x) : Real) with hn
  set D := metricDiffCovDerivAt (I := I) 0 A B gRef x with hD
  have hsymmA : A.inner x v w = A.inner x w v := A.symm x v w
  have hsymmB : B.inner x v w = B.inner x w v := B.symm x v w
  have hpol : A.inner x v w - B.inner x v w
      = ((A.inner x (v + w) (v + w) - B.inner x (v + w) (v + w))
         - (A.inner x v v - B.inner x v v)
         - (A.inner x w w - B.inner x w w)) / 2 := by
    rw [metric_add_self A x v w, metric_add_self B x v w]; rw [hsymmA, hsymmB]; ring
  have hqf : forall u : TangentSpace I x,
      |A.inner x u u - B.inner x u u|
        <= n * metricDerivNorm (I := I) 0 A B gRef x * gRef.inner x u u := fun u =>
    metricQuadFormDiff_le_metricDerivNorm (I := I) A B gRef x u
  have hvw := hqf (v + w)
  have hv := hqf v
  have hw := hqf w
  have hmn : 0 <= n := by rw [hn]; positivity
  have hmd : 0 <= metricDerivNorm (I := I) 0 A B gRef x := Real.sqrt_nonneg _
  have hgnn : forall u : TangentSpace I x, 0 <= gRef.inner x u u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp
    · exact (gRef.pos x u hu).le
  rw [hpol, abs_div, abs_of_pos (by norm_num : (0:Real) < 2)]
  rw [div_le_iff₀ (by norm_num : (0:Real) < 2)]
  set p1 := A.inner x (v + w) (v + w) - B.inner x (v + w) (v + w) with hp1
  set p2 := A.inner x v v - B.inner x v v with hp2
  set p3 := A.inner x w w - B.inner x w w with hp3
  have htri : |p1 - p2 - p3| <= |p1| + |p2| + |p3| := by
    have h1 := abs_add_le (p1 - p2) (-p3)
    have h2 := abs_add_le p1 (-p2)
    simp only [abs_neg, sub_eq_add_neg] at h1 h2 ⊢
    linarith [h1, h2]
  nlinarith [htri, hvw, hv, hw, hmn, hmd, hgnn (v + w), hgnn v, hgnn w,
    mul_nonneg (mul_nonneg hmn hmd) (hgnn v),
    mul_nonneg (mul_nonneg hmn hmd) (hgnn w),
    mul_nonneg (mul_nonneg hmn hmd) (hgnn (v + w))]

omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCInf_inner
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef)
    (x : M) (v w : TangentSpace I x) :
    Tendsto (fun k => (gSeq k).inner x v w) atTop (nhds (gInf.inner x v w)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let n : ℝ := Module.finrank ℝ (TangentSpace I x)
  let S : ℝ := gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hS : 0 ≤ S := by
    have hnonneg : ∀ z : TangentSpace I x, 0 ≤ gRef.inner x z z := by
      intro z
      by_cases hz : z = 0
      · subst hz
        simp
      · exact (gRef.pos x z hz).le
    dsimp only [S]
    linarith [hnonneg (v + w), hnonneg v, hnonneg w]
  have hden : 0 < n * S + 1 := by positivity
  obtain ⟨k₀, hk₀⟩ := hconv {x} isCompact_singleton 0 (ε / (n * S + 1)) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  have hpoint : metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x <
      ε / (n * S + 1) := lt_of_le_of_lt
    (derivNorm_le_sup (I := I) isCompact_singleton le_rfl
      (gSeq k) gInf gRef (Set.mem_singleton x))
    (hk₀ k hk)
  have hbound := metricInnerApply_diff_le (I := I) (gSeq k) gInf gRef x v w
  change |(gSeq k).inner x v w - gInf.inner x v w| ≤
    n * metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x * S at hbound
  rw [Real.dist_eq]
  have hprod : n * metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x * S ≤
      (n * S) * (ε / (n * S + 1)) := by
    have hnorm : 0 ≤ metricDerivNorm (I := I) 0 (gSeq k) gInf gRef x :=
      Real.sqrt_nonneg _
    nlinarith [hpoint.le, mul_nonneg hn hS]
  have hfrac : (n * S) * (ε / (n * S + 1)) < ε := by
    have hid : (n * S) * (ε / (n * S + 1)) = (n * S) * ε / (n * S + 1) := by
      rw [mul_div_assoc]
    rw [hid, div_lt_iff₀ hden]
    nlinarith [hε, mul_nonneg hn hS]
  exact lt_of_le_of_lt (le_trans hbound hprod) hfrac

omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricCInf_unique
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (A B gRefA gRefB : SmoothRiemannianMetric I M)
    (hA : MetricCInfConvOnCompacts (I := I) gSeq A gRefA)
    (hB : MetricCInfConvOnCompacts (I := I) gSeq B gRefB) : A = B := by
  refine metric_ext_inner A B fun x => ?_
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  exact tendsto_nhds_unique
    (metricCInf_inner (I := I) gSeq A gRefA hA x v w)
    (metricCInf_inner (I := I) gSeq B gRefB hB x v w)

omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricInner_cauchy
    (gk : Nat -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x)
    (hcauchy : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x < eps) :
    CauchySeq (fun k => (gk k).inner x v w) := by
  set n : Real := (Module.finrank Real (TangentSpace I x) : Real) with hn
  set S : Real := gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w with hS
  have hSnn : 0 <= S := by
    rw [hS]
    have hgnn : forall u : TangentSpace I x, 0 <= gRef.inner x u u := by
      intro u
      by_cases hu : u = 0
      · subst hu; simp
      · exact (gRef.pos x u hu).le
    have := hgnn (v + w); have := hgnn v; have := hgnn w; linarith
  have hnnn : 0 <= n := by rw [hn]; positivity
  rw [Metric.cauchySeq_iff]
  intro eps heps
  obtain ⟨k0, hk0⟩ := hcauchy (eps / (n * S + 1)) (by positivity)
  refine ⟨k0, fun m hm l hl => ?_⟩
  rw [Real.dist_eq]
  have hbound : |(gk m).inner x v w - (gk l).inner x v w|
      <= n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S := by
    have h := metricInnerApply_diff_le (I := I) (gk m) (gk l) gRef x v w
    rw [← hn, ← hS] at h
    exact h
  have hmd : metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x < eps / (n * S + 1) :=
    hk0 m hm l hl
  have hmdnn : 0 <= metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x := Real.sqrt_nonneg _
  have hdenpos : 0 < n * S + 1 := by positivity
  have hkey : n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S <
      eps := by
    have hprod : n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S
        <= (n * S) * (eps / (n * S + 1)) := by
      have h1 : metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x
          <= eps / (n * S + 1) := hmd.le
      nlinarith [h1, hnnn, hmdnn, hSnn, mul_nonneg hnnn hSnn]
    have hfrac : (n * S) * (eps / (n * S + 1)) < eps := by
      have hid : (n * S) * (eps / (n * S + 1)) = (n * S) * eps / (n * S + 1) := by
        rw [mul_div_assoc]
      rw [hid, div_lt_iff₀ hdenpos]
      nlinarith [heps, mul_nonneg hnnn hSnn]
    linarith
  calc |(gk m).inner x v w - (gk l).inner x v w|
      <= n * metricDerivNorm (I := I) 0 (gk m) (gk l) gRef x * S := hbound
    _ < eps := hkey

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metricLimit_uniq
    (gk : Nat -> SmoothRiemannianMetric I M) (A B : SmoothRiemannianMetric I M)
    (hcauchy : forall x : M, forall v w : TangentSpace I x,
      CauchySeq (fun k => (gk k).inner x v w))
    (psiA : Nat -> Nat) (hpsiA : StrictMono psiA)
    (psiB : Nat -> Nat) (hpsiB : StrictMono psiB)
    (hA : forall x : M, Filter.Tendsto (fun m => (gk (psiA m)).inner x) Filter.atTop
      (nhds (A.inner x)))
    (hB : forall x : M, Filter.Tendsto (fun m => (gk (psiB m)).inner x) Filter.atTop
      (nhds (B.inner x))) :
    A = B := by
  refine metric_ext_inner A B fun x => ?_
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  have hAvw : Filter.Tendsto (fun m => (gk (psiA m)).inner x v w) Filter.atTop
      (nhds (A.inner x v w)) := by
    have hc : Continuous fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
        T v w :=
      (ContinuousLinearMap.apply Real Real w).continuous.comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) v).continuous
    exact (hc.tendsto _).comp (hA x)
  have hBvw : Filter.Tendsto (fun m => (gk (psiB m)).inner x v w) Filter.atTop
      (nhds (B.inner x v w)) := by
    have hc : Continuous fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
        T v w :=
      (ContinuousLinearMap.apply Real Real w).continuous.comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) v).continuous
    exact (hc.tendsto _).comp (hB x)
  have hfullA : Filter.Tendsto (fun k => (gk k).inner x v w) Filter.atTop
      (nhds (A.inner x v w)) :=
    tendsto_nhds_of_cauchySeq_of_subseq (hcauchy x v w) hpsiA.tendsto_atTop hAvw
  have hfullB : Filter.Tendsto (fun k => (gk k).inner x v w) Filter.atTop
      (nhds (B.inner x v w)) :=
    tendsto_nhds_of_cauchySeq_of_subseq (hcauchy x v w) hpsiB.tendsto_atTop hBvw
  exact tendsto_nhds_unique hfullA hfullB


omit [Module.Finite ℝ E] in
theorem metricPreconvFull
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M) (gSeq : Nat -> SmoothRiemannianMetric I M)
    (hbdd : forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
      forall k : Nat, forall z, z ∈ K' ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C)
    (hlow : exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq k).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\ exists gInf : SmoothRiemannianMetric I M,
      (forall x : M, Filter.Tendsto (fun m => (gSeq (phi m)).inner x) Filter.atTop
        (nhds (gInf.inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k)) gInf gRef x < eps := by
  classical
  obtain ⟨phi0, hphi0, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd phi0 gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : Nat, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨phid, hphid, hPphid⟩ := exists_diag_subseq
    (fun n phi => forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phi k))) gInf gRef z < eps)
    (fun n phi hphi => by
      obtain ⟨psi, hpsi, hu⟩ := hpatch (e n) phi hphi
      refine ⟨psi, hpsi, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p eps heps
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n phi psi hpsi hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩)
    (fun n phi m hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  refine ⟨phi0 ∘ phid, hphi0.comp hphid, gInf, ?_, fun eps heps => ?_⟩
  · intro x
    have h := (hconv x).comp hphid.tendsto_atTop
    change Tendsto (fun m => (gSeq (phi0 (phid m))).inner x) atTop (𝓝 (gInf.inner x)) at h
    exact h
  · obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
      (fun z hz => hcovN (Set.mem_univ z))
    have perN : forall n, n ∈ F -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phid k))) gInf gRef z < eps :=
      fun n _ => hPphid n eps heps
    choose k0fn hk0fn using perN
    refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
    obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
    simpa only [Function.comp_apply] using
      hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
        (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

omit [Module.Finite ℝ E] in
theorem metricPreconvNorm
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M) (gSeq : Nat -> SmoothRiemannianMetric I M)
    (hbdd : forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
      forall k : Nat, forall z, z ∈ K' ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C)
    (hlow : exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq k).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\ exists gInf : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k)) gInf gRef x < eps := by
  classical
  obtain ⟨phi0, hphi0, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd phi0 gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : Nat, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨phid, hphid, hPphid⟩ := exists_diag_subseq
    (fun n phi => forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phi k))) gInf gRef z < eps)
    (fun n phi hphi => by
      obtain ⟨psi, hpsi, hu⟩ := hpatch (e n) phi hphi
      refine ⟨psi, hpsi, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p eps heps
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n phi psi hpsi hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩)
    (fun n phi m hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  refine ⟨phi0 ∘ phid, hphi0.comp hphid, gInf, fun eps heps => ?_⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
    (fun z hz => hcovN (Set.mem_univ z))
  have perN : forall n, n ∈ F -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= p -> forall z, z ∈ C (e n) ->
        metricDerivNorm (I := I) a (gSeq (phi0 (phid k))) gInf gRef z < eps :=
    fun n _ => hPphid n eps heps
  choose k0fn hk0fn using perN
  refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
  obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
  simpa only [Function.comp_apply] using
    hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
      (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

omit [Module.Finite ℝ E] in
theorem netNormDiag
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (e : Nat -> Real)
    (hbdd : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) (e n)) gRef z <= C)
    (hlow : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) (e n)).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gNet : Nat -> SmoothRiemannianMetric I M,
        forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
          forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq
    (fun n rho => exists gLim : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (rho k) (e n)) gLim gRef x < eps)
    (fun n rho hrho => by
      obtain ⟨psi, hpsi, gLim, hlim⟩ :=
        metricPreconvNorm (I := I) hne K hK p gRef (fun k => gSeq (rho k) (e n))
          (hbdd n rho hrho) (hlow n rho hrho)
      refine ⟨psi, hpsi, gLim, ?_⟩
      intro eps heps
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩)
    (fun n rho psi hpsi hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using
          hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha x hx⟩)
    (fun n rho m hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      refine ⟨k0 + m, fun k hk a ha x hx => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha x hx
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  choose gNet hgNet using hPphi
  exact ⟨phi, hphi, gNet, hgNet⟩

omit [Module.Finite ℝ E] in
theorem netFullDiag
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (e : Nat -> Real)
    (hbdd : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) (e n)) gRef z <= C)
    (hlow : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) (e n)).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gNet : Nat -> SmoothRiemannianMetric I M,
        (forall n : Nat, forall x : M,
          Filter.Tendsto (fun k => (gSeq (phi k) (e n)).inner x) Filter.atTop
            (nhds ((gNet n).inner x))) /\
        forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
          forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq
    (fun n rho => exists gLim : SmoothRiemannianMetric I M,
      (forall x : M, Filter.Tendsto (fun k => (gSeq (rho k) (e n)).inner x)
        Filter.atTop (nhds (gLim.inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (rho k) (e n)) gLim gRef x < eps)
    (fun n rho hrho => by
      obtain ⟨psi, hpsi, gLim, hinner, hlim⟩ :=
        metricPreconvFull (I := I) hne K hK p gRef (fun k => gSeq (rho k) (e n))
          (hbdd n rho hrho) (hlow n rho hrho)
      refine ⟨psi, hpsi, gLim, ?_, ?_⟩
      · intro x
        simpa only [Function.comp_apply] using hinner x
      · intro eps heps
        obtain ⟨k0, hk0⟩ := hlim eps heps
        exact ⟨k0, fun k hk a ha x hx => by
          simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩)
    (fun n rho psi hpsi hP => by
      obtain ⟨gLim, hinner, hlim⟩ := hP
      refine ⟨gLim, ?_, fun eps heps => ?_⟩
      · intro x
        have h := (hinner x).comp hpsi.tendsto_atTop
        change Tendsto (fun k => (gSeq (rho (psi k)) (e n)).inner x) atTop
          (𝓝 (gLim.inner x)) at h
        exact h
      · obtain ⟨k0, hk0⟩ := hlim eps heps
        exact ⟨k0, fun k hk a ha x hx => by
          simpa only [Function.comp_apply] using
            hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha x hx⟩)
    (fun n rho m hP => by
      obtain ⟨gLim, hinner, hlim⟩ := hP
      refine ⟨gLim, ?_, fun eps heps => ?_⟩
      · intro x
        exact (Filter.tendsto_add_atTop_iff_nat
          (f := fun k => (gSeq (rho k) (e n)).inner x) m).1 (hinner x)
      · obtain ⟨k0, hk0⟩ := hlim eps heps
        refine ⟨k0 + m, fun k hk a ha x hx => ?_⟩
        have hval := hk0 (k - m) (by omega) a ha x hx
        simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
        exact hval)
  choose gNet hgNet using hPphi
  exact ⟨phi, hphi, gNet, fun n => (hgNet n).1, fun n => (hgNet n).2⟩


omit [Module.Finite ℝ E] [I.Boundaryless] [SigmaCompactSpace M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem MetricCInfConvOnCompacts.metric_deriv_norm_le
    [Module.Finite ℝ E]
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (gInf g₀ gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef)
    {a : ℕ} {x : M} {δ : ℝ}
    (hbound : ∀ k, metricDerivNorm (I := I) a (gSeq k) g₀ gRef x ≤ δ) :
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤ δ := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨k₀, hk₀⟩ := hconv {x} isCompact_singleton a η hη
  have hpoint : metricDerivNorm (I := I) a (gSeq k₀) gInf gRef x < η :=
    lt_of_le_of_lt
      (derivNorm_le_sup (I := I) isCompact_singleton le_rfl
        (gSeq k₀) gInf gRef (Set.mem_singleton x))
      (hk₀ k₀ le_rfl)
  have hsymm := metricDerivNorm_symm (I := I) a gInf (gSeq k₀) gRef x
  calc
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤
        metricDerivNorm (I := I) a gInf (gSeq k₀) gRef x +
          metricDerivNorm (I := I) a (gSeq k₀) g₀ gRef x :=
      metricDerivNorm_triangle (I := I) a gInf (gSeq k₀) g₀ gRef x
    _ ≤ δ + η := by rw [hsymm]; linarith [hbound k₀]

omit [Module.Finite ℝ E] in
omit [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem netCauchyAt
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gNet : Nat -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hnet : forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps) :
    forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi l) t) gRef x < eps := by
  intro t ht eps heps
  have hLpos : (0 : Real) < L + 1 := by linarith
  set delta : Real := eps / (4 * (L + 1)) with hdelta
  have hdelta_pos : 0 < delta := by rw [hdelta]; positivity
  obtain ⟨n, hn⟩ := hdense t ht delta hdelta_pos
  obtain ⟨k0, hk0⟩ := hnet n (eps / 4) (by positivity)
  refine ⟨k0, fun m hm l hl a ha x hxK => ?_⟩
  have h1 : metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n)) gRef x
      <= L * |t - e n| :=
    hgLip (phi m) t ht (e n) (he n) a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (phi m) (e n)) (gNet n) gRef x < eps / 4 :=
    hk0 m hm a ha x hxK
  have h3 : metricDerivNorm (I := I) a (gNet n) (gSeq (phi l) (e n)) gRef x < eps / 4 := by
    rw [metricDerivNorm_symm]
    exact hk0 l hl a ha x hxK
  have h4 : metricDerivNorm (I := I) a (gSeq (phi l) (e n)) (gSeq (phi l) t) gRef x
      <= L * |t - e n| := by
    have h := hgLip (phi l) (e n) (he n) t ht a ha x hxK
    rwa [abs_sub_comm] at h
  have htri : metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi l) t) gRef x <=
      metricDerivNorm (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n)) gRef x
      + (metricDerivNorm (I := I) a (gSeq (phi m) (e n)) (gNet n) gRef x
        + (metricDerivNorm (I := I) a (gNet n) (gSeq (phi l) (e n)) gRef x
          + metricDerivNorm (I := I) a (gSeq (phi l) (e n)) (gSeq (phi l) t) gRef x)) := by
    refine le_trans
      (metricDerivNorm_triangle (I := I) a (gSeq (phi m) t) (gSeq (phi m) (e n))
        (gSeq (phi l) t) gRef x) ?_
    have htri2 := metricDerivNorm_triangle (I := I) a (gSeq (phi m) (e n)) (gNet n)
      (gSeq (phi l) t) gRef x
    have htri3 := metricDerivNorm_triangle (I := I) a (gNet n) (gSeq (phi l) (e n))
      (gSeq (phi l) t) gRef x
    linarith
  have hdbound : L * |t - e n| <= L * delta :=
    mul_le_mul_of_nonneg_left hn.le hL
  have hsmall : 2 * L * delta < eps / 2 := by
    have hstep : 2 * L * delta < 2 * (L + 1) * delta := by nlinarith
    have heq : 2 * (L + 1) * delta = eps / 2 := by
      rw [hdelta]
      field_simp
      ring
    linarith
  nlinarith [htri, h1, h2, h3, h4, hdbound, hsmall]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem fullOfSubseq
    [Module.Finite ℝ E]
    (K : Set M) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gLim gRef : SmoothRiemannianMetric I M) (psi : Nat -> Nat) (hpsi : StrictMono psi)
    (hcauchy : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall m : Nat, k0 <= m -> forall l : Nat, k0 <= l ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq m) (gSeq l) gRef x < eps)
    (hsub : forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (psi k)) gLim gRef x < eps) :
    forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k) gLim gRef x < eps := by
  intro eps heps
  obtain ⟨kC, hkC⟩ := hcauchy (eps / 2) (by positivity)
  obtain ⟨kS, hkS⟩ := hsub (eps / 2) (by positivity)
  let j : Nat := max kC kS
  refine ⟨kC, fun k hk a ha x hxK => ?_⟩
  have hjC : kC <= psi j := le_trans (Nat.le_max_left kC kS) (hpsi.id_le j)
  have hjS : kS <= j := Nat.le_max_right kC kS
  have h1 : metricDerivNorm (I := I) a (gSeq k) (gSeq (psi j)) gRef x < eps / 2 :=
    hkC k hk (psi j) hjC a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (psi j)) gLim gRef x < eps / 2 :=
    hkS j hjS a ha x hxK
  have htri := metricDerivNorm_triangle (I := I) a (gSeq k) (gSeq (psi j)) gLim gRef x
  linarith

omit [Module.Finite ℝ E] in
omit [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem infLipOfConv
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gInf : Real -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat)
    (L : Real)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hconv : forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps) :
    forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t| := by
  intro s hs t ht a ha x hxK
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨kS, hkS⟩ := hconv s hs (eps / 2) (by positivity)
  obtain ⟨kT, hkT⟩ := hconv t ht (eps / 2) (by positivity)
  let k0 : Nat := max kS kT
  have hkS0 : kS <= k0 := Nat.le_max_left kS kT
  have hkT0 : kT <= k0 := Nat.le_max_right kS kT
  have h1 : metricDerivNorm (I := I) a (gInf s) (gSeq (phi k0) s) gRef x < eps / 2 := by
    rw [metricDerivNorm_symm]
    exact hkS k0 hkS0 a ha x hxK
  have h2 : metricDerivNorm (I := I) a (gSeq (phi k0) s) (gSeq (phi k0) t) gRef x
      <= L * |s - t| :=
    hgLip (phi k0) s hs t ht a ha x hxK
  have h3 : metricDerivNorm (I := I) a (gSeq (phi k0) t) (gInf t) gRef x < eps / 2 :=
    hkT k0 hkT0 a ha x hxK
  have htri : metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <=
      metricDerivNorm (I := I) a (gInf s) (gSeq (phi k0) s) gRef x
      + (metricDerivNorm (I := I) a (gSeq (phi k0) s) (gSeq (phi k0) t) gRef x
        + metricDerivNorm (I := I) a (gSeq (phi k0) t) (gInf t) gRef x) := by
    refine le_trans
      (metricDerivNorm_triangle (I := I) a (gInf s) (gSeq (phi k0) s) (gInf t) gRef x) ?_
    have htri2 := metricDerivNorm_triangle (I := I) a (gSeq (phi k0) s)
      (gSeq (phi k0) t) (gInf t) gRef x
    linarith
  linarith

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem windowOfNet
    [Module.Finite ℝ E]
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gInf : Real -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hInfLip : forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t|)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hnet : forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gInf (e n)) gRef x < eps) :
    exists phi' : Nat -> Nat, StrictMono phi' /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t, t ∈ Set.Icc beta psiT ->
          metricDerivNormSupOn (I := I) K p (gSeq (phi' k) t) (gInf t) gRef < eps := by
  refine ⟨phi, hphi, ?_⟩
  refine windowPreconv (I := I) K beta psiT p (fun k => gSeq (phi k)) gInf gRef L hL
    (fun k => hgLip (phi k)) hInfLip (Set.range e) ?_ ?_
  · intro t ht delta hdelta
    obtain ⟨n, hn⟩ := hdense t ht delta hdelta
    exact ⟨e n, ⟨n, rfl⟩, he n, hn⟩
  · rintro tau ⟨n, rfl⟩ _ eps heps
    exact hnet n eps heps

structure WindowGInfOut
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) : Prop where
  out :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gInf : Real -> SmoothRiemannianMetric I M,
        forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t, t ∈ Set.Icc beta psiT ->
            metricDerivNormSupOn (I := I) K p (gSeq (phi k) t) (gInf t) gRef < eps

omit [Module.Finite ℝ E] in
theorem windowGInf
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hbdd : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) t) gRef z <= C)
    (hlow : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gInf : Real -> SmoothRiemannianMetric I M,
        forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t, t ∈ Set.Icc beta psiT ->
            metricDerivNormSupOn (I := I) K p (gSeq (phi k) t) (gInf t) gRef < eps := by
  classical
  obtain ⟨phi, hphi, gNet, _hnetInner, hnetNorm⟩ :=
    netFullDiag (I := I) hne K hK p gRef gSeq e
      (fun n rho hrho q K' hK' => hbdd rho hrho (e n) (he n) q K' hK')
      (fun n rho hrho => hlow rho hrho (e n) (he n))
  have htime : forall t, t ∈ Set.Icc beta psiT ->
      exists psi : Nat -> Nat, StrictMono psi /\
        exists gT : SmoothRiemannianMetric I M,
          (forall x : M, Filter.Tendsto (fun m => (gSeq (phi (psi m)) t).inner x)
            Filter.atTop (nhds (gT.inner x))) /\
          forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall a : Nat, a <= p -> forall x, x ∈ K ->
              metricDerivNorm (I := I) a (gSeq (phi (psi k)) t) gT gRef x < eps := by
    intro t ht
    obtain ⟨psi, hpsi, gT, hinner, hnorm⟩ :=
      metricPreconvFull (I := I) hne K hK p gRef (fun k => gSeq (phi k) t)
        (hbdd phi hphi t ht) (hlow phi hphi t ht)
    refine ⟨psi, hpsi, gT, ?_, ?_⟩
    · intro x
      simpa only [Function.comp_apply] using hinner x
    · intro eps heps
      obtain ⟨k0, hk0⟩ := hnorm eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩
  let psiAt : (t : Real) -> t ∈ Set.Icc beta psiT -> Nat -> Nat :=
    fun t ht => Classical.choose (htime t ht)
  have hpsiAt : forall t ht, StrictMono (psiAt t ht) := by
    intro t ht
    exact (Classical.choose_spec (htime t ht)).1
  let gAt : (t : Real) -> t ∈ Set.Icc beta psiT -> SmoothRiemannianMetric I M :=
    fun t ht => Classical.choose (Classical.choose_spec (htime t ht)).2
  have hgAt : forall t ht,
      (forall x : M, Filter.Tendsto (fun m => (gSeq (phi ((psiAt t ht) m)) t).inner x)
        Filter.atTop (nhds ((gAt t ht).inner x))) /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi ((psiAt t ht) k)) t) (gAt t ht) gRef x < eps := by
    intro t ht
    exact Classical.choose_spec (Classical.choose_spec (htime t ht)).2
  let gInf : Real -> SmoothRiemannianMetric I M :=
    fun t => if ht : t ∈ Set.Icc beta psiT then gAt t ht else gRef
  have hfull : forall t, t ∈ Set.Icc beta psiT -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
    intro t ht eps heps
    have hcauchy :=
      netCauchyAt (I := I) K beta psiT p gSeq gNet gRef phi L hL hgLip e he hdense hnetNorm
        t ht
    have hsub : forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a ((fun k => gSeq (phi k) t) ((psiAt t ht) k))
            (gAt t ht) gRef x < eps := by
      intro eps heps
      exact (hgAt t ht).2 eps heps
    obtain ⟨k0, hk0⟩ :=
      fullOfSubseq (I := I) K p (fun k => gSeq (phi k) t) (gAt t ht) gRef
        (psiAt t ht) (hpsiAt t ht) hcauchy hsub eps heps
    refine ⟨k0, fun k hk a ha x hx => ?_⟩
    have hgInf_t : gInf t = gAt t ht := by
      dsimp [gInf]
      exact dif_pos ht
    rw [hgInf_t]
    exact hk0 k hk a ha x hx
  have hInfLip :
      forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t| :=
    infLipOfConv (I := I) K beta psiT p gSeq gInf gRef phi L hgLip hfull
  obtain ⟨phi', hphi', hwin⟩ :=
    windowOfNet (I := I) K beta psiT p gSeq gInf gRef phi hphi L hL hgLip hInfLip e he
      hdense (fun n eps heps => hfull (e n) (he n) eps heps)
  exact ⟨phi', hphi', gInf, hwin⟩

omit [Module.Finite ℝ E] in
theorem windowGInfOut
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hbdd : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) t) gRef z <= C)
    (hlow : forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v) :
    WindowGInfOut (I := I) K beta psiT p gSeq gRef := by
  exact
    ⟨windowGInf (I := I) hne K hK beta psiT p gSeq gRef e he hdense L hL hgLip hbdd hlow⟩

end HCGCompactness
end DifferentialGeometry
