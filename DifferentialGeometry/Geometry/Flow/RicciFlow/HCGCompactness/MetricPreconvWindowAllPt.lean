import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointwise form of the all-compacts window preconvergence

`windowGInfAll` delivers the window convergence through the raw supremum
`metricDerivNormSupOn`, a bare `Real.sSup`.  Consumers that need PER-POINT
smallness cannot extract it from `sSup < ε` alone: without a `BddAbove`
witness the supremum could be the junk value `0`.  This file provides the
pointwise companion `windowGInfAll_pt`, discharging `BddAbove` from the
theorem's own data instead of a (missing) continuity API:

* on singleton compacts the sup set is a finite image of `Set.Iic p`, so the
  sup smallness from `windowGInfAll` is genuinely pointwise
  (`derivNorm_le_sup_sing`);
* the difference seminorm splits through a singleton-tail comparison metric
  `gSeq (φ m0) t` by the triangle inequality, and the two one-metric terms are
  bounded by the `hbdd` hypothesis instantiated along `φ`
  (`derivNorm_le_cov_add`), giving the `BddAbove` witness on any compact `K`;
* `le_csSup` then converts each sup smallness to the pointwise statement.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

/-- The metric-difference seminorm is bounded by the sum of the two one-metric
covariant-derivative norms: `|∇^a(g - h)|_gRef ≤ |∇^a g|_gRef + |∇^a h|_gRef`. -/
theorem derivNorm_le_cov_add
    (a : Nat) (g h gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) a g h gRef x <=
      metricCovDerivNorm (I := I) a g gRef x + metricCovDerivNorm (I := I) a h gRef x := by
  simp only [metricDerivNorm, metricDiffCovDerivAt, metricCovDerivNorm]
  have hsplit : metricCovDeriv (I := I) g gRef a x - metricCovDeriv (I := I) h gRef a x
      = metricCovDeriv (I := I) g gRef a x + -(metricCovDeriv (I := I) h gRef a x) :=
    sub_eq_add_neg _ _
  rw [hsplit]
  have hneg : Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
        (-(metricCovDeriv (I := I) h gRef a x))
      = Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
        (metricCovDeriv (I := I) h gRef a x) :=
    normSq0S_neg (I := I) gRef x (a + 2) (metricCovDeriv (I := I) h gRef a x)
  refine le_trans (sqrtNormSq0S_add_le (I := I) gRef x (a + 2) _ _) ?_
  rw [hneg]

/-- On a singleton compact the defining set of `metricDerivNormSupOn` is a
finite image of `Set.Iic p`, so each order `a ≤ p` is bounded by the supremum
(no continuity input needed). -/
theorem derivNorm_le_sup_sing
    (p : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (z : M)
    (a : Nat) (ha : a <= p) :
    metricDerivNorm (I := I) a gk gInf gRef z <=
      metricDerivNormSupOn (I := I) {z} p gk gInf gRef := by
  have heq : {r : Real | exists b : Nat, b <= p ∧ exists x : M, x ∈ ({z} : Set M) ∧
        metricDerivNorm (I := I) b gk gInf gRef x = r}
      = (fun b => metricDerivNorm (I := I) b gk gInf gRef z) '' Set.Iic p := by
    ext r
    constructor
    · rintro ⟨b, hb, x, hx, hr⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨b, Set.mem_Iic.2 hb, hr⟩
    · rintro ⟨b, hb, hr⟩
      exact ⟨b, Set.mem_Iic.1 hb, z, Set.mem_singleton z, hr⟩
  have hbdd : BddAbove {r : Real | exists b : Nat, b <= p ∧ exists x : M, x ∈ ({z} : Set M) ∧
      metricDerivNorm (I := I) b gk gInf gRef x = r} := by
    rw [heq]
    exact ((Set.finite_Iic p).image _).bddAbove
  exact le_csSup hbdd ⟨a, ha, z, Set.mem_singleton z, rfl⟩

/-- **Pointwise all-compacts, all-orders window preconvergence.**  The
companion of `windowGInfAll` with the window smallness delivered PER POINT
(each order `a ≤ p`, each `x ∈ K`) instead of through the raw supremum
`metricDerivNormSupOn`.  Same hypotheses, same single subsequence `φ` and
single limit family `gInf`. -/
theorem windowGInfAll_pt
    [WeaklyLocallyCompactSpace M]
    (hne : Nonempty M)
    (beta psiT : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hgLip : forall K' : Set M, IsCompact K' -> forall p : Nat,
      exists L : Real, 0 <= L /\
        forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
          forall a : Nat, a <= p -> forall x, x ∈ K' ->
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
        forall K : Set M, IsCompact K -> forall p : Nat, forall eps : Real, 0 < eps ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t, t ∈ Set.Icc beta psiT -> forall a : Nat, a <= p -> forall x, x ∈ K ->
              metricDerivNorm (I := I) a (gSeq (phi k) t) (gInf t) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, gInf, hsup⟩ :=
    windowGInfAll (I := I) hne beta psiT gRef gSeq e he hdense hgLip hbdd hlow
  refine ⟨phi, hphi, gInf, ?_⟩
  intro K hK p eps heps
  obtain ⟨k0, hk0⟩ := hsup K hK p eps heps
  refine ⟨k0, fun k hk t ht a hap x hx => ?_⟩
  -- uniform covariant-derivative bounds along `phi` at time `t`, per order
  choose Cf hCf using fun q : Nat => hbdd phi hphi t ht q K hK
  -- `BddAbove` for the `(K, p)` sup set at `(k, t)`: split through a
  -- singleton-tail comparison index `m0` at each base point
  have hbddAbove : BddAbove {r : Real | exists b : Nat, b <= p ∧ exists z : M, z ∈ K ∧
      metricDerivNorm (I := I) b (gSeq (phi k) t) (gInf t) gRef z = r} := by
    refine ⟨(Finset.range (p + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos p)⟩
      (fun b => Cf b + Cf b + 1), ?_⟩
    rintro r ⟨b, hbp, z, hzK, rfl⟩
    obtain ⟨m0, hm0⟩ := hsup {z} isCompact_singleton p 1 zero_lt_one
    have hz : metricDerivNorm (I := I) b (gSeq (phi m0) t) (gInf t) gRef z < 1 :=
      lt_of_le_of_lt
        (derivNorm_le_sup_sing (I := I) p (gSeq (phi m0) t) (gInf t) gRef z b hbp)
        (hm0 m0 le_rfl t ht)
    have htri := metricDerivNorm_triangle (I := I) b (gSeq (phi k) t) (gSeq (phi m0) t)
      (gInf t) gRef z
    have hcov : metricDerivNorm (I := I) b (gSeq (phi k) t) (gSeq (phi m0) t) gRef z
        <= Cf b + Cf b :=
      le_trans (derivNorm_le_cov_add (I := I) b (gSeq (phi k) t) (gSeq (phi m0) t) gRef z)
        (add_le_add (hCf b k z hzK) (hCf b m0 z hzK))
    have hle : metricDerivNorm (I := I) b (gSeq (phi k) t) (gInf t) gRef z
        <= Cf b + Cf b + 1 := by linarith
    exact le_trans hle
      (Finset.le_sup' (fun b => Cf b + Cf b + 1) (Finset.mem_range.2 (Nat.lt_succ_of_le hbp)))
  exact lt_of_le_of_lt (le_csSup hbddAbove ⟨a, hap, x, hx, rfl⟩) (hk0 k hk t ht)

end HCGCompactness
end DifferentialGeometry
