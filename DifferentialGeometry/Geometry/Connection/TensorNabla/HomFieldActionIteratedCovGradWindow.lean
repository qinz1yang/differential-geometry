import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS

/-!
# Iterated covariant gradients of a fixed full-Hom-field action: derived-field expansion and
windowed fibre bound

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the **iterated-gradient calculus of a single fixed
full-Hom-field action** `appFullSec Q W` (`FullHomCovariantCalculusRS`) at a generic contravariant
valence `r` and *arbitrary* source/target covariant ranks `m`, `c` (in particular rank-*reducing*
fields `c < m`, e.g. metric traces, which the base-raising tower normal form `NormalFormFull`
cannot host):

* `homFieldAction_iteratedCovGrad_expansion` — the **derived-field expansion**: for every gradient
  order `k` there is a family of fixed smooth full-Hom fields
  `D i : Hom(T^{(r, m + i)}, T^{(r, c + k)})` (built from `Q` by iterated section covariant
  gradients `homTensorRSCovGradSec` and slot extensions `slotExtendFullSec`) with
  ```
  ∇^k (Q · W) = ∑_{i < k + 1} (D i) · (∇^i W)
  ```
  for every smooth compactly-supported `(r, m)`-tensor `W` — proved by induction on `k` through the
  section-level full-Hom covariant product rule `covGrad_appFullSec_eq`, the new top jet carried by
  the slot extension and the differentiated coefficient staying on the old jets;

* `exists_appFullSec_iteratedCovGrad_window_bound` — the **windowed fibre bound**: a per-order
  nonnegative constant family `cc : ℕ → ℝ`, depending only on the fixed field `Q` (never on `W`),
  with
  ```
  rfns(∇^k (Q · W))(x) ≤ cc k · ∑_{i < k + 1} rfns(∇^i W)(x),
  ```
  each derived-field summand bounded by the uniform `g`-fibre-operator contraction envelope
  `exists_uniform_riemannianFiberNormSq_appFullRS_le` of its fixed field;

* `exists_appFullSec_on_jet_iteratedCovGrad_window_bound` — the **order-shifted window** for an
  action on the `j`-th covariant jet: for a fixed field `Q : Hom(T^{(r, s + j)}, T^{(r, c)})`,
  ```
  rfns(∇^k (Q · ∇^j S))(x) ≤ cc k · ∑_{i < 1 + k} rfns(∇^{i + j} S)(x),
  ```
  the window of `S` entering at contracted order `j` with width `1` — exactly the
  `(p, w) = (j, 1)` graded-curvature-jet window shape consumed by the order-resolved
  curvature-jet splits (`IsGradedCurvJetRS`, `OrderSeparatedCurvatureJetRS`).

The constants are uniform over the closed manifold and over the contracted section; all genuinely
analytic content is inherited from the full-Hom calculus (`FullHomCovariantCalculusRS`), whose
smoothness children consumers transitively depend on.  Geometer convention; all fibre norms are the
intrinsic `riemannianFiberNormSq`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **The derived-field expansion of the iterated covariant gradients of a fixed full-Hom-field
action.** For a fixed smooth full-Hom field section `Q : Hom(T^{(r,m)}, T^{(r,c)})` and every
gradient order `k`, there is a family of fixed smooth full-Hom field sections
`D i : Hom(T^{(r, m + i)}, T^{(r, c + k)})` with
```
∇^k (appFullSec Q W) = ∑_{i < k + 1} appFullSec (D i) (∇^i W)
```
for *every* smooth compactly-supported `(r, m)`-tensor `W`.  The family is built from `Q` by
iterated Hom-section covariant gradients (`homTensorRSCovGradSec`, the differentiated-coefficient
contribution, staying on the jet `∇^i W`) and slot extensions (`slotExtendFullSec`, the spectator
contribution, moving up to the next jet `∇^{i+1} W`), via the section-level full-Hom covariant
product rule `covGrad_appFullSec_eq`; the source/target ranks are fully generic (in particular the
field may be rank-reducing, `c < m`, as for a metric trace).  Proved by induction on `k`. -/
theorem homFieldAction_iteratedCovGrad_expansion (g : SmoothRiemannianMetric I M) (r m c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r m c I) (k : ℕ) :
    ∃ D : (i : ℕ) → HomTensorRSField (E := E) (M := M) r (m + i) (c + k) I,
      ∀ W : SmoothCcTensor g r m,
        iteratedCovGrad g r c k (appFullSec (I := I) (M := M) g r m c Q W) =
          ∑ i ∈ Finset.range (k + 1),
            appFullSec (I := I) (M := M) g r (m + i) (c + k) (D i)
              (iteratedCovGrad g r m i W) := by
  classical
  induction k with
  | zero =>
      refine ⟨fun i => match i with | 0 => Q | (_ + 1) => 0, fun W => ?_⟩
      rw [Finset.sum_range_one]
      rfl
  | succ k ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨fun i => match i with
        | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (m + 0) (c + k) (D 0)
        | (i + 1) =>
            (if i + 1 < k + 1 then
                homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
              else 0) +
              slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i), fun W => ?_⟩

      rw [show iteratedCovGrad g r c (k + 1) (appFullSec (I := I) (M := M) g r m c Q W) =
          covGrad (I := I) (M := M) g r (c + k)
            (iteratedCovGrad g r c k (appFullSec (I := I) (M := M) g r m c Q W)) from rfl,
        hD W, covGrad_finset_sum]

      rw [show (∑ i ∈ Finset.range (k + 1), covGrad (I := I) (M := M) g r (c + k)
            (appFullSec (I := I) (M := M) g r (m + i) (c + k) (D i)
              (iteratedCovGrad g r m i W))) =
          ∑ i ∈ Finset.range (k + 1),
            (appFullSec (I := I) (M := M) g r (m + i) (c + (k + 1))
                (homTensorRSCovGradSec (I := I) (M := M) g r (m + i) (c + k) (D i))
                (iteratedCovGrad g r m i W) +
              appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
                (slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
                (iteratedCovGrad g r m (i + 1) W)) from
        Finset.sum_congr rfl (fun i _ => by
          rw [covGrad_appFullSec_eq (I := I) (M := M) g r (m + i) (c + k) (D i)
            (iteratedCovGrad g r m i W)]
          rfl)]
      rw [Finset.sum_add_distrib]

      rw [Finset.sum_range_succ' (fun j =>
        appFullSec (I := I) (M := M) g r (m + j) (c + (k + 1))
          ((match j with
            | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (m + 0) (c + k) (D 0)
            | (i + 1) =>
                (if i + 1 < k + 1 then
                    homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                  else 0) +
                  slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i)))
          (iteratedCovGrad g r m j W)) (k + 1)]

      rw [show (∑ i ∈ Finset.range (k + 1),
            appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              ((if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0) +
                slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
              (iteratedCovGrad g r m (i + 1) W)) =
          (∑ i ∈ Finset.range (k + 1),
            appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0)
              (iteratedCovGrad g r m (i + 1) W)) +
          (∑ i ∈ Finset.range (k + 1),
            appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (slotExtendFullSec (I := I) (M := M) g r (m + i) (c + k) (D i))
              (iteratedCovGrad g r m (i + 1) W)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [appFullSec_add_left]]

      rw [show (∑ i ∈ Finset.range (k + 1),
            appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (if i + 1 < k + 1 then
                  homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1))
                else 0)
              (iteratedCovGrad g r m (i + 1) W)) =
          ∑ i ∈ Finset.range k,
            appFullSec (I := I) (M := M) g r (m + (i + 1)) (c + (k + 1))
              (homTensorRSCovGradSec (I := I) (M := M) g r (m + (i + 1)) (c + k) (D (i + 1)))
              (iteratedCovGrad g r m (i + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (k + 1 < k + 1)), appFullSec_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hi; omega : i + 1 < k + 1)]]

      rw [Finset.sum_range_succ' (fun i =>
        appFullSec (I := I) (M := M) g r (m + i) (c + (k + 1))
          (homTensorRSCovGradSec (I := I) (M := M) g r (m + i) (c + k) (D i))
          (iteratedCovGrad g r m i W)) k]

      abel

set_option linter.unusedSectionVars false in
/-- **The windowed fibre bound for the iterated covariant gradients of a fixed full-Hom-field
action.** For a fixed smooth full-Hom field section `Q : Hom(T^{(r,m)}, T^{(r,c)})` on a closed
Riemannian manifold there is a nonnegative per-gradient-order constant family `cc : ℕ → ℝ` —
depending only on `Q`, never on the contracted section — such that for every smooth
compactly-supported `(r, m)`-tensor `W`, every gradient order `k`, and every point `x`,
```
rfns(∇^k (appFullSec Q W))(x) ≤ cc k · ∑_{i < k + 1} rfns(∇^i W)(x).
```
By the derived-field expansion `homFieldAction_iteratedCovGrad_expansion`, `∇^k (Q · W)` is a
finite sum of fixed-field actions on the jets `∇^i W`; each summand is bounded by the uniform
`g`-fibre-operator contraction envelope of its fixed derived field
(`exists_uniform_riemannianFiberNormSq_appFullRS_le`), and the finite sum is accumulated by
`riemannianFiberNormSq_sum_le_card_mul`. -/
theorem exists_appFullSec_iteratedCovGrad_window_bound (g : SmoothRiemannianMetric I M)
    (r m c : ℕ) (Q : HomTensorRSField (E := E) (M := M) r m c I) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (W : SmoothCcTensor g r m) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
            ((iteratedCovGrad g r c k
              (appFullSec (I := I) (M := M) g r m c Q W)).toSection x) ≤
          cc k * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
              ((iteratedCovGrad g r m i W).toSection x) := by
  classical

  choose D hD using fun k =>
    homFieldAction_iteratedCovGrad_expansion (I := I) (M := M) g r m c Q k

  set C : ℕ → ℕ → ℝ := fun k i =>
    (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
      (fun x : M => D k i x) (D k i).contMDiff).choose with hC_def
  have hC_nn : ∀ k i, 0 ≤ C k i := fun k i =>
    (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
      (fun x : M => D k i x) (D k i).contMDiff).choose_spec.1
  have hC_bound : ∀ (k i : ℕ) (V : SmoothCcTensor g r (m + i)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
          ((appFullRS (I := I) (M := M) g r (m + i) (c + k) (fun x : M => D k i x)
            (D k i).contMDiff V).toSection x) ≤
        C k i * riemannianFiberNormSq (I := I) (M := M) g r (m + i) x (V.toSection x) :=
    fun k i V x =>
      (exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (m + i) (c + k)
        (fun x : M => D k i x) (D k i).contMDiff).choose_spec.2 V x
  refine ⟨fun k => ((k + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (k + 1), C k i,
    fun k => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hC_nn k i),
    fun W k x => ?_⟩

  set a : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
    ((iteratedCovGrad g r m i W).toSection x) with ha_def
  have ha_nn : ∀ i, 0 ≤ a i := fun i =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + i) x _

  rw [hD k W, SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (c + k) x
    (Finset.range (k + 1))
    (fun i => (appFullSec (I := I) (M := M) g r (m + i) (c + k) (D k i)
      (iteratedCovGrad g r m i W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ i ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
          ((appFullSec (I := I) (M := M) g r (m + i) (c + k) (D k i)
            (iteratedCovGrad g r m i W)).toSection x) ≤ C k i * a i :=
    fun i _ => hC_bound k i (iteratedCovGrad g r m i W) x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ i ∈ Finset.range (k + 1), C k i * a i) ≤
      (∑ i ∈ Finset.range (k + 1), C k i) * ∑ i ∈ Finset.range (k + 1), a i := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k i)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) hi
  calc ((k + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (k + 1), C k i * a i
      ≤ ((k + 1 : ℕ) : ℝ) * ((∑ i ∈ Finset.range (k + 1), C k i) *
          ∑ i ∈ Finset.range (k + 1), a i) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = ((k + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (k + 1), C k i) *
          ∑ i ∈ Finset.range (k + 1), a i := by ring

/-- **Heterogeneous rank-congruence for `covGrad` (file-local).** If two covariant ranks agree
(`h : a = b`) and the smooth compactly-supported `(r, ·)`-tensors are heterogeneously equal, then
so are their covariant gradients. -/
private theorem covGrad_heq_congr_hw (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g r a Y) (covGrad (I := I) (M := M) g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous composition of iterated covariant gradients (file-local).** Applying `i`
covariant gradients to the `j`-th covariant jet `∇^j S` is heterogeneously equal to the
`(j + i)`-fold iterated gradient of `S` (the two living in the ranks `(s + j) + i` and
`s + (j + i)`, which agree as naturals).  Proved by induction on the outer order `i`. -/
private theorem iteratedCovGrad_comp_heq_hw (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (S : SmoothCcTensor g r s) (i : ℕ) :
    HEq (iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S))
      (iteratedCovGrad g r s (j + i) S) := by
  induction i with
  | zero => exact HEq.rfl
  | succ i ihi =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + j) (j := i)
        (iteratedCovGrad g r s j S)]
      rw [show iteratedCovGrad g r s (j + (i + 1)) S =
        covGrad (I := I) (M := M) g r (s + (j + i)) (iteratedCovGrad g r s (j + i) S) from rfl]
      exact covGrad_heq_congr_hw (I := I) (M := M) g r
        (by omega : (s + j) + i = s + (j + i)) ihi

/-- **The intrinsic fibre norm is invariant under a rank-cast of heterogeneously equal sections
(file-local).** -/
private theorem rfns_toSection_heq_congr_hw (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **Composing iterated covariant gradients, in fibre-norm form.** The intrinsic squared fibre
norm of `∇^i (∇^j S)` at `x` equals that of `∇^{j + i} S` (the ranks `(s + j) + i` and
`s + (j + i)` agree as naturals; `rfns` is invariant under that rank-cast). -/
theorem rfns_iteratedCovGrad_comp (g : SmoothRiemannianMetric I M) (r s j i : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + j) + i) x
        ((iteratedCovGrad g r (s + j) i (iteratedCovGrad g r s j S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (j + i)) x
        ((iteratedCovGrad g r s (j + i) S).toSection x) :=
  rfns_toSection_heq_congr_hw (I := I) (M := M) g r
    (by omega : (s + j) + i = s + (j + i))
    (iteratedCovGrad_comp_heq_hw (I := I) (M := M) g r s j S i) x

/-- **Gradient-order congruence of the iterated-gradient fibre norm (file-local).** Equal gradient
orders give equal fibre norms (the rank indices recast along the order equality). -/
private theorem rfns_iteratedCovGrad_order_congr_hw (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad g r s n' S).toSection x) := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
/-- **The order-shifted windowed fibre bound: a fixed full-Hom-field action on the `j`-th covariant
jet is `(j, 1)`-window controlled.** For a fixed smooth full-Hom field section
`Q : Hom(T^{(r, s + j)}, T^{(r, c)})` on a closed Riemannian manifold there is a nonnegative
per-gradient-order constant family `cc : ℕ → ℝ` — depending only on `Q` — such that for every
smooth compactly-supported `(r, s)`-tensor `S`, every gradient order `k`, and every point `x`,
```
rfns(∇^k (appFullSec Q (∇^j S)))(x) ≤ cc k · ∑_{i < 1 + k} rfns(∇^{i + j} S)(x).
```
This is the windowed bound `exists_appFullSec_iteratedCovGrad_window_bound` at `W := ∇^j S`, the
inner window re-indexed onto the jets of `S` by `rfns_iteratedCovGrad_comp` — the window of `S`
entering at contracted order `j` with width `1`, exactly the `(p, w) = (j, 1)`
graded-curvature-jet window shape. -/
theorem exists_appFullSec_on_jet_iteratedCovGrad_window_bound (g : SmoothRiemannianMetric I M)
    (r s j c : ℕ) (Q : HomTensorRSField (E := E) (M := M) r (s + j) c I) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (S : SmoothCcTensor g r s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (c + k) x
            ((iteratedCovGrad g r c k
              (appFullSec (I := I) (M := M) g r (s + j) c Q
                (iteratedCovGrad g r s j S))).toSection x) ≤
          cc k * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g r (s + (i + j)) x
              ((iteratedCovGrad g r s (i + j) S).toSection x) := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g r (s + j) c Q
  refine ⟨cc, hcc_nn, fun S k x => ?_⟩
  refine (hcc (iteratedCovGrad g r s j S) k x).trans (le_of_eq ?_)
  refine congrArg (fun t => cc k * t) ?_

  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rfns_iteratedCovGrad_comp (I := I) (M := M) g r s j i S x]
  exact rfns_iteratedCovGrad_order_congr_hw (I := I) (M := M) g r s
    (by omega : j + i = i + j) S x

end Connection
end Integral
end DifferentialGeometry

end
