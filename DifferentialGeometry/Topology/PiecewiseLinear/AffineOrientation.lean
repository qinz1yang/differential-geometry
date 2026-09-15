import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem det_ne_zero_of_affine_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → E} (hp : AffineIndependent ℝ p) (A : Matrix ι ι ℝ)
    (hsum : ∀ i, ∑ j, A i j = 1)
    (hpoint : ∀ i, ∑ j, A i j • q j = p i) : A.det ≠ 0 := by
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hcz : ∀ j, ∑ i, c i * A i j = 0 := by
    intro j
    simpa only [Matrix.vecMul, dotProduct, Pi.zero_apply] using congrFun hc j
  have hcSum : ∑ i, c i = 0 := by
    calc
      ∑ i, c i = ∑ i, c i * ∑ j, A i j := by simp_rw [hsum, mul_one]
      _ = ∑ i, ∑ j, c i * A i j := by simp_rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, c i * A i j := Finset.sum_comm
      _ = 0 := by simp_rw [hcz, Finset.sum_const_zero]
  have hcPoint : ∑ i, c i • p i = 0 := by
    calc
      ∑ i, c i • p i = ∑ i, c i • ∑ j, A i j • q j := by simp_rw [hpoint]
      _ = ∑ i, ∑ j, (c i * A i j) • q j := by simp_rw [Finset.smul_sum, smul_smul]
      _ = ∑ j, ∑ i, (c i * A i j) • q j := Finset.sum_comm
      _ = ∑ j, (∑ i, c i * A i j) • q j := by simp_rw [Finset.sum_smul]
      _ = 0 := by simp_rw [hcz, zero_smul, Finset.sum_const_zero]
  apply hcne
  funext i
  exact hp.eq_zero_of_sum_eq_zero hcSum hcPoint i (Finset.mem_univ i)

noncomputable def simplexCoordinateMatrix (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N) :
    Matrix (Fin N) (Fin N) ℝ := by
  let _ := r
  exact fun i j => weights t ((Finset.orderIsoOfFin s hs) i).1
    ((Finset.orderIsoOfFin t ht) j).1

theorem simplexCoordinateMatrix_row_sum (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N)
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) (i : Fin N) :
    ∑ j, simplexCoordinateMatrix r hs ht i j = 1 := by
  let _ := r
  let x := ((Finset.orderIsoOfFin s hs) i).1
  have hx : x ∈ convexHull ℝ (t : Set E) :=
    hst (subset_convexHull ℝ _ ((Finset.orderIsoOfFin s hs) i).2)
  change ∑ j, weights t x ((Finset.orderIsoOfFin t ht) j).1 = 1
  exact ((Finset.orderIsoOfFin t ht).toEquiv.sum_comp (fun v : t => weights t x v)).trans
    (by simpa only [Finset.sum_coe_sort] using sum_weights hx)

theorem simplexCoordinateMatrix_row_smul (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N)
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) (i : Fin N) :
    let _ := r
    ∑ j, simplexCoordinateMatrix r hs ht i j • ((Finset.orderIsoOfFin t ht) j).1 =
      ((Finset.orderIsoOfFin s hs) i).1 := by
  let _ := r
  let x := ((Finset.orderIsoOfFin s hs) i).1
  have hx : x ∈ convexHull ℝ (t : Set E) :=
    hst (subset_convexHull ℝ _ ((Finset.orderIsoOfFin s hs) i).2)
  change ∑ j, weights t x ((Finset.orderIsoOfFin t ht) j).1 •
    ((Finset.orderIsoOfFin t ht) j).1 = x
  exact ((Finset.orderIsoOfFin t ht).toEquiv.sum_comp
    (fun v : t => weights t x v • (v : E))).trans
    ((Finset.sum_coe_sort t (fun v => weights t x v • v)).trans (sum_weights_smul hx))

theorem simplexCoordinateMatrix_det_ne_zero (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N)
    (hindep : AffineIndependent ℝ ((↑) : s → E))
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    (simplexCoordinateMatrix r hs ht).det ≠ 0 := by
  let _ := r
  have hp := hindep.comp_embedding (Finset.orderIsoOfFin s hs).toEquiv.toEmbedding
  exact det_ne_zero_of_affine_coordinates hp _
    (simplexCoordinateMatrix_row_sum r hs ht hst)
    (simplexCoordinateMatrix_row_smul r hs ht hst)

noncomputable def affineSimplexOrientationSign (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N) : ℤ :=
  (SignType.sign (simplexCoordinateMatrix r hs ht).det : ℤ)

theorem affineSimplexOrientationSign_eq_one_or_neg_one (r : LinearOrder E)
    {N : ℕ} {s t : Finset E} (hs : s.card = N) (ht : t.card = N)
    (hindep : AffineIndependent ℝ ((↑) : s → E))
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    affineSimplexOrientationSign r hs ht = 1 ∨ affineSimplexOrientationSign r hs ht = -1 := by
  have hn := simplexCoordinateMatrix_det_ne_zero r hs ht hindep hst
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · right
    simp only [affineSimplexOrientationSign, sign_neg hneg, SignType.coe_neg_one]
  · left
    simp only [affineSimplexOrientationSign, sign_pos hpos, SignType.coe_one]

theorem simplexCoordinateMatrix_self (r : LinearOrder E)
    {N : ℕ} {s : Finset E} (hs : s.card = N)
    (hindep : AffineIndependent ℝ ((↑) : s → E)) :
    simplexCoordinateMatrix r hs hs = 1 := by
  let _ := r
  ext i j
  let e := Finset.orderIsoOfFin s hs
  have hxi : (e i).1 ∈ s := (e i).2
  have hw := weights_eq hindep (subset_convexHull ℝ _ hxi)
    (w := fun v => if v = (e i).1 then 1 else 0)
    (by simp [hxi]) (by simp [ite_smul, hxi]) (e j).1 (e j).2
  have heq : (e j).1 = (e i).1 ↔ j = i :=
    ⟨fun h => e.injective (Subtype.ext h), fun h => congrArg (fun k => (e k).1) h⟩
  change weights s (e i).1 (e j).1 = if i = j then 1 else 0
  simpa only [heq, eq_comm] using hw

theorem affineSimplexOrientationSign_self (r : LinearOrder E)
    {N : ℕ} {s : Finset E} (hs : s.card = N)
    (hindep : AffineIndependent ℝ ((↑) : s → E)) :
    affineSimplexOrientationSign r hs hs = 1 := by
  simp only [affineSimplexOrientationSign, simplexCoordinateMatrix_self r hs hindep,
    Matrix.det_one, sign_one, SignType.coe_one]

theorem simplexCoordinateMatrix_mul (r : LinearOrder E)
    {N : ℕ} {s t u : Finset E} (hs : s.card = N) (ht : t.card = N) (hu : u.card = N)
    (hindep : AffineIndependent ℝ ((↑) : u → E))
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E))
    (htu : convexHull ℝ (t : Set E) ⊆ convexHull ℝ (u : Set E)) :
    simplexCoordinateMatrix r hs ht * simplexCoordinateMatrix r ht hu =
      simplexCoordinateMatrix r hs hu := by
  let _ := r
  ext i j
  let x := ((Finset.orderIsoOfFin s hs) i).1
  let y := ((Finset.orderIsoOfFin u hu) j).1
  have hxt : x ∈ convexHull ℝ (t : Set E) :=
    hst (subset_convexHull ℝ _ ((Finset.orderIsoOfFin s hs) i).2)
  have hy : y ∈ u := ((Finset.orderIsoOfFin u hu) j).2
  have hw : weights u x y = ∑ v ∈ t, weights t x v * weights u v y := by
    have h := weights_sum_smul hindep t (p := id)
      (fun v hv => htu (subset_convexHull ℝ _ hv))
      (fun v hv => weights_nonneg hxt hv) (sum_weights hxt) y hy
    simpa only [id_eq, sum_weights_smul hxt] using h
  change (∑ k, weights t x ((Finset.orderIsoOfFin t ht) k).1 *
    weights u ((Finset.orderIsoOfFin t ht) k).1 y) = weights u x y
  exact ((Finset.orderIsoOfFin t ht).toEquiv.sum_comp
    (fun v : t => weights t x v * weights u v y)).trans
    ((Finset.sum_coe_sort t (fun v => weights t x v * weights u v y)).trans hw.symm)

theorem affineSimplexOrientationSign_mul (r : LinearOrder E)
    {N : ℕ} {s t u : Finset E} (hs : s.card = N) (ht : t.card = N) (hu : u.card = N)
    (hindep : AffineIndependent ℝ ((↑) : u → E))
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E))
    (htu : convexHull ℝ (t : Set E) ⊆ convexHull ℝ (u : Set E)) :
    affineSimplexOrientationSign r hs ht * affineSimplexOrientationSign r ht hu =
      affineSimplexOrientationSign r hs hu := by
  simp only [affineSimplexOrientationSign, ← simplexCoordinateMatrix_mul r hs ht hu hindep hst htu,
    Matrix.det_mul, sign_mul, SignType.coe_mul]

end DifferentialGeometry.Topology.PiecewiseLinear
