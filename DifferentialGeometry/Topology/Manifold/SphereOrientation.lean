import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

open Manifold Metric Module
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry

private instance sphereFinrankFact (n : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sphereOutwardDeterminant (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) : ℝ :=
  Matrix.det (fun i j : Fin (n + 1) ↦
    (Fin.cases (motive := fun _ ↦ EuclideanSpace ℝ (Fin (n + 1)))
      (x : EuclideanSpace ℝ (Fin (n + 1)))
      (fun k ↦ NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
        (mfderiv (𝓡 n) (𝓡 (n + 1))
          (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
            (y : EuclideanSpace ℝ (Fin (n + 1)))) x (b k))) j) i)

private theorem det_frame_cons {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (b c : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => D (c k)) j) =
      ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => D (b k)) j) * b.det c := by
  classical
  set e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis with he
  set vb : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun j => Fin.cases x (fun k => D (b k)) j with hvb
  set vc : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun j => Fin.cases x (fun k => D (c k)) j with hvc
  set Ψb : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.constr ℝ vb with hΨb
  set Ψc : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.constr ℝ vc with hΨc
  have hevb : e.det vb = LinearMap.det Ψb := by
    have h := e.det_comp Ψb e
    have hcomp : Ψb ∘ e = vb := by
      funext j
      simp [hΨb]
    rw [hcomp, e.det_self, mul_one] at h
    exact h
  have hevc : e.det vc = LinearMap.det Ψc := by
    have h := e.det_comp Ψc e
    have hcomp : Ψc ∘ e = vc := by
      funext j
      simp [hΨc]
    rw [hcomp, e.det_self, mul_one] at h
    exact h
  set w : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun j => Fin.cases (e 0) (fun k => ∑ l, (b.repr (c k)) l • e (Fin.succ l)) j with hw
  set A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.constr ℝ w with hA
  have hAw : ∀ j, A (e j) = w j := fun j => by
    rw [hA]
    exact Basis.constr_basis (b := e) (S := ℝ) w j
  have hw0 : w 0 = e 0 := by simp [hw]
  have hwsucc : ∀ k : Fin n, w (Fin.succ k) =
      ∑ l, (b.repr (c k)) l • e (Fin.succ l) := fun k => by simp [hw]
  have hPsi0 : Ψb (e 0) = x := by
    rw [hΨb, Basis.constr_basis, hvb]
    simp
  have hPsik : ∀ k : Fin n, Ψb (∑ l, (b.repr (c k)) l • e (Fin.succ l)) = D (c k) := by
    intro k
    have hterm : ∀ l : Fin n, Ψb ((b.repr (c k)) l • e (Fin.succ l)) =
        (b.repr (c k)) l • D (b l) := by
      intro l
      rw [map_smul, hΨb, Basis.constr_basis, hvb]
      simp
    calc Ψb (∑ l, (b.repr (c k)) l • e (Fin.succ l))
        = ∑ l, (b.repr (c k)) l • D (b l) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun l _ => hterm l
      _ = D (∑ l, (b.repr (c k)) l • b l) := by
          rw [map_sum]
          simp only [map_smul]
      _ = D (c k) := by rw [b.sum_repr]
  have hcomp : Ψc = Ψb.comp A := by
    apply e.ext
    intro j
    rw [hΨc, Basis.constr_basis, LinearMap.comp_apply, hAw j]
    refine Fin.cases ?_ ?_ j
    · rw [hw0, hPsi0]
      simp [hvc]
    · intro k
      rw [hwsucc k, hPsik k]
      simp [hvc]
  have hdet : LinearMap.det Ψc = LinearMap.det Ψb * LinearMap.det A := by
    rw [hcomp, LinearMap.det_comp]
  have hAdet : LinearMap.det A = b.det c := by
    have hAe : A ∘ e = w := by
      funext j
      simp [hA]
    have h1 : LinearMap.det A = e.det w := by
      have h := e.det_comp A e
      rw [hAe, e.det_self, mul_one] at h
      exact h.symm
    rw [h1, Basis.det_apply, Basis.det_apply]
    have h00 : (e.toMatrix w) 0 0 = 1 := by
      rw [Basis.toMatrix_apply, hw0, Basis.repr_self]
      simp
    have hk0 : ∀ k : Fin n, (e.toMatrix w) (Fin.succ k) 0 = 0 := by
      intro k
      rw [Basis.toMatrix_apply, hw0, Basis.repr_self]
      exact Finsupp.single_eq_of_ne (Fin.succ_ne_zero k)
    have h0k : ∀ k : Fin n, (e.toMatrix w) 0 (Fin.succ k) = 0 := by
      intro k
      rw [Basis.toMatrix_apply, hwsucc k, map_sum]
      simp only [map_smul, Basis.repr_self]
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero l).symm, smul_zero]
    have hkl : ∀ k l : Fin n,
        (e.toMatrix w) (Fin.succ k) (Fin.succ l) = (b.toMatrix c) k l := by
      intro k l
      rw [Basis.toMatrix_apply, hwsucc l, map_sum]
      simp only [map_smul, Basis.repr_self]
      rw [Finsupp.finsetSum_apply, Basis.toMatrix_apply]
      rw [Finset.sum_eq_single k]
      · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      · intro l' _ hl'
        rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne]
        · simp
        · exact fun h => hl' (Fin.succ_injective _ h).symm
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hsub : (e.toMatrix w).submatrix Fin.succ Fin.succ = b.toMatrix c := by
      ext k l
      rw [Matrix.submatrix_apply, hkl]
    rw [Matrix.det_succ_column_zero]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · rw [h00, Fin.succAbove_zero, hsub]
      simp
    · intro i _ hi
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      rw [hk0 k]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
  rw [hevc, hevb, hdet, hAdet]

private theorem frame_det_ne_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hD : Function.Injective D) (hxnorm : ‖x‖ = 1)
    (htan : ∀ v, ⟪x, D v⟫_ℝ = 0)
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases x (fun k => D (b k)) j) ≠ 0 := by
  classical
  set e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis with he
  set v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun j => Fin.cases x (fun k => D (b k)) j with hv
  set Ψ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    e.constr ℝ v with hΨ
  have hdet : e.det v = LinearMap.det Ψ := by
    have h := e.det_comp Ψ e
    have hcomp : Ψ ∘ e = v := by
      funext j
      simp [hΨ]
    rw [hcomp, e.det_self, mul_one] at h
    exact h
  rw [hdet]
  have hker : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have hrepr : u = ∑ i : Fin (n + 1), (e.repr u) i • e i := (e.sum_repr u).symm
    have hΨu : Ψ u = (e.repr u) 0 • x +
        D (∑ k : Fin n, (e.repr u) (Fin.succ k) • b k) := by
      calc Ψ u = Ψ (∑ i, (e.repr u) i • e i) := by
            conv_lhs => rw [hrepr]
        _ = ∑ i, (e.repr u) i • v i := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΨ, Basis.constr_basis]
        _ = (e.repr u) 0 • v 0 +
              ∑ k : Fin n, (e.repr u) (Fin.succ k) • v (Fin.succ k) := by
            rw [Fin.sum_univ_succ]
        _ = (e.repr u) 0 • x +
              D (∑ k : Fin n, (e.repr u) (Fin.succ k) • b k) := by
            rw [hv]
            simp only [Fin.cases_zero, Fin.cases_succ]
            rw [map_sum]
            simp only [map_smul]
    have h0 : (e.repr u) 0 = 0 := by
      have hinner : ⟪x, (e.repr u) 0 • x +
          D (∑ k : Fin n, (e.repr u) (Fin.succ k) • b k)⟫_ℝ = 0 := by
        rw [← hΨu, hu, inner_zero_right]
      rw [inner_add_right, inner_smul_right, htan, add_zero, inner_self_eq_norm_sq_to_K,
        hxnorm] at hinner
      simpa using hinner
    have hD0 : D (∑ k : Fin n, (e.repr u) (Fin.succ k) • b k) = 0 := by
      have hzero : (e.repr u) 0 • x +
          D (∑ k : Fin n, (e.repr u) (Fin.succ k) • b k) = 0 := by
        rw [← hΨu]
        exact hu
      rwa [h0, zero_smul, zero_add] at hzero
    have hcoeff : ∑ k : Fin n, (e.repr u) (Fin.succ k) • b k = 0 := by
      simpa using hD (by simpa using hD0)
    have hall : ∀ k : Fin n, (e.repr u) (Fin.succ k) = 0 := by
      intro k
      have hmap := congrArg b.repr hcoeff
      rw [map_sum, map_zero] at hmap
      simp only [map_smul, Basis.repr_self] at hmap
      have hval : (∑ l : Fin n, (e.repr u) (Fin.succ l) • Finsupp.single l (1 : ℝ)) k =
          (e.repr u) (Fin.succ k) := by
        rw [Finsupp.finsetSum_apply, Finset.sum_eq_single k]
        · rw [Finsupp.smul_apply, Finsupp.single_eq_same]
          simp
        · intro l _ hl
          rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne]
          · simp
          · exact hl.symm
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      have hk := congrArg (fun f : Fin n →₀ ℝ => f k) hmap
      rwa [hval] at hk
    rw [hrepr, Fin.sum_univ_succ]
    simp only [h0, zero_smul, zero_add]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hall k, zero_smul]
  exact fun hdetzero =>
    ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := Ψ)).mp hdetzero) (by rw [hker])

theorem sphereOutwardDeterminant_ne_zero (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    sphereOutwardDeterminant n x b ≠ 0 := by
  classical
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (mvfderiv (𝓡 n)
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        (y : EuclideanSpace ℝ (Fin (n + 1)))) x).toLinearMap
  have hframe : sphereOutwardDeterminant n x b =
      ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
        (fun j => Fin.cases (x : EuclideanSpace ℝ (Fin (n + 1))) (fun k => D (b k)) j) :=
    rfl
  have hinj : Function.Injective D := injective_mvfderiv_subtypeVal_sphere (n := n) x
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    have h := Metric.mem_sphere.mp x.2
    rwa [dist_zero_right] at h
  have htan : ∀ v, ⟪(x : EuclideanSpace ℝ (Fin (n + 1))), D v⟫_ℝ = 0 := by
    intro v
    have hmem : mvfderiv (𝓡 n)
        (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
          (y : EuclideanSpace ℝ (Fin (n + 1)))) x v ∈
        (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin (n + 1)))})ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := n) x]
      exact ⟨v, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  rw [hframe]
  exact frame_det_ne_zero (x : EuclideanSpace ℝ (Fin (n + 1))) D hinj hnorm htan b

def sphereOutwardOrientation (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Orientation ℝ (TangentSpace (𝓡 n) x) (Fin n) :=
  if 0 < sphereOutwardDeterminant n x (EuclideanSpace.basisFun (Fin n) ℝ).toBasis then
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  else
    -((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation)

theorem sphereOutwardOrientation_characterization (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    b.orientation = sphereOutwardOrientation n x ↔ 0 < sphereOutwardDeterminant n x b := by
  classical
  let bs := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let D : (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => (mvfderiv (𝓡 n)
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        (y : EuclideanSpace ℝ (Fin (n + 1)))) x).toLinearMap
  have hframe : ∀ (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)),
      sphereOutwardDeterminant n x b =
        ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis).det
          (fun j => Fin.cases (x : EuclideanSpace ℝ (Fin (n + 1))) (fun k => D x (b k)) j) :=
    fun x b => rfl
  have hmul : ∀ (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)),
      sphereOutwardDeterminant n x b = sphereOutwardDeterminant n x bs * bs.det b := by
    intro x b
    rw [hframe x b, hframe x bs]
    exact det_frame_cons (x : EuclideanSpace ℝ (Fin (n + 1))) (D x) bs b
  have hpos_swap : ∀ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (0 < bs.det b) ↔ (0 < b.det bs) := by
    intro b
    have hunit : bs.det b * b.det bs = 1 := by
      rw [Basis.det_mul_det bs b bs, Basis.det_self]
    rw [eq_inv_of_mul_eq_one_right hunit, inv_pos]
  have hneg_of : ∀ y : ℝ, y ≠ 0 → (y < 0 ↔ ¬ 0 < y) := by
    intro y hy
    exact ⟨fun h hpos => absurd h (not_lt.mpr hpos.le),
      fun h => lt_of_le_of_ne (le_of_not_gt h) hy⟩
  have hneg_swap : ∀ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      bs.det b < 0 ↔ b.det bs < 0 := by
    intro b
    rw [hneg_of _ (bs.isUnit_det b).ne_zero, hneg_of _ (b.isUnit_det bs).ne_zero, hpos_swap b]
  change b.orientation = (if 0 < sphereOutwardDeterminant n x bs then bs.orientation
    else -bs.orientation) ↔ 0 < sphereOutwardDeterminant n x b
  by_cases h : 0 < sphereOutwardDeterminant n x bs
  · erw [if_pos h, b.orientation_eq_iff_det_pos bs, hmul x b]
    exact (hpos_swap b).symm.trans (mul_pos_iff_of_pos_left h).symm
  · have hneg : sphereOutwardDeterminant n x bs < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) (sphereOutwardDeterminant_ne_zero n x bs)
    erw [if_neg h, ← Basis.orientation_ne_iff_eq_neg bs b.orientation, ne_eq,
      not_congr (b.orientation_eq_iff_det_pos bs)]
    erw [← hneg_of _ (b.isUnit_det bs).ne_zero, ← hneg_swap b, hmul x b]
    have key : 0 < sphereOutwardDeterminant n x bs * bs.det b ↔ bs.det b < 0 := by
      rw [mul_pos_iff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
        · exact absurd h1 (not_lt.mpr hneg.le)
        · exact h2
      · intro hb
        exact Or.inr ⟨hneg, hb⟩
    exact key.symm

private theorem continuous_sphereOutwardDeterminant_chartFrame (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Continuous (fun y : (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) p).baseSet =>
      sphereOutwardDeterminant n y.1
        (((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).map
          ((tangentChartEquiv (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
            p y.1 y.2).symm))) := by
  classical
  let S : Type := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let bs := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let ι : S → EuclideanSpace ℝ (Fin (n + 1)) := fun y => y
  have hι : ContMDiff (𝓡 n) (𝓡 (n + 1)) 1 ι := contMDiff_coe_sphere
  have htmap : Continuous (tangentMap (𝓡 n) (𝓡 (n + 1)) ι) :=
    hι.continuous_tangentMap le_rfl
  have hsnd : Continuous (fun q : TangentBundle (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) => q.2) :=
    (contMDiff_snd_tangentBundle_modelSpace
      (I := 𝓡 (n + 1)) (H := EuclideanSpace ℝ (Fin (n + 1))) (n := 0)).continuous
  have hsec : ∀ k : Fin n, Continuous (fun y : ↥e.baseSet =>
      (e.toOpenPartialHomeomorph.symm (y.1, bs k) : TangentBundle (𝓡 n) S)) := by
    intro k
    exact (Bundle.Trivialization.continuousOn_symm_prodMk_left e (v := bs k)).comp_continuous
      continuous_subtype_val (fun y => y.2)
  let frame : ↥e.baseSet → Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun y j =>
    Fin.cases (y.1 : EuclideanSpace ℝ (Fin (n + 1)))
      (fun k => (NormedSpace.fromTangentSpace (ι y.1)
        ((tangentMap (𝓡 n) (𝓡 (n + 1)) ι
          (e.toOpenPartialHomeomorph.symm (y.1, bs k))).2) :
          EuclideanSpace ℝ (Fin (n + 1)))) j
  have hframe : ∀ j : Fin (n + 1), Continuous (fun y : ↥e.baseSet => frame y j) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · change Continuous fun y : ↥e.baseSet => ((y.1 : S) : EuclideanSpace ℝ (Fin (n + 1)))
      exact continuous_subtype_val.comp continuous_subtype_val
    · intro k
      refine (hsnd.comp (htmap.comp (hsec k))).congr (fun y => ?_)
      rfl
  have hM : Continuous (fun y : ↥e.baseSet => Matrix.of (fun i j => frame y j i)) := by
    apply continuous_matrix
    intro i j
    exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp (hframe j)
  refine hM.matrix_det.congr fun y => ?_
  have hentry : ∀ j : Fin (n + 1), frame y j =
      Fin.cases (y.1 : EuclideanSpace ℝ (Fin (n + 1)))
        (fun k => (NormedSpace.fromTangentSpace (ι y.1) (mfderiv (𝓡 n) (𝓡 (n + 1)) ι y.1
          ((bs.map ((e.linearEquivAt ℝ y.1 y.2).symm)) k)) :
            EuclideanSpace ℝ (Fin (n + 1)))) j := by
    intro j
    refine Fin.cases rfl ?_ j
    intro k
    change (NormedSpace.fromTangentSpace (ι y.1)
        ((tangentMap (𝓡 n) (𝓡 (n + 1)) ι
          (e.toOpenPartialHomeomorph.symm (y.1, bs k))).2) :
          EuclideanSpace ℝ (Fin (n + 1))) =
      (NormedSpace.fromTangentSpace (ι y.1) (mfderiv (𝓡 n) (𝓡 (n + 1)) ι y.1
        ((bs.map ((e.linearEquivAt ℝ y.1 y.2).symm)) k)) :
          EuclideanSpace ℝ (Fin (n + 1)))
    rw [show (e.toOpenPartialHomeomorph.symm (y.1, bs k) : TangentBundle (𝓡 n) S) =
        ⟨y.1, e.symm y.1 (bs k)⟩ from (Bundle.Trivialization.mk_symm e y.2 (bs k)).symm]
    rw [show (tangentMap (𝓡 n) (𝓡 (n + 1)) ι
        (⟨y.1, e.symm y.1 (bs k)⟩ : TangentBundle (𝓡 n) S)).2 =
        mfderiv (𝓡 n) (𝓡 (n + 1)) ι y.1 (e.symm y.1 (bs k)) from rfl,
      ← Bundle.Trivialization.linearEquivAt_symm_apply (R := ℝ) e y.1 y.2 (bs k),
      Basis.map_apply]
  change (Matrix.of (fun i j => frame y j i)).det =
    sphereOutwardDeterminant n y.1 (bs.map ((e.linearEquivAt ℝ y.1 y.2).symm))
  unfold sphereOutwardDeterminant
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [hentry j]

theorem sphereOutwardOrientation_locallyConstant (n : ℕ) (hn : 1 ≤ n) :
    ∀ p x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) p).baseSet,
      ∃ U : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
        IsOpen U ∧ x ∈ U ∧
        ∃ hU : U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n)) p).baseSet,
        ∀ y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ∀ hy : y ∈ U,
          Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) _ p y (hU hy))
              (sphereOutwardOrientation n y) =
            Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) _ p x hx)
              (sphereOutwardOrientation n x) := by
  intro p x hx
  classical
  let _ := hn
  let S : Type := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let bs := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let F : ↥e.baseSet → ℝ := fun y => sphereOutwardDeterminant n y.1
    (bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm))
  have hF : Continuous F := continuous_sphereOutwardDeterminant_chartFrame n p
  have hne : ∀ y : ↥e.baseSet, F y ≠ 0 := fun y => sphereOutwardDeterminant_ne_zero n y.1 _
  have key : ∀ y : ↥e.baseSet,
      (0 < F y → Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
        (sphereOutwardOrientation n y.1) = bs.orientation) ∧
      (F y < 0 → Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
        (sphereOutwardOrientation n y.1) = -bs.orientation) := by
    intro y
    have hmap : (bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).map
        (tangentChartEquiv (𝓡 n) S p y.1 y.2) = bs := by
      ext k
      simp [Basis.map_apply]
    constructor
    · intro hpos
      have hb : (bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).orientation =
          sphereOutwardOrientation n y.1 :=
        (sphereOutwardOrientation_characterization n y.1 _).mpr hpos
      calc Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
            (sphereOutwardOrientation n y.1)
          = Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
              ((bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).orientation) := by
              rw [hb]
        _ = ((bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).map
              (tangentChartEquiv (𝓡 n) S p y.1 y.2)).orientation :=
              (Basis.orientation_map _ _).symm
        _ = bs.orientation := by rw [hmap]
    · intro hneg
      have hne' : sphereOutwardOrientation n y.1 ≠
          (bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).orientation := by
        intro h
        exact absurd ((sphereOutwardOrientation_characterization n y.1 _).mp h.symm)
          (not_lt.mpr hneg.le)
      calc Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
            (sphereOutwardOrientation n y.1)
          = -Orientation.map (Fin n) (tangentChartEquiv (𝓡 n) S p y.1 y.2)
              ((bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).orientation) := by
              rw [show sphereOutwardOrientation n y.1 =
                  -((bs.map ((tangentChartEquiv (𝓡 n) S p y.1 y.2).symm)).orientation) from
                (Basis.orientation_ne_iff_eq_neg _ _).mp hne', Orientation.map_neg]
        _ = -bs.orientation := by
              rw [← Basis.orientation_map, hmap]
  by_cases hpos : 0 < F ⟨x, hx⟩
  · let T : Set ↥e.baseSet := {y | 0 < F y}
    have hT : IsOpen T := isOpen_lt continuous_const hF
    obtain ⟨U₀, hU₀open, hU₀pre⟩ := isOpen_induced_iff.mp hT
    refine ⟨U₀ ∩ e.baseSet, hU₀open.inter e.open_baseSet, ⟨?_, hx⟩, fun y hy => hy.2, ?_⟩
    · have hxT : (⟨x, hx⟩ : ↥e.baseSet) ∈ T := hpos
      have : (⟨x, hx⟩ : ↥e.baseSet) ∈ Subtype.val ⁻¹' U₀ := by
        rw [hU₀pre]
        exact hxT
      exact this
    · intro y hy
      have hyT : (⟨y, hy.2⟩ : ↥e.baseSet) ∈ T := by
        have h : (⟨y, hy.2⟩ : ↥e.baseSet) ∈ Subtype.val ⁻¹' U₀ := hy.1
        rwa [hU₀pre] at h
      rw [(key ⟨y, hy.2⟩).1 hyT, (key ⟨x, hx⟩).1 hpos]
  · have hnegx : F ⟨x, hx⟩ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hne ⟨x, hx⟩)
    let T : Set ↥e.baseSet := {y | F y < 0}
    have hT : IsOpen T := isOpen_lt hF continuous_const
    obtain ⟨U₀, hU₀open, hU₀pre⟩ := isOpen_induced_iff.mp hT
    refine ⟨U₀ ∩ e.baseSet, hU₀open.inter e.open_baseSet, ⟨?_, hx⟩, fun y hy => hy.2, ?_⟩
    · have hxT : (⟨x, hx⟩ : ↥e.baseSet) ∈ T := hnegx
      have : (⟨x, hx⟩ : ↥e.baseSet) ∈ Subtype.val ⁻¹' U₀ := by
        rw [hU₀pre]
        exact hxT
      exact this
    · intro y hy
      have hyT : (⟨y, hy.2⟩ : ↥e.baseSet) ∈ T := by
        have h : (⟨y, hy.2⟩ : ↥e.baseSet) ∈ Subtype.val ⁻¹' U₀ := hy.1
        rwa [hU₀pre] at h
      rw [(key ⟨y, hy.2⟩).2 hyT, (key ⟨x, hx⟩).2 hnegx]

theorem sphereOrientation_eq_of_characterization (n : ℕ)
    (o o' : ManifoldOrientation (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)
    (ho : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b)
    (ho' : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o'.orientation x ↔ 0 < sphereOutwardDeterminant n x b) :
    o = o' := by
  apply ManifoldOrientation.ext
  intro x
  have : Module.Finite ℝ (TangentSpace (𝓡 n) x) := by
    change Module.Finite ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  let b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    Module.finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) x) hdim
  have key : (b.orientation = o.orientation x) ↔ (b.orientation = o'.orientation x) :=
    (ho x b).trans (ho' x b).symm
  rcases b.orientation_eq_or_eq_neg (o.orientation x) with h | h
  · exact h.trans (key.mp h.symm)
  · have hne : o.orientation x ≠ b.orientation := by
      intro hb
      exact Module.Ray.ne_neg_self b.orientation (hb.symm.trans h)
    have hne' : o'.orientation x ≠ b.orientation := fun hb => hne (key.mpr hb.symm).symm
    exact h.trans ((Basis.orientation_ne_iff_eq_neg b (o'.orientation x)).mp hne').symm

theorem exists_sphere_orientation (n : ℕ) (hn : 1 ≤ n) :
    ∃ o : ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n,
      ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
        b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b := by
  exact ⟨{ dimension_eq := finrank_euclideanSpace_fin
           orientation := sphereOutwardOrientation n
           locally_constant := sphereOutwardOrientation_locallyConstant n hn },
    fun x b => sphereOutwardOrientation_characterization n x b⟩

theorem exists_unique_sphere_orientation (n : ℕ) (hn : 1 ≤ n) :
    ∃! o : ManifoldOrientation (𝓡 n)
        (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n,
      ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
        b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b :=
  have h := exists_sphere_orientation n hn
  ⟨h.choose, h.choose_spec, fun o' ho' => sphereOrientation_eq_of_characterization n o' h.choose ho' h.choose_spec⟩

def sphereOrientation (n : ℕ) (hn : 1 ≤ n) :
    ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n :=
  (exists_unique_sphere_orientation n hn).exists.choose

theorem sphereOrientation_characterization (n : ℕ) (hn : 1 ≤ n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    b.orientation = (sphereOrientation n hn).orientation x ↔
      0 < sphereOutwardDeterminant n x b :=
  (exists_unique_sphere_orientation n hn).exists.choose_spec x b

theorem sphereOrientation_unique (n : ℕ) (hn : 1 ≤ n)
    (o : ManifoldOrientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)
    (ho : ∀ x, ∀ b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x),
      b.orientation = o.orientation x ↔ 0 < sphereOutwardDeterminant n x b) :
    o = sphereOrientation n hn :=
  (exists_unique_sphere_orientation n hn).unique ho
    (sphereOrientation_characterization n hn)

end DifferentialGeometry
