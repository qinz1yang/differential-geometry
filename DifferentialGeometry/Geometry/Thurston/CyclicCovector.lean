import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import DifferentialGeometry.Geometry.Thurston.FlatCircleDesc

/-!
# Integer coordinates for cyclic affine holonomy

A finite cyclic linear part and a full basis of the actual translation module construct an
invariant integer covector. Averaging basis coordinates is nonzero on the constructed free
axis. Multiplication by the finite order makes every actual affine group increment integral.
The full translation lattice and cyclic linear part are structural inputs of this tier;
no covector, circle map or torus fibre is assumed.
-/

set_option autoImplicit false

noncomputable section

open Module Function
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]
  {ι : Type*} [instIndex : Finite ι]

omit instFD in
private theorem basis_coord_integer (b : Basis ι ℝ V) (i : ι) {v : V}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ∃ m : ℤ, b.coord i v = m := by
  classical
  let instFintype : Fintype ι := Fintype.ofFinite ι
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  refine ⟨m i, ?_⟩
  rw [← hm, map_sum]
  simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

private def cyclicCoordinate (b : Basis ι ℝ V) (i : ι)
    (A : V ≃ₗᵢ[ℝ] V) (p : ℕ) : V →L[ℝ] ℝ :=
  ∑ k ∈ Finset.range p,
    (b.coord i).toContinuousLinearMap.comp (A ^ k).toContinuousLinearMap

omit instIndex in
private theorem cyclicCoordinate_apply (b : Basis ι ℝ V) (i : ι)
    (A : V ≃ₗᵢ[ℝ] V) (p : ℕ) (v : V) :
    cyclicCoordinate b i A p v = ∑ k ∈ Finset.range p, b.coord i ((A ^ k) v) := by
  simp [cyclicCoordinate]

omit instIndex in
private theorem cyclicCoordinate_invariant (b : Basis ι ℝ V) (i : ι)
    (A : V ≃ₗᵢ[ℝ] V) (p : ℕ) (horder : A ^ p = 1) (v : V) :
    cyclicCoordinate b i A p (A v) = cyclicCoordinate b i A p v := by
  rw [cyclicCoordinate_apply, cyclicCoordinate_apply]
  have hshift (k : ℕ) : (A ^ k) (A v) = (A ^ (k + 1)) v := by
    rw [pow_succ]
    rfl
  simp_rw [hshift]
  have h := (Finset.sum_range_succ (fun k => b.coord i ((A ^ k) v)) p).symm.trans
    (Finset.sum_range_succ' (fun k => b.coord i ((A ^ k) v)) p)
  simp only [horder, LinearIsometryEquiv.coe_one, id_eq, pow_zero] at h
  exact add_right_cancel h.symm

omit instFD in
private theorem invariant_zpow (ell : V →L[ℝ] ℝ) (A : V ≃ₗᵢ[ℝ] V)
    (hA : ∀ v, ell (A v) = ell v) (k : ℤ) (v : V) :
    ell ((A ^ k) v) = ell v := by
  have hi (x : V) : ell (A⁻¹ x) = ell x := by
    simpa using (hA (A⁻¹ x)).symm
  have h := zpow_induction_left (g := A) (P := fun B => ∀ x, ell (B x) = ell x)
    (by intro x; rfl)
    (by intro B hB x; change ell (A (B x)) = ell x; rw [hA, hB])
    (by intro B hB x; change ell (A⁻¹ (B x)) = ell x; rw [hi, hB]) k
  exact h v

omit instFD in
private theorem affine_power_coordinate (ell : V →L[ℝ] ℝ) (γ : V ≃ᵃⁱ[ℝ] V)
    (hγ : ∀ v, ell (γ.linearIsometryEquiv v) = ell v) (p : ℕ) :
    ell ((γ ^ p) 0) = (p : ℝ) * ell (γ 0) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ']
    change ell (γ ((γ ^ p) 0)) = _
    rw [affineIsometry_apply, map_add, hγ, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem exists_cyclicAffine_integerCovector
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (g : G) (hfree : ∀ x : V, g.val x ≠ x) (p : ℕ) (hp : 0 < p)
    (horder : g.val.linearIsometryEquiv ^ p = 1)
    (hcyclic : ∀ γ : G, ∃ k : ℤ,
      γ.val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ k) :
    ∃ ell : V →L[ℝ] ℝ, Surjective ell ∧
      (∀ γ : G, ∀ v : V, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      ∀ v ∈ affineTranslationModule G, ∃ m : ℤ, ell v = m := by
  classical
  let instFintype : Fintype ι := Fintype.ofFinite ι
  let A := g.val.linearIsometryEquiv
  obtain ⟨x, q, hx, hq⟩ := exists_affineAxis_point g.val
  have hq0 : q ≠ 0 := by
    intro heq
    exact hfree x (by simpa [heq] using hx)
  obtain ⟨i, hi⟩ : ∃ i, b.coord i q ≠ 0 := by
    by_contra! hzero
    apply hq0
    apply b.repr.injective
    ext i
    simpa [Basis.coord_apply] using hzero i
  let ell0 := cyclicCoordinate b i A p
  have hinv (v : V) : ell0 (A v) = ell0 v :=
    cyclicCoordinate_invariant b i A p horder v
  have hlin (γ : G) (v : V) : ell0 (γ.val.linearIsometryEquiv v) = ell0 v := by
    obtain ⟨k, hk⟩ := hcyclic γ
    rw [hk]
    exact invariant_zpow ell0 A hinv k v
  have hpq (k : ℕ) : (A ^ k) q = q := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ']; change A ((A ^ k) q) = q; rw [ih]; exact hq
  have heq : ell0 q = (p : ℝ) * b.coord i q := by
    rw [cyclicCoordinate_apply]
    simp_rw [hpq]
    simp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have he0 : ell0 q ≠ 0 := by rw [heq]; exact mul_ne_zero hp0 hi
  have hint (v : V) (hv : v ∈ affineTranslationModule G) :
      ∃ m : ℤ, ell0 v = m := by
    have hmem (k : ℕ) : (A ^ k) v ∈ affineTranslationModule G := by
      induction k with
      | zero => exact hv
      | succ k ih =>
        rw [pow_succ']
        exact affineTranslationModule_linear_mem G g ih
    choose m hm using fun k : Fin p =>
      basis_coord_integer b i (hb.symm ▸ hmem k.val)
    refine ⟨∑ k : Fin p, m k, ?_⟩
    rw [cyclicCoordinate_apply, ← Fin.sum_univ_eq_sum_range]
    simp_rw [hm]
    norm_cast
  have hpow (γ : G) : (γ.val ^ p).linearIsometryEquiv = 1 := by
    change affineLinearHom (γ.val ^ p) = 1
    rw [map_pow]
    change γ.val.linearIsometryEquiv ^ p = 1
    obtain ⟨k, hk⟩ := hcyclic γ
    rw [hk, ← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast, horder]
    simp
  have htrans (γ : G) : (γ.val ^ p) 0 ∈ affineTranslationModule G := by
    change AffineIsometryEquiv.constVAdd ℝ V ((γ.val ^ p) 0) ∈ G
    have he : AffineIsometryEquiv.constVAdd ℝ V ((γ.val ^ p) 0) = γ.val ^ p := by
      ext v
      change (γ.val ^ p) 0 + v = (γ.val ^ p) v
      have hv := affineIsometry_apply (γ.val ^ p) v
      rw [hpow] at hv
      simpa [add_comm] using hv.symm
    rw [he]
    exact G.pow_mem γ.property p
  let ell : V →L[ℝ] ℝ := (p : ℝ) • ell0
  refine ⟨ell, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.surjective_iff_ne_zero.mpr
    intro hzero
    have hz : ell q = 0 := congrArg (fun f : V →ₗ[ℝ] ℝ => f q) hzero
    exact (mul_ne_zero hp0 he0) hz
  · intro γ v
    change (p : ℝ) * ell0 (γ.val.linearIsometryEquiv v) = (p : ℝ) * ell0 v
    rw [hlin]
  · intro γ
    obtain ⟨m, hm⟩ := hint _ (htrans γ)
    refine ⟨m, ?_⟩
    change (p : ℝ) * ell0 (γ.val 0) = m
    exact (affine_power_coordinate ell0 γ.val (hlin γ) p).symm.trans hm
  · intro v hv
    obtain ⟨m, hm⟩ := hint v hv
    refine ⟨(p : ℤ) * m, ?_⟩
    change (p : ℝ) * ell0 v = _
    rw [hm]
    norm_cast

end DifferentialGeometry.Geometry.FlatSurface

open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_circleSubmersion_of_cyclicAffineCover (W : CompactCarrier)
    (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = Geometry.FlatSurface.affineTranslationModule G)
    (g : G) (hfree : ∀ x, g.val x ≠ x) (n : ℕ) (hn : 0 < n)
    (horder : g.val.linearIsometryEquiv ^ n = 1)
    (hcyclic : ∀ γ : G, ∃ k : ℤ,
      γ.val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ k)
    (p : E3 → W.Carrier) (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p)
    (hs : Surjective p) (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, (γ.val : E3 → E3) x = y) :
    ∃ (ell : E3 →L[ℝ] ℝ) (F : W.Carrier → Circle),
      Surjective ell ∧ ContMDiff W.model (𝓡 1) ∞ F ∧ Surjective F ∧
      (∀ z, Surjective (mfderiv W.model (𝓡 1) F z)) ∧
      ∀ x, F (p x) = AddCircle.diffeomorphCircle (ell x : AddCircle (1 : ℝ)) := by
  obtain ⟨ell, hel, hlin, hint, _hlat⟩ :=
    Geometry.FlatSurface.exists_cyclicAffine_integerCovector G b hb g hfree n hn horder hcyclic
  obtain ⟨F, hF, hFs, hFd, hFe⟩ :=
    exists_circleSubmersion_of_affineDeckCoordinate W G p hp hs hrel ell hel hlin hint
  exact ⟨ell, F, hel, hF, hFs, hFd, hFe⟩

end GC.GraphManifold.FlatTorus
