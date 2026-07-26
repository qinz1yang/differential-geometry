import DifferentialGeometry.Geometry.Comparison.Variation.JacobiGram
import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall

/-!
# Radial Gram data for volume comparison

This module connects the local radial-Jacobi producers to the Gram-matrix
calculus used by Bishop--Gromov comparison.
-/

noncomputable section

open Set Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

/-- Before the first selected normal-coordinate boundary, a linearly
independent family of variation directions gives linearly independent radial
Jacobi fields at every nonzero time.  Time scaling reduces the claim to the
time-one differential of `expMapDiffeo`, whose local-diffeomorphism derivative
is injective on its source.  The Gram/Riccati layer consumes this positivity
input; no separate no-conjugate-points hypothesis is required. -/
lemma radialJacobi_li
    {ι : Type*} {v : ι → E}
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {t : ℝ}
    (hv : LinearIndependent ℝ v) (ht : t ≠ 0)
    (htx_src : t • x ∈ (expMapDiffeo (I := I) g p).source)
    (htx_rad : ‖t • x‖ < expMapC2Radius (I := I) g p) :
    LinearIndependent ℝ fun i ↦
      radialJacobiField (I := I) g p x (v i) t := by
  let L := mfderiv 𝓘(ℝ, E) I
    (fun b : E ↦ (expMap (I := I) g p
      (show TangentSpace I p from b) : M)) (t • x)
  have hlocal := PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(ℝ, E)) (J := I) (n := 1) (expMapDiffeo (I := I) g p) htx_src
  have hLinj : Function.Injective L := by
    dsimp only [L]
    rw [← expDiffeo_mfderiv (I := I) g p htx_src]
    exact (hlocal.mfderivToContinuousLinearEquiv (by norm_num)).injective
  let u : ℝˣ := Units.mk0 t ht
  let us : ι → ℝˣ := fun _ ↦ u
  have hscaled : LinearIndependent ℝ fun i ↦ t • v i := by
    have hus : us • v = fun i ↦ t • v i := by
      funext i
      rfl
    rw [← hus]
    exact hv.units_smul us
  have hmapped : LinearIndependent ℝ fun i ↦ L (t • v i) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  have hfield :
      (fun i ↦ radialJacobiField (I := I) g p x (v i) t) =
        fun i ↦ L (t • v i) := by
    funext i
    rw [radialJacobi_scale (I := I) g p x (v i) t,
      radialJacobi_one (I := I) g p (t • x) (t • v i) htx_rad]
  rw [hfield]
  exact hmapped

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a common small radial scale, two radial Jacobi fields that vanish at the
center have zero Wronskian throughout every compact subinterval of `(0, 1)`.
The direction vectors are kept inside the common local-variation radius; a
later transverse-frame consumer may enforce this by a fixed positive scaling. -/
theorem radial_wronsk_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w z : E,
      ‖x‖ < r → ‖w‖ < r → ‖z‖ < r →
      ∀ {b : ℝ}, 0 < b → b < 1 → ∀ t ∈ Icc (0 : ℝ) b,
        jacobiWronskian g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w)
          (radialJacobiField (I := I) g p x z) t = 0 := by
  obtain ⟨rd, hrd, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨rj, hrj, hJac⟩ := exists_jacobi_Ioo (I := I) g p
  obtain ⟨r0, hr0, hJac0⟩ := exists_radialJacobi_zero_radius (I := I) g hEnorm p
  let re : ℝ := expMapC2Radius (I := I) g p
  let r : ℝ := min rd (min rj (min r0 re))
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  have hr : 0 < r := by
    dsimp [r, re]
    exact lt_min hrd (lt_min hrj (lt_min hr0 hre))
  refine ⟨r, hr, ?_⟩
  intro x w z hx hw hz b hb hblt t ht
  have hr_rd : r ≤ rd := min_le_left _ _
  have hr_rj : r ≤ rj := (min_le_right _ _).trans (min_le_left _ _)
  have hr_r0 : r ≤ r0 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_re : r ≤ re :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxrd : ‖x‖ < rd := hx.trans_le hr_rd
  have hxj : ‖x‖ < rj := hx.trans_le hr_rj
  have hx0 : ‖x‖ < r0 := hx.trans_le hr_r0
  have hxe : ‖x‖ < expMapC2Radius (I := I) g p := by
    simpa only [re] using hx.trans_le hr_re
  have hwrd : ‖w‖ < rd := hw.trans_le hr_rd
  have hzrd : ‖z‖ < rd := hz.trans_le hr_rd
  have hwj : ‖w‖ < rj := hw.trans_le hr_rj
  have hzj : ‖z‖ < rj := hz.trans_le hr_rj
  have hw0 : ‖w‖ < r0 := hw.trans_le hr_r0
  have hz0 : ‖z‖ < r0 := hz.trans_le hr_r0
  have hb1 : b ≤ 1 := hblt.le
  obtain ⟨hJdiff, hDJdiff⟩ := hdiff x w hxrd hwrd hb1
  obtain ⟨hKdiff, hDKdiff⟩ := hdiff x z hxrd hzrd hb1
  have hJ0 := hJac0 x w hx0 hw0
  have hK0 := hJac0 x z hx0 hz0
  have hJacJ : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa only [radialCurve] using hJ0
    · exact hJac x w hxj hwj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  have hJacK : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x z) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa only [radialCurve] using hK0
    · exact hJac x z hxj hzj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  exact wronskian_zero_on (I := I) (by norm_num) g
    (radialCurve (I := I) g p x)
    (radialJacobiField (I := I) g p x w)
    (radialJacobiField (I := I) g p x z)
    (radialCurve_contMDiffAt_Icc (I := I) g p x hb1 hxe)
    hJdiff hKdiff hDJdiff hDKdiff hJacJ hJacK
    (radialJacobi_zero (I := I) g p x w)
    (radialJacobi_zero (I := I) g p x z) t ht

end Radial

section PolarDensity

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def basisGram
    {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (f : κ → V) : Matrix κ κ ℝ :=
  Matrix.of fun i j => β (f i) (f j)

private lemma gram_basis_change
    {U V κ : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (L : U →L[ℝ] V)
    (e B : Module.Basis κ ℝ U) :
    basisGram β (fun i => L (B i)) =
      (e.toMatrix B).transpose * basisGram β (fun i => L (e i)) * e.toMatrix B := by
  classical
  ext i j
  change β (L (B i)) (L (B j)) = _
  rw [show B i = ∑ k, (e.repr (B i)) k • e k from (e.sum_repr (B i)).symm]
  rw [show B j = ∑ l, (e.repr (B j)) l • e l from (e.sum_repr (B j)).symm]
  simp only [basisGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Module.Basis.toMatrix_apply, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring_nf

private lemma gram_det_change
    {U V κ : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype κ] [DecidableEq κ]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (L : U →L[ℝ] V)
    (e B : Module.Basis κ ℝ U) :
    (basisGram β (fun i => L (B i))).det =
      (e.det B) ^ 2 * (basisGram β (fun i => L (e i))).det := by
  rw [gram_basis_change β L e B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Module.Basis.det_apply]
  ring

private noncomputable def basisIndexEquiv
    (B : Module.Basis (Option ι) ℝ E) :
    Option ι ≃ Fin (Module.finrank ℝ E) :=
  Fintype.equivOfCardEq (by
    simpa using (Module.finrank_eq_card_basis B).symm)

private noncomputable def modelBasisFor
    (B : Module.Basis (Option ι) ℝ E) : Module.Basis (Option ι) ℝ E :=
  (chartModelBasis E).reindex (basisIndexEquiv B).symm

private noncomputable def endpointGram
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {κ : Type*} (v : κ → E) : Matrix κ κ ℝ :=
  Matrix.of fun i j =>
    g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x (v i) 1)
      (radialJacobiField (I := I) g p x (v j) 1)

private lemma endpoint_det_basis
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    (endpointGram (I := I) g p x B).det =
      ((modelBasisFor B).det B) ^ 2 *
        (radialJacobiGram (I := I) g p x).det := by
  let q : M := expMap (I := I) g p (show TangentSpace I p from x)
  let L : E →L[ℝ] TangentSpace I q := mfderiv 𝓘(ℝ, E) I
    (fun z : E => (expMap (I := I) g p
      (show TangentSpace I p from z) : M)) x
  have hB : endpointGram (I := I) g p x B =
      basisGram (g.inner q) (fun i => L (B i)) := by
    ext i j
    simp only [endpointGram, basisGram, Matrix.of_apply]
    rw [radialJacobi_one (I := I) g p x (B i) hxrad,
      radialJacobi_one (I := I) g p x (B j) hxrad]
    rfl
  have hmodel : endpointGram (I := I) g p x (modelBasisFor B) =
      Matrix.reindex (basisIndexEquiv B).symm (basisIndexEquiv B).symm
        (radialJacobiGram (I := I) g p x) := by
    ext i j
    simp only [endpointGram, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, radialJacobiGram_apply, modelBasisFor,
      Module.Basis.reindex_apply, Equiv.symm_symm]
  have hmodelDet : (endpointGram (I := I) g p x (modelBasisFor B)).det =
      (radialJacobiGram (I := I) g p x).det := by
    rw [hmodel, Matrix.det_reindex_self]
  have hmodelGram :
      basisGram (g.inner q) (fun i => L ((modelBasisFor B) i)) =
        endpointGram (I := I) g p x (modelBasisFor B) := by
    ext i j
    simp only [basisGram, endpointGram, Matrix.of_apply]
    rw [radialJacobi_one (I := I) g p x ((modelBasisFor B) i) hxrad,
      radialJacobi_one (I := I) g p x ((modelBasisFor B) j) hxrad]
    rfl
  rw [hB]
  rw [gram_det_change (g.inner q) L (modelBasisFor B) B]
  rw [hmodelGram, hmodelDet]

private noncomputable def transverseEndGram
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (r : ℝ)
    (B : Module.Basis (Option ι) ℝ E) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    g.inner (radialCurve (I := I) g p u r)
      (radialJacobiField (I := I) g p (r • u) (B (some i)) 1)
      (radialJacobiField (I := I) g p (r • u) (B (some j)) 1)

private lemma bilin_smul_left
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (a : ℝ) (x y : V) :
    β (a • x) y = a * β x y := by
  have h := congrArg (fun A : V →L[ℝ] ℝ => A y) (β.map_smul a x)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h

private lemma bilin_smul_both
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (a : ℝ) (x y : V) :
    β (a • x) (a • y) = a ^ 2 * β x y := by
  rw [bilin_smul_left, (β x).map_smul]
  simp only [smul_eq_mul, pow_two]
  ring

private lemma endpoint_det_split
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u) (hperp : ∀ i, g.inner p u (B (some i)) = 0)
    {r : ℝ} (hr : 0 < r)
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    (endpointGram (I := I) g p (r • u) B).det =
      g.inner p u u * (transverseEndGram (I := I) g p u r B).det := by
  let q : M := radialCurve (I := I) g p u r
  let L : E →L[ℝ] TangentSpace I q := mfderiv 𝓘(ℝ, E) I
    (fun z : E => (expMap (I := I) g p
      (show TangentSpace I p from z) : M)) (r • u)
  have hfield : ∀ o : Option ι,
      radialJacobiField (I := I) g p (r • u) (B o) 1 = L (B o) := by
    intro o
    simpa only [L, q, radialCurve] using
      radialJacobi_one (I := I) g p (r • u) (B o) hrad
  have hgauss := gauss_lemma_pullback (I := I) g p
    (mem_expDomain_of_norm_lt_radius (I := I) g p hrad) hrad
  have hLru : L (r • u) = r • L u := L.map_smul r u
  have hdiagRaw : g.inner q (L (r • u)) (L (r • u)) =
      g.inner p (r • u) (r • u) := by
    simpa only [q, radialCurve, L] using hgauss.1
  have hdiagScaled : r ^ 2 * g.inner q (L u) (L u) =
      r ^ 2 * g.inner p u u := by
    rw [hLru] at hdiagRaw
    rw [bilin_smul_both] at hdiagRaw
    have hbaseScale : g.inner p (r • u) (r • u) =
        r ^ 2 * g.inner p u u :=
      bilin_smul_both (g.inner p) r u u
    rw [hbaseScale] at hdiagRaw
    exact hdiagRaw
  have hdiag : g.inner q (L u) (L u) = g.inner p u u := by
    nlinarith [sq_pos_of_pos hr]
  have hcross : ∀ i, g.inner q (L u) (L (B (some i))) = 0 := by
    intro i
    have horth : g.inner p (r • u) (B (some i)) = 0 := by
      calc
        g.inner p (r • u) (B (some i)) =
            r * g.inner p u (B (some i)) :=
          bilin_smul_left (g.inner p) r u (B (some i))
        _ = 0 := by rw [hperp i, mul_zero]
    have hs := hgauss.2 horth
    have hsRaw : g.inner q (L (r • u)) (L (B (some i))) = 0 := by
      simpa only [q, radialCurve, L] using hs
    have hs' : r * g.inner q (L u) (L (B (some i))) = 0 := by
      rw [hLru] at hsRaw
      rw [bilin_smul_left] at hsRaw
      exact hsRaw
    exact (mul_eq_zero.mp hs').resolve_left hr.ne'
  let e : Option ι ≃ ι ⊕ PUnit.{1} :=
    Equiv.optionEquivSumPUnit.{0} ι
  let D : Matrix PUnit.{1} PUnit.{1} ℝ :=
    Matrix.of fun _ _ => g.inner p u u
  have hblock :
      Matrix.reindex e e (endpointGram (I := I) g p (r • u) B) =
        Matrix.fromBlocks (transverseEndGram (I := I) g p u r B)
          0 0 D := by
    ext a b
    rcases a with i | a
    · rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          endpointGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
          transverseEndGram, radialCurve]
        rfl
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₁₂, hfield, hBu, q]
        rw [g.symm]
        exact hcross i
    · cases a
      rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr,
          Equiv.optionEquivSumPUnit_symm_inl, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₂₁, hfield, hBu, q]
        exact hcross j
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr, endpointGram, Matrix.of_apply,
          Matrix.fromBlocks_apply₂₂, D, hfield, hBu, q]
        exact hdiag
  have hreindexDet :
      (Matrix.reindex e e (endpointGram (I := I) g p (r • u) B)).det =
        (endpointGram (I := I) g p (r • u) B).det :=
    Matrix.det_reindex_self e _
  have hDdet : D.det = g.inner p u u := by
    rw [Matrix.det_unique]
    rfl
  have hdet : (endpointGram (I := I) g p (r • u) B).det =
      (transverseEndGram (I := I) g p u r B).det * D.det := by
    rw [← hreindexDet, hblock, Matrix.det_fromBlocks_zero₂₁]
  rw [hDdet] at hdet
  simpa only [mul_comm] using hdet

omit [Fintype ι] [DecidableEq ι] in
private lemma curveGram_end
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E) {r : ℝ}
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    curveGram (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (B (some i))) r =
      (r ^ 2) • transverseEndGram (I := I) g p u r B := by
  ext i j
  have hi : radialJacobiField (I := I) g p u (B (some i)) r =
      r • radialJacobiField (I := I) g p (r • u) (B (some i)) 1 := by
    calc
      radialJacobiField (I := I) g p u (B (some i)) r =
          radialJacobiField (I := I) g p (r • u) (r • B (some i)) 1 :=
        radialJacobi_scale (I := I) g p u (B (some i)) r
      _ = r • radialJacobiField (I := I) g p (r • u) (B (some i)) 1 :=
        radialJacobi_one_smul (I := I) g p (r • u) (B (some i)) r hrad
  have hj : radialJacobiField (I := I) g p u (B (some j)) r =
      r • radialJacobiField (I := I) g p (r • u) (B (some j)) 1 := by
    calc
      radialJacobiField (I := I) g p u (B (some j)) r =
          radialJacobiField (I := I) g p (r • u) (r • B (some j)) 1 :=
        radialJacobi_scale (I := I) g p u (B (some j)) r
      _ = r • radialJacobiField (I := I) g p (r • u) (B (some j)) 1 :=
        radialJacobi_one_smul (I := I) g p (r • u) (B (some j)) r hrad
  simp only [curveGram, Matrix.of_apply, Matrix.smul_apply, transverseEndGram]
  rw [hi, hj]
  simpa only [smul_eq_mul] using bilin_smul_both
    (g.inner (radialCurve (I := I) g p u r)) r
    (radialJacobiField (I := I) g p (r • u) (B (some i)) 1)
    (radialJacobiField (I := I) g p (r • u) (B (some j)) 1)

private lemma curveGram_det_scale
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E) {r : ℝ}
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    (curveGram (I := I) g (radialCurve (I := I) g p u)
      (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det =
        r ^ (2 * Fintype.card ι) *
          (transverseEndGram (I := I) g p u r B).det := by
  rw [curveGram_end (I := I) g p u B hrad, Matrix.det_smul]
  rw [← pow_mul]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma model_det_ne
    (B : Module.Basis (Option ι) ℝ E) :
    (modelBasisFor B).det B ≠ 0 :=
  ((modelBasisFor B).isUnit_det B).ne_zero

private lemma density_det_eq
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u) (hperp : ∀ i, g.inner p u (B (some i)) = 0)
    {r : ℝ} (hr : 0 < r)
    (hrad : ‖r • u‖ < expMapC2Radius (I := I) g p) :
    r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
        (radialJacobiGram (I := I) g p (r • u)).det =
      g.inner p u u *
        (curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det := by
  have hbasis := endpoint_det_basis (I := I) g p (r • u) B hrad
  have hsplit := endpoint_det_split (I := I) g p u B hBu hperp hr hrad
  have hcurve := curveGram_det_scale (I := I) g p u B hrad
  calc
    r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
          (radialJacobiGram (I := I) g p (r • u)).det =
        r ^ (2 * Fintype.card ι) *
          (endpointGram (I := I) g p (r • u) B).det := by
      rw [hbasis]
      ring
    _ = r ^ (2 * Fintype.card ι) *
          (g.inner p u u * (transverseEndGram (I := I) g p u r B).det) := by
      rw [hsplit]
    _ = g.inner p u u *
          (r ^ (2 * Fintype.card ι) *
            (transverseEndGram (I := I) g p u r B).det) := by ring
    _ = g.inner p u u *
        (curveGram (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (B (some i))) r).det := by
      rw [hcurve]

/-- Polar decomposition of the normal-coordinate density.

`B none` is the radial direction and `B (some i)` are transverse at the
center.  The positive constant records the fixed change from `B` to the model
basis used by `normalChartDensity`, and is independent of the radius. -/
theorem normalDensity_curve
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u)
    (hperp : ∀ i : ι, g.inner p u (B (some i)) = 0)
    {b : ℝ}
    (hsrc : MapsTo (fun r : ℝ => r • u) (Ioo (0 : ℝ) b)
      (expMapDiffeo (I := I) g p).source)
    (hrad : ∀ r ∈ Ioo (0 : ℝ) b,
      ‖r • u‖ < expMapC2Radius (I := I) g p) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Ioo (0 : ℝ) b,
      r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) =
        c * curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r := by
  let a : ℝ := |(modelBasisFor B).det B|
  let s : ℝ := Real.sqrt (g.inner p u u)
  have hu : u ≠ 0 := by
    rw [← hBu]
    exact B.ne_zero none
  have hguu : 0 < g.inner p u u := g.pos p u hu
  have ha : 0 < a := by
    simpa only [a, abs_pos] using model_det_ne (B := B)
  have hs : 0 < s := Real.sqrt_pos.2 hguu
  refine ⟨s / a, div_pos hs ha, ?_⟩
  intro r hrIoo
  have hr : 0 < r := hrIoo.1
  have hxsrc : r • u ∈ (expMapDiffeo (I := I) g p).source := hsrc hrIoo
  have hxrad : ‖r • u‖ < expMapC2Radius (I := I) g p := hrad r hrIoo
  have htransLI : LinearIndependent ℝ fun i : ι => B (some i) :=
    B.linearIndependent.comp (fun i : ι => some i) (Option.some_injective ι)
  have hcurveLI : LinearIndependent ℝ fun i : ι =>
      radialJacobiField (I := I) g p u (B (some i)) r :=
    radialJacobi_li (I := I) g p u htransLI hr.ne' hxsrc hxrad
  have hcurvePos : 0 <
      (curveGram (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r).det :=
    curveGram_det_pos (I := I) g (radialCurve (I := I) g p u)
      (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r hcurveLI
  have hnormalPos : 0 < (normalGramMatrix (I := I) g p (r • u)).det := by
    simpa only [normalGramMatrix] using
      paramGramMatrix_det_pos (I := I) g (expMapDiffeo (I := I) g p) hxsrc
  have hradialPos : 0 < (radialJacobiGram (I := I) g p (r • u)).det := by
    rw [← normalGram_radialMat (I := I) g p hxsrc hxrad]
    exact hnormalPos
  have hdet := density_det_eq (I := I) g p u B hBu hperp hr hxrad
  have hrpowSq : (r ^ Fintype.card ι) ^ 2 =
      r ^ (2 * Fintype.card ι) := by
    rw [← pow_mul]
    congr 1
    omega
  have haSq : a ^ 2 = ((modelBasisFor B).det B) ^ 2 := by
    simp only [a, sq_abs]
  have hsquares :
      (r ^ Fintype.card ι * a *
          Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det) ^ 2 =
        (s * curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r) ^ 2 := by
    calc
      (r ^ Fintype.card ι * a *
          Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det) ^ 2 =
          r ^ (2 * Fintype.card ι) * ((modelBasisFor B).det B) ^ 2 *
            (radialJacobiGram (I := I) g p (r • u)).det := by
        rw [mul_pow, mul_pow, hrpowSq, haSq, Real.sq_sqrt hradialPos.le]
      _ = g.inner p u u *
          (curveGram (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r).det :=
        hdet
      _ = (s * curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r) ^ 2 := by
        simp only [s, curveDensity]
        rw [mul_pow, Real.sq_sqrt hguu.le, Real.sq_sqrt hcurvePos.le]
  have hleftNonneg : 0 ≤ r ^ Fintype.card ι * a *
      Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det :=
    mul_nonneg (mul_nonneg (pow_nonneg hr.le _) ha.le) (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ s *
      curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r :=
    mul_nonneg hs.le (Real.sqrt_nonneg _)
  have hroot : r ^ Fintype.card ι * a *
        Real.sqrt (radialJacobiGram (I := I) g p (r • u)).det =
      s * curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r :=
    (sq_eq_sq₀ hleftNonneg hrightNonneg).1 hsquares
  rw [normalDensity_radial (I := I) g p hxsrc hxrad]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff ha.ne').2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hroot

end PolarDensity

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
