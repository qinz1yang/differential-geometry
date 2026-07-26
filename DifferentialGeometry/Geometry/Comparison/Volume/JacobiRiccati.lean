import DifferentialGeometry.Geometry.Comparison.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiShape

/-!
# Riccati trace comparison for Jacobi families

This file identifies the inverse-Gram curvature trace of a transverse Jacobi
family with Ricci curvature.  It is the geometric trace input for radial
Bishop comparison.
-/

noncomputable section

open Matrix Set
open scoped Matrix Manifold ContDiff Topology Matrix.Norms.Operator

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Volume

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem clm_sum_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {κ : Type*} [Fintype κ]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (v : κ → F) (w : F) :
    B (∑ i, v i) w = ∑ i, B (v i) w := by
  rw [map_sum, ContinuousLinearMap.sum_apply]

private theorem clm_smul_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (c : ℝ) (v w : F) :
    B (c • v) w = c * B v w := by
  have h := congrArg (fun L : F →L[ℝ] ℝ => L w) (B.map_smul c v)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem linIndep_of_ortho
    {κ : Type*} [Finite κ] [DecidableEq κ]
    (g : SmoothRiemannianMetric I M) (x : M) (e : κ → E)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    LinearIndependent ℝ e := by
  classical
  letI := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hpair := congrArg (fun z : E => g.inner x z (e j)) hc
  change g.inner x (∑ i, c i • e i) (e j) = g.inner x 0 (e j) at hpair
  rw [clm_sum_apply, map_zero, ContinuousLinearMap.zero_apply] at hpair
  rw [Finset.sum_eq_single j] at hpair
  · calc
      c j = c j * 1 := by rw [mul_one]
      _ = c j * g.inner x (e j) (e j) := by rw [hON j j, if_pos rfl]
      _ = g.inner x (c j • e j) (e j) :=
        (clm_smul_apply (g.inner x) (c j) (e j) (e j)).symm
      _ = 0 := hpair
  · intro i _ hij
    calc
      g.inner x (c i • e i) (e j) = c i * g.inner x (e i) (e j) :=
        clm_smul_apply (g.inner x) (c i) (e i) (e j)
      _ = c i * (if i = j then 1 else 0) := by rw [hON i j]
      _ = c i * 0 := by rw [if_neg (by simpa using hij)]
      _ = 0 := mul_zero _
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The inverse-Gram trace of the radial curvature matrix is Ricci curvature,
independently of the transverse basis used to form the Gram matrix. -/
theorem curvTrace_eq_ricci
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (u : TangentSpace I (γ t))
    (huvel : curveVelocity (I := I) γ t = u)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner (γ t) u u)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (e : Fin (Module.finrank ℝ E - 1) → TangentSpace I (γ t))
    (hON : ∀ i j, g.inner (γ t) (e i) (e j) = if i = j then 1 else 0)
    (hEperp : ∀ i, g.inner (γ t) (e i) u = 0) :
    trace ((curveGram (I := I) g γ V t)⁻¹ *
        curveCurvGram (I := I) g γ V t) =
      ricciTensor (I := I) g (γ t) u u := by
  classical
  let φ : E →ₗ[ℝ] ℝ := (g.inner (γ t) u).toLinearMap
  let W : Submodule ℝ E := LinearMap.ker φ
  have hφu : 0 < φ u := hu
  have hφsurj : Function.Surjective φ := by
    intro c
    refine ⟨(c / φ u) • u, ?_⟩
    calc
      φ ((c / φ u) • u) = (c / φ u) • φ u := φ.map_smul (c / φ u) u
      _ = c := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ c hφu.ne'
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφsurj
  have hfrange : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]
    simp
  have hfinrankW : Module.finrank ℝ ↥W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfrange] at hsum
    have : Module.finrank ℝ ↥W = Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]
    omega
  have hRuu : riemannOp (LeviCivita (I := I) g) (γ t) u u u = 0 := by
    have h := riemannOp_swap (LeviCivita (I := I) g) (γ t) u u u
    have hsum : riemannOp (LeviCivita (I := I) g) (γ t) u u u +
        riemannOp (LeviCivita (I := I) g) (γ t) u u u = 0 := by
      rw [eq_neg_iff_add_eq_zero] at h
      exact h
    have htwo : (2 : ℝ) • riemannOp (LeviCivita (I := I) g) (γ t) u u u = 0 := by
      rw [two_smul]
      exact hsum
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hRperp (z : E) :
      g.inner (γ t) u (riemannOp (LeviCivita (I := I) g) (γ t) z u u) = 0 := by
    calc
      g.inner (γ t) u (riemannOp (LeviCivita (I := I) g) (γ t) z u u) =
          g.inner (γ t) (riemannOp (LeviCivita (I := I) g) (γ t) z u u) u :=
        g.symm (γ t) _ _
      _ = g.inner (γ t) z
          (riemannOp (LeviCivita (I := I) g) (γ t) u u u) :=
        riemannOp_diag_symm (I := I) g (γ t) u z u
      _ = 0 := by rw [hRuu, map_zero]
  let T : W →ₗ[ℝ] W :=
    { toFun := fun z =>
        ⟨riemannOp (LeviCivita (I := I) g) (γ t) (z : E) u u, hRperp z⟩
      map_add' := fun z w => by
        apply Subtype.ext
        change (riemannOp (LeviCivita (I := I) g) (γ t) ((z : E) + (w : E)) u u) =
          riemannOp (LeviCivita (I := I) g) (γ t) (z : E) u u +
            riemannOp (LeviCivita (I := I) g) (γ t) (w : E) u u
        have hadd := (riemannOp (LeviCivita (I := I) g) (γ t)).map_add (z : E) (w : E)
        have happ := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u u) hadd
        simpa only [ContinuousLinearMap.add_apply] using happ
      map_smul' := fun c z => by
        apply Subtype.ext
        change (riemannOp (LeviCivita (I := I) g) (γ t) (c • (z : E)) u u) =
          c • riemannOp (LeviCivita (I := I) g) (γ t) (z : E) u u
        have hsmul := (riemannOp (LeviCivita (I := I) g) (γ t)).map_smul c (z : E)
        have happ := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u u) hsmul
        simpa only [ContinuousLinearMap.smul_apply] using happ }
  let vW : ι → W := fun i => ⟨V i t, hVperp i⟩
  have hLIW : LinearIndependent ℝ vW := by
    apply LinearIndependent.of_comp W.subtype
    simpa only [Function.comp_apply, vW] using hLI
  have hcardW : Fintype.card ι = Module.finrank ℝ W :=
    hcard.trans hfinrankW.symm
  have hspanV : Submodule.span ℝ (Set.range vW) = ⊤ :=
    hLIW.span_eq_top_of_card_eq_finrank' hcardW
  let bV : Module.Basis ι ℝ W := Module.Basis.mk hLIW hspanV.ge
  have hbV (i : ι) : bV i = vW i := by
    simp only [bV, Module.Basis.coe_mk]
  let a : Matrix ι ι ℝ := fun i k => bV.repr (T (bV i)) k
  have hTexp (i : ι) :
      riemannOp (LeviCivita (I := I) g) (γ t) (V i t) u u =
        ∑ k, a i k • V k t := by
    have hsum := bV.sum_repr (T (bV i))
    have hco := congrArg (fun z : W => (z : E)) hsum
    symm at hco
    simpa only [a, T, vW, hbV, Submodule.coe_sum,
      Submodule.coe_smul_of_tower] using hco
  let G := curveGram (I := I) g γ V t
  have hC : curveCurvGram (I := I) g γ V t = a * G := by
    ext i j
    simp only [curveCurvGram, G, curveGram, Matrix.of_apply, Matrix.mul_apply]
    rw [huvel, hTexp i, clm_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [clm_smul_apply]
  have hdet : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (curveGram_det_pos (I := I) g γ V t hLI))
  have hmatV : LinearMap.toMatrix bV bV T = aᵀ := by
    ext i j
    simp only [LinearMap.toMatrix_apply, a, Matrix.transpose_apply]
  have htraceA : trace a = LinearMap.trace ℝ W T := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bV T, hmatV, Matrix.trace_transpose]
  have hEperp' (i : Fin (Module.finrank ℝ E - 1)) : g.inner (γ t) u (e i) = 0 := by
    rw [g.symm (γ t) u (e i)]
    exact hEperp i
  let eW : Fin (Module.finrank ℝ E - 1) → W := fun i => ⟨e i, hEperp' i⟩
  have hLIe : LinearIndependent ℝ e := linIndep_of_ortho (I := I) g (γ t) e hON
  have hLIeW : LinearIndependent ℝ eW := by
    apply LinearIndependent.of_comp W.subtype
    simpa only [Function.comp_apply, eW] using hLIe
  have hcardE : Fintype.card (Fin (Module.finrank ℝ E - 1)) =
      Module.finrank ℝ W := by
    rw [Fintype.card_fin, hfinrankW]
  have hspanE : Submodule.span ℝ (Set.range eW) = ⊤ :=
    hLIeW.span_eq_top_of_card_eq_finrank' hcardE
  let bE : Module.Basis (Fin (Module.finrank ℝ E - 1)) ℝ W :=
    Module.Basis.mk hLIeW hspanE.ge
  have hbE (i : Fin (Module.finrank ℝ E - 1)) : bE i = eW i := by
    simp only [bE, Module.Basis.coe_mk]
  have hrepr (z : W) (i : Fin (Module.finrank ℝ E - 1)) :
      bE.repr z i = g.inner (γ t) (z : E) (e i) := by
    have hsum := bE.sum_repr z
    have hsumE := congrArg (fun q : W => (q : E)) hsum
    have hsumE' : ∑ j, bE.repr z j • (bE j : E) = (z : E) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hsumE
    have hpair := congrArg (fun q : E => g.inner (γ t) q (e i)) hsumE'
    change g.inner (γ t) (∑ j, bE.repr z j • (bE j : E)) (e i) =
      g.inner (γ t) (z : E) (e i) at hpair
    rw [clm_sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [hbE i] at hpair
      change g.inner (γ t) (bE.repr z i • e i) (e i) =
        g.inner (γ t) (z : E) (e i) at hpair
      rw [clm_smul_apply (B := g.inner (γ t)), hON i i,
        if_pos rfl, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [hbE j]
      change g.inner (γ t) (bE.repr z j • e j) (e i) = 0
      rw [clm_smul_apply (B := g.inner (γ t)), hON j i,
        if_neg (by simpa using hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have htraceE : LinearMap.trace ℝ W T =
      ∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner (γ t)
          (riemannOp (LeviCivita (I := I) g) (γ t) (e i) u u) (e i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bE T]
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hrepr, hbE]
    rfl
  calc
    trace (G⁻¹ * curveCurvGram (I := I) g γ V t) = trace a := by
      rw [hC]
      exact DifferentialGeometry.Analysis.trace_inv_mul_conj G a hdet
    _ = LinearMap.trace ℝ W T := htraceA
    _ = ∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner (γ t)
          (riemannOp (LeviCivita (I := I) g) (γ t) (e i) u u) (e i) := htraceE
    _ = ricciTensor (I := I) g (γ t) u u :=
      BonnetMyers.ricci_eq_sum_perp
        (I := I) g (γ t) u hu e hON hEperp

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- The square of the mean-curvature trace is bounded by the transverse
dimension times the quadratic shape trace. -/
theorem mean_sq_le_shape
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (u : TangentSpace I (γ t))
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hu : 0 < g.inner (γ t) u u)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (e : Fin (Module.finrank ℝ E - 1) → TangentSpace I (γ t))
    (hON : ∀ i j, g.inner (γ t) (e i) (e j) = if i = j then 1 else 0)
    (hEperp : ∀ i, g.inner (γ t) (e i) u = 0) :
    (curveMean (I := I) g γ V t) ^ 2 ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
        trace ((curveShape (I := I) g γ V t) ^ 2) := by
  classical
  obtain ⟨a, hDV⟩ := exists_deriv_coeff (I := I) g γ V t u hcard hu
    hVperp hDVperp hLI
  have hshape := shape_eq_coeff (I := I) g γ V t a hDV hLI hW
  let φ : E →ₗ[ℝ] ℝ := (g.inner (γ t) u).toLinearMap
  let W : Submodule ℝ E := LinearMap.ker φ
  have hφu : 0 < φ u := hu
  have hφsurj : Function.Surjective φ := by
    intro c
    refine ⟨(c / φ u) • u, ?_⟩
    calc
      φ ((c / φ u) • u) = (c / φ u) • φ u := φ.map_smul (c / φ u) u
      _ = c := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ c hφu.ne'
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφsurj
  have hfrange : Module.finrank ℝ (LinearMap.range φ) = 1 := by
    rw [hrange]
    simp
  have hfinrankW : Module.finrank ℝ W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfrange] at hsum
    have : Module.finrank ℝ W = Module.finrank ℝ (LinearMap.ker φ) := rfl
    rw [this]
    omega
  let vW : ι → W := fun i => ⟨V i t, hVperp i⟩
  let dW : ι → W := fun i =>
    ⟨covDerivAlong (I := I) g γ (V i) t, hDVperp i⟩
  have hLIW : LinearIndependent ℝ vW := by
    apply LinearIndependent.of_comp W.subtype
    simpa only [Function.comp_apply, vW] using hLI
  have hcardW : Fintype.card ι = Module.finrank ℝ W :=
    hcard.trans hfinrankW.symm
  have hspanV : Submodule.span ℝ (Set.range vW) = ⊤ :=
    hLIW.span_eq_top_of_card_eq_finrank' hcardW
  let bV : Module.Basis ι ℝ W := Module.Basis.mk hLIW hspanV.ge
  have hbV (i : ι) : bV i = vW i := by
    simp only [bV, Module.Basis.coe_mk]
  let A : W →ₗ[ℝ] W := bV.constr ℝ dW
  have hAbV (i : ι) : A (bV i) = dW i := by
    simp only [A, Module.Basis.constr_basis]
  have hdW (i : ι) : dW i = ∑ k, a i k • bV k := by
    apply Subtype.ext
    simpa only [dW, hbV, vW, Submodule.coe_sum,
      Submodule.coe_smul_of_tower] using hDV i
  have hmatV : LinearMap.toMatrix bV bV A = aᵀ := by
    ext i j
    rw [LinearMap.toMatrix_apply, hAbV, hdW]
    simp only [map_sum, map_smul, Module.Basis.repr_self, Matrix.transpose_apply]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · change a j i * (Finsupp.single i (1 : ℝ)) i = a j i
      rw [Finsupp.single_eq_same, mul_one]
    · intro k _ hki
      change a j k * (Finsupp.single k (1 : ℝ)) i = 0
      rw [Finsupp.single_eq_of_ne hki.symm, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
    { toFun := fun z =>
        { toFun := fun w => g.inner (γ t) (z : E) (w : E)
          map_add' := fun w w' => (g.inner (γ t) (z : E)).map_add (w : E) (w' : E)
          map_smul' := fun c w => (g.inner (γ t) (z : E)).map_smul c (w : E) }
      map_add' := fun z z' => by
        ext w
        have hadd := (g.inner (γ t)).map_add (z : E) (z' : E)
        have happ := congrArg (fun L : E →L[ℝ] ℝ => L (w : E)) hadd
        simpa only [ContinuousLinearMap.add_apply] using happ
      map_smul' := fun c z => by
        ext w
        have hsmul := (g.inner (γ t)).map_smul c (z : E)
        have happ := congrArg (fun L : E →L[ℝ] ℝ => L (w : E)) hsmul
        simpa only [ContinuousLinearMap.smul_apply] using happ }
  let qA : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
    { toFun := fun z => (q z).comp A
      map_add' := fun z z' => by
        ext w
        exact congrArg (fun L : W →ₗ[ℝ] ℝ => L (A w)) (q.map_add z z')
      map_smul' := fun c z => by
        ext w
        exact congrArg (fun L : W →ₗ[ℝ] ℝ => L (A w)) (q.map_smul c z) }
  have hself : q.comp A = qA := by
    apply bV.ext
    intro i
    apply bV.ext
    intro j
    change q (A (bV i)) (bV j) = q (bV i) (A (bV j))
    rw [hAbV i, hAbV j]
    simpa only [q, dW, hbV, vW] using sub_eq_zero.mp (hW i j)
  have hsymm (z w : W) : q (A z) w = q z (A w) := by
    have h := congrArg (fun L : W →ₗ[ℝ] W →ₗ[ℝ] ℝ => L z w) hself
    exact h
  have hEperp' (i : Fin (Module.finrank ℝ E - 1)) :
      g.inner (γ t) u (e i) = 0 := by
    rw [g.symm (γ t) u (e i)]
    exact hEperp i
  let eW : Fin (Module.finrank ℝ E - 1) → W := fun i => ⟨e i, hEperp' i⟩
  have hLIe : LinearIndependent ℝ e := linIndep_of_ortho (I := I) g (γ t) e hON
  have hLIeW : LinearIndependent ℝ eW := by
    apply LinearIndependent.of_comp W.subtype
    simpa only [Function.comp_apply, eW] using hLIe
  have hcardE : Fintype.card (Fin (Module.finrank ℝ E - 1)) =
      Module.finrank ℝ W := by
    rw [Fintype.card_fin, hfinrankW]
  have hspanE : Submodule.span ℝ (Set.range eW) = ⊤ :=
    hLIeW.span_eq_top_of_card_eq_finrank' hcardE
  let bE : Module.Basis (Fin (Module.finrank ℝ E - 1)) ℝ W :=
    Module.Basis.mk hLIeW hspanE.ge
  have hbE (i : Fin (Module.finrank ℝ E - 1)) : bE i = eW i := by
    simp only [bE, Module.Basis.coe_mk]
  have hrepr (z : W) (i : Fin (Module.finrank ℝ E - 1)) :
      bE.repr z i = g.inner (γ t) (z : E) (e i) := by
    have hsum := bE.sum_repr z
    have hsumE := congrArg (fun w : W => (w : E)) hsum
    have hsumE' : ∑ j, bE.repr z j • (bE j : E) = (z : E) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hsumE
    have hpair := congrArg (fun w : E => g.inner (γ t) w (e i)) hsumE'
    change g.inner (γ t) (∑ j, bE.repr z j • (bE j : E)) (e i) =
      g.inner (γ t) (z : E) (e i) at hpair
    rw [clm_sum_apply] at hpair
    rw [Finset.sum_eq_single i] at hpair
    · rw [hbE i] at hpair
      change g.inner (γ t) (bE.repr z i • e i) (e i) =
        g.inner (γ t) (z : E) (e i) at hpair
      rw [clm_smul_apply (B := g.inner (γ t)), hON i i,
        if_pos rfl, mul_one] at hpair
      exact hpair
    · intro j _ hji
      rw [hbE j]
      change g.inner (γ t) (bE.repr z j • e j) (e i) = 0
      rw [clm_smul_apply (B := g.inner (γ t)), hON j i,
        if_neg (by simpa using hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let B : Matrix (Fin (Module.finrank ℝ E - 1))
      (Fin (Module.finrank ℝ E - 1)) ℝ := LinearMap.toMatrix bE bE A
  have hBsymm : B.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp only [B, LinearMap.toMatrix_apply]
    rw [hrepr, hrepr, hbE i, hbE j]
    calc
      g.inner (γ t) (A (eW i) : E) (e j) =
          g.inner (γ t) (e i) (A (eW j) : E) := by
        simpa only [q, eW] using hsymm (eW i) (eW j)
      _ = g.inner (γ t) (A (eW j) : E) (e i) := g.symm (γ t) _ _
  have hshapeM : curveShape (I := I) g γ V t = LinearMap.toMatrix bV bV A := by
    rw [hshape, hmatV]
  have hmean : curveMean (I := I) g γ V t = trace B := by
    calc
      curveMean (I := I) g γ V t = trace (LinearMap.toMatrix bV bV A) := by
        rw [curveMean, hshapeM]
      _ = LinearMap.trace ℝ W A :=
        (LinearMap.trace_eq_matrix_trace ℝ bV A).symm
      _ = trace (LinearMap.toMatrix bE bE A) :=
        LinearMap.trace_eq_matrix_trace ℝ bE A
      _ = trace B := rfl
  have hsq : trace ((curveShape (I := I) g γ V t) ^ 2) = trace (B ^ 2) := by
    calc
      trace ((curveShape (I := I) g γ V t) ^ 2) =
          trace (LinearMap.toMatrix bV bV (A.comp A)) := by
        rw [hshapeM, pow_two, LinearMap.toMatrix_comp bV bV bV A A]
      _ = LinearMap.trace ℝ W (A.comp A) :=
        (LinearMap.trace_eq_matrix_trace ℝ bV (A.comp A)).symm
      _ = trace (LinearMap.toMatrix bE bE (A.comp A)) :=
        LinearMap.trace_eq_matrix_trace ℝ bE (A.comp A)
      _ = trace (B ^ 2) := by
        simp only [B, pow_two, LinearMap.toMatrix_comp bE bE bE A A]
  have hineq := DifferentialGeometry.Analysis.trace_sq_le_mul B hBsymm
  rw [hmean, hsq]
  simpa only [Fintype.card_fin] using hineq

/-- Under a Ricci lower bound, the radial mean curvature satisfies the scalar
Riccati differential inequality for the hyperbolic comparison model. -/
theorem mean_riccati_le
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (t q a : ℝ)
    (u : TangentSpace I (γ t))
    (huvel : curveVelocity (I := I) γ t = u)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (ha : 0 < a)
    (hu : g.inner (γ t) u u = a ^ 2)
    (hVperp : ∀ i, g.inner (γ t) u (V i t) = 0)
    (hDVperp : ∀ i,
      g.inner (γ t) u (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : LinearIndependent ℝ fun i => V i t)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ i, IsJacobiAt (I := I) g γ (V i) t)
    (e : Fin (Module.finrank ℝ E - 1) → TangentSpace I (γ t))
    (hON : ∀ i j, g.inner (γ t) (e i) (e j) = if i = j then 1 else 0)
    (hEperp : ∀ i, g.inner (γ t) (e i) u = 0)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    HasDerivAt (curveMean (I := I) g γ V)
        (-trace ((curveGram (I := I) g γ V t)⁻¹ *
            curveCurvGram (I := I) g γ V t) -
          trace ((curveShape (I := I) g γ V t) ^ 2)) t ∧
      -trace ((curveGram (I := I) g γ V t)⁻¹ *
          curveCurvGram (I := I) g γ V t) -
        trace ((curveShape (I := I) g γ V t) ^ 2) ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (q * a) ^ 2 -
        (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
  have hupos : 0 < g.inner (γ t) u u := by
    rw [hu]
    positivity
  have hderiv := hasDerivAt_mean_perp (I := I) hn g γ V t u hcard hupos
    hVperp hDVperp hγ hVdiff hDVdiff hLI hW hJ
  refine ⟨hderiv, ?_⟩
  have hcurv := curvTrace_eq_ricci (I := I) g γ V t u huvel hcard hupos
    hVperp hLI e hON hEperp
  have hshape := mean_sq_le_shape (I := I) g γ V t u hcard hupos hVperp
    hDVperp hLI hW e hON hEperp
  have hric := hRic (γ t) u
  rw [hu] at hric
  have hdR : (0 : ℝ) < ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hshapeDiv :
      (curveMean (I := I) g γ V t) ^ 2 /
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) ≤
        trace ((curveShape (I := I) g γ V t) ^ 2) := by
    rw [div_le_iff₀ hdR]
    simpa only [mul_comm] using hshape
  rw [hcurv]
  nlinarith

end Volume
end Riemannian
end Geometry
end DifferentialGeometry

end
