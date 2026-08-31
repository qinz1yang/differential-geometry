import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiCoord
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature
open CovariantDerivativeAlong
open Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u v w : TangentSpace I p)
    (hR : ∀ t ∈ Set.Icc (0 : Real) 1,
      ∀ X : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u t),
        riemannOp (LeviCivita (I := I) g)
          (intrinsicGeodesic (I := I) g hEnorm p u t) X
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) = 0) :
    g.inner (expMapIntrinsic (I := I) g hEnorm p u)
        (mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (v : E))
        (mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (w : E)) =
      g.inner p v w := by
  classical
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hγeq : (fun t : Real => intrinsicGeodesic (I := I) g hEnorm p u t) = γ := rfl
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    simpa only [γ] using intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ2 : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) γ :=
    hγ.of_le ENat.LEInfty.out
  obtain ⟨basis, hON0⟩ := exists_gOrthonormalBasis (I := I) g (γ 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    exists_parallel_frame (I := I) g γ (N := 2) (by norm_num) hγ2
      (L := 1) one_pos basis hON0
  have hfin : Module.finrank Real (TangentSpace I (γ 0)) ≠ 0 := by
    change Module.finrank Real E ≠ 0
    exact NeZero.out
  let : Nonempty (Fin (Module.finrank Real (TangentSpace I (γ 0)))) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hfin)
  have hcard (t : Real) :
      Fintype.card (Fin (Module.finrank Real (TangentSpace I (γ 0)))) =
        Module.finrank Real (TangentSpace I (γ t)) := by
    rw [Fintype.card_fin]
    rfl
  have hendpoint (a : TangentSpace I p) :
      ∃ P : ∀ t, TangentSpace I (γ t),
        P 0 = a ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          DifferentiableAt Real (chartRepAt (I := I) γ P t) t) ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          covDerivAlong (I := I) g γ P t = 0) ∧
        mfderiv 𝓘(Real, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from z)) (u : E) (a : E) = P 1 := by
    obtain ⟨δ, hδ, P, hP0, hPdiff, hPpar⟩ :=
      exists_global_parallel_transport_on_Ioo (I := I) g γ
        (N := 2) (by norm_num) hγ2 (L := 1) one_pos a
    let Fvar : Real → Real → M := fun s t =>
      intrinsicGeodesic (I := I) g hEnorm p (u + s • a) t
    let J : ∀ t, TangentSpace I (γ t) := fun t =>
      mfderiv 𝓘(Real, Real) I (fun s : Real => Fvar s t) 0 (1 : Real)
    let Z : ∀ t, TangentSpace I (γ t) := fun t => t • P t
    have hFvar : IsSmoothVariation (I := I) Fvar := by
      change ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
        (fun q : Real × Real =>
          intrinsicGeodesic (I := I) g hEnorm p (u + q.1 • a) q.2)
      exact (intrinsicVar_smooth (I := I) g hEnorm p (u : E) (a : E)).of_le
        ENat.LEInfty.out
    have hcentral : (fun t : Real => Fvar 0 t) = γ := by
      funext t
      simp only [Fvar, γ, zero_smul, add_zero]
    have hIoo (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        t ∈ Set.Ioo (-δ) (1 + δ) := by
      constructor <;> linarith [ht.1, ht.2, hδ]
    have hPdiff' (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        DifferentiableAt Real (chartRepAt (I := I) γ P t) t :=
      hPdiff t (hIoo t ht)
    have hPpar' (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        covDerivAlong (I := I) g γ P t = 0 :=
      hPpar t (hIoo t ht)
    have hZdiff (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        DifferentiableAt Real (chartRepAt (I := I) γ Z t) t := by
      rw [show Z = fun s => s • P s from rfl, chartRepAt_smulFun]
      exact differentiableAt_id.smul (hPdiff' t ht)
    have hZcov (t : Real) (ht : t ∈ Set.Ioo (-δ) (1 + δ)) :
        covDerivAlong (I := I) g γ Z t = P t := by
      rw [show Z = fun s => s • P s from rfl,
        covDerivAlong_smulFun (I := I) g γ (fun s : Real => s) P t
          differentiableAt_id (hPdiff t ht), hPpar t ht]
      simp
    have hDZdiff (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun s => covDerivAlong (I := I) g γ Z s) t) t := by
      have heq : ∀ᶠ s in 𝓝 t,
          covDerivAlong (I := I) g γ Z s = P s := by
        filter_upwards [isOpen_Ioo.mem_nhds (hIoo t ht)] with s hs
        exact hZcov s hs
      rw [(chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ heq).differentiableAt_iff]
      exact hPdiff' t ht
    have hJdiff (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        DifferentiableAt Real (chartRepAt (I := I) γ J t) t := by
      have h := variationField_chartRep_differentiableAt (I := I) Fvar hFvar t
      rw [hcentral] at h
      change DifferentiableAt Real (chartRepAt (I := I) γ J t) t at h
      exact h
    have hDJdiff (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        DifferentiableAt Real
          (chartRepAt (I := I) γ
            (fun s => covDerivAlong (I := I) g γ J s) t) t := by
      have h := variationField_covDeriv_chartRep_differentiableAt
        (I := I) g Fvar hFvar t
      rw [hcentral] at h
      change DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t at h
      exact h
    have hJacJ (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        IsJacobiAt (I := I) g γ J t := by
      have h := intrinsic_jacobi (I := I) g hEnorm p (u : E) (a : E) t
      rw [hγeq] at h
      change IsJacobiAt (I := I) g γ J t at h
      exact h
    have hJacZ (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
        IsJacobiAt (I := I) g γ Z t := by
      have heq : ∀ᶠ s in 𝓝 t,
          covDerivAlong (I := I) g γ Z s = P s := by
        filter_upwards [isOpen_Ioo.mem_nhds (hIoo t ht)] with s hs
        exact hZcov s hs
      have hD2 : covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ Z s) t = 0 := by
        rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
        exact hPpar' t ht
      change covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ Z s) t +
        riemannOp (LeviCivita (I := I) g) (γ t) (Z t)
          (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 0
      rw [hD2]
      have hcurv := hR t ht (Z t)
      simpa only [γ, zero_add] using hcurv
    have hCbound (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1)
        (i j : Fin (Module.finrank Real (TangentSpace I (γ 0)))) :
        |g.inner (γ t) (F i t)
          (riemannOp (LeviCivita (I := I) g) (γ t)
            (F j t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t))| ≤ 0 := by
      have hcurv := hR t ht (F j t)
      change |g.inner (γ t) (F i t)
        (riemannOp (LeviCivita (I := I) g) (γ t)
          (F j t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t))| ≤ 0
      rw [show riemannOp (LeviCivita (I := I) g) (γ t)
          (F j t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) = 0 by
        simpa only [γ] using hcurv]
      simp
    have hJ0 : J 0 = Z 0 := by
      have hconst : (fun s : Real => Fvar s 0) = fun _ : Real => p := by
        funext s
        exact intrinsicGeodesic_zero (I := I) g hEnorm p _
      simp only [J, Z, zero_smul]
      rw [hconst, mfderiv_const]
      rfl
    have hDJ0 : covDerivAlong (I := I) g γ J 0 =
        covDerivAlong (I := I) g γ Z 0 := by
      have hleft : (covDerivAlong (I := I) g γ J 0 : E) = a := by
        have h := intrinsic_jacobi_d0 (I := I) g hEnorm p (u : E) (a : E)
        rw [hγeq] at h
        change (covDerivAlong (I := I) g γ J 0 : E) = a at h
        exact h
      have hright : covDerivAlong (I := I) g γ Z 0 = P 0 :=
        hZcov 0 (by constructor <;> linarith [hδ])
      rw [hleft, hright, hP0]
    have hJZ := jacobi_unique (I := I) (n := (2 : ℕ)) (by norm_num)
      g γ F J Z (C := 0) (by norm_num)
      (fun _ _ => hγ2.contMDiffAt)
      hFdiff hFpar hFON (fun t _ => hcard t)
      hJdiff hZdiff hDJdiff hDZdiff hJacJ hJacZ hCbound
      (by norm_num) hJ0 hDJ0
    have hJP : J 1 = P 1 := by
      have h := hJZ 1 (by norm_num)
      simpa only [Z, one_smul] using h
    have hJone : J 1 =
        mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (a : E) := by
      have h := intrinsic_jacobi_one (I := I) g hEnorm p (u : E) (a : E)
      change J 1 =
        mfderiv 𝓘(Real, E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (u : E) (a : E) at h
      exact h
    refine ⟨P, hP0, hPdiff', hPpar', ?_⟩
    exact hJone.symm.trans hJP
  obtain ⟨V, hV0, hVdiff, hVpar, hVone⟩ := hendpoint v
  obtain ⟨W, hW0, hWdiff, hWpar, hWone⟩ := hendpoint w
  have hinner := parallel_transport_preserves_inner_product (I := I) g γ
    (N := 2) (by norm_num) hγ2 V W hVdiff hWdiff hVpar hWpar
      1 (by norm_num)
  rw [← hVone, ← hWone, hV0, hW0] at hinner
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p u
  rw [hγ0] at hinner
  change g.inner (expMapIntrinsic (I := I) g hEnorm p u)
      (mfderiv 𝓘(Real, E) I
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from z)) (u : E) (v : E))
      (mfderiv 𝓘(Real, E) I
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from z)) (u : E) (w : E)) =
    g.inner p v w
  with_unfolding_all exact hinner

end DifferentialGeometry.Geometry.Riemannian.Exponential
