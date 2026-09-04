import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiCoord
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete
import DifferentialGeometry.Geometry.Metric.LocalIsometryRigidity
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import DifferentialGeometry.Topology.Covering.SimplyConnected

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

theorem expMapIntrinsic_isLocalDiffeomorphAt_of_riemannOp_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u : E) :
    IsLocalDiffeomorphAt (modelWithCornersSelf Real E) I 1
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)) u := by
  let q : M := expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from u)
  let F : E → M := fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)
  have hF : ContMDiffAt (modelWithCornersSelf Real E) I ∞ F u := by
    exact (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt
  let Df : E →L[Real] TangentSpace I q :=
    mfderiv (modelWithCornersSelf Real E) I F u
  let eQ : TangentSpace I q ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) q
  let D : E →L[Real] E := eQ.toContinuousLinearMap.comp Df
  have hinner : ∀ v w : E, g.inner q (Df v) (Df w) = g.inner p v w := by
    intro v w
    exact expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
      (I := I) g hEnorm p (show TangentSpace I p from u)
      (show TangentSpace I p from v) (show TangentSpace I p from w)
      (fun t ht X => hR _ X _ _)
  have hDinj : Function.Injective D := by
    intro v w hvw
    have hzero : D (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have hDfw : Df (v - w) = 0 := by
      apply eQ.injective
      simpa [D] using hzero
    have hnorm : g.inner p (v - w) (v - w) = 0 := by
      rw [← hinner (v - w) (v - w), hDfw]
      simp
    have hpos : v - w = 0 := by
      by_contra hn
      have := g.pos p (v - w) hn
      linarith
    exact sub_eq_zero.mp hpos
  have hDker : D.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  have hDsurj : Function.Surjective D := by
    exact LinearMap.surjective_of_injective hDinj
  have hDrange : D.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hDsurj
  let eD : E ≃L[Real] E := ContinuousLinearEquiv.ofBijective D hDker hDrange
  let G : TangentSpace I q →L[Real] E :=
    eD.symm.toContinuousLinearMap.comp eQ.toContinuousLinearMap
  have hleft : Df ∘L G = ContinuousLinearMap.id Real (TangentSpace I q) := by
    apply ContinuousLinearMap.ext
    intro y
    apply eQ.injective
    change D (eD.symm (eQ y)) = eQ y
    exact eD.apply_symm_apply _
  have hright : G ∘L Df = ContinuousLinearMap.id Real E := by
    apply ContinuousLinearMap.ext
    intro v
    change eD.symm (D v) = v
    exact eD.symm_apply_apply _
  apply DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
    (n := (1 : WithTop ℕ∞)) (by norm_num) (by norm_num)
    (hF.of_le (by norm_num))
  exact ContinuousLinearMap.IsInvertible.of_inverse hleft hright

theorem expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    IsLocalDiffeomorph (modelWithCornersSelf Real E) I ∞
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)) := by
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
  apply DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty
    isOpen_univ
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffOn
  intro u _
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from z)
  let q : M := F u
  let Df : E →L[Real] TangentSpace I q :=
    mfderiv (modelWithCornersSelf Real E) I F u
  let eQ : TangentSpace I q ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) q
  let D : E →L[Real] E := eQ.toContinuousLinearMap.comp Df
  have hinner : ∀ v w : E, g.inner q (Df v) (Df w) = g.inner p v w := by
    intro v w
    exact expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
      (I := I) g hEnorm p (show TangentSpace I p from u)
      (show TangentSpace I p from v) (show TangentSpace I p from w)
      (fun t ht X => hR _ X _ _)
  have hDinj : Function.Injective D := by
    intro v w hvw
    have hzero : D (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have hDfw : Df (v - w) = 0 := by
      apply eQ.injective
      simpa [D] using hzero
    have hnorm : g.inner p (v - w) (v - w) = 0 := by
      rw [← hinner (v - w) (v - w), hDfw]
      simp
    have hpos : v - w = 0 := by
      by_contra hn
      have := g.pos p (v - w) hn
      linarith
    exact sub_eq_zero.mp hpos
  have hDker : D.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  have hDsurj : Function.Surjective D := LinearMap.surjective_of_injective hDinj
  let eD : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective D hDker (LinearMap.range_eq_top.mpr hDsurj)
  let G : TangentSpace I q →L[Real] E :=
    eD.symm.toContinuousLinearMap.comp eQ.toContinuousLinearMap
  have hleft : Df ∘L G = ContinuousLinearMap.id Real (TangentSpace I q) := by
    apply ContinuousLinearMap.ext
    intro y
    apply eQ.injective
    change D (eD.symm (eQ y)) = eQ y
    exact eD.apply_symm_apply _
  have hright : G ∘L Df = ContinuousLinearMap.id Real E := by
    apply ContinuousLinearMap.ext
    intro v
    change eD.symm (D v) = v
    exact eD.symm_apply_apply _
  have hmf : (mfderiv (modelWithCornersSelf Real E) I F u).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hleft hright
  have hmdiff : MDifferentiableAt (modelWithCornersSelf Real E) I F u :=
    ((intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hderiv :
      fderiv Real (writtenInExtChartAt (modelWithCornersSelf Real E) I u F)
        (extChartAt (modelWithCornersSelf Real E) u u) =
        mfderiv (modelWithCornersSelf Real E) I F u := by
    rw [hmdiff.mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  exact hderiv ▸ hmf

theorem expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u v w : E) :
    (inner Real (show TangentSpace I p from v)
      (show TangentSpace I p from w) : Real) =
      g.inner (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u))
        (mfderiv (modelWithCornersSelf Real E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) u v)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun z : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) u w) := by
  rw [inner_eq_of_isMetricNorm (I := I) g hEnorm p v w]
  exact (expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
    (I := I) g hEnorm p (show TangentSpace I p from u)
    (show TangentSpace I p from v) (show TangentSpace I p from w)
    (fun t ht X => hR _ X _ _)).symm

noncomputable def expMapIntrinsic_diffeomorph_of_isCoveringMap_of_riemannOp_eq_zero
    [SimplyConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M)
    (hcover : IsCoveringMap
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z))) :
    Diffeomorph (modelWithCornersSelf Real E) I E M ∞ := by
  have hlocal_infty := expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  exact hcover.diffeomorphSc hlocal_infty

end DifferentialGeometry.Geometry.Riemannian.Exponential
