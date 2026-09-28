import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Coordinates
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Rigidity
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
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

private noncomputable def affineDiffeomorph
    (L : E ≃L[Real] E) (u v : E) :
    Diffeomorph (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) E E ∞ where
  toEquiv :=
    { toFun := fun z => v + L (z - u)
      invFun := fun z => u + L.symm (z - v)
      left_inv := by
        intro z
        simp
      right_inv := by
        intro z
        simp }
  contMDiff_toFun :=
    (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff
  contMDiff_invFun :=
    (contDiff_const.add (L.symm.contDiff.comp (contDiff_id.sub contDiff_const))).contMDiff

private theorem affineDiffeomorph_apply
    (L : E ≃L[Real] E) (u v z : E) :
    affineDiffeomorph L u v z = v + L (z - u) := rfl

private theorem affineDiffeomorph_mfderiv
    (L : E ≃L[Real] E) (u v z : E) :
    mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
      (affineDiffeomorph L u v) z = L.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact (((L.toContinuousLinearMap.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const u))).const_add v).fderiv

variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
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
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g (γ 0)
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
    ext v
    rfl
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
  rw [hEnorm.inner_eq p v w]
  exact (expMapIntrinsic_mfderiv_inner_of_radial_curvature_zero
    (I := I) g hEnorm p (show TangentSpace I p from u)
    (show TangentSpace I p from v) (show TangentSpace I p from w)
    (fun t ht X => hR _ X _ _)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_flat_exp_deck_diffeomorph
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u v : E)
    (huv : expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from u) =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from v)) :
    ∃ A : Diffeomorph (modelWithCornersSelf Real E)
        (modelWithCornersSelf Real E) E E ∞,
      A u = v ∧
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from A z)) =
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from z)) ∧
      ∀ z a b : E,
        (inner Real (show TangentSpace I p from
            mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
              A z a)
          (show TangentSpace I p from
            mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
              A z b) : Real) =
        inner Real (show TangentSpace I p from a)
          (show TangentSpace I p from b) := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from z)
  change F u = F v at huv
  let eP : TangentSpace I p ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) p
  let gE : SmoothRiemannianMetric (modelWithCornersSelf Real E) E :=
    Diffeomorph.pullbackMetricCross (flatModelMetric (TangentSpace I p))
      eP.symm.toDiffeomorph
  have hePmf : ∀ z : E, ∀ a : TangentSpace (modelWithCornersSelf Real E) z,
      mfderiv (modelWithCornersSelf Real E)
          (modelWithCornersSelf Real (TangentSpace I p))
          eP.symm.toDiffeomorph z a =
        (show TangentSpace
          (modelWithCornersSelf Real (TangentSpace I p))
          (eP.symm.toDiffeomorph z) from
            eP.symm (show E from a)) := by
    intro z a
    rw [mfderiv_eq_fderiv]
    change fderiv Real (fun x : E => eP.symm x) z (show E from a) = _
    rw [eP.symm.hasFDerivAt.fderiv]
    rfl
  have hgE : ∀ z a b : E,
      gE.inner z a b =
        inner Real (show TangentSpace I p from a)
          (show TangentSpace I p from b) := by
    intro z a b
    with_unfolding_all
      rw [show gE = Diffeomorph.pullbackMetricCross
        (flatModelMetric (TangentSpace I p)) eP.symm.toDiffeomorph from rfl,
        Diffeomorph.pullbackMetricCross_inner,
        hePmf z a, hePmf z b]
      rfl
  have hlocal := expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  let dFu : E ≃L[Real] E :=
    (hlocal.mfderivToContinuousLinearEquiv (by norm_num) u).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) (F u))
  let dFv : E ≃L[Real] E :=
    (hlocal.mfderivToContinuousLinearEquiv (by norm_num) v).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) (F v))
  let L : E ≃L[Real] E := dFu.trans dFv.symm
  let A := affineDiffeomorph L u v
  have hAu : A u = v := by
    simp [A, affineDiffeomorph_apply]
  have hL_apply (a : E) : dFv (L a) = dFu a := by
    simp [L]
  have hLinner : ∀ a b : E,
      inner Real (show TangentSpace I p from L a)
          (show TangentSpace I p from L b) =
        inner Real (show TangentSpace I p from a)
          (show TangentSpace I p from b) := by
    intro a b
    have hu := expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero
      (I := I) g hEnorm hR p u a b
    have hv := expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero
      (I := I) g hEnorm hR p v (L a) (L b)
    change inner Real (show TangentSpace I p from a)
        (show TangentSpace I p from b) =
      g.inner (F u)
        (show TangentSpace I (F u) from dFu a)
        (show TangentSpace I (F u) from dFu b) at hu
    change inner Real (show TangentSpace I p from L a)
        (show TangentSpace I p from L b) =
      g.inner (F v)
        (show TangentSpace I (F v) from dFv (L a))
        (show TangentSpace I (F v) from dFv (L b)) at hv
    rw [← huv] at hv
    rw [hL_apply a, hL_apply b] at hv
    exact hv.trans hu.symm
  have hApres : ∀ z a b : E,
      gE.inner z a b =
        gE.inner (A z)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) A z a)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) A z b) := by
    intro z a b
    with_unfolding_all
      rw [hgE, hgE, affineDiffeomorph_mfderiv]
      exact (hLinner a b).symm
  have hFpres := expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  have hFpres' : ∀ z : E,
      ∀ a b : TangentSpace (modelWithCornersSelf Real E) z,
        gE.inner z a b =
          g.inner (F z)
            (mfderiv (modelWithCornersSelf Real E) I F z a)
            (mfderiv (modelWithCornersSelf Real E) I F z b) := by
    intro z a b
    with_unfolding_all
      exact (hgE z a b).trans (hFpres z a b)
  have hFApres : ∀ z a b : E,
      gE.inner z a b =
        g.inner (F (A z))
          (mfderiv (modelWithCornersSelf Real E) I (F ∘ A) z a)
          (mfderiv (modelWithCornersSelf Real E) I (F ∘ A) z b) := by
    intro z a b
    rw [mfderiv_comp_apply z
        ((hlocal.mdifferentiable (by norm_num)) (A z))
        ((A.mdifferentiable (by norm_num)) z) a,
      mfderiv_comp_apply z
        ((hlocal.mdifferentiable (by norm_num)) (A z))
        ((A.mdifferentiable (by norm_num)) z) b]
    exact (hApres z a b).trans (hFpres' (A z) _ _)
  have hF_eq : F ∘ A = F := by
    have hFAlocal : IsLocalDiffeomorph (modelWithCornersSelf Real E) I ∞
        (F ∘ A) := fun z =>
      (A.isLocalDiffeomorph z).comp I M (hlocal (A z))
    apply DifferentialGeometry.Geometry.Riemannian.localIso_rigid
      (I := modelWithCornersSelf Real E) (J := I)
      gE g
      hFAlocal
      hlocal hFApres hFpres' u
    · change F (A u) = F u
      rw [hAu]
      exact huv.symm
    · apply ContinuousLinearMap.ext
      intro a
      rw [mfderiv_comp_apply u ((hlocal.mdifferentiable (by norm_num)) (A u))
        ((A.mdifferentiable (by norm_num)) u) a,
        affineDiffeomorph_mfderiv]
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) (F u)).injective
      rw [hAu, huv]
      change dFv (L a) = dFu a
      exact hL_apply a
  refine ⟨A, hAu, ?_, ?_⟩
  · simpa [F, Function.comp_def] using hF_eq
  · intro z a b
    rw [affineDiffeomorph_mfderiv]
    exact hLinner a b

set_option backward.isDefEq.respectTransparency false in
private theorem flat_exp_deck_diffeomorph_eq_of_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M)
    (A B : Diffeomorph (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) E E ∞)
    (hAF : (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from A z)) =
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)))
    (hBF : (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from B z)) =
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)))
    (hAinner : ∀ z a b : E,
      (inner Real (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            A z a)
        (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            A z b) : Real) =
      inner Real (show TangentSpace I p from a)
        (show TangentSpace I p from b))
    (hBinner : ∀ z a b : E,
      (inner Real (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            B z a)
        (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            B z b) : Real) =
      inner Real (show TangentSpace I p from a)
        (show TangentSpace I p from b))
    {z : E} (hz : A z = B z) : A = B := by
  let F : E → M := fun y => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from y)
  let eP : TangentSpace I p ≃L[Real] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) p
  let gE : SmoothRiemannianMetric (modelWithCornersSelf Real E) E :=
    Diffeomorph.pullbackMetricCross (flatModelMetric (TangentSpace I p))
      eP.symm.toDiffeomorph
  have hePmf : ∀ y : E, ∀ a : TangentSpace (modelWithCornersSelf Real E) y,
      mfderiv (modelWithCornersSelf Real E)
          (modelWithCornersSelf Real (TangentSpace I p))
          eP.symm.toDiffeomorph y a =
        (show TangentSpace
          (modelWithCornersSelf Real (TangentSpace I p))
          (eP.symm.toDiffeomorph y) from
            eP.symm (show E from a)) := by
    intro y a
    rw [mfderiv_eq_fderiv]
    change fderiv Real (fun x : E => eP.symm x) y (show E from a) = _
    rw [eP.symm.hasFDerivAt.fderiv]
    rfl
  have hgE : ∀ y : E, ∀ a b : TangentSpace (modelWithCornersSelf Real E) y,
      gE.inner y a b =
        inner Real (show TangentSpace I p from (show E from a))
          (show TangentSpace I p from (show E from b)) := by
    intro y a b
    with_unfolding_all
      rw [show gE = Diffeomorph.pullbackMetricCross
        (flatModelMetric (TangentSpace I p)) eP.symm.toDiffeomorph from rfl,
        Diffeomorph.pullbackMetricCross_inner,
        hePmf y a, hePmf y b]
      rfl
  have hApres : ∀ y : E, ∀ a b : TangentSpace (modelWithCornersSelf Real E) y,
      gE.inner y a b =
        gE.inner (A y)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) A y a)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) A y b) := by
    intro y a b
    rw [hgE, hgE]
    with_unfolding_all
      exact (hAinner y a b).symm
  have hBpres : ∀ y : E, ∀ a b : TangentSpace (modelWithCornersSelf Real E) y,
      gE.inner y a b =
        gE.inner (B y)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) B y a)
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) B y b) := by
    intro y a b
    rw [hgE, hgE]
    with_unfolding_all
      exact (hBinner y a b).symm
  have hlocal := expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  have hderiv :
      mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) A z =
        mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E) B z := by
    apply ContinuousLinearMap.ext
    intro a
    rw [hz]
    apply (hlocal.mfderivToContinuousLinearEquiv (by norm_num) (B z)).injective
    have hcomp : F ∘ A = F ∘ B := by
      change (fun y : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from A y)) =
        (fun y : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from B y))
      exact hAF.trans hBF.symm
    have hmf := congrArg
      (fun f : E → M =>
        mfderiv (modelWithCornersSelf Real E) I f z a) hcomp
    rw [mfderiv_comp_apply z
        ((hlocal.mdifferentiable (by norm_num)) (A z))
        ((A.mdifferentiable (by norm_num)) z) a,
      mfderiv_comp_apply z
        ((hlocal.mdifferentiable (by norm_num)) (B z))
        ((B.mdifferentiable (by norm_num)) z) a] at hmf
    rw [hz] at hmf
    exact hmf
  apply Diffeomorph.ext
  exact congrFun (DifferentialGeometry.Geometry.Riemannian.localIso_rigid
    (I := modelWithCornersSelf Real E)
    (J := modelWithCornersSelf Real E)
    gE gE A.isLocalDiffeomorph B.isLocalDiffeomorph
    hApres hBpres z hz hderiv)

set_option backward.isDefEq.respectTransparency false in
theorem expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    IsCoveringMap
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)) := by
  classical
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from z)
  have hlocal := expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨v, hv, _⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm p x
    exact ⟨show E from v, hv⟩
  change IsCoveringMap F
  intro x
  obtain ⟨u₀, hu₀⟩ := hsurj x
  obtain ⟨φ, hu₀U, hφ⟩ := hlocal u₀
  let U : Set E := φ.source
  let V : Set M := φ.target
  have hφF : Set.EqOn F φ U := by
    simpa only [F, U] using hφ
  have hUopen : IsOpen U := φ.open_source
  have hVopen : IsOpen V := φ.open_target
  have hxV : x ∈ V := by
    have hmap := φ.toPartialEquiv.map_source hu₀U
    change φ u₀ ∈ V at hmap
    rw [← hφF hu₀U] at hmap
    rw [hu₀] at hmap
    exact hmap
  let Fx : Type _ := F ⁻¹' ({x} : Set M)
  have hFxnonempty : Nonempty Fx := ⟨⟨u₀, hu₀⟩⟩
  let _ : Nonempty Fx := hFxnonempty
  let _ : DiscreteTopology Fx :=
    (IsDiscrete.of_openPartialHomeomorph F subset_rfl
      (fun e _ => by
        obtain ⟨ψ, he, hψ⟩ := hlocal.isLocalHomeomorph e
        exact ⟨ψ, he, by simpa only [F] using hψ.symm⟩)).1
  have hdeck_exists (e : Fx) :
      ∃ A : Diffeomorph (modelWithCornersSelf Real E)
          (modelWithCornersSelf Real E) E E ∞,
        A u₀ = e.1 ∧
        F ∘ A = F ∧
        ∀ z a b : E,
          (inner Real (show TangentSpace I p from
              mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
                A z a)
            (show TangentSpace I p from
              mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
                A z b) : Real) =
            inner Real (show TangentSpace I p from a)
              (show TangentSpace I p from b) := by
    have heq : F u₀ = F e.1 := hu₀.trans e.2.symm
    simpa only [F, Function.comp_def] using exists_flat_exp_deck_diffeomorph
      (I := I) g hEnorm hR p u₀ e.1 heq
  let deck (e : Fx) := (hdeck_exists e).choose
  have hdeck_u (e : Fx) : deck e u₀ = e.1 :=
    (hdeck_exists e).choose_spec.1
  have hdeck_F (e : Fx) : F ∘ deck e = F :=
    (hdeck_exists e).choose_spec.2.1
  have hdeck_inner (e : Fx) : ∀ z a b : E,
      (inner Real (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (deck e) z a)
        (show TangentSpace I p from
          mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (deck e) z b) : Real) =
        inner Real (show TangentSpace I p from a)
          (show TangentSpace I p from b) :=
    (hdeck_exists e).choose_spec.2.2
  let sheet : Fx → Set E := fun e => deck e '' U
  have hsheet_open (e : Fx) : IsOpen (sheet e) :=
    (deck e).toHomeomorph.isOpenMap U hUopen
  have hlocal_surj : Set.SurjOn F U V := by
    intro y hy
    let z : E := φ.toPartialEquiv.invFun y
    have hzU : z ∈ U := φ.toPartialEquiv.map_target hy
    refine ⟨z, hzU, ?_⟩
    rw [hφF hzU]
    exact φ.toPartialEquiv.right_inv hy
  have hsheet_surj (e : Fx) : Set.SurjOn F (sheet e) V := by
    intro y hy
    obtain ⟨z, hzU, hFz⟩ := hlocal_surj hy
    refine ⟨deck e z, ⟨z, hzU, rfl⟩, ?_⟩
    rw [show F (deck e z) = F z from congrFun (hdeck_F e) z]
    exact hFz
  have hsheet_inj (e : Fx) : Set.InjOn F (sheet e) := by
    intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨z₁, hz₁U, rfl⟩ := hy₁
    obtain ⟨z₂, hz₂U, rfl⟩ := hy₂
    have hz : z₁ = z₂ := by
      apply φ.toPartialEquiv.injOn hz₁U hz₂U
      rw [← hφF hz₁U, ← hφF hz₂U]
      exact (congrFun (hdeck_F e) z₁).symm.trans
        (heq.trans (congrFun (hdeck_F e) z₂))
    exact congrArg (deck e) hz
  have hsheet_disjoint : Pairwise (Function.onFun Disjoint sheet) := by
    intro e₁ e₂ hne
    change Disjoint (sheet e₁) (sheet e₂)
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨z₁, hz₁U, hz₁⟩ := hy₁
    obtain ⟨z₂, hz₂U, hz₂⟩ := hy₂
    have hFz : F z₁ = F z₂ := by
      calc
        F z₁ = F (deck e₁ z₁) := (congrFun (hdeck_F e₁) z₁).symm
        _ = F y := congrArg F hz₁
        _ = F (deck e₂ z₂) := congrArg F hz₂.symm
        _ = F z₂ := congrFun (hdeck_F e₂) z₂
    have hz : z₁ = z₂ := by
      apply φ.toPartialEquiv.injOn hz₁U hz₂U
      rw [← hφF hz₁U, ← hφF hz₂U]
      exact hFz
    subst z₂
    have hdeck_eq : deck e₁ = deck e₂ :=
      flat_exp_deck_diffeomorph_eq_of_eq
        (I := I) g hEnorm hR p (deck e₁) (deck e₂)
        (by simpa [F, Function.comp_def] using hdeck_F e₁)
        (by simpa [F, Function.comp_def] using hdeck_F e₂)
        (hdeck_inner e₁) (hdeck_inner e₂) (hz₁.trans hz₂.symm)
    apply hne
    apply Subtype.ext
    calc
      e₁.1 = deck e₁ u₀ := (hdeck_u e₁).symm
      _ = deck e₂ u₀ := by rw [hdeck_eq]
      _ = e₂.1 := hdeck_u e₂
  have hsheet_exhaustive : F ⁻¹' V ⊆ ⋃ e, sheet e := by
    intro y hy
    obtain ⟨z, hzU, hFz⟩ := hlocal_surj hy
    obtain ⟨B, hBz, hBF, hBinner⟩ :=
      exists_flat_exp_deck_diffeomorph
        (I := I) g hEnorm hR p z y hFz
    have hBu₀_fiber : F (B u₀) = x := by
      rw [show F (B u₀) = F u₀ by
        simpa [F, Function.comp_def] using congrFun hBF u₀]
      exact hu₀
    let e : Fx := ⟨B u₀, hBu₀_fiber⟩
    have hdeck_eq : deck e = B :=
      flat_exp_deck_diffeomorph_eq_of_eq
        (I := I) g hEnorm hR p (deck e) B
        (by simpa [F, Function.comp_def] using hdeck_F e)
        hBF (hdeck_inner e) hBinner (hdeck_u e)
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    refine ⟨z, hzU, ?_⟩
    rw [hdeck_eq, hBz]
  have hopen_iff (e : Fx) {W : Set M} (hWV : W ⊆ V) :
      IsOpen W ↔ IsOpen (F ⁻¹' W ∩ sheet e) := by
    constructor
    · intro hW
      exact (hW.preimage hlocal.contMDiff.continuous).inter (hsheet_open e)
    · intro hpre
      have himage : F '' (F ⁻¹' W ∩ sheet e) = W := by
        apply Set.Subset.antisymm
        · rintro _ ⟨y, ⟨hyW, _⟩, rfl⟩
          exact hyW
        · intro y hyW
          obtain ⟨z, hzsheet, hFz⟩ := hsheet_surj e (hWV hyW)
          have hzW : F z ∈ W := by rw [hFz]; exact hyW
          exact ⟨z, ⟨hzW, hzsheet⟩, hFz⟩
      rw [← himage]
      exact hlocal.isOpenMap _ hpre
  have hnonemptyME : Nonempty (M → E) := ⟨Function.surjInv hsurj⟩
  let _ : Nonempty (M → E) := hnonemptyME
  refine IsEvenlyCovered.of_trivialization
    (t := hVopen.trivializationDiscrete (ι := Fx) sheet V hopen_iff
      hsheet_inj hsheet_surj hsheet_disjoint hsheet_exhaustive) ?_
  simpa only [IsOpen.trivializationDiscrete_baseSet] using hxV

noncomputable def expMapIntrinsicDiffeomorphOfRiemannOpEqZero
    [ConnectedSpace M]
    [SimplyConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    Diffeomorph (modelWithCornersSelf Real E) I E M ∞ := by
  have hlocal_infty := expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p
  exact (expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p).diffeomorphSc hlocal_infty

@[simp] theorem expMapIntrinsic_diffeomorph_apply
    [ConnectedSpace M]
    [SimplyConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (z : E) :
    expMapIntrinsicDiffeomorphOfRiemannOpEqZero
        (I := I) g hEnorm hR p z =
      expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem expMapIntrinsic_diffeomorph_isometry_of_riemannOp_eq_zero
    [ConnectedSpace M]
    [SimplyConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x),
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (z : E)
    (a b : TangentSpace (modelWithCornersSelf Real E) z) :
    g.inner
        (expMapIntrinsicDiffeomorphOfRiemannOpEqZero
          (I := I) g hEnorm hR p z)
        (mfderiv (modelWithCornersSelf Real E) I
          (expMapIntrinsicDiffeomorphOfRiemannOpEqZero
            (I := I) g hEnorm hR p) z a)
        (mfderiv (modelWithCornersSelf Real E) I
          (expMapIntrinsicDiffeomorphOfRiemannOpEqZero
            (I := I) g hEnorm hR p) z b) =
      inner Real
        (show TangentSpace I p from (show E from a))
        (show TangentSpace I p from (show E from b)) := by
  exact (expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero
    (I := I) g hEnorm hR p z a b).symm

end DifferentialGeometry.Geometry.Riemannian.Exponential
