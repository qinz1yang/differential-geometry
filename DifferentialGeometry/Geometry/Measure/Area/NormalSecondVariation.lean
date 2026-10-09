import DifferentialGeometry.Geometry.Submanifold.Variation.SecondMetricDerivative
import DifferentialGeometry.Geometry.Submanifold.Variation.NormalMetricDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.CompactSupportFlowAcceleration
import DifferentialGeometry.Geometry.Measure.Area.SecondMetricDerivative
import DifferentialGeometry.Geometry.Measure.Area.FlowFrameDensity
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace

/-! # Actual normal second variation of the original area density

The original complex immersion, its induced metric and the same compact flow
are retained. The acceleration term is explicit; no stationarity is assumed.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.Variation Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem hasDerivAt_deriv_compactSupportFlow_areaDensity_of_normal_velocity
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hnormal : ∀ (q : N) (v : ℂ),
      g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q v) = 0)
    (φ : N → ℝ) (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hXc : HasCompactSupport X)
    (hvelocity : ∀ q : N,
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) : E) =
          φ q • ν q)
    (z : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    let gN := g.pullback (fun q : N => U q) hU hi
    let P : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)
    let DX : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      sourceSectionCovariantDerivative g U (fun q => X (U q)) z (b i)
    let A : ∀ x : M, TangentSpace 𝓘(ℝ, E) x := fun x =>
      (LeviCivita g).toFun X x (X x)
    let DA : Fin 2 → TangentSpace 𝓘(ℝ, E) (U z) := fun i =>
      sourceSectionCovariantDerivative g U (fun q => A (U q)) z (b i)
    let h : Fin 2 → Fin 2 → ℝ := fun i j => g.inner (U z) (ν z)
      (secondFundamentalFormAmbientAt gN g (fun q : N => U q) z (b i) (b j))
    HasDerivAt (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z))
      (riemannianAreaDensity g U z *
        ((∑ i : Fin 2, (g.inner (U z) (DX i) (DX i) + g.inner (U z) (DA i) (P i))) -
          φ z ^ 2 * (∑ i : Fin 2,
            g.inner (U z) ((riemannOp (LeviCivita g) (U z)) (ν z) (P i) (P i)) (ν z)) -
          φ z ^ 2 * ((h 0 0 - h 1 1) ^ 2 + 4 * (h 0 1) ^ 2))) 0 := by
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let F : ℝ × ℂ → M := fun p => Φ p.1 (U p.2)
  let V : Set (ℝ × ℂ) := univ ×ˢ (N : Set ℂ)
  let P (a : ℝ × ℂ) (p : ℝ × ℂ) : E :=
    mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p a
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun x => g.inner x
  let gN := g.pullback (fun q : N => U q) hU hi
  let G := fun t => (Diffeomorph.pullbackMetric g (Φ t)).pullback
    (fun q : N => U q) hU hi
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp
      (hU.contMDiffAt (x := (⟨q, hq⟩ : N)))).contMDiffWithinAt
  have hV : IsOpen V := isOpen_univ.prod N.isOpen
  have hzV : (0, (z : ℂ)) ∈ V := ⟨mem_univ _, z.property⟩
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun p : ℝ × ℂ => (p.1, U p.2)) V :=
    contMDiffOn_fst.prodMk (hUon.comp contMDiffOn_snd (fun _ hp => hp.2))
  have hFprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V :=
    (Diffeomorph.contMDiff_compactSupportFlow X hX hXc).comp_contMDiffOn hmap
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V := by
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hFprod
  have hFd (t : ℝ) (q : N) :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F (t, q) :=
    ((hFprod (t, q) ⟨mem_univ _, q.property⟩).contMDiffAt
      (hV.mem_nhds ⟨mem_univ _, q.property⟩)).mdifferentiableAt (by simp)
  have hspace (t : ℝ) (q : N) (a : ℂ) :
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y => F (t, y)) q a : E) =
        P (0, a) (t, q) := by
    have h := mfderiv_parameter_slice (hFd t q) a
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hΦ₀ : Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) M ∞ :=
    Diffeomorph.compactSupportFlow_zero (I := 𝓘(ℝ, E)) X hX hXc
  have hcentral : (fun q => F (0, q)) = U := by
    funext q
    exact DFunLike.congr_fun hΦ₀ (U q)
  have hP₀ (q : N) (a : ℂ) : P (0, a) (0, q) =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q a : E) := by
    rw [← hspace, hcentral]
    rfl
  have hW (q : N) : P (1, 0) (0, q) = φ q • ν q := by
    have h := mfderiv_parameter_time (hFd 0 q) 1
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.symm.trans (hvelocity q)
  have hnormalF : ∀ q, (0, q) ∈ V → ∀ a : ℂ,
      g.inner (F (0, q))
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, q) (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, q) (0, a)) = 0 := by
    intro q hq a
    let qN : N := ⟨q, hq.2⟩
    change B (F (0, q)) (P (1, 0) (0, qN)) (P (0, a) (0, qN)) = 0
    rw [hW, hP₀, congrFun hcentral q]
    change g.inner (U qN) (φ qN • ν qN)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U qN a) = 0
    rw [map_smul, _root_.smul_apply, smul_eq_mul, hnormal, mul_zero]
  have hUz : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    DifferentialGeometry.mdifferentiableAt_subtype_iff.mp
      (hU.mdifferentiableAt (x := z) (by simp))
  have hPcomp (t : ℝ) (a : ℂ) : P (0, a) (t, z) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ t) (U z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z a) : E) := by
    rw [← hspace]
    have h := mfderiv_comp (z : ℂ)
      ((Φ t).contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hUz
    change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => F (t, q)) z : ℂ →L[ℝ] E) = _ at h
    rw [h]
    rfl
  have hcoefeq (t : ℝ) (v w : ℂ) : (G t).inner z v w =
      B (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z)) := by
    let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
    let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
    let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ t) (U z)
    have hLD : L = D := DifferentialGeometry.mfderiv_restrict_open U N z
    change B (F (t, z)) (A (L v)) (A (L w)) =
      B (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z))
    rw [hLD]
    exact congrArg₂ (fun a c : E => B (F (t, z)) a c)
      (hPcomp t v).symm (hPcomp t w).symm
  have hcoef (v w : ℂ) : HasDerivAt (fun t => (G t).inner z v w)
      (-2 * φ z * g.inner (U z) (ν z) (diskMapCovariantPartial g U z v w)) 0 := by
    have hd := hasDerivAt_gramCoefficient_of_normal_velocity g hV hF hzV hnormalF v w
    change HasDerivAt
      (fun t => B (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z)))
      (-2 * B (F (0, z)) (P (1, 0) (0, z))
        (sourceCovariantPartial g (fun q => F (0, q)) z v w : E)) 0 at hd
    rw [hcentral, congrFun hcentral (z : ℂ), hW] at hd
    change HasDerivAt
      (fun t => B (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z)))
      (-2 * g.inner (U z) (φ z • ν z) (diskMapCovariantPartial g U z v w)) 0 at hd
    have hfactor : -2 * g.inner (U z) (φ z • ν z) (diskMapCovariantPartial g U z v w) =
        -2 * φ z * g.inner (U z) (ν z) (diskMapCovariantPartial g U z v w) := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring
    rw [hfactor] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun t => hcoefeq t v w))
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let ℓ : E →L[ℝ] ℝ := g.inner (U z) (ν z)
  let H : ℂ → ℂ → ℝ := fun v w => ℓ (Q v w)
  have hdiag (v : ℂ) :
      g.inner (U z) (ν z) (diskMapCovariantPartial g U z v v) = H v v :=
    (inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
      N gN g U hU z (ν z) (hnormal z) v).symm
  have hcoefdiag (v : ℂ) : HasDerivAt (fun t => (G t).inner z v v)
      (-2 * φ z * H v v) 0 := by
    simpa only [hdiag] using hcoef v v
  have hHsum (v w : ℂ) : H (v + w) (v + w) = H v v + 2 * H v w + H w w := by
    have hsymm : Q w v = Q v w :=
      secondFundamentalFormAmbientAt_symmetric gN g
        ((hU.contMDiffAt (x := z)).of_le (by simp)) w v
    change ℓ (Q (v + w) (v + w)) = ℓ (Q v v) + 2 * ℓ (Q v w) + ℓ (Q w w)
    simp only [map_add, _root_.add_apply, hsymm]
    ring
  have hcoefmixed (v w : ℂ) : HasDerivAt (fun t => (G t).inner z v w)
      (-2 * φ z * H v w) 0 := by
    have hd := (((hcoefdiag (v + w)).sub (hcoefdiag v)).sub (hcoefdiag w)).div_const 2
    have heq : (fun t => (G t).inner z v w) =ᶠ[𝓝 (0 : ℝ)]
        fun t => ((G t).inner z (v + w) (v + w) - (G t).inner z v v -
          (G t).inner z w w) / 2 := by
      apply Eventually.of_forall
      intro t
      let L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (G t).inner z
      have hsymm : L w v = L v w := (G t).symm z w v
      change L v w = (L (v + w) (v + w) - L v v - L w w) / 2
      simp only [map_add, _root_.add_apply, hsymm]
      ring
    apply (hd.congr_of_eventuallyEq heq).congr_deriv
    change ((-2 * φ z * H (v + w) (v + w) - (-2 * φ z * H v v)) -
      (-2 * φ z * H w w)) / 2 = -2 * φ z * H v w
    rw [hHsum]
    ring
  have hflowvelocity (x : M) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => Φ t x) 0 (1 : ℝ) : E) = X x := by
    have hd := (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc x 0).mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hd
    have hv' : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => Φ t x) 0 (1 : ℝ) : E) =
        X (Φ 0 x) := by
      change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => Φ t x) 0 (1 : ℝ) : E) =
        (1 : ℝ) • X (Φ 0 x) at hv
      simpa only [one_smul] using hv
    exact hv'.trans (congrArg (fun p : M => (X p : E)) (DFunLike.congr_fun hΦ₀ x))
  have hXnormal : (X (U z) : E) = φ z • (ν z : E) :=
    (hflowvelocity (U z)).symm.trans (hvelocity z)
  let T : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let D : ℂ → E := fun v => sourceSectionCovariantDerivative g U (fun q => X (U q)) z v
  let A : ∀ x : M, TangentSpace 𝓘(ℝ, E) x := fun x =>
    (LeviCivita g).toFun X x (X x)
  let DA : ℂ → E := fun v => sourceSectionCovariantDerivative g U (fun q => A (U q)) z v
  let R : M → E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fun x => riemannOp (LeviCivita g) x
  let K : ℂ → ℝ := fun v => B (U z) (R (U z) (ν z) (T v) (T v)) (ν z)
  let e : ℂ → ℝ := fun v =>
    B (U z) (D v) (D v) - φ z ^ 2 * K v + B (U z) (DA v) (T v)
  have hsecond (v : ℂ) : HasDerivAt (deriv (fun t => (G t).inner z v v)) (2 * e v) 0 := by
    let γ : ℝ → M := fun r => U ((z : ℂ) + r • v)
    let f : ℝ → ℝ → M := fun t r => Φ t (γ r)
    have hfzero (r : ℝ) : f 0 r = γ r := DFunLike.congr_fun hΦ₀ (γ r)
    have hfield (r : ℝ) : (centralVariationField (I := 𝓘(ℝ, E)) f r : E) = X (γ r) :=
      hflowvelocity (γ r)
    have hfieldzero : (centralVariationField (I := 𝓘(ℝ, E)) f 0 : E) = X (U z) := by
      have harg : (z : ℂ) + (0 : ℝ) • v = (z : ℂ) := by
        rw [zero_smul, add_zero]
      exact (hfield 0).trans (congrArg (fun q : ℂ => (X (U q) : E)) harg)
    have hbase : f 0 0 = U z := by
      simpa only [γ, zero_smul, add_zero] using hfzero 0
    have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ) : E) = T v := by
      have hc := congrArg
        (fun c : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 (1 : ℝ) : E))
        (funext hfzero)
      exact hc.trans (source_mfderiv_line hUz v)
    have hD : (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationField (I := 𝓘(ℝ, E)) f) 0 : E) = D v := by
      change (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
          (centralVariationField (I := 𝓘(ℝ, E)) f) 0 : E) =
        (covDerivAlong (I := 𝓘(ℝ, E)) g γ (fun r => X (γ r)) 0 : E)
      exact covDerivAlong_congr_curve g _ _
        (Eventually.of_forall hfzero) (Eventually.of_forall hfield)
    have hacc : (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0 : E) = DA v :=
      covDerivAlong_centralAcceleration_compactSupportFlow g X hX hXc γ 0
    have hindex : indexFormIntegrand (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationField (I := 𝓘(ℝ, E)) f)
        (centralVariationField (I := 𝓘(ℝ, E)) f) 0 =
        B (U z) (D v) (D v) - φ z ^ 2 * K v := by
      change B (f 0 0)
          (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
            (centralVariationField (I := 𝓘(ℝ, E)) f) 0)
          (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
            (centralVariationField (I := 𝓘(ℝ, E)) f) 0) -
        B (f 0 0) (R (f 0 0) (centralVariationField (I := 𝓘(ℝ, E)) f 0)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f 0) 0 (1 : ℝ)))
          (centralVariationField (I := 𝓘(ℝ, E)) f 0) = _
      rw [hD, hfieldzero, hvel, hbase, hXnormal]
      let n : E := ν z
      change B (U z) (D v) (D v) -
        B (U z) (R (U z) (φ z • n) (T v) (T v)) (φ z • n) =
          B (U z) (D v) (D v) - φ z ^ 2 * B (U z) (R (U z) n (T v) (T v)) n
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      ring
    have hpair : B (F (0, z))
        (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
          (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0)
        (P (0, v) (0, z)) = B (U z) (DA v) (T v) := by
      have ha := congrArg (fun a : E => B (F (0, z)) a (P (0, v) (0, z))) hacc
      have hb' := congrArg₂ (fun (x : M) (w : E) => B x (DA v) w)
        (congrFun hcentral (z : ℂ)) (hP₀ z v)
      exact ha.trans hb'
    have hd := hasDerivAt_deriv_gramDiagonal_local g hV hF hzV v
    have heq : (fun t => (G t).inner z v v) =ᶠ[𝓝 (0 : ℝ)]
        fun t => B (F (t, z)) (P (0, v) (t, z)) (P (0, v) (t, z)) :=
      Eventually.of_forall (fun t => hcoefeq t v v)
    apply (hd.congr_of_eventuallyEq heq.deriv).congr_deriv
    change 2 * (indexFormIntegrand (I := 𝓘(ℝ, E)) g (f 0)
        (centralVariationField (I := 𝓘(ℝ, E)) f)
        (centralVariationField (I := 𝓘(ℝ, E)) f) 0 +
      B (F (0, z))
        (covDerivAlong (I := 𝓘(ℝ, E)) g (f 0)
          (centralVariationAcceleration (I := 𝓘(ℝ, E)) g f) 0)
        (P (0, v) (0, z))) = 2 * e v
    rw [hindex, hpair]
  have hPregular (a : ℝ × ℂ) : ContMDiffOn 𝓘(ℝ, ℝ × ℂ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p)
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p a)) V :=
    contMDiffOn_source_partial hV hF (m := ∞) (by simp) a
  have hcoefregular (v w : ℂ) : ContDiffAt ℝ 2 (fun t => (G t).inner z v w) 0 := by
    have hp : ContDiffAt ℝ ∞
        (fun p => B (F p) (P (0, v) p) (P (0, w) p)) (0, (z : ℂ)) :=
      ((contDiffOn_sourceSectionPairing g hF (hPregular (0, v))
        (hPregular (0, w))) (0, z) hzV).contDiffAt (hV.mem_nhds hzV)
    have ht : ContDiffAt ℝ ∞ (fun t : ℝ => (t, (z : ℂ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hc := hp.comp 0 ht
    have heq : (fun t => (G t).inner z v w) =
        fun t => B (F (t, z)) (P (0, v) (t, z)) (P (0, w) (t, z)) :=
      funext (fun t => hcoefeq t v w)
    rw [heq]
    exact hc.of_le (by simp)
  have hG₀ : G 0 = gN := by
    have hpull : Diffeomorph.pullbackMetric g (Φ 0) = g :=
      (congrArg (fun Ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞ =>
        Diffeomorph.pullbackMetric g Ψ) hΦ₀).trans (Diffeomorph.pullbackMetric_refl g)
    exact congrArg (fun k : SmoothRiemannianMetric 𝓘(ℝ, E) M =>
      k.pullback (fun q : N => U q) hU hi) hpull
  have h00 : (G 0).inner z (b 0) (b 0) = 1 := by
    rw [hG₀]
    exact (hb 0 0).trans (ite_eq_left rfl)
  have h01 : (G 0).inner z (b 0) (b 1) = 0 := by
    rw [hG₀]
    exact (hb 0 1).trans (ite_eq_right (by decide : (0 : Fin 2) ≠ 1))
  have h11 : (G 0).inner z (b 1) (b 1) = 1 := by
    rw [hG₀]
    exact (hb 1 1).trans (ite_eq_left rfl)
  have hJ : HasDerivAt (deriv (fun t => tangentTwoJacobian (G t) (b 0) (b 1)))
      (e (b 0) + e (b 1) -
        φ z ^ 2 * ((H (b 0) (b 0) - H (b 1) (b 1)) ^ 2 + 4 * (H (b 0) (b 1)) ^ 2)) 0 := by
    have hd := hasDerivAt_deriv_tangentTwoJacobian_at_conformal
      (hcoefregular (b 0) (b 0)) (hcoefregular (b 1) (b 1))
      (hcoefregular (b 0) (b 1)) h01 (h00.trans h11.symm)
    apply hd.congr_deriv
    change (deriv (deriv (fun t => (G t).inner z (b 0) (b 0))) 0 +
        deriv (deriv (fun t => (G t).inner z (b 1) (b 1))) 0) / 2 -
      ((deriv (fun t => (G t).inner z (b 0) (b 0)) 0 -
          deriv (fun t => (G t).inner z (b 1) (b 1)) 0) ^ 2 +
        4 * (deriv (fun t => (G t).inner z (b 0) (b 1)) 0) ^ 2) /
        (4 * (G 0).inner z (b 0) (b 0)) = _
    rw [(hsecond (b 0)).deriv, (hsecond (b 1)).deriv,
      (hcoefdiag (b 0)).deriv, (hcoefdiag (b 1)).deriv,
      (hcoefmixed (b 0) (b 1)).deriv, h00]
    ring
  have hscale := (compactSupportFlow_density_eq_mul_fixed_frame
    N g U hU hi z b hb X hX hXc).1
  have hderivscale : (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => riemannianAreaDensity g U z *
        deriv (fun s => tangentTwoJacobian (G s) (b 0) (b 1)) t := by
    have heq := funext hscale
    apply Eventually.of_forall
    intro t
    rw [heq, deriv_const_mul_field]
  have hfinal := (hJ.const_mul (riemannianAreaDensity g U z)).congr_of_eventuallyEq hderivscale
  apply hfinal.congr_deriv
  change riemannianAreaDensity g U z * (e (b 0) + e (b 1) -
      φ z ^ 2 * ((H (b 0) (b 0) - H (b 1) (b 1)) ^ 2 + 4 * (H (b 0) (b 1)) ^ 2)) =
    riemannianAreaDensity g U z *
      ((∑ i : Fin 2, (B (U z) (D (b i)) (D (b i)) + B (U z) (DA (b i)) (T (b i)))) -
        φ z ^ 2 * (∑ i : Fin 2, K (b i)) -
        φ z ^ 2 * ((H (b 0) (b 0) - H (b 1) (b 1)) ^ 2 + 4 * (H (b 0) (b 1)) ^ 2))
  simp only [Fin.sum_univ_two, e]
  ring

end DifferentialGeometry.Geometry
