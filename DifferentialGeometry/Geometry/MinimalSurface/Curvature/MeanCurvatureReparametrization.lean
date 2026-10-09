import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Composition
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Mathlib.Tactic.Module

set_option autoImplicit false

noncomputable section

open Bundle Filter _root_.Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology _root_.Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A source local isometry contributes no second fundamental form; the
composition identity is obtained from actual smooth curves and their velocities. -/
private theorem secondFundamentalForm_comp_diagonal
    (N P : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (gP : SmoothRiemannianMetric 𝓘(ℝ, ℂ) P)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : N → P) (U : P → M)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U)
    (hmetric : ∀ (q : N) (v w : TangentSpace 𝓘(ℝ, ℂ) q),
      gP.inner (ψ q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q w) = gN.inner q v w)
    (hsurj : ∀ q : N, Function.Surjective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q))
    (z : N) (v : ℂ) :
    secondFundamentalFormAmbientAt gN g (U ∘ ψ) z v v =
      secondFundamentalFormAmbientAt gP g U (ψ z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z v) := by
  have hzero (q : N) (a b : ℂ) :
      (secondFundamentalFormAmbientAt gN gP ψ q a b : ℂ) = 0 := by
    let Q : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := secondFundamentalFormAmbientAt gN gP ψ q
    let G : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := gP.inner (ψ q)
    let D : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q
    obtain ⟨w, hw⟩ := hsurj q (Q a b)
    have hn : G (Q a b) (D w) = 0 :=
      secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map hψ hmetric q a b w
    have hself : G (Q a b) (Q a b) = 0 :=
      (congrArg (fun c : ℂ => G (Q a b) c) hw).symm.trans hn
    change Q a b = 0
    by_contra hne
    exact (ne_of_gt (gP.pos (ψ q) (Q a b) hne)) hself
  obtain ⟨γ, hγ, _, hv⟩ := exists_contMDiff_curve_with_velocity_range_subset
    (I := 𝓘(ℝ, ℂ)) BoundarylessManifold.isInteriorPoint (v : TangentSpace 𝓘(ℝ, ℂ) z)
    (Filter.univ_mem : Set.univ ∈ 𝓝 z)
  have hc := secondFundamentalFormDiagonalAlongCurve_comp gN gP g hψ hU γ 0
  rw [← secondFundamentalFormAmbientAt_diagonal_along_curve gN g (hU.comp hψ) γ hγ 0,
    ← secondFundamentalFormAmbientAt_diagonal_along_curve gP g hU
      (fun t => ψ (γ t)) (hψ.comp hγ) 0,
    ← secondFundamentalFormAmbientAt_diagonal_along_curve gN gP hψ γ hγ 0] at hc
  let Q : N → ℂ →L[ℝ] ℂ →L[ℝ] E := fun q =>
    secondFundamentalFormAmbientAt gN g (U ∘ ψ) q
  let R : P → ℂ →L[ℝ] ℂ →L[ℝ] E := fun p =>
    secondFundamentalFormAmbientAt gP g U p
  let D : N → ℂ →L[ℝ] ℂ := fun q => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q
  have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t => ψ (γ t)) 0 : ℝ →L[ℝ] ℂ) 1 =
      D (γ 0) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1) :=
    mfderiv_comp_apply 0 (hψ.mdifferentiable (by simp) (γ 0))
      (hγ.mdifferentiable (by simp) 0) 1
  let S : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := secondFundamentalFormAmbientAt gN gP ψ (γ 0)
  let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (ψ (γ 0))
  have hraw : Q (γ 0) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1)
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1) =
    R (ψ (γ 0))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t => ψ (γ t)) 0 : ℝ →L[ℝ] ℂ) 1)
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t => ψ (γ t)) 0 : ℝ →L[ℝ] ℂ) 1) +
      L (S ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1)) := hc
  have hS : S ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1)
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) 1) = 0 := hzero (γ 0) _ _
  rw [hS, map_zero, add_zero, hvel] at hraw
  have htransport := congrArg (fun q : TangentBundle 𝓘(ℝ, ℂ) N =>
    Q q.1 q.2 q.2 = R (ψ q.1) (D q.1 q.2) (D q.1 q.2)) hv
  exact htransport.mp hraw

/-- Pull an actual zero-trace orthonormal frame back through the source
coordinate differential. No conformality of the new coordinates is required. -/
private theorem exists_zero_trace_frame_reparametrized
    (N P : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (gP : SmoothRiemannianMetric 𝓘(ℝ, ℂ) P)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : N → P) (U : P → M)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U)
    (hmetric : ∀ (q : N) (v w : TangentSpace 𝓘(ℝ, ℂ) q),
      gP.inner (ψ q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q w) = gN.inner q v w)
    (hbij : ∀ q : N, Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ q))
    (z : N)
    (a : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) (ψ z)))
    (ha : ∀ i j, gP.inner (ψ z) (a i) (a j) = if i = j then 1 else 0)
    (htrace : ∑ i : Fin 2, secondFundamentalFormAmbientAt gP g U (ψ z) (a i) (a i) = 0) :
    ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z),
      (∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0) ∧
      ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (U ∘ ψ) z (b i) (b i) = 0 := by
  classical
  let D : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z
  let e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr (hbij z).injective)
    (LinearMap.range_eq_top.mpr (hbij z).surjective)
  let a₀ : Module.Basis (Fin 2) ℝ ℂ := a
  let b₀ : Module.Basis (Fin 2) ℝ ℂ := a₀.map e.symm.toLinearEquiv
  have hbval (i : Fin 2) : D (b₀ i) = a₀ i := by
    change e (a₀.map e.symm.toLinearEquiv i) = a₀ i
    simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply]
  let G : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := gP.inner (ψ z)
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g (U ∘ ψ) z
  let R : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gP g U (ψ z)
  refine ⟨b₀, ?_, ?_⟩
  · intro i j
    calc
      gN.inner z (b₀ i) (b₀ j) = G (D (b₀ i)) (D (b₀ j)) := (hmetric z _ _).symm
      _ = G (a₀ i) (a₀ j) := congrArg₂ (fun v w : ℂ => G v w) (hbval i) (hbval j)
      _ = if i = j then 1 else 0 := ha i j
  · have hdiag (i : Fin 2) : Q (b₀ i) (b₀ i) = R (a₀ i) (a₀ i) := by
      have h : Q (b₀ i) (b₀ i) = R (D (b₀ i)) (D (b₀ i)) :=
        secondFundamentalForm_comp_diagonal N P gN gP g ψ U hψ hU hmetric
          (fun q => (hbij q).surjective) z (b₀ i)
      rw [hbval] at h
      exact h
    exact (Finset.sum_congr rfl (fun i _ => hdiag i)).trans htrace

/- The following finite-dimensional trace calculation originates in cusp_05's
stationarity scratch, with the explicit-basis and nonrecursive rewriting repairs
independently checked in cusp_13's acceleration-trace scratch. -/
private theorem bilinear_trace_eq_inverse_gram
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (z : N) (Q : ℂ →L[ℝ] ℂ →L[ℝ] F)
    (hsym : Q Complex.I 1 = Q 1 Complex.I)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0) :
    (∑ i : Fin 2, Q (b i) (b i)) =
      (gN.inner z (1 : ℂ) (1 : ℂ) * gN.inner z Complex.I Complex.I -
        gN.inner z (1 : ℂ) Complex.I ^ 2)⁻¹ •
      (gN.inner z Complex.I Complex.I • Q 1 1 +
        gN.inner z (1 : ℂ) (1 : ℂ) • Q Complex.I Complex.I -
        (2 * gN.inner z (1 : ℂ) Complex.I) • Q 1 Complex.I) := by
  classical
  let b₀ : Module.Basis (Fin 2) ℝ ℂ := b
  change (∑ i : Fin 2, Q (b₀ i) (b₀ i)) = _
  let G : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := gN.inner z
  have hG : ∀ i j, G (b₀ i : ℂ) (b₀ j : ℂ) = if i = j then 1 else 0 := hb
  let a := G (1 : ℂ) (1 : ℂ)
  let c := G Complex.I Complex.I
  let d := G (1 : ℂ) Complex.I
  let Δ := a * c - d ^ 2
  let xx := (b₀ 0).re ^ 2 + (b₀ 1).re ^ 2
  let yy := (b₀ 0).im ^ 2 + (b₀ 1).im ^ 2
  let xy := (b₀ 0).re * (b₀ 0).im + (b₀ 1).re * (b₀ 1).im
  have hd : G Complex.I (1 : ℂ) = d := gN.symm z Complex.I (1 : ℂ)
  have hsplit (v : ℂ) : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hcoeff (v : ℂ) (i : Fin 2) : G v (b₀ i) = b₀.repr v i := by
    calc
      _ = G (∑ j : Fin 2, b₀.repr v j • b₀ j) (b₀ i) :=
        congrArg (fun u => G u (b₀ i)) (b₀.sum_repr v).symm
      _ = _ := by
        simp only [Fin.sum_univ_two, map_add, _root_.add_apply,
          map_smul, _root_.smul_apply, smul_eq_mul]
        fin_cases i <;> simp [hG]
  have hexp (v : ℂ) : (∑ i : Fin 2, G v (b₀ i) • b₀ i) = v := by
    simp_rw [hcoeff]
    exact b₀.sum_repr v
  have hrow1 (i : Fin 2) : G (1 : ℂ) (b₀ i) =
      a * (b₀ i).re + d * (b₀ i).im := by
    calc
      _ = G (1 : ℂ) ((b₀ i).re • (1 : ℂ) + (b₀ i).im • Complex.I) :=
        congrArg (G (1 : ℂ)) (hsplit (b₀ i))
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]; dsimp only [a, d]; ring
  have hrowI (i : Fin 2) : G Complex.I (b₀ i) =
      d * (b₀ i).re + c * (b₀ i).im := by
    calc
      _ = G Complex.I ((b₀ i).re • (1 : ℂ) + (b₀ i).im • Complex.I) :=
        congrArg (G Complex.I) (hsplit (b₀ i))
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul, hd]; dsimp only [c]; ring
  have hr1 := congrArg Complex.re (hexp 1)
  have hi1 := congrArg Complex.im (hexp 1)
  have hrI := congrArg Complex.re (hexp Complex.I)
  have hiI := congrArg Complex.im (hexp Complex.I)
  simp only [Fin.sum_univ_two, hrow1, hrowI, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, sub_zero, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im] at hr1 hi1 hrI hiI
  have h00 : a * xx + d * xy = 1 := by dsimp only [xx, xy]; nlinarith only [hr1]
  have h01 : a * xy + d * yy = 0 := by dsimp only [xy, yy]; nlinarith only [hi1]
  have h10 : d * xx + c * xy = 0 := by dsimp only [xx, xy]; nlinarith only [hrI]
  have h11 : d * xy + c * yy = 1 := by dsimp only [xy, yy]; nlinarith only [hiI]
  have ha : 0 < a := gN.pos z (1 : ℂ) (show (1 : ℂ) ≠ 0 from one_ne_zero)
  let w : ℂ := Complex.I - (d / a) • (1 : ℂ)
  have hw : w ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [w, Complex.real_smul] at hi
  have hdet : a * G w w = Δ := by
    simp only [w, map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, hd]
    change a * (c - d / a * d - d / a * (d - d / a * a)) = a * c - d ^ 2
    field_simp [ne_of_gt ha]
    ring
  have hΔ : 0 < Δ := hdet ▸ mul_pos ha (gN.pos z w hw)
  have hxxmul : Δ * xx = c := by
    calc
      _ = c * (a * xx + d * xy) - d * (d * xx + c * xy) := by dsimp only [Δ]; ring
      _ = c := by rw [h00, h10]; ring
  have hyymul : Δ * yy = a := by
    calc
      _ = a * (d * xy + c * yy) - d * (a * xy + d * yy) := by dsimp only [Δ]; ring
      _ = a := by rw [h11, h01]; ring
  have hxymul : Δ * xy = -d := by
    calc
      _ = c * (a * xy + d * yy) - d * (d * xy + c * yy) := by dsimp only [Δ]; ring
      _ = -d := by rw [h01, h11]; ring
  have hxx : xx = Δ⁻¹ * c := by
    calc
      xx = Δ⁻¹ * (Δ * xx) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hΔ), one_mul]
      _ = Δ⁻¹ * c := congrArg (fun r => Δ⁻¹ * r) hxxmul
  have hyy : yy = Δ⁻¹ * a := by
    calc
      yy = Δ⁻¹ * (Δ * yy) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hΔ), one_mul]
      _ = Δ⁻¹ * a := congrArg (fun r => Δ⁻¹ * r) hyymul
  have hxy : xy = Δ⁻¹ * (-d) := by
    calc
      xy = Δ⁻¹ * (Δ * xy) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hΔ), one_mul]
      _ = Δ⁻¹ * (-d) := congrArg (fun r => Δ⁻¹ * r) hxymul
  have hQ (v : ℂ) : Q v v =
      v.re ^ 2 • Q 1 1 + v.im ^ 2 • Q Complex.I Complex.I +
        (2 * v.re * v.im) • Q 1 Complex.I := by
    calc
      _ = Q (v.re • (1 : ℂ) + v.im • Complex.I)
          (v.re • (1 : ℂ) + v.im • Complex.I) :=
        congrArg₂ (fun u w => Q u w) (hsplit v) (hsplit v)
      _ = _ := by simp only [map_add, add_apply, map_smul, smul_apply, hsym]; module
  have hsum : (∑ i : Fin 2, Q (b₀ i) (b₀ i)) =
      xx • Q 1 1 + yy • Q Complex.I Complex.I + (2 * xy) • Q 1 Complex.I := by
    rw [Fin.sum_univ_two, hQ (b₀ 0), hQ (b₀ 1)]
    dsimp only [xx, yy, xy]
    module
  rw [hsum, hxx, hyy, hxy]
  change (Δ⁻¹ * c) • Q 1 1 + (Δ⁻¹ * a) • Q Complex.I Complex.I +
      (2 * (Δ⁻¹ * -d)) • Q 1 Complex.I =
    Δ⁻¹ • (c • Q 1 1 + a • Q Complex.I Complex.I - (2 * d) • Q 1 Complex.I)
  module

/-- The sheet rank and the actual source-coordinate rank locate the image in
an open immersion locus of the original map. Rank away from this image is unused. -/
private theorem exists_original_immersion_locus
    (N : TopologicalSpace.Opens ℂ) (U F : ℂ → M) (ψ : ℂ → ℂ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : N => ψ q))
    (hmaps : Set.MapsTo ψ N (Metric.ball 0 1))
    (hsurj : ∀ z : N, Function.Surjective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : N => ψ q) z))
    (hiF : ∀ z : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => F q) z))
    (heq : Set.EqOn F (U ∘ ψ) N) :
    ∃ (P : TopologicalSpace.Opens ℂ)
      (_ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun p : P => U p))
      (_ : ∀ p : P, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : P => U q) p)),
      (P : Set ℂ) ⊆ Metric.ball 0 1 ∧ Set.MapsTo ψ N P := by
  let B : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let UB : B → M := fun p => U p
  let ψB : N → B := fun q => ⟨ψ q, hmaps q.property⟩
  have hUB : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UB :=
    hU.comp_contMDiff contMDiff_subtype_val (fun q => q.property)
  have hψB : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψB :=
    (ContMDiff.subtypeVal_comp_iff B ψB).mp hψ
  have hcomp : (fun q : N => F q) = UB ∘ ψB :=
    funext (fun q => heq q.property)
  have hdψ (q : N) : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψB q : ℂ →L[ℝ] ℂ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p : N => ψ p) q :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp ψB q).symm
  have hdf (q : N) : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => F p) q :
      ℂ →L[ℝ] E) = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UB (ψB q) : ℂ →L[ℝ] E).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψB q : ℂ →L[ℝ] ℂ) := by
    rw [hcomp]
    exact mfderiv_comp q (hUB.mdifferentiable (by simp) _) (hψB.mdifferentiable (by simp) _)
  have hirank (q : N) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UB (ψB q) : ℂ →L[ℝ] E) := by
    let D : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψB q
    have hD : Function.Surjective D := by
      change Function.Surjective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψB q : ℂ →L[ℝ] ℂ)
      rw [hdψ]
      exact hsurj q
    intro v w hvw
    obtain ⟨a, ha⟩ := hD v
    obtain ⟨b, hb⟩ := hD w
    have hab : a = b := hiF q (by
      rw [hdf]
      change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UB (ψB q) : ℂ →L[ℝ] E) (D a) =
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UB (ψB q) : ℂ →L[ℝ] E) (D b)
      rw [ha, hb]
      exact hvw)
    exact ha.symm.trans ((congrArg D hab).trans hb)
  let A : Set B := {p | _root_.Manifold.IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UB p}
  have hA : IsOpen A := IsOpen.isImmersionAt
  let P : TopologicalSpace.Opens ℂ :=
    ⟨Subtype.val '' A, B.isOpenEmbedding'.isOpenMap A hA⟩
  have hPB : (P : Set ℂ) ⊆ Metric.ball 0 1 := by
    rintro p ⟨q, _, rfl⟩
    exact q.property
  have hUP : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun p : P => U p) :=
    (hU.mono hPB).comp_contMDiff contMDiff_subtype_val (fun p => p.property)
  have hiUP (p : P) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : P => U q) p) := by
    obtain ⟨q, hq, heqp⟩ := p.property
    have hqImm : _root_.Manifold.IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UB q := hq
    have hqinj := hqImm.mfderiv_injective (by simp)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : B => U y) q : ℂ →L[ℝ] E) at hqinj
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y : P => U y) p : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open] at hqinj ⊢
    rw [heqp] at hqinj
    exact hqinj
  refine ⟨P, hUP, hiUP, hPB, ?_⟩
  intro q hq
  refine ⟨ψB ⟨q, hq⟩, ?_, rfl⟩
  exact DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp) hUB (ψB ⟨q, hq⟩) (hirank ⟨q, hq⟩)

/-- A genuine change of source coordinates preserves the zero induced mean
trace of the original harmonic conformal disk. The original map may branch
outside the image of the sheet. The conclusion is the full, unaveraged
inverse-Gram trace for the same `F` and its canonical pullback metric. -/
theorem inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
    (N : TopologicalSpace.Opens ℂ)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U F : ℂ → M) (ψ : ℂ → ℂ)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : N => ψ q))
    (hmaps : Set.MapsTo ψ N (Metric.ball 0 1))
    (hbij : ∀ z : N, Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : N => ψ q) z))
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => F q))
    (hiF : ∀ z : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => F q) z))
    (heq : Set.EqOn F (U ∘ ψ) N)
    (hconf : ∀ p ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U p)
    (htension : ∀ p ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U p = 0)
    (z : N) :
    let gN := g.pullback (fun q : N => F q) hF hiF
    let II : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g (fun q : N => F q) z
    let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (F z)
    let A := G (D 1) (D 1)
    let B := G (D 1) (D Complex.I)
    let C := G (D Complex.I) (D Complex.I)
    (A * C - B ^ 2)⁻¹ •
      (C • II 1 1 + A • II Complex.I Complex.I - (2 * B) • II 1 Complex.I) = 0 := by
  classical
  dsimp only
  obtain ⟨P, hUP, hiUP, hPB, hψPmem⟩ := exists_original_immersion_locus N U F ψ hU hψ
    hmaps (fun q => (hbij q).surjective) hiF heq
  let ψP : N → P := fun q => ⟨ψ q, hψPmem q.property⟩
  let UP : P → M := fun p => U p
  let f : N → M := fun q => F q
  let gN := g.pullback f hF hiF
  let gP := g.pullback UP hUP hiUP
  have hψP : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψP :=
    (ContMDiff.subtypeVal_comp_iff P ψP).mp hψ
  have hcomp : f = UP ∘ ψP := funext (fun q => heq q.property)
  have hdψ (q : N) : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψP q : ℂ →L[ℝ] ℂ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p : N => ψ p) q :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp ψP q).symm
  have hbijP (q : N) : Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψP q) := by
    rw [hdψ]
    exact hbij q
  have hmetricψ (q : N) (v w : TangentSpace 𝓘(ℝ, ℂ) q) :
      gP.inner (ψP q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψP q v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψP q w) = gN.inner q v w := by
    let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun p => g.inner p
    let dU : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UP (ψP q)
    let dψ : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψP q
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q : ℂ →L[ℝ] E) = dU.comp dψ := by
      rw [hcomp]
      exact mfderiv_comp q (hUP.mdifferentiable (by simp) _) (hψP.mdifferentiable (by simp) _)
    change B (UP (ψP q)) (dU (dψ v)) (dU (dψ w)) =
      B (f q) ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q : ℂ →L[ℝ] E) v)
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q : ℂ →L[ℝ] E) w)
    have hbase : B (f q) = B (UP (ψP q)) := congrArg (fun k : N → M => B (k q)) hcomp
    rw [hbase, hdf]
    rfl
  have hmetricU (p : P) (v w : ℂ) :
      g.inner (U p) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p w) = gP.inner p v w := by
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U p)
    have hd : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : P => U q) p : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U p :=
      DifferentialGeometry.mfderiv_restrict_open U P p
    exact (congrArg (fun D : ℂ →L[ℝ] E => G (D v) (D w)) hd).symm
  obtain ⟨a, ha, htrace⟩ := exists_orthonormal_secondFundamentalForm_trace_eq_zero_of_disk_tension
    P gP g U hUP hmetricU (ψP z) (hconf _ (hPB (ψP z).property))
      (htension _ (hPB (ψP z).property))
  obtain ⟨b, hb, htraceComp⟩ := exists_zero_trace_frame_reparametrized N P gN gP g ψP UP
    hψP hUP hmetricψ hbijP z a ha htrace
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g f z
  have htraceF : (∑ i : Fin 2, Q (b i) (b i)) = 0 := by
    have he := congrArg (fun k : N → M =>
      ∑ i : Fin 2, (secondFundamentalFormAmbientAt gN g k z : ℂ →L[ℝ] ℂ →L[ℝ] E)
        (b i) (b i)) hcomp
    exact he.trans htraceComp
  have hsym : Q Complex.I (1 : ℂ) = Q (1 : ℂ) Complex.I :=
    secondFundamentalFormAmbientAt_symmetric gN g (hF.contMDiffAt.of_le (by simp)) _ _
  have htraceEq := bilinear_trace_eq_inverse_gram N gN z Q hsym b hb
  have hzero := htraceEq.symm.trans htraceF
  have hinner (v w : ℂ) : gN.inner z v w =
      g.inner (F z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z w) := by
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (F z)
    have hd : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => F q) z : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z :=
      DifferentialGeometry.mfderiv_restrict_open F N z
    exact congrArg (fun D : ℂ →L[ℝ] E => G (D v) (D w)) hd
  simp only [hinner] at hzero
  exact hzero

end DifferentialGeometry.Geometry
