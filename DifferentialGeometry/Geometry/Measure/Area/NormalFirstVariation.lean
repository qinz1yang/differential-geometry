import DifferentialGeometry.Geometry.Submanifold.Variation.NormalMetricDerivative
import DifferentialGeometry.Geometry.Measure.Area.GramFirstDerivative
import DifferentialGeometry.Geometry.Measure.Area.FlowFrameDensity
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace

/-! # Normal first variation of the original area density

The original complex immersion and its induced metric are retained. A supplied
orthonormal basis at one point stays fixed in variation time; no smooth global
frame or conformal parametrization is used.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open scoped ContDiff Manifold Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The actual area density under the supplied canonical flow has derivative
minus its original density times the normal speed and the normal scalar trace
of the second fundamental form for the same induced metric. -/
theorem hasDerivAt_compactSupportFlow_areaDensity_of_normal_velocity
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
    HasDerivAt
      (fun t => riemannianAreaDensity g (Diffeomorph.compactSupportFlow X hX hXc t ∘ U) z)
      (-φ z * riemannianAreaDensity g U z *
        ∑ i : Fin 2, g.inner (U z) (ν z)
          (secondFundamentalFormAmbientAt
            (g.pullback (fun q : N => U q) hU hi) g (fun q : N => U q) z
            (b i) (b i))) 0 := by
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
  let H (v : ℂ) : ℝ := g.inner (U z) (ν z)
    (secondFundamentalFormAmbientAt gN g (fun q : N => U q) z v v)
  have hdiag (v : ℂ) :
      g.inner (U z) (ν z) (diskMapCovariantPartial g U z v v) = H v :=
    (inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
      N gN g U hU z (ν z) (hnormal z) v).symm
  have hcoefdiag (v : ℂ) : HasDerivAt (fun t => (G t).inner z v v)
      (-2 * φ z * H v) 0 := by
    simpa only [hdiag] using hcoef v v
  have hframe : LinearIndependent ℝ ![b 0, b 1] := by
    convert b.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  have hGram := hasDerivAt_tangentTwoJacobian
    (x := fun _ => z) (v := fun _ => b 0) (w := fun _ => b 1)
    (hcoefdiag (b 0)) (hcoef (b 0) (b 1)) (hcoefdiag (b 1)) hframe
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
  have hJ₀ : tangentTwoJacobian (G 0) (b 0) (b 1) = 1 := by
    simp [tangentTwoJacobian, h00, h01, h11]
  have hJ : HasDerivAt (fun t => tangentTwoJacobian (G t) (b 0) (b 1))
      (-φ z * (H (b 0) + H (b 1))) 0 := by
    convert hGram using 1
    rw [h00, h01, h11, hJ₀]
    ring
  have hscale := (compactSupportFlow_density_eq_mul_fixed_frame
    N g U hU hi z b hb X hX hXc).1
  have hd := (hJ.const_mul (riemannianAreaDensity g U z)).congr_of_eventuallyEq
    (Eventually.of_forall hscale)
  convert hd using 1
  dsimp only [H, gN]
  rw [Fin.sum_univ_two]
  ring

end DifferentialGeometry.Geometry
