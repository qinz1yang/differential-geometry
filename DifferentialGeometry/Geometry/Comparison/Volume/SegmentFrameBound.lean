import DifferentialGeometry.Geometry.Comparison.Volume.SegmentGauss
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentPole

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Matrix Set
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
private theorem fullDens_eq_trans
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p)
    (hu : 0 < g.inner p u u)
    (B : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I p))
    (hB : ∀ i j, g.inner p (B i) (B j) = if i = j then 1 else 0)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0) :
    curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (fun i t => intrinsicJacobi (I := I) g hEnorm p u
          (B i) t) 1 =
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 := by
  classical
  let d : Nat := Module.finrank Real E - 1
  let ell : Real := Real.sqrt (g.inner p u u)
  have hell : 0 < ell := Real.sqrt_pos.2 hu
  have hell_sq : ell ^ 2 = g.inner p u u := Real.sq_sqrt hu.le
  have hn : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.out : Module.finrank Real E ≠ 0)
  have hdim : d + 1 = Module.finrank Real E := by
    simpa only [d] using Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn.ne')
  let a : Option (Fin d) → TangentSpace I p
    | none => ell⁻¹ • u
    | some i => v ⟨i, by simpa only [d] using i.2⟩
  let D := (tangentMetricData_gen (I := I) g p).metric
  letI : InnerProductSpace.Core Real (TangentSpace I p) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I p) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I p) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I p) :=
    @InnerProductSpace.ofCore Real (TangentSpace I p) _ _ _ D.toCore.toCore
  have hinner (w z : TangentSpace I p) :
      (Inner.inner Real w z : Real) = g.inner p w z := rfl
  have ha : Orthonormal Real a := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner]
    rcases i with _ | i <;> rcases j with _ | j
    · change g.inner p (ell⁻¹ • u) (ell⁻¹ • u) = 1
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← hell_sq]
      field_simp [hell.ne']
    · change g.inner p (ell⁻¹ • u)
          (v ⟨j, by simpa only [d] using j.2⟩) = 0
      simp only [map_smul, ContinuousLinearMap.smul_apply, hperp, smul_eq_mul,
        mul_zero]
    · change g.inner p (v ⟨i, by simpa only [d] using i.2⟩)
          (ell⁻¹ • u) = 0
      rw [g.symm]
      simp only [map_smul, ContinuousLinearMap.smul_apply, hperp, smul_eq_mul,
        mul_zero]
    · simpa only [a, Option.some.injEq] using
        hON ⟨i, by simpa only [d] using i.2⟩
          ⟨j, by simpa only [d] using j.2⟩
  have hcard :
      Fintype.card (Option (Fin d)) =
        Module.finrank Real (TangentSpace I p) := by
    simpa only [Fintype.card_option, Fintype.card_fin] using hdim
  let Ba : Module.Basis (Option (Fin d)) Real (TangentSpace I p) :=
    basisOfOrthonormalOfCardEqFinrank ha hcard
  have hBa (i : Option (Fin d)) : Ba i = a i := by
    exact congr_fun (coe_basisOfOrthonormalOfCardEqFinrank ha hcard) i
  let e : Option (Fin d) ≃ Fin (Module.finrank Real E) :=
    (finSuccEquiv d).symm.trans (finCongr hdim)
  let Bs : Module.Basis (Option (Fin d)) Real (TangentSpace I p) :=
    B.reindex e.symm
  have hBs (i : Option (Fin d)) :
      Bs i = B (e i) := by
    simp only [Bs, Module.Basis.reindex_apply, Equiv.symm_symm]
  have hBsON : ∀ i j, g.inner p (Bs i) (Bs j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [hBs, hBs, hB]
    rw [if_congr e.injective.eq_iff rfl rfl]
  have hBaON : ∀ i j, g.inner p (Ba i) (Ba j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [hBa, hBa, ← hinner]
    exact (orthonormal_iff_ite (𝕜 := Real) (v := a)).mp ha i j
  have dens_one
      (B : Module.Basis (Option (Fin d)) Real (TangentSpace I p))
      (hB : ∀ i j, g.inner p (B i) (B j) =
        if i = j then 1 else 0) :
      curveDensity (I := I) g (fun _ : Real => p)
          (fun i (_ : Real) => B i) 0 = 1 := by
    have hgram :
        curveGram (I := I) g (fun _ : Real => p)
            (fun i (_ : Real) => B i) 0 = 1 := by
      ext i j
      simpa only [curveGram, Matrix.of_apply, Matrix.one_apply] using hB i j
    rw [curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
  let Cb : Matrix (Option (Fin d)) (Option (Fin d)) Real := Ba.toMatrix Bs
  have hcoord (i : Option (Fin d)) :
      Bs i = ∑ k, Cb k i • Ba k := by
    simpa only [Cb, Module.Basis.toMatrix_apply] using (Ba.sum_repr (Bs i)).symm
  have hCb := curveDensity_recomb (I := I) g (fun _ : Real => p)
    (fun i (_ : Real) => Ba i) (fun i (_ : Real) => Bs i) 0 Cb hcoord
  have hdet_basis : |Cb.det| = 1 := by
    rw [dens_one Ba hBaON, dens_one Bs hBsON, mul_one] at hCb
    exact hCb.symm
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let Vt : Fin d → ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm p u
      (v ⟨i, by simpa only [d] using i.2⟩)
  let Va : Option (Fin d) → ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm p u (Ba i)
  let C : Matrix (Option (Fin d)) (Option (Fin d)) Real :=
    Matrix.diagonal fun i => i.elim ell⁻¹ (fun _ => 1)
  have hjac_smul :
      intrinsicJacobi (I := I) g hEnorm p u (ell⁻¹ • u) 1 =
        ell⁻¹ • intrinsicJacobi (I := I) g hEnorm p u u 1 := by
    let L :=
      mfderiv 𝓘(Real, E) I
        (fun b : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from b))
        (show E from u)
    have hcol (w : TangentSpace I p) :
        intrinsicJacobi (I := I) g hEnorm p u w 1 =
          L (show E from w) :=
      intrinsic_jacobi_one (I := I) g hEnorm p u w
    rw [hcol (ell⁻¹ • u), hcol u]
    exact L.map_smul ell⁻¹ (show E from u)
  have hrec (i : Option (Fin d)) :
      Va i 1 =
        ∑ k, C k i • velJacFrame (I := I) g hEnorm p u
          (fun j => v ⟨j, by simpa only [d] using j.2⟩) k 1 := by
    rcases i with _ | i
    · rw [show Va none 1 =
          intrinsicJacobi (I := I) g hEnorm p u (ell⁻¹ • u) 1 by
            simp only [Va, hBa, a]]
      rw [hjac_smul, radialJac_eq_vel (I := I) g hEnorm p u]
      simp only [C, Matrix.diagonal_apply]
      simp
    · rw [show Va (some i) 1 =
          intrinsicJacobi (I := I) g hEnorm p u
            (v ⟨i, by simpa only [d] using i.2⟩) 1 by
            simp only [Va, hBa, a]]
      simp only [C, Matrix.diagonal_apply]
      simp
  have hCdet : C.det = ell⁻¹ := by
    simp [C]
  have hCabs : |C.det| = ell⁻¹ := by
    rw [hCdet, abs_of_pos (inv_pos.2 hell)]
  have hscale := curveDensity_recomb (I := I) g γ
    (velJacFrame (I := I) g hEnorm p u
      (fun j => v ⟨j, by simpa only [d] using j.2⟩))
    Va 1 C hrec
  have hsplit := velJac_density_split (I := I) g hEnorm p u
    (fun j => v ⟨j, by simpa only [d] using j.2⟩)
    (fun j => hperp ⟨j, by simpa only [d] using j.2⟩)
  have hadapt :
      curveDensity (I := I) g γ Va 1 =
        curveDensity (I := I) g γ Vt 1 := by
    rw [hscale, hCabs, hsplit]
    rw [← mul_assoc, inv_mul_cancel₀ hell.ne', one_mul]
  have hbasis := jacDens_basis (I := I) g hEnorm p u Ba Bs
  rw [show |Ba.det Bs| = 1 by simpa only [Cb] using hdet_basis, one_mul] at hbasis
  have hreindex := curveDensity_reindex (I := I) g γ
    (fun i t => intrinsicJacobi (I := I) g hEnorm p u
      (B i) t) 1 e
  calc
    curveDensity (I := I) g γ
        (fun i t => intrinsicJacobi (I := I) g hEnorm p u
          (B i) t) 1 =
      curveDensity (I := I) g γ
          (fun i t => intrinsicJacobi (I := I) g hEnorm p u (Bs i) t) 1 := by
          simpa only [hBs] using hreindex.symm
    _ = curveDensity (I := I) g γ Va 1 := by
          simpa only [Va] using hbasis
    _ = curveDensity (I := I) g γ Vt 1 := hadapt
    _ = curveDensity (I := I) g γ
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 := by
          congr 2

omit [T2Space (TangentBundle I M)] in
theorem expDens_scale
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p)
    (hu : 0 < g.inner p u u)
    (B : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I p))
    (hB : ∀ i j, g.inner p (B i) (B j) = if i = j then 1 else 0)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    {t : Real} (ht : 0 < t) :
    t ^ (Module.finrank Real E - 1) *
        curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p (t • u))
          (fun i s => intrinsicJacobi (I := I) g hEnorm p (t • u) (B i) s) 1 =
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t := by
  have hinner :
      g.inner p (t • u) (t • u) = t ^ 2 * g.inner p u u := by
    let β : E →L[Real] E →L[Real] Real := g.inner p
    let U : E := u
    change β (t • U) (t • U) = t ^ 2 * β U U
    have hleft : β (t • U) (t • U) = t * β U (t • U) := by
      have h := congrArg (fun A : E →L[Real] Real => A (t • U)) (β.map_smul t U)
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
    have hright : β U (t • U) = t * β U U := by
      simpa only [smul_eq_mul] using (β U).map_smul t U
    rw [hleft, hright, pow_two]
    ring
  have htu : 0 < g.inner p (t • u) (t • u) := by
    rw [hinner]
    exact mul_pos (sq_pos_of_pos ht) hu
  have hperp' : ∀ i, g.inner p (t • u) (v i) = 0 := by
    intro i
    have h := congrArg (fun A : TangentSpace I p →L[Real] Real => A (v i))
      ((g.inner p).map_smul t u)
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, hperp i, mul_zero] using h
  rw [fullDens_eq_trans (I := I) g hEnorm p (t • u) htu B hB v hON hperp']
  have hscale := transDens_scale (I := I) g hEnorm p u v t
  rw [abs_of_pos ht] at hscale
  exact hscale.symm

theorem expDens_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p)
    (B : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I p))
    (hB : ∀ i j, g.inner p (B i) (B j) = if i = j then 1 else 0)
    (q : Real)
    (hq : 0 ≤ q) (hu : u ≠ 0)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) 1,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (fun i t => intrinsicJacobi (I := I) g hEnorm p u
          (B i) t) 1 ≤
      hypDensity (q * Real.sqrt (g.inner p u u))
        (Module.finrank Real E - 1) 1 := by
  have hu_pos : 0 < g.inner p u u := g.pos p u hu
  by_cases hd : 0 < Module.finrank Real E - 1
  · obtain ⟨v, hON, hperp, hbound⟩ :=
      transDens_le_one (I := I) g hEnorm p u q hq hd hu_pos hno hRic
    rw [fullDens_eq_trans (I := I) g hEnorm p u hu_pos B hB v hON hperp]
    exact hbound
  · have hd0 : Module.finrank Real E - 1 = 0 := Nat.eq_zero_of_not_pos hd
    let v : Fin (Module.finrank Real E - 1) → TangentSpace I p :=
      fun i => isEmptyElim (hd0 ▸ i)
    have hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0 := by
      intro i
      exact isEmptyElim (hd0 ▸ i)
    have hperp : ∀ i, g.inner p u (v i) = 0 := by
      intro i
      exact isEmptyElim (hd0 ▸ i)
    rw [fullDens_eq_trans (I := I) g hEnorm p u hu_pos B hB v hON hperp]
    have hgram :
        curveGram (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 = 1 := by
      ext i
      exact isEmptyElim (hd0 ▸ i)
    rw [curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
    simp only [hd0, hypDensity, pow_zero, le_refl]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
