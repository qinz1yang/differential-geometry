import DifferentialGeometry.Geometry.Submanifold.NormalBundle.DiskWeingartenNorm
import DifferentialGeometry.Geometry.Measure.Area.NormalSecondVariation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

local notation "D" =>
  TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem original_disk_normal_second_density_with_mean_and_acceleration
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z))
    (ν : ∀ q : D, TangentSpace (𝓡 3) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle (𝓡 3) M)))
    (hunit : ∀ q : D, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : D) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q v) = 0) :
    ∃ (hf : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q))
      (hi : ∀ q : D, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q)),
      let gD := g.pullback (fun q : D => U q) hf hi
      ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      ∀ (X : ∀ x : M, TangentSpace (𝓡 3) x)
        (hX : ContMDiff (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle (𝓡 3) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) :
              EuclideanSpace ℝ (Fin 3)) = φ q • ν q) →
      ∀ (z : D) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z)),
        (∀ i j, gD.inner z (b i) (b j) = if i = j then 1 else 0) →
        let Φ := Diffeomorph.compactSupportFlow X hX hXc
        let P : Fin 2 → TangentSpace (𝓡 3) (U z) := fun i =>
          mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z (b i)
        let II := secondFundamentalFormAmbientAt gD g (fun q : D => U q) z
        let A : ∀ x : M, TangentSpace (𝓡 3) x := fun x =>
          (LeviCivita g).toFun X x (X x)
        let DA : Fin 2 → TangentSpace (𝓡 3) (U z) := fun i =>
          sourceSectionCovariantDerivative g U (fun q => A (U q)) z (b i)
        HasDerivAt (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z))
          (riemannianAreaDensity g U z *
            (gD.inner z (gradFun gD φ z) (gradFun gD φ z) -
              φ z ^ 2 *
                ((∑ i : Fin 2, g.inner (U z)
                    ((riemannOp (LeviCivita g) (U z)) (ν z) (P i) (P i)) (ν z)) +
                  ∑ i : Fin 2, ∑ j : Fin 2,
                    g.inner (U z) (II (b i) (b j)) (II (b i) (b j))) +
              φ z ^ 2 * (∑ i : Fin 2, g.inner (U z) (ν z) (II (b i) (b i))) ^ 2 +
              ∑ i : Fin 2, g.inner (U z) (DA i) (P i))) 0 := by
  obtain ⟨_, s, _, hDs, hUs⟩ := hExt
  have hf : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun q : D => U q) :=
    hUs.comp_contMDiff contMDiff_subtype_val
      (fun q => hDs (Metric.ball_subset_closedBall q.property))
  have hi : ∀ q : D, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => U p) q) := by
    intro q
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hImm q (Metric.ball_subset_closedBall q.property)
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U (D : Set ℂ) :=
    hUs.mono (fun q hq => hDs (Metric.ball_subset_closedBall hq))
  have hnormalU (q : D) (v : ℂ) :
      g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U q v) = 0 := by
    have hd := DifferentialGeometry.mfderiv_restrict_open
      (I := 𝓘(ℝ, ℂ)) (J := 𝓡 3) U D q
    exact (congrArg
      (fun L : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) => g.inner (U q) (ν q) (L v)) hd).symm.trans
      (hnormal q v)
  refine ⟨hf, hi, ?_⟩
  dsimp only
  intro φ hφ _hφc X hX hXc hvelocity z b hb
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  have hΦ₀ : Φ 0 = Diffeomorph.refl (𝓡 3) M ∞ :=
    Diffeomorph.compactSupportFlow_zero (I := 𝓡 3) X hX hXc
  have hflowvelocity (x : M) :
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t : ℝ => Φ t x) 0 (1 : ℝ) :
        EuclideanSpace ℝ (Fin 3)) = X x := by
    have hd := (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc x 0).mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) => L (1 : ℝ)) hd
    have hv' : (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t : ℝ => Φ t x) 0 (1 : ℝ) :
        EuclideanSpace ℝ (Fin 3)) = X (Φ 0 x) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t : ℝ => Φ t x) 0 (1 : ℝ) :
          EuclideanSpace ℝ (Fin 3)) = (1 : ℝ) • X (Φ 0 x) at hv
      simpa only [one_smul] using hv
    exact hv'.trans (congrArg (fun p : M => (X p : EuclideanSpace ℝ (Fin 3)))
      (DFunLike.congr_fun hΦ₀ x))
  have hXnormal (q : D) : (X (U q) : EuclideanSpace ℝ (Fin 3)) =
      φ q • (ν q : EuclideanSpace ℝ (Fin 3)) :=
    (hflowvelocity (U q)).symm.trans (hvelocity q)
  have hXU : ContMDiffOn 𝓘(ℝ, ℂ) ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
      (fun q : ℂ => (⟨U q, X (U q)⟩ : TangentBundle (𝓡 3) M)) (D : Set ℂ) :=
    hX.comp_contMDiffOn hUon
  let gD := g.pullback (fun q : D => U q) hf hi
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    secondFundamentalFormAmbientAt gD g (fun q : D => U q) z
  let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    g.inner (U z)
  let n : EuclideanSpace ℝ (Fin 3) := ν z
  let ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := B n
  let P : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun q : D => U q) z
  let T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z
  let DX : Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i =>
    sourceSectionCovariantDerivative g U (fun q => X (U q)) z (b i)
  let A : ∀ x : M, TangentSpace (𝓡 3) x := fun x => (LeviCivita g).toFun X x (X x)
  let DA : Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i =>
    sourceSectionCovariantDerivative g U (fun q => A (U q)) z (b i)
  let C : ℝ := ∑ i : Fin 2, B
    ((riemannOp (LeviCivita g) (U z)) (ν z) (T (b i)) (T (b i))) (ν z)
  have henergy : (∑ i : Fin 2, B (DX i) (DX i)) =
      gD.inner z (gradFun gD φ z) (gradFun gD φ z) +
        φ z ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j)) :=
    normalVariation_covariantDerivative_norm_sq_complex D g (by simp) U hf hi
      ν hν hunit hnormal φ hφ (fun q => X (U q)) hXU hXnormal z b hb
  classical
  let frame : Option (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
    fun i => i.elim n (fun j => P (b j))
  have hframe : ∀ i j, B (frame i) (frame j) = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hunit z
      | some j => exact hnormal z (b j)
    | some i =>
      cases j with
      | none => exact (g.symm (U z) _ _).trans (hnormal z (b i))
      | some j =>
        have h : B (P (b i)) (P (b j)) = if i = j then 1 else 0 := hb i j
        simpa only [frame, Option.elim_some, Option.some.injEq] using h
  have hcard : Fintype.card (Option (Fin 2)) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (U z)) := by
    change Fintype.card (Option (Fin 2)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp
  have hIInormal (a c w : ℂ) : B (Q a c) (P w) = 0 :=
    secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hf (fun _ _ _ => rfl) z a c w
  have hIInorm (a c : ℂ) : B (Q a c) (Q a c) = (ℓ (Q a c)) ^ 2 := by
    have h : B (Q a c) (Q a c) =
        ∑ i : Option (Fin 2), (B (frame i) (Q a c)) ^ 2 :=
      inner_self_eq_sum_sq g (U z) hcard frame hframe (Q a c)
    change B (Q a c) (Q a c) = (ℓ (Q a c)) ^ 2
    rw [h]
    simp only [Fintype.sum_option, frame, Option.elim_none, Option.elim_some]
    have hz (i : Fin 2) : B (P (b i)) (Q a c) = 0 :=
      (g.symm (U z) _ _).trans (hIInormal a c (b i))
    simp only [ℓ, hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  have hsym : Q (b 1) (b 0) = Q (b 0) (b 1) :=
    secondFundamentalFormAmbientAt_symmetric gD g (hf.contMDiffAt.of_le (by simp)) (b 1) (b 0)
  have hshape : (ℓ (Q (b 0) (b 0)) - ℓ (Q (b 1) (b 1))) ^ 2 +
      4 * (ℓ (Q (b 0) (b 1))) ^ 2 =
        2 * (∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j))) -
          (∑ i : Fin 2, ℓ (Q (b i) (b i))) ^ 2 := by
    let β : Fin 2 → ℂ := fun i => b i
    have hsymModel : Q (β 1) (β 0) = Q (β 0) (β 1) := hsym
    change (ℓ (Q (β 0) (β 0)) - ℓ (Q (β 1) (β 1))) ^ 2 +
        4 * (ℓ (Q (β 0) (β 1))) ^ 2 =
          2 * (∑ i : Fin 2, ∑ j : Fin 2, B (Q (β i) (β j)) (Q (β i) (β j))) -
            (∑ i : Fin 2, ℓ (Q (β i) (β i))) ^ 2
    simp_rw [hIInorm]
    simp only [Fin.sum_univ_two, hsymModel]
    ring
  have hsecond := hasDerivAt_deriv_compactSupportFlow_areaDensity_of_normal_velocity
    D g U hf hi ν hnormalU φ X hX hXc hvelocity z b hb
  apply hsecond.congr_deriv
  change riemannianAreaDensity g U z *
      ((∑ i : Fin 2, (B (DX i) (DX i) + B (DA i) (T (b i)))) - φ z ^ 2 * C -
        φ z ^ 2 * ((ℓ (Q (b 0) (b 0)) - ℓ (Q (b 1) (b 1))) ^ 2 +
          4 * (ℓ (Q (b 0) (b 1))) ^ 2)) =
    riemannianAreaDensity g U z *
      (gD.inner z (gradFun gD φ z) (gradFun gD φ z) -
        φ z ^ 2 * (C + ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j))) +
        φ z ^ 2 * (∑ i : Fin 2, ℓ (Q (b i) (b i))) ^ 2 +
        ∑ i : Fin 2, B (DA i) (T (b i)))
  rw [Finset.sum_add_distrib, henergy, hshape]
  ring

end DifferentialGeometry.Geometry
