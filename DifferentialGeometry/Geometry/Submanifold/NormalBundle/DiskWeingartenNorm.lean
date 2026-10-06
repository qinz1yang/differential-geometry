import DifferentialGeometry.Geometry.Submanifold.NormalBundle.WeingartenNorm
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskTensionTrace
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem normalVariation_covariantDerivative_norm_sq_complex
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = 3) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ)
    (W : ∀ q : ℂ, TangentSpace 𝓘(ℝ, E) (U q))
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℂ => (⟨U q, W q⟩ : TangentBundle 𝓘(ℝ, E) M)) (N : Set ℂ))
    (hW_eq : ∀ q : N, (W q : E) = φ q • ν q)
    (z : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
    (∑ i : Fin 2, g.inner (U z)
      (sourceSectionCovariantDerivative g U W z (b i))
      (sourceSectionCovariantDerivative g U W z (b i))) =
      gN.inner z (gradFun gN φ z) (gradFun gN φ z) +
        φ z ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
          g.inner (U z) (II (b i) (b j)) (II (b i) (b j)) := by
  classical
  dsimp only
  let A := EuclideanSpace ℝ (Fin 2)
  have hdimTwo : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  let L : ℂ ≃ₗᵢ[ℝ] A :=
    ((stdOrthonormalBasis ℝ ℂ).reindex (finCongr hdimTwo)).repr
  let e : A ≃L[ℝ] ℂ := L.symm.toContinuousLinearEquiv
  let O : TopologicalSpace.Opens A :=
    TopologicalSpace.Opens.mk (e ⁻¹' (N : Set ℂ)) (N.isOpen.preimage e.continuous)
  let ψ : O → N := fun q => ⟨e q, q.property⟩
  have hψ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ ψ :=
    (ContMDiff.subtypeVal_comp_iff N ψ).mp
      (e.contDiff.contMDiff.comp contMDiff_subtype_val)
  have hdψ (q : O) : (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ψ q : A →L[ℝ] ℂ) =
      e.toContinuousLinearMap := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp ψ q]
    change mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun p : O => e p) q = _
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact e.mfderiv_eq
  let V : A → M := fun q => U (e q)
  have hV : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (fun q : O => V q) := hU.comp hψ
  have hdV (q : O) :
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : O => V p) q : A →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) (ψ q)).comp
          e.toContinuousLinearMap := by
    have hc := mfderiv_comp q (hU.mdifferentiable (by simp) (ψ q))
      (hψ.mdifferentiable (by simp) q)
    change (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : O => V p) q : A →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) (ψ q) : ℂ →L[ℝ] E).comp
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ψ q : A →L[ℝ] ℂ) at hc
    rw [hdψ] at hc
    exact hc
  have hj (q : O) : Function.Injective
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : O => V p) q) := by
    rw [hdV]
    exact (hi (ψ q)).comp e.injective
  let gN := g.pullback (fun q : N => U q) hU hi
  let gO := g.pullback (fun q : O => V q) hV hj
  have hmetric (q : O) (a c : A) : gO.inner q a c = gN.inner (ψ q) (e a) (e c) := by
    change g.inner (V q)
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : O => V p) q a)
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : O => V p) q c) = _
    rw [hdV]
    rfl
  let y : O := ⟨e.symm z, by change e (e.symm (z : ℂ)) ∈ (N : Set ℂ); simp⟩
  have hy : e (y : A) = (z : ℂ) := e.apply_symm_apply z
  have hψy : ψ y = z := Subtype.ext hy
  let b₀ : Module.Basis (Fin 2) ℝ ℂ := b
  let b' : Module.Basis (Fin 2) ℝ A := b₀.map e.symm.toLinearEquiv
  have hb' (i j : Fin 2) : gO.inner y (b' i) (b' j) = if i = j then 1 else 0 := by
    refine (hmetric y (b' i) (b' j)).trans ?_
    let BN : N → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun q => gN.inner q
    change BN (ψ y) (e (e.symm (b₀ i))) (e (e.symm (b₀ j))) = _
    rw [e.apply_symm_apply, e.apply_symm_apply, hψy]
    exact hb i j
  let ν₀ : N → E := fun q => ν q
  let W₀ : ℂ → E := W
  have hWmodel (q : N) : W₀ q = φ q • ν₀ q := hW_eq q
  -- The representatives below are only used on the open preimage O.
  let n : ∀ q : A, TangentSpace 𝓘(ℝ, E) (V q) := fun q =>
    if h : e q ∈ (N : Set ℂ) then ν ⟨e q, h⟩ else 0
  let p : A → ℝ := fun q => if h : e q ∈ (N : Set ℂ) then φ ⟨e q, h⟩ else 0
  let n₀ : A → E := n
  have hn (q : O) : n₀ q = ν₀ (ψ q) := by
    have hq : e (q : A) ∈ (N : Set ℂ) := q.property
    change (if h : e (q : A) ∈ (N : Set ℂ) then ν₀ ⟨e q, h⟩ else (0 : E)) =
      ν₀ (ψ q)
    rw [dite_eq_left hq]
  have hp (q : O) : p q = φ (ψ q) := by
    have hq : e (q : A) ∈ (N : Set ℂ) := q.property
    change (if h : e (q : A) ∈ (N : Set ℂ) then φ ⟨e q, h⟩ else 0) = φ (ψ q)
    rw [dite_eq_left hq]
  have hnres : ContMDiff 𝓘(ℝ, A) (𝓘(ℝ, E).tangent) ∞
      (fun q : O => (⟨V q, n q⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    have heq : (fun q : O => (⟨V q, n q⟩ : TangentBundle 𝓘(ℝ, E) M)) =
        (fun q : O => (⟨U (ψ q), ν (ψ q)⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
      funext q
      exact congrArg (fun v : TangentSpace 𝓘(ℝ, E) (V q) =>
        (⟨V q, v⟩ : TangentBundle 𝓘(ℝ, E) M)) (hn q)
    rw [heq]
    exact hν.comp hψ
  have hnon : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨V q, n q⟩ : TangentBundle 𝓘(ℝ, E) M)) (O : Set A) := by
    intro q hq
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, A)) (I' := 𝓘(ℝ, E).tangent)
      (f := fun r : A => (⟨V r, n r⟩ : TangentBundle 𝓘(ℝ, E) M))).mp
        (hnres.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hpres : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℝ) ∞ (fun q : O => p q) := by
    have heq : (fun q : O => p q) = φ ∘ ψ := funext hp
    rw [heq]
    exact hφ.comp hψ
  have hpon : ContDiffOn ℝ ∞ p (O : Set A) := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp
      (hpres.contMDiffAt (x := ⟨q, hq⟩))).contDiffAt.contDiffWithinAt
  have hunit' (q : A) (hq : q ∈ O) : g.inner (V q) (n q) (n q) = 1 := by
    let q' : O := ⟨q, hq⟩
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (V q)
    change B (n₀ q') (n₀ q') = 1
    rw [hn q']
    exact hunit (ψ q')
  have hnormal' (q : A) (hq : q ∈ O) (a : A) :
      g.inner (V q) (n q) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V q a) = 0 := by
    let q' : O := ⟨q, hq⟩
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (V q)
    change B (n₀ q') (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V q' a) = 0
    rw [← DifferentialGeometry.mfderiv_restrict_open V O q', hdV, hn q']
    exact hnormal (ψ q') (e a)
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) :=
    (contMDiff_proj (TangentSpace 𝓘(ℝ, E))).comp_contMDiffOn hW
  have hVon : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ V (O : Set A) :=
    hUon.comp e.contDiff.contMDiff.contMDiffOn (fun _ hq => hq)
  have hdVfull (q : A) (hq : q ∈ O) (a : A) :
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V q a : E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e q) (e a) := by
    let DV : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V q
    let DU : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e q)
    change DV a = DU (e a)
    have hc := mfderiv_comp q
      (((hUon (e q) hq).contMDiffAt (N.isOpen.mem_nhds hq)).mdifferentiableAt (by simp))
      ((e.contDiff : ContDiff ℝ ∞ e).contMDiff.mdifferentiable (by simp) q)
    change DV = DU.comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) e q : A →L[ℝ] ℂ) at hc
    rw [e.mfderiv_eq] at hc
    exact congrArg (fun T : A →L[ℝ] E => T a) hc
  have hline (q a : A) (t : ℝ) : e (q + t • a) = e q + t • e a := by
    rw [map_add, map_smul]
  let DW : ℂ → E := fun a => sourceSectionCovariantDerivative g U W z a
  let DW' : A → E := fun a =>
    sourceSectionCovariantDerivative g V (fun q => p q • n q) y a
  have hsection (a : A) : DW' a = DW (e a) := by
    change (sourceSectionCovariantDerivative g V (fun q => p q • n q) y a : E) =
      sourceSectionCovariantDerivative g U W z (e a)
    apply covDerivAlong_congr_curve g
      (fun t => p ((y : A) + t • a) • n ((y : A) + t • a))
      (fun t => W ((z : ℂ) + t • e a))
    · filter_upwards [] with t
      change U (e ((y : A) + t • a)) = U ((z : ℂ) + t • e a)
      rw [hline, hy]
    · have ht : Tendsto (fun t : ℝ => (y : A) + t • a) (𝓝 0) (𝓝 (y : A)) := by
        have hc : Continuous (fun t : ℝ => (y : A) + t • a) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
      filter_upwards [ht.eventually (O.isOpen.mem_nhds y.property)] with t ht
      let q : O := ⟨(y : A) + t • a, ht⟩
      change p q • n₀ q = W₀ ((z : ℂ) + t • e a)
      rw [hp, hn, ← hWmodel]
      exact congrArg W₀
        ((hline y a t).trans (congrArg (fun r : ℂ => r + t • e a) hy))
  let C : ℂ → ℂ → E := fun a c => sourceCovariantPartial g U z a c
  let C' : A → A → E := fun a c => sourceCovariantPartial g V y a c
  have hpartial (a c : A) : C' a c = C (e a) (e c) := by
    change (sourceCovariantPartial g V y a c : E) =
      sourceCovariantPartial g U z (e a) (e c)
    apply covDerivAlong_congr_curve g
      (fun t => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V ((y : A) + t • a) c)
      (fun t => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U ((z : ℂ) + t • e a) (e c))
    · filter_upwards [] with t
      change U (e ((y : A) + t • a)) = U ((z : ℂ) + t • e a)
      rw [hline, hy]
    · have ht : Tendsto (fun t : ℝ => (y : A) + t • a) (𝓝 0) (𝓝 (y : A)) := by
        have hc : Continuous (fun t : ℝ => (y : A) + t • a) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
      filter_upwards [ht.eventually (O.isOpen.mem_nhds y.property)] with t ht
      rw [hdVfull _ ht, hline, hy]
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let Q' : A →L[ℝ] A →L[ℝ] E :=
    secondFundamentalFormAmbientAt gO g (fun q : O => V q) y
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  let ℓ : E →L[ℝ] ℝ := B (ν₀ z)
  have hB : (g.inner (V y) : E →L[ℝ] E →L[ℝ] ℝ) = B := by
    change (g.inner (U (e (y : A))) : E →L[ℝ] E →L[ℝ] ℝ) = B
    rw [hy]
  have hnormalU (a : ℂ) : B (ν₀ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z a) = 0 := by
    rw [← DifferentialGeometry.mfderiv_restrict_open U N z]
    exact hnormal z a
  have hdiag (a : A) : ℓ (Q' a a) = ℓ (Q (e a) (e a)) := by
    let correction : A := (Curvature.metricCov gO)
      (fun q : O => (a : TangentSpace 𝓘(ℝ, A) q)) y a
    let P' : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) V y
    have heq : Q' a a = C' a a - P' correction :=
      (immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_contMDiffOn
        O V hVon g gO y a a).symm
    have hnormalV : ℓ (P' correction) = 0 := by
      have hd := hdVfull y y.property correction
      change P' correction =
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e (y : A)) : ℂ →L[ℝ] E) (e correction) at hd
      rw [hy] at hd
      exact (congrArg ℓ hd).trans (hnormalU (e correction))
    rw [heq, map_sub, hnormalV, sub_zero, hpartial]
    exact (inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
      N gN g U hU z (ν z) hnormalU (e a)).symm
  have hQsym (a c : ℂ) : Q a c = Q c a :=
    secondFundamentalFormAmbientAt_symmetric gN g (hU.contMDiffAt.of_le (by simp)) a c
  have hQ'sym (a c : A) : Q' a c = Q' c a :=
    secondFundamentalFormAmbientAt_symmetric gO g (hV.contMDiffAt.of_le (by simp)) a c
  have hpair (a c : A) : ℓ (Q' a c) = ℓ (Q (e a) (e c)) := by
    have hsum := hdiag (a + c)
    simp only [map_add, _root_.add_apply, hQsym (e c) (e a), hQ'sym c a] at hsum
    have ha := hdiag a
    have hc := hdiag c
    linarith only [hsum, ha, hc]
  let P : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
  let frame : Option (Fin 2) → E := fun i => i.elim (ν₀ z) (fun j => P (b j))
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
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) (U z)) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact hdim.symm
  have hnorm (v : E) (hv : ∀ i : Fin 2, B v (P (b i)) = 0) : B v v = (ℓ v) ^ 2 := by
    have h : B v v = ∑ i : Option (Fin 2), (B (frame i) v) ^ 2 :=
      inner_self_eq_sum_sq g (U z) hcard frame hframe v
    change B v v = (B (ν₀ z) v) ^ 2
    rw [h]
    simp only [Fintype.sum_option, frame, Option.elim_none, Option.elim_some]
    have hzero (i : Fin 2) : B (P (b i)) v = 0 := (g.symm (U z) _ _).trans (hv i)
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  have hQnormal (a c w : ℂ) : B (Q a c) (P w) = 0 :=
    secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hU (fun _ _ _ => rfl) z a c w
  have hQ'normal (a c : A) (w : ℂ) : B (Q' a c) (P w) = 0 := by
    have h := secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hV (gN := gO) (gM := g) (fun _ _ _ => rfl) y a c (e.symm w)
    change (g.inner (V y) : E →L[ℝ] E →L[ℝ] ℝ) (Q' a c)
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun q : O => V q) y (e.symm w)) = 0 at h
    rw [hB, hdV] at h
    change B (Q' a c)
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) (ψ y) : ℂ →L[ℝ] E)
        (e (e.symm w))) = 0 at h
    rw [e.apply_symm_apply, hψy] at h
    exact h
  have hQnorm (a c : A) : B (Q' a c) (Q' a c) =
      B (Q (e a) (e c)) (Q (e a) (e c)) := by
    rw [hnorm _ (fun i => hQ'normal a c (b i)),
      hnorm _ (fun i => hQnormal (e a) (e c) (b i)), hpair]
  have hdp : (mvfderiv 𝓘(ℝ, A) (fun q : O => p q) y : A →L[ℝ] ℝ) =
      (mvfderiv 𝓘(ℝ, ℂ) φ z : ℂ →L[ℝ] ℝ).comp e.toContinuousLinearMap := by
    have heq : (fun q : O => p q) = φ ∘ ψ := funext hp
    rw [heq, mvfderiv_comp y (hφ.mdifferentiable (by simp) (ψ y))
      (hψ.mdifferentiable (by simp) y), hdψ]
    change (mvfderiv 𝓘(ℝ, ℂ) φ (ψ y) : ℂ →L[ℝ] ℝ).comp
      e.toContinuousLinearMap = _
    rw [hψy]
  have hgrad : gO.inner y (gradFun gO (fun q : O => p q) y)
      (gradFun gO (fun q : O => p q) y) =
        gN.inner z (gradFun gN φ z) (gradFun gN φ z) := by
    rw [inner_gradFun_self_eq_sum_sq gO (fun q : O => p q) y b' hb',
      inner_gradFun_self_eq_sum_sq gN φ z b hb]
    apply Finset.sum_congr rfl
    intro i _
    let dp : A →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, A) (fun q : O => p q) y
    let dφ : ℂ →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, ℂ) φ z
    have hd : dp = dφ.comp e.toContinuousLinearMap := hdp
    change dp (e.symm (b₀ i)) ^ 2 = dφ (b₀ i) ^ 2
    have hv : dp (e.symm (b₀ i)) = dφ (b₀ i) :=
      (congrArg (fun T : A →L[ℝ] ℝ => T (e.symm (b₀ i))) hd).trans
        (congrArg dφ (e.apply_symm_apply (b₀ i)))
    exact congrArg (fun r : ℝ => r ^ 2) hv
  have henergy := normalVariation_covariantDerivative_norm_sq O g hdim V hV hj
    n hnon hunit' hnormal' p hpon y b' hb'
  change (∑ i : Fin 2, (g.inner (V y) : E →L[ℝ] E →L[ℝ] ℝ)
    (DW' (b' i)) (DW' (b' i))) =
      gO.inner y (gradFun gO (fun q : O => p q) y) (gradFun gO (fun q : O => p q) y) +
        p y ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
          (g.inner (V y) : E →L[ℝ] E →L[ℝ] ℝ) (Q' (b' i) (b' j)) (Q' (b' i) (b' j)) at henergy
  rw [hB, hgrad, hp, hψy] at henergy
  have hbmap (i : Fin 2) : e (b' i) = b₀ i := e.apply_symm_apply (b₀ i)
  have hsumDW : (∑ i : Fin 2, B (DW' (b' i)) (DW' (b' i))) =
      ∑ i : Fin 2, B (DW (b₀ i)) (DW (b₀ i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun v : E => B v v)
      ((hsection (b' i)).trans (congrArg DW (hbmap i)))
  have hsumQ : (∑ i : Fin 2, ∑ j : Fin 2, B (Q' (b' i) (b' j)) (Q' (b' i) (b' j))) =
      ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b₀ i) (b₀ j)) (Q (b₀ i) (b₀ j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hQnorm (b' i) (b' j)).trans
      (congrArg₂ (fun a c : ℂ => B (Q a c) (Q a c)) (hbmap i) (hbmap j))
  have henergyModel : (∑ i : Fin 2, B (DW' (b' i)) (DW' (b' i))) =
      gN.inner z (gradFun gN φ z) (gradFun gN φ z) +
        φ z ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
          B (Q' (b' i) (b' j)) (Q' (b' i) (b' j)) := henergy
  exact hsumDW.symm.trans (henergyModel.trans
    (congrArg (fun q : ℝ => gN.inner z (gradFun gN φ z) (gradFun gN φ z) +
      φ z ^ 2 * q) hsumQ))

end DifferentialGeometry.Geometry
