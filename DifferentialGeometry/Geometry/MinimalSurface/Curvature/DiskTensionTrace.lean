import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem secondFundamentalForm_disk_diagonal_eq_sub_tangent
    (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (z : N) (v : ℂ) :
    ∃ a : TangentSpace 𝓘(ℝ, ℂ) z,
      secondFundamentalFormAmbientAt gN g (fun q : N => U q) z v v =
        diskMapCovariantPartial g U z v v -
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z a := by
  classical
  let line : ℝ → ℂ := fun t => (z : ℂ) + t • v
  let γ : ℝ → N := fun t => if h : line t ∈ (N : Set ℂ) then ⟨line t, h⟩ else z
  have hline : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), line t ∈ (N : Set ℂ) := by
    apply hline.continuous.continuousAt.preimage_mem_nhds
    apply N.isOpen.mem_nhds
    change (z : ℂ) + (0 : ℝ) • v ∈ (N : Set ℂ)
    rw [zero_smul, add_zero]
    exact z.property
  have hval : (fun t => (γ t : ℂ)) =ᶠ[𝓝 (0 : ℝ)] line := by
    filter_upwards [hmem] with t ht
    simp only [γ, dite_eq_left ht]
  have hγ0 : γ 0 = z := by
    apply Subtype.ext
    simpa only [line, zero_smul, add_zero] using hval.eq_of_nhds
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ 0 := by
    apply (ContMDiffAt.subtypeVal_comp_iff N γ 0).mp
    exact hline.contMDiff.contMDiffAt.congr_of_eventuallyEq hval
  have hv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ) : ℂ) = v := by
    have hsub : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 : ℝ →L[ℝ] ℂ) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t => (γ t : ℂ)) 0 :=
      (DifferentialGeometry.mfderiv_subtypeVal_comp γ 0).symm
    have hd : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t => (γ t : ℂ)) 0 :
        ℝ →L[ℝ] ℂ) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) line 0 := hval.mfderiv_eq
    have hl : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) line 0 : ℝ →L[ℝ] ℂ) (1 : ℝ) = v := by
      have hid : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) line 0 : ℝ →L[ℝ] ℂ) (1 : ℝ) =
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) z : ℂ →L[ℝ] ℂ) v :=
        source_mfderiv_line (r := (id : ℂ → ℂ)) (z := (z : ℂ)) mdifferentiableAt_id v
      have hident : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) z : ℂ →L[ℝ] ℂ) =
          ContinuousLinearMap.id ℝ ℂ := mfderiv_id
      exact hid.trans (congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hident)
    exact (congrArg (fun L : ℝ →L[ℝ] ℂ => L (1 : ℝ)) (hsub.trans hd)).trans hl
  have hcurve : (fun t => U (γ t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => U (line t)) :=
    hval.fun_comp U
  have hvelocity : ∀ᶠ t in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (γ s)) t (1 : ℝ) : E) =
        diskMapPartial U (line t) v := by
    filter_upwards [hcurve.eventuallyEq_nhds, hmem] with t ht htm
    have hd : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (γ s)) t :
        ℝ →L[ℝ] E) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (line s)) t :=
      ht.mfderiv_eq
    have hvel := congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hd
    have hUt : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (line t) :=
      (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨line t, htm⟩))).mdifferentiableAt
        (by simp)
    have hl : HasDerivAt line v t := by
      simpa only [line, id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const v).const_add (z : ℂ)
    have hc := tangent_velocity_comp hUt hl.differentiableAt
    have hc' := congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E)) hc
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (line s)) t (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (line t) (deriv line t) at hc'
    have hlinevel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (line s)) t (1 : ℝ) : E) =
        diskMapPartial U (line t) v :=
      hc'.trans (congrArg (fun w : ℂ => (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (line t) w : E)) hl.deriv)
    exact hvel.trans hlinevel
  have hacc : (covariantAcceleration g (fun t => U (γ t)) 0 : E) =
      diskMapCovariantPartial g U z v v := by
    exact covDerivAlong_congr_curve g
      (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => U (γ s)) t (1 : ℝ))
      (fun t => diskMapPartial U (line t) v) hcurve hvelocity
  have hII := secondFundamentalFormAmbientAt_diagonal_along_curve_of_contMDiffAt
    gN g (iota := fun q : N => U q) γ 0
    (hU.contMDiffAt.of_le (by simp)) (hγ.of_le (by simp))
  let II : N → ℂ →L[ℝ] ℂ →L[ℝ] E := fun q =>
    secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
  let D : N → ℂ →L[ℝ] E := fun q => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q
  let a : ℂ := covariantAcceleration gN γ 0
  have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) (γ 0) : ℂ →L[ℝ] E) =
      D (γ 0) := DifferentialGeometry.mfderiv_restrict_open U N (γ 0)
  have hraw : II (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ) : ℂ)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ) : ℂ) =
    (covariantAcceleration g (fun t => U (γ t)) 0 : E) -
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) (γ 0) : ℂ →L[ℝ] E) a := hII
  rw [hv, hacc, hdf, hγ0] at hraw
  exact ⟨a, hraw⟩

/-- Pairing with a genuine normal removes the source-connection term in the
actual second fundamental form of the restricted disk map. -/
theorem inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial
    (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (z : N) (W : TangentSpace 𝓘(ℝ, E) (U z))
    (hW : ∀ a : ℂ, g.inner (U z) W (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z a) = 0)
    (v : ℂ) :
    g.inner (U z) W (secondFundamentalFormAmbientAt gN g (fun q : N => U q) z v v) =
      g.inner (U z) W (diskMapCovariantPartial g U z v v) := by
  obtain ⟨a, ha⟩ := secondFundamentalForm_disk_diagonal_eq_sub_tangent N gN g U hU z v
  rw [ha, map_sub, hW a, sub_zero]

/-- Harmonicity kills the coordinate trace of the actual induced second
fundamental form. No conformality is needed for this coordinate identity. -/
theorem secondFundamentalForm_disk_coordinate_trace_eq_zero_of_tension_eq_zero
    (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) = gN.inner z v w)
    (z : N) (htension : diskMapTension g U z = 0) :
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z (1 : ℂ) (1 : ℂ) +
      secondFundamentalFormAmbientAt gN g (fun q : N => U q) z Complex.I Complex.I = 0 := by
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let S : E := Q (1 : ℂ) (1 : ℂ) + Q Complex.I Complex.I
  have hmetric' : ∀ (q : N) (v w : TangentSpace 𝓘(ℝ, ℂ) q),
      g.inner (U q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q w) = gN.inner q v w := by
    intro q v w
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q := DifferentialGeometry.mfderiv_restrict_open U N q
    exact (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U q) (L v) (L w)) hdf).trans
      (hmetric q v w)
  have hnormal : ∀ a : ℂ, G S (D a) = 0 := by
    intro a
    have h1raw := secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hU hmetric' z (1 : ℂ) (1 : ℂ) a
    have hIraw := secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hU hmetric' z Complex.I Complex.I a
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) z : ℂ →L[ℝ] E) = D :=
      DifferentialGeometry.mfderiv_restrict_open U N z
    have h1 : G (Q (1 : ℂ) (1 : ℂ)) (D a) = 0 := by
      have h := congrArg (fun L : ℂ →L[ℝ] E => G (Q (1 : ℂ) (1 : ℂ)) (L a)) hdf
      exact h.symm.trans h1raw
    have hI : G (Q Complex.I Complex.I) (D a) = 0 := by
      have h := congrArg (fun L : ℂ →L[ℝ] E => G (Q Complex.I Complex.I) (L a)) hdf
      exact h.symm.trans hIraw
    simp only [S, map_add, _root_.add_apply, h1, hI, add_zero]
  let C1 : E := diskMapCovariantPartial g U z 1 1
  let CI : E := diskMapCovariantPartial g U z Complex.I Complex.I
  have hτ : C1 + CI = 0 := htension
  have hp1 : G S (Q (1 : ℂ) (1 : ℂ)) = G S C1 :=
    inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial N gN g U hU z S hnormal 1
  have hpI : G S (Q Complex.I Complex.I) = G S CI :=
    inner_secondFundamentalForm_disk_diagonal_eq_covariantPartial N gN g U hU z S hnormal Complex.I
  have hpair : G S S = 0 := by
    change G S (Q (1 : ℂ) (1 : ℂ) + Q Complex.I Complex.I) = 0
    rw [map_add, hp1, hpI, ← map_add, hτ, map_zero]
  change S = 0
  by_contra hS
  exact (ne_of_gt (g.pos (U z) S hS)) hpair

/-- Conformality converts the zero coordinate trace into a zero trace in an
orthonormal basis for the actual induced metric. -/
theorem exists_orthonormal_secondFundamentalForm_trace_eq_zero_of_disk_tension
    (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) = gN.inner z v w)
    (z : N) (hconf : DiskMapConformalAt g U z)
    (htension : diskMapTension g U z = 0) :
    ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z),
      (∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0) ∧
      ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (fun q : N => U q) z (b i) (b i) = 0 := by
  classical
  let coeff := diskMapConformalCoefficient g U z
  have h11 : gN.inner z (1 : ℂ) (1 : ℂ) = coeff := (hmetric z (1 : ℂ) (1 : ℂ)).symm
  have hcoeff : 0 < coeff := h11 ▸ gN.pos z (1 : ℂ) (show (1 : ℂ) ≠ 0 from one_ne_zero)
  let s : ℝ := (Real.sqrt coeff)⁻¹
  have hsqrt : Real.sqrt coeff ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hcoeff)
  have hs : s ≠ 0 := inv_ne_zero hsqrt
  have hscale : s * s * coeff = 1 := by
    dsimp only [s]
    field_simp [hsqrt]
    nlinarith only [Real.sq_sqrt hcoeff.le]
  let b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z) :=
    Complex.basisOneI.unitsSMul (fun _ => Units.mk0 s hs)
  have hb0 : (b 0 : ℂ) = s • (1 : ℂ) := by
    change (Complex.basisOneI.unitsSMul (fun _ => Units.mk0 s hs)) _ = _
    rw [Module.Basis.unitsSMul_apply]
    change s • (Complex.basisOneI _) = _
    rw [Complex.coe_basisOneI]
    rfl
  have hb1 : (b 1 : ℂ) = s • Complex.I := by
    change (Complex.basisOneI.unitsSMul (fun _ => Units.mk0 s hs)) _ = _
    rw [Module.Basis.unitsSMul_apply]
    change s • (Complex.basisOneI _) = _
    rw [Complex.coe_basisOneI]
    rfl
  have h1I : gN.inner z (1 : ℂ) Complex.I = 0 := by
    rw [← hmetric]
    exact hconf.1
  have hI1 : gN.inner z Complex.I (1 : ℂ) = 0 := by
    exact (gN.symm z Complex.I (1 : ℂ)).trans h1I
  have hII : gN.inner z Complex.I Complex.I = coeff := by
    calc
      _ = g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) :=
        (hmetric z Complex.I Complex.I).symm
      _ = coeff := hconf.2.symm
  let G : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := gN.inner z
  let II : ℂ →L[ℝ] ℂ →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  have hG11 : G (1 : ℂ) (1 : ℂ) = coeff := h11
  have hG1I : G (1 : ℂ) Complex.I = 0 := h1I
  have hGI1 : G Complex.I (1 : ℂ) = 0 := hI1
  have hGII : G Complex.I Complex.I = coeff := hII
  let bC : Module.Basis (Fin 2) ℝ ℂ := b
  have hbC0 : bC 0 = s • (1 : ℂ) := hb0
  have hbC1 : bC 1 = s • Complex.I := hb1
  have h00 : G (bC 0) (bC 0) = 1 := by
    simp only [hbC0, map_smul, _root_.smul_apply, smul_eq_mul, hG11]
    nlinarith only [hscale]
  have h01 : G (bC 0) (bC 1) = 0 := by
    simp only [hbC0, hbC1, map_smul, _root_.smul_apply, smul_eq_mul, hG1I, mul_zero]
  have h10 : G (bC 1) (bC 0) = 0 := by
    simp only [hbC1, hbC0, map_smul, _root_.smul_apply, smul_eq_mul, hGI1, mul_zero]
  have h11' : G (bC 1) (bC 1) = 1 := by
    simp only [hbC1, map_smul, _root_.smul_apply, smul_eq_mul, hGII]
    nlinarith only [hscale]
  refine ⟨b, ?_, ?_⟩
  · intro i j
    change G (bC i) (bC j) = if i = j then 1 else 0
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11'
  · have hzero : II (1 : ℂ) (1 : ℂ) + II Complex.I Complex.I = 0 :=
      secondFundamentalForm_disk_coordinate_trace_eq_zero_of_tension_eq_zero
        N gN g U hU hmetric z htension
    change (∑ i : Fin 2, II (b i : ℂ) (b i : ℂ)) = 0
    simp only [Fin.sum_univ_two, hb0, hb1, map_smul, _root_.smul_apply,
      ← smul_add, hzero, smul_zero]

end DifferentialGeometry.Geometry
