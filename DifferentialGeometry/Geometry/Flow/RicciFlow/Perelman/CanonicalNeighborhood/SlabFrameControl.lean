import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame
import DifferentialGeometry.Geometry.Metric.Family.Basic

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]

theorem exists_local_uniform_frame_comparison
    {J : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : tensor0SFamilyContinuousOnSet (I := I) 2 J
      (fun t => metricTensorField (I := I) (g t)))
    (t₀ : J) (x : M) :
    let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
    ∃ basisE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E,
      ∃ W : Set (J × ↥e₀.baseSet), IsOpen W ∧
        (t₀, ⟨x, mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x⟩) ∈ W ∧
        ∀ q ∈ W, ∀ (r : ℕ) (A : Tensor0SSpace r I (q.2 : M)),
          (∑ k : Fin r → Fin (Module.finrank ℝ E),
            component0S (I := I)
              ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt q.2.property) A k ^ 2) ≤
            2 ^ r * normSq0S (I := I) (g q.1) q.2 r A := by
  classical
  dsimp only
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
  let P := J × ↥e₀.baseSet
  let q₀ : P := (t₀, ⟨x, mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x⟩)
  obtain ⟨basisE, hON⟩ := exists_trivONBasis (I := I) (g t₀) x
  let G : P → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => gramE (I := I) e₀ (g q.1) basisE q.2
  have ht : Continuous (fun q : P => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun q : P => (q.2 : M)) :=
    continuous_subtype_val.comp continuous_snd
  have hv (i : Fin (Module.finrank ℝ E)) :
      Continuous (fun q : P => TotalSpace.mk' E (E := TangentSpace I)
        (q.2 : M) (e₀.localFrame basisE i q.2)) :=
    (frame_e_mdiffOn (I := I) e₀ basisE i).continuousOn.comp_continuous hx
      (fun q => q.2.property)
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hev := hg.eval_continuous ht (fun q : P => q.1.property) hx
      (v := fun k q => e₀.localFrame basisE (![i, j] k) q.2)
      (fun k => hv (![i, j] k))
    exact hev.congr fun q => metricTensorField_apply (I := I) (g q.1) q.2
      (fun k => e₀.localFrame basisE (![i, j] k) q.2)
  have hG0 : G q₀ = 1 := gramE_eq_one (I := I) e₀ (g t₀) basisE hON
  have hinvc : ContinuousAt Inv.inv (G q₀) := by
    apply continuousAt_matrix_inv
    rw [hG0, Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hGi : ContinuousAt (fun q : P => (G q)⁻¹) q₀ := hinvc.comp hG.continuousAt
  have hi0 : (G q₀)⁻¹ = 1 := by
    rw [hG0]
    exact Matrix.inv_eq_left_inv (by rw [one_mul])
  let n := Fintype.card (Fin (Module.finrank ℝ E))
  let eps : ℝ := 1 / (2 * ((n : ℝ) + 1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hsmall : (n : ℝ) * eps ≤ 1 / 2 := by
    dsimp [eps]
    rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hev : ∀ᶠ q in 𝓝 q₀, ∀ i j : Fin (Module.finrank ℝ E),
      |(G q)⁻¹ i j - (if i = j then 1 else 0)| ≤ eps := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun q : P => (G q)⁻¹ i j) q₀ :=
      (continuousAt_pi.mp ((continuousAt_pi.mp hGi) i)) j
    have hb : ∀ᶠ z in 𝓝 ((G q₀)⁻¹ i j), |z - (if i = j then 1 else 0)| ≤ eps := by
      rw [hi0, Matrix.one_apply]
      refine Filter.eventually_of_mem
        (Metric.closedBall_mem_nhds (x := if i = j then (1 : ℝ) else 0) heps) fun z hz => ?_
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hz
    exact hc.eventually hb
  obtain ⟨W, hWsub, hWopen, hqW⟩ := mem_nhds_iff.mp hev
  refine ⟨basisE, W, hWopen, hqW, ?_⟩
  intro q hq r A
  have hQlb := Matrix.quad_lb_of_near_id
    (fun i j => (G q)⁻¹ i j) eps heps.le
    (hWsub hq) hsmall
  have hkey := sum_comp_sq_le_pow_normSq0S (I := I) (g q.1) q.2 r
    ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt q.2.property)
    (fun i j => (G q)⁻¹ i j) 2 two_pos
    (gramInv_inverse (I := I) e₀ (g q.1) basisE q.2.property)
    (fun i j => gramInv_symm (I := I) e₀ (g q.1) basisE q.2 i j) hQlb A
  simpa only [component0S_apply, tensor0SComponent_apply] using hkey

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
