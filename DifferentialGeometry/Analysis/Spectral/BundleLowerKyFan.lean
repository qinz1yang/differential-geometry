import DifferentialGeometry.Analysis.Spectral.LowerKyFan
import DifferentialGeometry.Bundle.OrthonormalFrame
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section
open Bundle Filter Set
open scoped Topology InnerProductSpace BigOperators

private def matrixToCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap

private theorem continuous_matrixToCLM (n : ℕ) : Continuous (matrixToCLM n) :=
  (matrixToCLM n).continuous_of_finiteDimensional

private theorem continuousWithinAt_lowerKyFanSum
    {Z : Type*} [TopologicalSpace Z] {s : Set Z} {z : Z} {n k : ℕ}
    {A : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hA : ContinuousWithinAt A s z) (hsymm : ∀ y, (A y).IsSymmetric)
    (hk : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    ContinuousWithinAt (fun y => (hsymm y).lowerKyFanSum k) s z := by
  have hsub : ContinuousWithinAt (fun y =>
      (⟨A y, hsymm y⟩ : {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) //
        T.IsSymmetric})) s z := tendsto_subtype_rng.mpr hA
  exact (LinearMap.IsSymmetric.continuous_lowerKyFanSum k hk).continuousAt.comp_continuousWithinAt hsub

private theorem toEuclideanLin_toMatrix_repr
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {n : ℕ} (basis : OrthonormalBasis (Fin n) ℝ W) (A : W →ₗ[ℝ] W) (x : W) :
    Matrix.toEuclideanLin (LinearMap.toMatrix basis.toBasis basis.toBasis A)
      (basis.repr x) = basis.repr (A x) := by
  apply PiLp.ext
  intro i
  exact congrFun (LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis A x) i

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  [∀ x, FiniteDimensional ℝ (V x)]

theorem ContinuousWithinAt.lowerKyFanSum_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z} {z₀ : Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousWithinAt (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s z₀)
    (hsymm : ∀ z, (A z).IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ (V (b z₀))) :
    ContinuousWithinAt (fun z => (hsymm z).lowerKyFanSum k) s z₀ := by
  classical
  have hb : ContinuousWithinAt b s z₀ := by
    rw [continuousWithinAt_hom_bundle] at hA
    exact hA.1
  let n := Module.finrank ℝ (V (b z₀))
  let v := stdOrthonormalBasis ℝ (V (b z₀))
  obtain ⟨U, hU, hbU, e, heCont, he, -⟩ :=
    exists_continuous_orthonormal_sections (F := F) (b z₀) v v.orthonormal
  let C : Z → Matrix (Fin n) (Fin n) ℝ :=
    fun z i j => ⟪e i (b z), A z (e j (b z))⟫_ℝ
  let B : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun z => matrixToCLM n (C z)
  have hC : ContinuousWithinAt C s z₀ := by
    apply continuousWithinAt_pi.2
    intro i
    apply continuousWithinAt_pi.2
    intro j
    have hei := ((heCont i).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    have hej := ((heCont j).continuousAt (hU.mem_nhds hbU)).comp_continuousWithinAt hb
    exact hei.inner_bundle (hA.clm_bundle_apply hej)
  have hB : ContinuousWithinAt B s z₀ :=
    (continuous_matrixToCLM n).continuousAt.comp_continuousWithinAt hC
  have hBsymm : ∀ z, (B z).IsSymmetric := by
    intro z
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ext i j
    change ⟪e j (b z), A z (e i (b z))⟫_ℝ = ⟪e i (b z), A z (e j (b z))⟫_ℝ
    rw [real_inner_comm]
    exact hsymm z _ _
  have hkB : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hk
  have hspec : ContinuousWithinAt (fun z => (hBsymm z).lowerKyFanSum k) s z₀ :=
    continuousWithinAt_lowerKyFanSum hB hBsymm hkB
  have heq : ∀ z, b z ∈ U →
      (hsymm z).lowerKyFanSum k = (hBsymm z).lowerKyFanSum k := by
    intro z hz
    have hdim : Module.finrank ℝ (V (b z)) = n := by
      let ex := (trivializationAt F V (b z)).continuousLinearEquivAt ℝ (b z)
        (mem_baseSet_trivializationAt F V (b z))
      let ey := (trivializationAt F V (b z₀)).continuousLinearEquivAt ℝ (b z₀)
        (mem_baseSet_trivializationAt F V (b z₀))
      exact ex.toLinearEquiv.finrank_eq.trans ey.toLinearEquiv.finrank_eq.symm
    let basis : OrthonormalBasis (Fin n) ℝ (V (b z)) :=
      OrthonormalBasis.mk (he (b z) hz)
        ((he (b z) hz).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by simp only [Fintype.card_fin, hdim]; rfl)).ge
    have hmat : C z = LinearMap.toMatrix basis.toBasis basis.toBasis (A z).toLinearMap := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
      simp only [C, basis, OrthonormalBasis.coe_mk]
      rfl
    have hcomm : ∀ x, B z (basis.repr x) = basis.repr (A z x) := by
      intro x
      change Matrix.toEuclideanLin (C z) (basis.repr x) = basis.repr (A z x)
      rw [hmat]
      exact toEuclideanLin_toMatrix_repr basis (A z).toLinearMap x
    exact (hsymm z).lowerKyFanSum_eq_of_intertwining (hBsymm z) basis.repr hcomm
      (hk.trans_eq hdim.symm)
  apply hspec.congr_of_eventuallyEq
  · filter_upwards [hb.eventually (hU.mem_nhds hbU)] with z hz
    exact heq z hz
  · exact heq z₀ hbU

theorem ContinuousOn.lowerKyFanSum_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z}
    {A : ∀ z, V (b z) →L[ℝ] V (b z)}
    (hA : ContinuousOn (fun z =>
      (TotalSpace.mk' (F →L[ℝ] F) (b z) (A z) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) s)
    (hsymm : ∀ z, (A z).IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ F) :
    ContinuousOn (fun z => (hsymm z).lowerKyFanSum k) s := by
  intro z hz
  let e := (trivializationAt F V (b z)).continuousLinearEquivAt ℝ (b z)
    (mem_baseSet_trivializationAt F V (b z))
  exact (hA z hz).lowerKyFanSum_bundle hsymm
    (hk.trans_eq e.toLinearEquiv.finrank_eq.symm)

end
