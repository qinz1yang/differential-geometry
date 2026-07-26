import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalFrameField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra

/-!
# Fixed-family Parseval expansions: rough Laplacian trace and slot-`0` fibre pairing

For a closed smooth Riemannian manifold `(M, g)` and a fixed finite family of smooth global
tangent vector fields `V a` whose fibre values reproduce every tangent vector through the
metric (`∑ a, ⟨V a x, u⟩_g • V a x = u`, a *Parseval frame family*,
`exists_smooth_parseval_frame_family`), this file re-expresses two moving-orthonormal-frame
traces as sums over the fixed family:

* `rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum` — the rough (connection)
  Laplacian of a smooth compactly-supported `(0, k)`-tensor is the fixed-family trace of its
  second covariant derivative,
  `Δ_∇T (x) = ∑ a, ∇²_{V a, V a} T (x)`.
  The moving `g_x`-orthonormal frame in the definition of `rawTensorConnLap` is converted to
  the fixed family through the bundled bilinear second-covariant-derivative read
  `rawTensorConnLap_psi_bilinAt` (value-tensoriality in both direction slots) and the bilinear
  trace conversion `parseval_family_sum_bilin_eq`.

* `tensorInnerPointwise_succ_eq_parseval_sum_slot0` — the intrinsic `(0, s+1)`-tensor fibre
  inner product splits over the fixed family in the leading covariant slot,
  `⟨A, B⟩_{s+1}(x) = ∑ a, ⟨A(V a x, ·), B(V a x, ·)⟩_s(x)`,
  the slot-`0` reads being the `tensor0SAsRS`-wrapped bare curries of the unit-section
  evaluations. This is the fixed-family form of the existential-frame decomposition
  `tensorInnerPointwise_succ_eq_sum_slot0Curry`: the `g_x`-orthonormal split
  (`tensorInnerPointwise_eq_sum_componentS_mul`, `fiberNormSqComponent_slot0Curry`) is
  converted to the family by `parseval_family_sum_bilin_eq` applied to the bilinear map
  `(u, v) ↦ ⟨A(u, ·), B(v, ·)⟩_s(x)`.

Both identities remove the moving-centre obstruction from integrated Bochner–Weitzenböck
telescoping: every direction that appears is a fixed smooth global field, on which the
per-direction covariant integration-by-parts engines apply directly.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
private local instance : Module.Finite ℝ E := inferInstance

set_option linter.unusedSectionVars false in
/-- **Fixed-family Parseval representation of the rough Laplacian.** For a fixed family of
smooth tangent vector fields `V a` whose fibre values reproduce every tangent vector through
the metric, the rough (connection) Laplacian of a smooth compactly-supported `(0, k)`-tensor
is the fixed-family trace of its second covariant derivative:
$$
  \Delta_\nabla T (x) = \sum_a \nabla^2_{V_a, V_a} T (x).
$$
The moving `g_x`-orthonormal frame trace (`rawTensorConnLap_eq_frame_trace`) is converted to
the fixed family by the bilinear trace conversion `parseval_family_sum_bilin_eq` applied to
the bundled bilinear second-covariant-derivative read `rawTensorConnLap_psi_bilinAt`, whose
values at the fibre vectors of smooth fields are the genuine second covariant derivatives
(`rawTensorConnLap_psi_bilinAt_apply`). -/
theorem rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum
    (g : SmoothRiemannianMetric I M) {N : ℕ}
    (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (k : ℕ) (T : SmoothCcTensor g 0 k) (x : M) :
    rawTensorConnLap (I := I) g 0 k (fun z : M => T.toSection z) x =
      ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 k (V a) (V a)
        (fun y : M => T.toSection y) x := by
  classical
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun j => smoothOrthoFrame (I := I) g x j x
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set Ψ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace 0 k I x :=
    rawTensorConnLap_psi_bilinAt (I := I) g 0 k (fun z : M => T.toSection z) hT x with hΨ
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 k I x :=
    LinearMap.mk₂ ℝ (fun u v => Ψ u v)
      (fun u u' v => by beta_reduce; rw [map_add, ContinuousLinearMap.add_apply])
      (fun c u v => by beta_reduce; rw [map_smul, ContinuousLinearMap.smul_apply])
      (fun u v v' => by beta_reduce; rw [map_add])
      (fun c u v => by beta_reduce; rw [map_smul])
  have hframe := rawTensorConnLap_eq_frame_trace (I := I) g 0 k
    (fun z : M => T.toSection z) hT x e horth
  have hpars := parseval_family_sum_bilin_eq (I := I) (M := M) g x
    (fun a : Fin N => V a x) (hPar x) e horth B
  have hBval : ∀ u v : TangentSpace I x, B u v = Ψ u v := fun u v => rfl
  have hψa : ∀ a : Fin N, Ψ (V a x) (V a x) =
      tensorSecondCovDeriv (I := I) g 0 k (V a) (V a)
        (fun y : M => T.toSection y) x := by
    intro a
    have hVa_at := ((hV a) x).mdifferentiableAt (by simp)
    have happly := rawTensorConnLap_psi_bilinAt_apply (I := I) g 0 k
      (fun z : M => T.toSection z) hT (X := V a) (Y := V a) hVa_at hVa_at
    rw [hΨ, happly, tensorSecondCovDeriv_def]
  calc rawTensorConnLap (I := I) g 0 k (fun z : M => T.toSection z) x
      = ∑ i : Fin (Module.finrank ℝ E), Ψ (e i) (e i) := hframe
    _ = ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) :=
        Finset.sum_congr rfl (fun i _ => (hBval (e i) (e i)).symm)
    _ = ∑ a : Fin N, B (V a x) (V a x) := hpars.symm
    _ = ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 k (V a) (V a)
        (fun y : M => T.toSection y) x := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hBval (V a x) (V a x), hψa a]

set_option linter.unusedSectionVars false in
/-- Two `(0, s)`-tensor fibre elements agreeing on every model tuple are equal. -/
private lemma tensor0S_eq_of_toModel_eq {s : ℕ} {x : M} {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' :=
  Tensor0SSpace.toModel_injective (ContinuousMultilinearMap.ext h)

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper `tensor0SAsRS` is additive. -/
private lemma tensor0SAsRS_add (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C + D) =
      tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D := by
  have h : (tensor0SAsRS (I := I) (M := M) x (C + D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
        (tensor0SAsRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C + D) =
      tensor00Scalar (I := I) (M := M) x τ • C + tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.add_apply,
      smul_eq_mul]
    ring
  exact h

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper `tensor0SAsRS` is `ℝ`-homogeneous. -/
private lemma tensor0SAsRS_smul (t : ℕ) (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (c • C) =
      c • tensor0SAsRS (I := I) (M := M) x C := by
  have h : (tensor0SAsRS (I := I) (M := M) x (c • C) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      c • (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (c • C) =
      c • (tensor00Scalar (I := I) (M := M) x τ • C)
    rw [smul_comm]
  exact h

set_option linter.unusedSectionVars false in
/-- **Slot-`0` fixed-family Parseval expansion of the `(0, s+1)` fibre pairing.** For a fixed
family of tangent fields whose fibre values at `x` reproduce every tangent vector through the
metric, the intrinsic `(0, s+1)`-tensor fibre inner product splits over the family in the
leading covariant slot:
$$
  \langle A, B\rangle_{s+1}(x) = \sum_a \langle A(V_a x, \cdot), B(V_a x, \cdot)\rangle_s(x),
$$
the slot-`0` reads being the `tensor0SAsRS`-wrapped bare curries of the unit-section
evaluations. This is the fixed-family companion of the existential-orthonormal-frame
decomposition `tensorInnerPointwise_succ_eq_sum_slot0Curry`: the orthonormal slot-`0` split
(`tensorInnerPointwise_eq_sum_componentS_mul` with the leading index split by `Fin.consEquiv`
and identified per-component by `fiberNormSqComponent_slot0Curry`) is converted to the family
by `parseval_family_sum_bilin_eq` applied to the slot-`0`-read bilinear map
`(u, v) ↦ ⟨A(u, ·), B(v, ·)⟩_s(x)`. -/
theorem tensorInnerPointwise_succ_eq_parseval_sum_slot0
    (g : SmoothRiemannianMetric I M) {N : ℕ}
    (V : Fin N → Π b : M, TangentSpace I b)
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (s : ℕ) (x : M) (A B : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ a : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
                (unitZeroSec (I := I) (M := M) x))) (V a x))))
          (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
                (unitZeroSec (I := I) (M := M) x))) (V a x)))) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hsq, _hexp, _hrfns⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  have hn' : n = Module.finrank ℝ E := hn
  subst hn'
  set K₀ : Fin 0 → Fin (Module.finrank ℝ E) := fun j => j.elim0
  have hsplit0 : tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (slot0Curry (I := I) (M := M) g x s e K₀ A i))
          (TensorRSSpace.toModel (slot0Curry (I := I) (M := M) g x s e K₀ B i)) := by
    rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 (s + 1) x e bse rfl
      hbse horth A B]
    rw [Finset.sum_eq_single K₀]
    · rw [← Fintype.sum_equiv
            (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
            (fun pr : Fin (Module.finrank ℝ E) × (Fin s → Fin (Module.finrank ℝ E)) =>
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A
                  (Module.finrank ℝ E) e K₀ (Fin.cons pr.1 pr.2) *
                fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B
                  (Module.finrank ℝ E) e K₀ (Fin.cons pr.1 pr.2))
            (fun J : Fin (s + 1) → Fin (Module.finrank ℝ E) =>
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A
                  (Module.finrank ℝ E) e K₀ J *
                fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B
                  (Module.finrank ℝ E) e K₀ J)
            (fun pr => by simp [Fin.consEquiv])]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x e bse rfl hbse
        horth (slot0Curry (I := I) (M := M) g x s e K₀ A i)
        (slot0Curry (I := I) (M := M) g x s e K₀ B i)]
      rw [Finset.sum_eq_single K₀]
      · refine Finset.sum_congr rfl (fun J' _ => ?_)
        rw [fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ A i J',
          fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ B i J']
      · intro K _ hK
        exact absurd (Subsingleton.elim K K₀) hK
      · intro h; exact absurd (Finset.mem_univ K₀) h
    · intro K _ hK
      exact absurd (Subsingleton.elim K K₀) hK
    · intro h; exact absurd (Finset.mem_univ K₀) h
  set A₀ : Tensor0SSpace (s + 1) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
      (unitZeroSec (I := I) (M := M) x)
  set B₀ : Tensor0SSpace (s + 1) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
      (unitZeroSec (I := I) (M := M) x)
  have hsplit : tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x A₀) (e i))))
          (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x B₀) (e i)))) := by
    rw [hsplit0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ A i,
      slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ B i]
  set Bmap : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v =>
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x A₀) u)))
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x B₀) v))))
      (fun u u' v => by
        beta_reduce
        rw [map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A₀) u u',
          tensor0SAsRS_add, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left])
      (fun c u v => by
        beta_reduce
        rw [map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A₀) c u,
          tensor0SAsRS_smul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
          smul_eq_mul])
      (fun u v v' => by
        beta_reduce
        rw [map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) B₀) v v',
          tensor0SAsRS_add, TensorRSSpace.toModel_add, tensorInnerPointwise_add_right])
      (fun c u v => by
        beta_reduce
        rw [map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) B₀) c v,
          tensor0SAsRS_smul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right,
          smul_eq_mul])
  have hpars := parseval_family_sum_bilin_eq (I := I) (M := M) g x
    (fun a : Fin N => V a x) (hPar x) e horth Bmap
  have hBval : ∀ u v : TangentSpace I x, Bmap u v =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x A₀) u)))
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x B₀) v))) :=
    fun u v => rfl
  calc tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel A) (TensorRSSpace.toModel B)
      = ∑ i : Fin (Module.finrank ℝ E),
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x A₀) (e i))))
            (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x B₀) (e i)))) := hsplit
    _ = ∑ i : Fin (Module.finrank ℝ E), Bmap (e i) (e i) :=
        Finset.sum_congr rfl (fun i _ => (hBval (e i) (e i)).symm)
    _ = ∑ a : Fin N, Bmap (V a x) (V a x) := hpars.symm
    _ = ∑ a : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x A₀) (V a x))))
            (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x B₀) (V a x)))) :=
        Finset.sum_congr rfl (fun a _ => hBval (V a x) (V a x))

end Connection
end Integral
end DifferentialGeometry

end
