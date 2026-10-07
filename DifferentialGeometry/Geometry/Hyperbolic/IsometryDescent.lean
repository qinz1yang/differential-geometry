import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Homotopy
import DifferentialGeometry.Geometry.Metric.Isometry.Descent
import DifferentialGeometry.Topology.Homotopy.OrbitQuotient

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  {Γ Λ : Type*} [Group Γ] [Group Λ]
  [MulAction Γ (Hyperboloid E)] [MulAction Λ (Hyperboloid E')]
  [IsIsometricSMul Λ (Hyperboloid E')]
  {M N : Type*} [PseudoMetricSpace M] [PseudoMetricSpace N]

theorem exists_isometryEquiv_homotopic_of_equivariant_isometry
    (φ : Γ → Λ) (hφ : Function.Surjective φ) (e : Hyperboloid E ≃ᵢ Hyperboloid E')
    (he : ∀ γ x, e (γ • x) = φ γ • e x)
    (p : MulAction.orbitRel.Quotient Γ (Hyperboloid E) ≃ₜ M)
    (q : MulAction.orbitRel.Quotient Λ (Hyperboloid E') ≃ₜ N)
    (hpball : ∀ (x : Hyperboloid E) (r : ℝ), 0 < r →
      (fun y => p (Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E)) y)) '' Metric.ball x r =
        Metric.ball (p (Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E)) x)) r)
    (hqball : ∀ (x : Hyperboloid E') (r : ℝ), 0 < r →
      (fun y => q (Quotient.mk (MulAction.orbitRel Λ (Hyperboloid E')) y)) '' Metric.ball x r =
        Metric.ball (q (Quotient.mk (MulAction.orbitRel Λ (Hyperboloid E')) x)) r)
    (F : C(Hyperboloid E, Hyperboloid E'))
    (hF : ∀ γ x, F (γ • x) = φ γ • F x) (u : C(M, N))
    (hu : ∀ x, q (Quotient.mk (MulAction.orbitRel Λ (Hyperboloid E')) (F x)) =
      u (p (Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E)) x))) :
    ∃ i : M ≃ᵢ N,
      (∀ x, i (p (Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E)) x)) =
        q (Quotient.mk (MulAction.orbitRel Λ (Hyperboloid E')) (e x))) ∧
      u.Homotopic (i : C(M, N)) := by
  let π : Hyperboloid E → MulAction.orbitRel.Quotient Γ (Hyperboloid E) :=
    Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E))
  let π' : Hyperboloid E' → MulAction.orbitRel.Quotient Λ (Hyperboloid E') :=
    Quotient.mk (MulAction.orbitRel Λ (Hyperboloid E'))
  let P : Hyperboloid E → M := p ∘ π
  let Q : Hyperboloid E' → N := q ∘ π'
  let d := e.toHomeomorph.orbitQuotient φ hφ he
  let j : M ≃ₜ N := p.symm.trans (d.trans q)
  have hcomm (x : Hyperboloid E) : Q (e x) = j (P x) := by
    change q (π' (e x)) = q (d (p.symm (p (π x))))
    rw [p.symm_apply_apply]
    rfl
  have hP : Function.Surjective P := by
    intro x
    obtain ⟨y, hy⟩ := Quotient.mk_surjective (p.symm x)
    refine ⟨y, ?_⟩
    change p (Quotient.mk (MulAction.orbitRel Γ (Hyperboloid E)) y) = x
    rw [hy, p.apply_symm_apply]
  have hj : Isometry j := e.isometry_of_image_ball P Q hP hpball hqball j j.injective hcomm
  let i : M ≃ᵢ N := { j.toEquiv with isometry_toFun := hj }
  refine ⟨i, fun x => (hcomm x).symm, ?_⟩
  let Fc : C(MulAction.orbitRel.Quotient Γ (Hyperboloid E),
      MulAction.orbitRel.Quotient Λ (Hyperboloid E')) := F.orbitQuotientMap φ hF
  let Ec : C(MulAction.orbitRel.Quotient Γ (Hyperboloid E),
      MulAction.orbitRel.Quotient Λ (Hyperboloid E')) :=
    (e : C(Hyperboloid E, Hyperboloid E')).orbitQuotientMap φ he
  have hFE : Fc.Homotopic Ec :=
    ⟨(interpolationHomotopy F e).orbitQuotient φ
      (interpolationHomotopy_equivariant F e φ hF he)⟩
  let qc : C(MulAction.orbitRel.Quotient Λ (Hyperboloid E'), N) := ⟨q, q.continuous⟩
  let pc : C(M, MulAction.orbitRel.Quotient Γ (Hyperboloid E)) := ⟨p.symm, p.symm.continuous⟩
  have hu' : qc.comp (Fc.comp pc) = u := by
    ext x
    obtain ⟨y, hy⟩ := hP x
    rw [← hy]
    change q (Fc (p.symm (p (π y)))) = u (P y)
    rw [p.symm_apply_apply]
    exact hu y
  have hi' : qc.comp (Ec.comp pc) = (i : C(M, N)) := by
    ext x
    rfl
  have h := (ContinuousMap.Homotopic.refl qc).comp
    (hFE.comp (ContinuousMap.Homotopic.refl pc))
  rwa [hu', hi'] at h

end DifferentialGeometry.Hyperboloid
