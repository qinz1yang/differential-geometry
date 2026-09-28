import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalSign
import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalExtension
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_signed_supported_collar_extension
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, A (p, 0) = (η p, 0))
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ r : ℝ, 0 < r ∧ ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → (q.1, σ * q.2) ∈ A.source ∧ F q = A (q.1, σ * q.2)) ∧
        (∀ p : S2, F (p, 0) = (η p, 0)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioo l u ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨σ, hσ, hpos⟩ := exists_constant_axial_sign A hsource (fun p => congrArg Prod.snd (hzero p))
  have hσne : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  let D : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => 0) (fun _ => σ)
      contMDiff_const contMDiff_const (fun _ => hσne)
  let B := D.toPartialDiffeomorph.trans A
  have hBs (p : S2) : (p, (0 : ℝ)) ∈ B.source := by
    refine ⟨mem_univ _, ?_⟩
    change (p, 0 + σ * 0) ∈ A.source
    simpa only [mul_zero, add_zero] using hsource p
  have hB0 (p : S2) : B (p, 0) = (η p, 0) := by
    change A (p, 0 + σ * 0) = _
    simpa only [mul_zero, add_zero] using hzero p
  have hBp (p : S2) : 0 < deriv (fun t => (B (p, t)).2) 0 := by
    have hf : DifferentiableAt ℝ (fun t => (A (p, t)).2) 0 := by
      have hm := (A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds (hsource p))).comp 0
        (contMDiffAt_const.prodMk contMDiffAt_id)
      exact (contMDiff_snd.contMDiffAt.comp 0 hm).contDiffAt.differentiableAt (by simp)
    have heq : (fun t => (B (p, t)).2) = (fun t => (A (p, σ * t)).2) := by
      funext t
      change (A (p, 0 + σ * t)).2 = _
      rw [zero_add]
    rw [heq]
    have hσ0 : σ * (id (0 : ℝ)) = 0 := by simp
    have hd : HasDerivAt (fun t => (A (p, t)).2)
        (deriv (fun t => (A (p, t)).2) 0) (σ * id (0 : ℝ)) := hσ0.symm ▸ hf.hasDerivAt
    have hh := hd.comp 0 ((hasDerivAt_id 0).const_mul σ)
    have hcomp : (fun t => (A (p, σ * t)).2) = (fun t => (A (p, t)).2) ∘ (fun t => σ * t) := rfl
    rw [hcomp, hh.deriv]
    simpa only [mul_one, mul_comm] using hpos p
  obtain ⟨r, hr, F, hF, hFzero, _, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_collar_extension_of_positive_axial_derivative B η hη hBs hB0 hBp l u hl hu
  refine ⟨σ, hσ, r, hr, F, ?_, hFzero, K, hK, hKU, hfix, hfixi⟩
  intro q hq
  have hh := hF q hq
  change (q ∈ univ ∧ (q.1, 0 + σ * q.2) ∈ A.source) ∧ F q = A (q.1, 0 + σ * q.2) at hh
  rw [zero_add] at hh
  exact ⟨hh.1.2, hh.2⟩

theorem exists_signed_supported_compact_collar_extension
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    {r R l u : ℝ} (hr : 0 < r) (hrR : r < R) (hlR : l < -R) (hRu : R < u)
    (hsource : univ ×ˢ Icc (-R) R ⊆ A.source)
    (hzero : ∀ p : S2, A (p,0) = (η p,0))
    (himage : A '' (univ ×ˢ Icc (-R) R) ⊆ univ ×ˢ Ioo l u) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F q = A (q.1,σ * q.2)) ∧
        (∀ p : S2, F (p,0) = (η p,0)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioo l u ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  have hR : 0 < R := hr.trans hrR
  have hz (p : S2) : (p,(0 : ℝ)) ∈ A.source :=
    hsource ⟨mem_univ _,by constructor <;> linarith⟩
  obtain ⟨σ,hσ,ε,hε,G,hG,hGzero,K₀,hK₀,hK₀band,hGfix,_⟩ :=
    exists_signed_supported_collar_extension A η hη hz hzero l u (by linarith) (by linarith)
  have hσne : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  let D : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => 0) (fun _ => σ)
      contMDiff_const contMDiff_const (fun _ => hσne)
  let B := D.toPartialDiffeomorph.trans A
  have hDq (q : SphereCylinder) : D q = (q.1,σ * q.2) := by
    change (q.1,0 + σ * q.2) = _
    rw [zero_add]
  have hDband : MapsTo D (univ ×ˢ Icc (-R) R) (univ ×ˢ Icc (-R) R) := by
    intro q hq
    rw [hDq]
    refine ⟨mem_univ _,?_⟩
    rcases hσ with h | h
    · simpa only [h,one_mul] using hq.2
    · rw [h,neg_one_mul]
      exact ⟨neg_le_neg hq.2.2,by simpa only [neg_neg] using neg_le_neg hq.2.1⟩
  have hBs : univ ×ˢ Icc (-R) R ⊆ B.source :=
    fun q hq => ⟨mem_univ _,hsource (hDband hq)⟩
  have hBi : B '' (univ ×ˢ Icc (-R) R) ⊆ univ ×ˢ Ioo l u := by
    rintro q ⟨z,hz,rfl⟩
    exact himage ⟨D z,hDband hz,rfl⟩
  have hGB (q : SphereCylinder) (hq : |q.2| < ε) : G q = B q := by
    change G q = A (D q)
    rw [hDq]
    exact (hG q hq.le).2
  obtain ⟨F,hF,K,hK,hKU,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_compact_cylinder_collar_of_germ B hr hrR hε hBs G hGB
      (univ ×ˢ Ioo l u) (fun q hq => ⟨mem_univ _,hlR.trans_le hq.2.1,hq.2.2.trans_lt hRu⟩)
      hBi K₀ hK₀ hK₀band hGfix
  have hFexact (q : SphereCylinder) (hq : |q.2| ≤ r) : F q = A (q.1,σ * q.2) := by
    rw [hF q hq]
    exact congrArg A (hDq q)
  refine ⟨σ,hσ,F,hFexact,?_,K,hK,hKU,hfix,hfixi⟩
  intro p
  rw [hFexact (p,0) (by simpa using hr.le),mul_zero,hzero]


end DifferentialGeometry.Topology.Manifold
