import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornBaseCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFirstScalarLevel
import Mathlib.Data.Finset.Lattice.Fold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornScalarLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCollarMatching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InwardDatumChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatumOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricEventDebit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import DifferentialGeometry.Geometry.Neck.ScalarCutReindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornParameterRescaling

open private scalar_le_on_retainedCore_of_truncated_bound from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFirstScalarLevel

open private exists_fin_chosen_data exists_precision_order_compatible
  precision_order_compatible_of_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMetricEvent


set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_common_deep_coordinates_after_rescaling
    {δ : ℝ} (k : ∀ c, P.hornIndex c → ℕ)
    (N : ∀ c e, NormalizedNeck D.terminal.metric δ (k c e))
    (Θ : ∀ c, P.hornIndex c → neckCentralOpen δ → positiveHornDomain)
    (hΘ : ∀ c e, IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (Θ c e))
    (hmap : ∀ c e q, P.horn c e (Θ c e q).val =
      (N c e).chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q))
    (height : ∀ c, P.hornIndex c → ℝ) (hheight : ∀ c e, 0 < height c e)
    (hbound : ∀ c e q, height c e ≤ (Θ c e q).val.2) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
      (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
      (lambda : ℝ) (hlambda : 0 < lambda),
      let P' := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
      ∃ F : ∀ c, P.hornIndex c → neckCentralOpen δ → positiveHornDomain,
        (∀ c e, IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (F c e)) ∧
        (∀ c e q, P'.horn c e (F c e q).val =
          (N c e).chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q)) ∧
        ∀ c e q, (P'.hornCollar c e).radius + R + 3 < (F c e q).val.2 := by
  classical
  let J := Σ c : P.component, P.hornIndex c.val
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  let : Fintype J := Fintype.ofFinite J
  have hex : ∃ m : ℝ, 0 < m ∧ ∀ c e, m ≤ height c e := by
    by_cases hne : (Finset.univ : Finset J).Nonempty
    · let m := Finset.univ.inf' hne (fun j : J => height j.1.val j.2)
      refine ⟨m,(Finset.lt_inf'_iff hne).mpr (fun j _ => hheight j.1.val j.2),?_⟩
      intro c e
      have hc : c ∈ P.component := by
        by_contra hnot
        exact (P.hornIndex_empty c hnot).false e
      exact Finset.inf'_le _ (Finset.mem_univ (⟨⟨c,hc⟩,e⟩ : J))
    · refine ⟨1,zero_lt_one,?_⟩
      intro c e
      have hc : c ∈ P.component := by
        by_contra hnot
        exact (P.hornIndex_empty c hnot).false e
      exact (hne ⟨⟨⟨c,hc⟩,e⟩,Finset.mem_univ _⟩).elim
  obtain ⟨m,hm,hmheight⟩ := hex
  let r := fun c (e : P.hornIndex c) => min (P.hornCollar c e).radius (m / 4)
  have hr : ∀ c e, 0 < r c e := fun c e =>
    lt_min (P.hornCollar c e).radius_pos (by positivity)
  have hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius := fun _ _ => min_le_left _ _
  let lambda := 4 * (R + 4) / m
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  let A : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => 0) (fun _ => lambda)
      contMDiff_const contMDiff_const (fun _ => ne_of_gt hlambda)
  let F := fun c (e : P.hornIndex c) (q : neckCentralOpen δ) =>
    (⟨A (Θ c e q).val,mem_univ _,by
      change 0 < 0 + lambda * (Θ c e q).val.2
      simpa only [zero_add] using mul_pos hlambda (Θ c e q).property.2⟩ : positiveHornDomain)
  have hF : ∀ c e, IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (F c e) := by
    intro c e
    apply isSmoothEmbedding_intoOpen NeckCylinderModel NeckCylinderModel positiveHornDomain
    change IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (A ∘ (Subtype.val : positiveHornDomain → NeckCylinder) ∘ Θ c e)
    exact IsSmoothEmbedding.comp
      (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding A)
      (isSmoothEmbedding_fromOpen NeckCylinderModel NeckCylinderModel positiveHornDomain
        (Θ c e) (hΘ c e)) (by simp)
  refine ⟨r,hr,hle,lambda,hlambda,F,hF,?_,?_⟩
  · intro c e q
    change P.horn c e ((Θ c e q).val.1, (0 + lambda * (Θ c e q).val.2) / lambda) = _
    rw [zero_add, mul_div_cancel_left₀ _ hlambda.ne']
    exact hmap c e q
  · intro c e q
    change lambda * r c e + R + 3 < 0 + lambda * (Θ c e q).val.2
    have hrm : r c e ≤ m / 4 := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left ((hmheight c e).trans (hbound c e q)) hlambda.le
    have hupper := mul_le_mul_of_nonneg_left hrm hlambda.le
    have heq : lambda * m = 4 * (R + 4) := by dsimp only [lambda]; field_simp
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_common_deep_coordinates_of_neck_family
    {β : ℝ} (hε : ε ≤ 1 / 8646) (hεβ : ε < β) (hβ1 : β < 1)
    {Q : ℝ} (hQ : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q)
    (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
    (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
    (hδε : ∀ c e, δ₀ c e ≤ ε)
    (hkN : ∀ c e, ⌊ε⁻¹⌋₊ + 1 ≤ k c e)
    (hcenter : ∀ c e, (N c e).center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))
    (hscale : ∀ c e, (N c e).scale = Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (hδ : ∀ c e, δ₀ c e ≤ β),
      ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
        (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
        (lambda : ℝ) (hlambda : 0 < lambda),
        let P' := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
        ∃ Θ : ∀ c, P.hornIndex c → neckCentralOpen β → positiveHornDomain,
          (∀ c e, IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ (Θ c e)) ∧
          (∀ c e q, P'.horn c e (Θ c e q).val =
            ((N c e).monoDelta (hδ c e) hβ1).chart
              (Opens.inclusion (neckCentralOpen_le_buffer β) q)) ∧
          ∀ c e q, (P'.hornCollar c e).radius + R + 3 < (Θ c e q).val.2 := by
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hδ : ∀ c e, δ₀ c e ≤ β := fun c e => (hδε c e).trans hεβ.le
  have hcoords (c) (e : P.hornIndex c) :
      ∃ Θ : neckCentralOpen β → positiveHornDomain,
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
        (∀ q, P.horn c e (Θ q).val =
          ((N c e).monoDelta (hδ c e) hβ1).chart
            (Opens.inclusion (neckCentralOpen_le_buffer β) q)) ∧
        ∃ m : ℝ, 0 < m ∧ ∀ q, m ≤ (Θ q).val.2 := by
    have hk : 2 ≤ k c e := by
      have hlarge : (1 : ℝ) ≤ ε⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ P.epsilon_pos).mpr (by linarith)
      have hi : 1 ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hlarge)
      have hh := hkN c e
      omega
    have hδε := hδε c e
    have hcenter := hcenter c e
    have hscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ₀ c e) * (N c e).scale := by
      rw [hscale c e]
      have hf : (1 / 2 : ℝ) ≤ 1 - 4323 * δ₀ c e := by linarith [hδε.trans hε]
      have hp : 0 < Q := by nlinarith
      nlinarith
    exact P.exists_neck_coordinates_with_positive_height_of_base_scalar_bound c e (N c e)
      hk ((hδε.trans hε).trans (by norm_num)) (hδ c e) hβ1
      ((inv_lt_inv₀ (P.epsilon_pos.trans hεβ) (N c e).delta_pos).mpr (hδε.trans_lt hεβ))
      hcenter hscale
  classical
  choose Θ hΘ hmap height hheight hbound using hcoords
  obtain ⟨r,hr,hle,lambda,hlambda,F,hF,hFmap,hFdepth⟩ :=
    exists_common_deep_coordinates_after_rescaling P k
      (fun c e => (N c e).monoDelta (hδ c e) hβ1) Θ hΘ hmap
      height hheight hbound R hR
  exact ⟨hδ,r,hr,hle,lambda,hlambda,F,hF,hFmap,hFdepth⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_common_scale_horn_matching_of_neck_family :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * ε)⁻¹ →
        ∀ {Q : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        ∀ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e)),
          (∀ c e, δ₀ c e ≤ ε) →
          (∀ c e, ⌊ε⁻¹⌋₊ + 1 ≤ k c e) →
          (∀ c e, (N c e).center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) →
          (∀ c e, (N c e).scale = Q) →
          ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * ε) (hε1 : 2 * ε < 1),
              ∀ c e, ∃ (a : ℝ) (β : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) (σ : ℝ),
                (Padapt.hornCollar c e).radius + δ⁻¹ < a ∧
                (β = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β = sphereAntipodalDiffeomorph (n := 2)) ∧ (σ = 1 ∨ σ = -1) ∧
                ∃ F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder,
                  (∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                    ∃ hq : (β q,σ*s) ∈ neckBuffer (2 * ε),
                      0 < (F (q,a+s)).2 ∧
                      Padapt.horn c e (F (q,a+s)) =
                        ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β q,σ*s),hq⟩) ∧
                  ∃ K : Set NeckCylinder, IsCompact K ∧
                    K ⊆ univ ×ˢ Ioi (Padapt.hornCollar c e).radius ∧
                    EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_horn_neck_collar_matching_of_deep_coordinates
  refine ⟨min (eta / 2) (1 / 17292),lt_min (by positivity) (by norm_num),?_⟩
  intro D ε Λ P hε δ hδ hfit Q hQ δ₀ k N hδε hkN hcenter hscale
  have hβeta : 2 * ε ≤ eta := by linarith [hε.trans (min_le_left _ _)]
  have hεsmall : ε ≤ 1 / 8646 := (hε.trans (min_le_right _ _)).trans (by norm_num)
  have hεβ : ε < 2 * ε := by linarith [P.epsilon_pos]
  have hβ1 : 2 * ε < 1 := by linarith [hε.trans (min_le_right _ _)]
  obtain ⟨hδ₀,r,hr,hle,lambda,hlambda,Θ,hΘ,hmap,hdepth⟩ :=
    P.exists_common_deep_coordinates_of_neck_family hεsmall hεβ hβ1 hQ δ₀ k N hδε hkN
      hcenter hscale δ⁻¹ (inv_nonneg.mpr hδ.le)
  let Padapt := TerminalCorePresentation.monoEpsilon
    ((P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda) hεβ.le
  refine ⟨r,hr,hle,lambda,hlambda,hδ₀,hβ1,?_⟩
  intro c e
  have hk : ⌈(2 * ε)⁻¹⌉₊ ≤ k c e := by
    have hi : (2 * ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ P.epsilon_pos hεβ.le
    exact (Nat.ceil_mono hi).trans ((Nat.ceil_le_floor_add_one ε⁻¹).trans (hkN c e))
  obtain ⟨a,ha,β,σ,hβ,hσ,F,hF,K,hK,hKr,hfix,hfixi⟩ :=
    hmatch Padapt hβeta c e ((N c e).monoDelta (hδ₀ c e) hβ1) le_rfl hk
      (Θ c e) (hΘ c e) (hmap c e) (ρ := (Padapt.hornCollar c e).radius)
      (Padapt.hornCollar c e).radius_pos.le hδ hfit (hdepth c e)
  exact ⟨a,β,σ,ha,hβ,hσ,F,hF,K,hK,hKr,hfix,hfixi⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology.Manifold

universe u

private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_reparametrized_horn_matching_of_neck_family :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * ε)⁻¹ →
        ∀ {Q : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        ∀ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e)),
          (∀ c e, δ₀ c e ≤ ε) →
          (∀ c e, ⌊ε⁻¹⌋₊ + 1 ≤ k c e) →
          (∀ c e, (N c e).center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) →
          (∀ c e, (N c e).scale = Q) →
          ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * ε) (hε1 : 2 * ε < 1)
              (a : ∀ c, P.hornIndex c → ℝ)
              (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
              (γ : ∀ c, P.hornIndex c → ℝ)
              (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (K : ∀ c, P.hornIndex c → Set NeckCylinder)
              (hK : ∀ c e, IsCompact (K c e))
              (hfix : ∀ c e q, q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
              (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
              let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
              ∀ c e, (Padapt.hornCollar c e).radius + δ⁻¹ < a c e ∧
                (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β c e = sphereAntipodalDiffeomorph (n := 2)) ∧
                (γ c e = 1 ∨ γ c e = -1) ∧
                (range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                  range (fun q : HalfNeckCylinder => Padapt.horn c e q.val)) ∧
                ∀ q : Sphere 2, ∀ s : ℝ, |s| ≤ δ⁻¹ →
                  ∃ hq : (β c e q, γ c e * s) ∈ neckBuffer (2 * ε),
                    P'.horn c e (q, a c e - s) =
                      ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β c e q,γ c e*s),hq⟩ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_common_scale_horn_matching_of_neck_family
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hδpos hfit Q hQ δ₀ k N hδε hk hcenter hscale
  obtain ⟨r,hr,hle,lambda,hlambda,hδ,hε1,hmatching⟩ :=
    hmatch P hε hδpos hfit hQ δ₀ k N hδε hk hcenter hscale
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  classical
  choose a β σ ha hβ hσ F hchart K hK hKρ hfix hfixi using hmatching
  let γ : ∀ c, P.hornIndex c → ℝ := fun c e => -(σ c e)
  have hfixed (c) (e : P.hornIndex c) (q : NeckCylinder)
      (hq : q.2 ≤ (Padapt.hornCollar c e).radius) : F c e q = q :=
    hfix c e (fun hqK => (not_lt_of_ge hq) (hKρ c e hqK).2)
  refine ⟨r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfixed,hfix,?_⟩
  dsimp only
  intro c e
  refine ⟨ha c e,hβ c e,?_,Padapt.reparametrizeHornsOfCompactSupport_range F hfixed K hK hfix c e,?_⟩
  · rcases hσ c e with h | h
    · exact Or.inr (congrArg Neg.neg h)
    · exact Or.inl (by dsimp only [γ]; rw [h]; norm_num)
  · intro q s hs
    obtain ⟨hq,hpos,heq⟩ := hchart c e q (-s) (by simpa only [abs_neg] using hs)
    have hsign : σ c e * (-s) = γ c e * s := by dsimp only [γ]; ring
    have hq' : (β c e q,γ c e * s) ∈ neckBuffer (2 * ε) := hsign ▸ hq
    refine ⟨hq',?_⟩
    change Padapt.horn c e (F c e (q,a c e-s)) = _
    have hsub : (⟨(β c e q,σ c e*(-s)),hq⟩ : neckBuffer (2 * ε)) =
        ⟨(β c e q,γ c e*s),hq'⟩ := Subtype.ext (Prod.ext rfl hsign)
    change Padapt.horn c e (F c e (q,a c e + -s)) = _ at heq
    simpa only [sub_eq_add_neg] using heq.trans
      (congrArg ((N c e).monoDelta (hδ c e) hε1).chart hsub)

private theorem exists_common_scale_reparametrized_horn_necks_of_base_bound :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * ε)⁻¹ →
        ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → ∀ y : Sphere 2,
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := ((P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda)
          ∃ (t δ₀ : ∀ c, Padapt.hornIndex c → ℝ) (k : ∀ c, Padapt.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (a : ∀ c, Padapt.hornIndex c → ℝ)
            (β : ∀ c, Padapt.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
            (γ : ∀ c, Padapt.hornIndex c → ℝ)
            (F : ∀ c, Padapt.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel,
              NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∀ c e, 0 < t c e ∧ (N c e).center = Padapt.horn c e (y,t c e) ∧
              (N c e).scale = Q ∧ δ₀ c e ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e ∧
              (Padapt.hornCollar c e).radius+δ⁻¹ < a c e ∧
              (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨ β c e = sphereAntipodalDiffeomorph
                (n := 2)) ∧
              (γ c e = 1 ∨ γ c e = -1) ∧
              (range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                range (fun q : HalfNeckCylinder => Padapt.horn c e q.val)) ∧
              ∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                ∃ hq : (β c e q,γ c e*s) ∈ neckBuffer (δ₀ c e),
                  P'.horn c e (q,a c e-s) = (N c e).chart ⟨(β c e q,γ c e*s),hq⟩ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_reparametrized_horn_matching_of_neck_family
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hδpos hfit Q hQ y
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  obtain ⟨t,δ₀,k,N,hN⟩ := P.exists_neck_family_scale_eq (Q := Q) y (by nlinarith)
  obtain ⟨r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfix,hF,hmatching⟩ :=
    hmatch P hε hδpos hfit hQ δ₀ k N
      (fun c e => (hN c e).2.2.2.1) (fun c e => (hN c e).2.2.2.2)
      (fun c e => by rw [(hN c e).2.1]; exact ⟨(y,t c e),⟨mem_univ _,(hN c e).1⟩,rfl⟩)
      (fun c e => (hN c e).2.2.1)
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let Nm := fun c e => (N c e).monoDelta (hδ c e) hε1
  refine ⟨r,hr,hle,lambda,hlambda,(fun c e => lambda * t c e),(fun _ _ => 2 * ε),k,
    Nm,a,β,γ,F,K,hK,hfix,hF,rfl,?_⟩
  intro c e
  have hcenter : (Nm c e).center = Padapt.horn c e (y,lambda * t c e) := by
    change (N c e).center = P.horn c e (y,(lambda * t c e) / lambda)
    rw [mul_div_cancel_left₀ _ hlambda.ne']
    exact (hN c e).2.1
  exact ⟨mul_pos hlambda (hN c e).1,hcenter,(hN c e).2.2.1,le_rfl,
    (hN c e).2.2.2.2,hmatching c e⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology.Manifold

universe u

private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)

private local instance {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ) :
    Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2+1) := ⟨by simp⟩

private theorem exists_oriented_horn_neck_data_of_matching
    {D : OneStepIncoming.{u}} {ε Λ δ δw : ℝ}
    (P : TerminalCorePresentation D ε Λ)
    (hδpos : 0 < δ) (hδ1 : δ < 1) (hδwi : δw⁻¹ = δ⁻¹ + 1)
    (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
    (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
    (hδ : ∀ c e, δ₀ c e ≤ δ)
    (a : ∀ c, P.hornIndex c → ℝ)
    (ha : ∀ c e, δ⁻¹ + 1 < a c e)
    (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
    (γ : ∀ c, P.hornIndex c → ℝ)
    (hγ : ∀ c e, γ c e = 1 ∨ γ c e = -1)
    (hmatch : ∀ c e (q : Sphere 2) (s : ℝ), |s| ≤ δw⁻¹ →
      ∃ hq : (β c e q, γ c e * s) ∈ neckBuffer (δ₀ c e),
        P.horn c e (q, a c e - s) = (N c e).chart ⟨(β c e q, γ c e * s), hq⟩) :
    ∃ (e : P.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (he : ∀ j, sphereDiffeo (n := 2) (e j) spherePoint =
        ((N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1).sphereMark)
      (side : P.HornCutIndex → Bool) (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2),
      let d := fun j => ((N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1).rotatedDatum (e j) (he j) (side j)
      (∀ j, LinearMap.det (e j).toLinearMap = 1) ∧
      (∀ j (q : bufferedCylinder δ),
        (d j).oriented.map q = P.horn j.1.val j.2 (ν j q.val.1,a j.1.val j.2-q.val.2)) ∧
      let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
      ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
        (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
        (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,side) ∈
          scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹ ↔ side = true) ∧
        MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
          (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius^2)⁻¹))
          D.slab.terminalRegularOpen := by
  classical
  let N' := fun j : P.HornCutIndex => (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
  choose side hside using fun j : P.HornCutIndex => NormalizedNeck.exists_side_of_axial_sign
    (γ j.1.val j.2) (sq_eq_one_iff.mpr (hγ j.1.val j.2))
  have hrotation (j : P.HornCutIndex) : ∃ e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace,
      LinearMap.det e.toLinearMap = 1 ∧ sphereDiffeo (n := 2) e spherePoint = (N' j).sphereMark := by
    obtain ⟨e,hdet,he,_⟩ := (N' j).exists_rotatedDatum (side j)
    exact ⟨e,hdet,he⟩
  choose e hdet he using hrotation
  let d := fun j : P.HornCutIndex => (N' j).rotatedDatum (e j) (he j) (side j)
  let ν := fun j : P.HornCutIndex =>
    ((sphereDiffeo (n := 2) (e j)).toEquiv.trans (β j.1.val j.2).toEquiv.symm)
  have hm (j : P.HornCutIndex) (q : bufferedCylinder δ) :
      (d j).oriented.map q = P.horn j.1.val j.2 (ν j q.val.1,a j.1.val j.2-q.val.2) := by
    have hwidth : |q.val.2| ≤ δw⁻¹ := by
      rw [hδwi]
      exact abs_le.mpr ⟨by linarith [q.property.1],q.property.2.le⟩
    obtain ⟨hmem,hmap⟩ := hmatch j.1.val j.2 (ν j q.val.1) q.val.2 hwidth
    rw [hmap,normalizedDatum.oriented_map,NormalizedNeck.rotatedDatum_map]
    change (N j.1.val j.2).chart _ = _
    apply congrArg (N j.1.val j.2).chart
    apply Subtype.ext
    change (bufferedCylinderRotation δ (e j)
      (bufferedCylinderOrientation δ (d j).retainedSign (d j).retainedSign_sq q)).val =
      (β j.1.val j.2 (ν j q.val.1),γ j.1.val j.2*q.val.2)
    rw [bufferedCylinderRotation_apply,bufferedCylinderOrientation_apply]
    have hs : (d j).retainedSign = γ j.1.val j.2 := hside j
    rw [hs]
    exact Prod.ext ((β j.1.val j.2).apply_symm_apply _).symm rfl
  refine ⟨e,he,side,ν,hdet,hm,?_⟩
  exact P.retained_oriented_neck_family_of_horn_matching hδpos hδ1 a ha _ _ d ν hm

private theorem exists_common_scale_oriented_horn_necks_of_base_bound :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : 2 * ε ≤ δ) (hδ1 : δ < 1), δ⁻¹+2 < (2 * ε)⁻¹ →
        ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → ∀ y : Sphere 2,
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
          ∃ (t δ₀ : ∀ c, Padapt.hornIndex c → ℝ) (k : ∀ c, Padapt.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (hδ : ∀ c e, δ₀ c e ≤ δ)
            (a : ∀ c, Padapt.hornIndex c → ℝ)
            (F : ∀ c, Padapt.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel,
              NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            let N' := fun j : P'.HornCutIndex => (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
            P'.core = Padapt.core ∧
            (∀ c e, 0 < t c e ∧ (N c e).center = Padapt.horn c e (y,t c e) ∧
              (N c e).scale = Q ∧ δ₀ c e ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e) ∧
            ∃ (e : P'.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
              (he : ∀ j, sphereDiffeo (n := 2) (e j) spherePoint = (N' j).sphereMark)
              (side : P'.HornCutIndex → Bool)
              (ν : P'.HornCutIndex → Sphere 2 ≃ Sphere 2),
              let d := fun j => (N' j).rotatedDatum (e j) (he j) (side j)
              (∀ j, LinearMap.det (e j).toLinearMap = 1) ∧
              (∀ c e, δ⁻¹+1 < a c e) ∧
              (∀ j (q : bufferedCylinder δ),
                (d j).oriented.map q = P'.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) ∧
              let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
              ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,side) ∈
                  scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                    (P'.coreRadius^2)⁻¹ ↔
                  side = true) ∧
                MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                  (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f
                    (P'.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  obtain ⟨eta,heta,hmatching⟩ := exists_common_scale_reparametrized_horn_necks_of_base_bound
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit Q hQ y
  have hδpos : 0 < δ := (mul_pos (by norm_num) P.epsilon_pos).trans_le hεδ
  let δw := (δ⁻¹+1)⁻¹
  have hδw : 0 < δw := inv_pos.mpr (by positivity)
  have hδwi : δw⁻¹ = δ⁻¹+1 := inv_inv _
  have hfitw : δw⁻¹+1 < (2 * ε)⁻¹ := by rw [hδwi]; linarith
  obtain ⟨r,hr,hle,lambda,hlambda,t,δ₀,k,N,a,β,γ,F,K,hK,hfix,hF,hcore,hdata⟩ :=
    hmatching P hε hδw hfitw Q hQ y
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let hδ : ∀ c e, δ₀ c e ≤ δ := fun c e => (hdata c e).2.2.2.1.trans hεδ
  have ham (c) (e : P'.hornIndex c) : δ⁻¹+1 < a c e := by
    have hh := (hdata c e).2.2.2.2.2.1
    rw [hδwi] at hh
    have hp := (Padapt.hornCollar c e).radius_pos
    linarith
  obtain ⟨e,he,side,ν,hdet,hm,hgeometry⟩ := exists_oriented_horn_neck_data_of_matching
    P' hδpos hδ1 hδwi δ₀ k N hδ a ham β γ
      (fun c e => (hdata c e).2.2.2.2.2.2.2.1)
      (fun c e => (hdata c e).2.2.2.2.2.2.2.2.2)
  refine ⟨r,hr,hle,lambda,hlambda,t,δ₀,k,N,hδ,a,F,K,hK,hfix,hF,hcore,?_,e,he,side,ν,hdet,ham,hm,hgeometry⟩
  intro c e
  exact ⟨(hdata c e).1,(hdata c e).2.1,(hdata c e).2.2.1,(hdata c e).2.2.2.1,
    (hdata c e).2.2.2.2.1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Function TopologicalSpace Manifold MeasureTheory Filter
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u v
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)

private theorem exists_finite_oriented_neck_data_of_chosen_family
    {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)
    {δ : ℝ} (hδ1 : δ < 1) {m : ℕ} {Q : ℝ}
    (δ₀ : P.HornCutIndex → ℝ) (k : P.HornCutIndex → ℕ)
    (N : ∀ j, NormalizedNeck D.terminal.metric (δ₀ j) (k j))
    (hδ : ∀ j, δ₀ j ≤ δ)
    (rot : P.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hrot : ∀ j, Geometry.sphereDiffeo (n := 2) (rot j) spherePoint =
      ((N j).monoDelta (hδ j) hδ1).sphereMark)
    (side : P.HornCutIndex → Bool) (ν : P.HornCutIndex → Sphere 2 ≃ Sphere 2)
    (a : ∀ c, P.hornIndex c → ℝ)
    (hm : ∀ j, m ≤ k j) (hscale : ∀ j, (N j).scale = Q)
    (hmap : ∀ j (q : bufferedCylinder δ),
      (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented.map q =
        P.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2))
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding
      (neckAmbientMap D.slab.terminalRegularOpen
        (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented))
    (hd : Pairwise fun i j => Disjoint
      (range (neckAmbientMap D.slab.terminalRegularOpen
        (((N i).monoDelta (hδ i) hδ1).rotatedDatum (rot i) (hrot i) (side i)).oriented))
      (range (neckAmbientMap D.slab.terminalRegularOpen
        (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented)))
    (hRet : let f := (fun j => neckAmbientMap D.slab.terminalRegularOpen
          (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented)
      MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
        (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
          D.terminal.metric f (P.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen)
    (hcutside : let d := fun j =>
        (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented
      let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
      ∀ j s, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j, s) ∈
        scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
          (P.coreRadius ^ 2)⁻¹ ↔ s = true) :
    ∃ e : Fin (Nat.card P.HornCutIndex) ≃ P.HornCutIndex,
      let d := fun j =>
        ((((N (e j)).monoDelta (hδ (e j)) hδ1).rotatedDatum
          (rot (e j)) (hrot (e j)) (side (e j))).oriented.lowerOrder (hm (e j)))
      (∀ j, metricScalarAt D.terminal.metric (N (e j)).center = Q) ∧
      (∀ j, (d j).retainedSide = true) ∧
      (∀ j (q : bufferedCylinder δ),
        (d j).map q = P.horn (e j).1.val (e j).2
          (ν (e j) q.val.1, a (e j).1.val (e j).2 - q.val.2)) ∧
      let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
      ∃ (hfFin : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
        (hdFin : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
        (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j)) ∧
        MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
          (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
            D.terminal.metric f (P.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen ∧
          ∀ j s, cuttingSphereComponent (fun j => (d j).precision_pos) f hfFin hdFin (j, s) ∈
            scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
              (P.coreRadius ^ 2)⁻¹ ↔ s = true := by
  classical
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  let : Finite P.HornCutIndex := inferInstance
  let dHigh := fun j =>
    (((N j).monoDelta (hδ j) hδ1).rotatedDatum (rot j) (hrot j) (side j)).oriented
  let dLow : ∀ j, normalizedDatum D.terminal.metric (N j).center δ m :=
    fun j => (dHigh j).lowerOrder (hm j)
  obtain ⟨hlowMap, hlowSide, hscalar, _, _, hlocal⟩ :=
    NormalizedNeck.lowerOrder_oriented_rotatedDatum_family
      D.slab.terminalRegularOpen N hδ hδ1 rot hrot side hm hscale
  let fLow := fun j => neckAmbientMap D.slab.terminalRegularOpen (dLow j)
  obtain ⟨e, _, _, _, hfFin, hdFin, _, _, hRetFin, hsideFin⟩ :=
    exists_fin_chosen_data D.slab.terminalRegularOpen D.terminal.metric fLow
      (P.coreRadius ^ 2)⁻¹ (fun j => (dLow j).precision_pos) hf hd hRet hcutside
  refine ⟨e, (fun j => hscalar (e j)), (fun j => hlowSide (e j)), ?_,
    hfFin, hdFin, (fun j => hlocal (e j)), hRetFin, hsideFin⟩
  intro j q
  change (dLow (e j)).map q = _
  rw [congrFun (hlowMap (e j)) q]
  exact hmap (e j) q

private theorem exists_finite_oriented_horn_neck_data_of_base_bound :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : 2 * ε ≤ δ) (hδ1 : δ < 1), δ⁻¹ + 2 < (2 * ε)⁻¹ →
        ∀ m : ℕ, m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 →
        ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → ∀ y : Sphere 2,
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda;
          0 < Q ∧
          ∃ (F : ∀ c, Padapt.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = Padapt.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j)) ∧
                  MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen ∧
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  ∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j) hδ1).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ 2 * ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j)) := by
  classical
  obtain ⟨eta, heta, hchoose⟩ := exists_common_scale_oriented_horn_necks_of_base_bound.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit m hm Q hQ y
  let : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
        ThreeModel D.slab.terminalRegularOpen.isOpen)
  obtain ⟨r,hr,hle,lambda,hlambda,t,δ₀,k,N,hδ,a,F,K,hK,hfix,hF,hcore,hdata,
    rot,hrot,side,ν,hdet,ha,hmap,hf,hd,hside,hRet⟩ := hchoose P hε hεδ hδ1 hfit Q hQ y
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let Ns := fun j : P'.HornCutIndex => N j.1.val j.2
  let hm' : ∀ j : P'.HornCutIndex, m + 6 ≤ k j.1.val j.2 :=
    fun j => hm.trans (hdata j.1.val j.2).2.2.2.2
  obtain ⟨e, hscalar, hsideFin, hmapFin, hfFin, hdFin, hlocalFin, hRetFin, hfacesFin⟩ :=
    exists_finite_oriented_neck_data_of_chosen_family P' hδ1
      (fun j => δ₀ j.1.val j.2) (fun j => k j.1.val j.2) Ns
      (fun j => hδ j.1.val j.2) rot hrot side ν a hm'
      (fun j => (hdata j.1.val j.2).2.2.1) hmap hf hd hRet hside
  let d := fun j =>
    (((Ns (e j)).monoDelta (hδ (e j).1.val (e j).2) hδ1).rotatedDatum
      (rot (e j)) (hrot (e j)) (side (e j))).oriented.lowerOrder (hm' (e j))
  have hQpos : 0 < Q := (mul_pos
    (mul_pos (by norm_num) (zero_lt_one.trans_le P.Lambda_ge_one))
    (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))).trans hQ
  refine ⟨r, hr, hle, lambda, hlambda, hQpos, F, K, hK, hfix, hF, hcore, e,
    (fun j => t (e j).1.val (e j).2), (fun j => a (e j).1.val (e j).2),
    ν ∘ e, (fun j => (Ns (e j)).center), d, ?_, ?_, hsideFin, hmapFin,
    hfFin, hdFin, hlocalFin, hRetFin, hfacesFin, ?_⟩
  · intro j
    exact ⟨(hdata (e j).1.val (e j).2).1,
      (hdata (e j).1.val (e j).2).2.1, hscalar j⟩
  · intro j
    exact ha (e j).1.val (e j).2
  · refine ⟨(fun j => δ₀ (e j).1.val (e j).2),
      (fun j => k (e j).1.val (e j).2), (fun j => Ns (e j)),
      (fun j => hδ (e j).1.val (e j).2), (fun j => rot (e j)),
      (fun j => hrot (e j)), (fun j => side (e j)), (fun j => hm' (e j)),
      ?_, ?_, ?_⟩
    · intro j
      exact ⟨rfl, (hdata (e j).1.val (e j).2).2.2.1,
        (hdata (e j).1.val (e j).2).2.2.2.1,
        (hdata (e j).1.val (e j).2).2.2.2.2⟩
    · intro j
      exact hdet (e j)
    · intro j
      exact HEq.rfl


theorem exists_horn_cut_metricCutCapEvent_of_base_scalar_bound :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ ∃ hquarter : δ < 1 / 4, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q → ∀ y : Sphere 2,
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda;
          ∃ (F : ∀ c, Padapt.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = Padapt.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ 2 * ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j))) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial :=
        D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
        cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
        f (fun i => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel
          (fun j => (d j).precision_pos) f hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
  classical
  choose c hc C hC A hA hsmall hfactory using
    exists_uniform_metricCutCapEvent_volume_debit_with_cap_precision.{u}
  choose δcap hδcap hcapHalf hcapScalar using
    exists_metricCutCapEvent_capRegion_scalar_lower A hA
  choose eta heta hchoose using exists_finite_oriented_horn_neck_data_of_base_bound.{u}
  apply Exists.intro c
  apply Exists.intro hc
  apply Exists.intro C
  apply And.intro hC
  apply Exists.intro A
  apply Exists.intro hA
  apply And.intro hsmall
  intro Dcap hDcap m accuracy haccuracy
  have choice := hfactory Dcap hDcap m accuracy haccuracy δcap hδcap
  let δ : ℝ := Classical.choose choice
  have hδ := (Classical.choose_spec choice).1
  have hquarter := (Classical.choose_spec choice).2.1
  choose ε₀ hε₀ hεeta hεδ hεsmall hwidth horder using exists_precision_order_compatible hδ heta m
  apply Exists.intro δ
  apply And.intro hδ
  apply Exists.intro hquarter
  apply Exists.intro (ε₀ / 2)
  apply And.intro (by positivity : 0 < ε₀ / 2)
  intro D ε Λ P hε Q hQ y
  have hεdouble : 2 * ε ≤ ε₀ := by linarith only [hε]
  have hcompat := precision_order_compatible_of_le (mul_pos (by norm_num) P.epsilon_pos)
    hεdouble hεeta hεδ hεsmall hwidth horder
  have hεeta' : ε ≤ eta := by linarith only [hcompat.1,P.epsilon_pos]
  have hm : m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 := hcompat.2.2.2.2.trans
    (Nat.add_le_add_right (Nat.floor_mono (inv_anti₀ P.epsilon_pos
      (by linarith only [P.epsilon_pos] : ε ≤ 2 * ε))) 1)
  choose r hr hle lambda hlambda hQpos F K hK hfix hF hcore e t a ν x₀ d hcenter ha
    hside hmap hf hd hlocal hRet hfaces horiginal using
    hchoose P hεeta' hcompat.2.1 (hquarter.trans (by norm_num)) hcompat.2.2.2.1 m hm Q hQ y
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
    (P'.coreRadius ^ 2)⁻¹
  have hone (j) : cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,true) ∈ R ∧
      cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,false) ∉ R := by
    exact ⟨(hfaces j true).mpr rfl,fun h => Bool.false_ne_true ((hfaces j false).mp h)⟩
  have hevent := (Classical.choose_spec choice).2.2 D.slab D.terminal (fun _ => δ)
    (fun j => (d j).precision_pos)
    (fun _ => le_rfl) x₀ d f hf hd hlocal (fun _ => rfl) R hRet D.singular hone
    Q hQpos (fun j => (hcenter j).2.2)
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
    cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  choose oQ oRet oDisc B aCap hboundary E hDisc hCap htrace htubes hG hL hOld hBoundary
    hpin hfloor hvol hrec dCap hcapMap hcapSide w hOutput hw hcapPrecision hlow using hevent
  have hcapMake := hcapScalar (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
    f hf hd hlocal R hnontrivial
    (t₀ := D.startTime) (t₁ := D.endTime) (D := Dcap) (ε := accuracy) (m := m)
  have hbound := hcapMake oQ oRet oDisc E (fun b => (B b).toHomeomorph)
    (fun b => (aCap b).toHomeomorph) hboundary hDisc hCap htrace
    D.slab.terminalRegularOpen D.terminal.metric hRet c hc x₀ (fun _ => m + 6) d
    (fun _ => rfl) (fun _ => m + 4) hrec dCap hcapMap hcapSide w
    hcapPrecision (fun _ => by omega) (Q / 2) hlow hOutput
  have hbound' : ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
    intro q hq
    convert hbound q hq using 1
    ring
  refine ⟨r,hr,hle,lambda,hlambda,F,K,hK,hfix,hF,hcore,e,t,a,ν,x₀,d,hcenter,ha,hside,hmap,
    hf,hd,hlocal,hRet,hfaces,horiginal,?_⟩
  exact ⟨oQ,oRet,oDisc,B,aCap,hboundary,E,hDisc,hCap,htrace,htubes,hG,hL,hOld,hBoundary,
    hpin,hfloor,hvol,hrec,dCap,hcapMap,hcapSide,w,hOutput,hw,hbound'⟩

theorem exists_horn_cut_metricCutCapEvent_at_base_bounded_scale :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ ∃ hquarter : δ < 1 / 4, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ BaseBound Qtarget : ℝ,
      let Q := max (2 * BaseBound) (8 * Qtarget) + 1
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → Λ * (P.coreRadius ^ 2)⁻¹ ≤ BaseBound → ∀ y : Sphere 2,
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda;
          ∃ (F : ∀ c, Padapt.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = Padapt.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ 2 * ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j))) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial :=
        D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
        cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
        f (fun i => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel
          (fun j => (d j).precision_pos) f hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        ∀ q ∈ E.capRegion, 2 * Qtarget ≤ metricScalarAt E.outputMetric q := by
  classical
  choose c hc C hC A hA hsmall hfamily using
    exists_horn_cut_metricCutCapEvent_of_base_scalar_bound.{u}
  refine ⟨c,hc,C,hC,A,hA,hsmall,?_⟩
  intro Dcap hDcap m accuracy haccuracy
  choose δ hδ hquarter ε₀ hε₀ hmake using hfamily Dcap hDcap m accuracy haccuracy
  refine ⟨δ,hδ,hquarter,ε₀,hε₀,?_⟩
  intro BaseBound Qtarget
  dsimp only
  intro D ε Λ P hε hbase y
  let Q := max (2 * BaseBound) (8 * Qtarget) + 1
  have hQ : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q := by
    have hbound : 2 * (Λ * (P.coreRadius ^ 2)⁻¹) ≤ 2 * BaseBound :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    have hmax := le_max_left (2 * BaseBound) (8 * Qtarget)
    dsimp only [Q]
    linarith only [hbound,hmax]
  choose r hr hle lambda hlambda F K hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap
    hf hd hlocal hRet hfaces horiginal hevent using hmake P hε Q hQ y
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
    (P'.coreRadius ^ 2)⁻¹
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
    cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  choose oQ oRet oDisc B aCap hboundary E hDisc hCap htrace htubes hG hL hOld hBoundary
    hpin hfloor hvol hrec dCap hcapMap hcapSide w hOutput hw hcapLower using hevent
  refine ⟨r,hr,hle,lambda,hlambda,F,K,hK,hfix,hF,hcore,e,t,a,ν,x₀,d,hcenter,ha,hside,hmap,
    hf,hd,hlocal,hRet,hfaces,horiginal,?_⟩
  refine ⟨oQ,oRet,oDisc,B,aCap,hboundary,E,hDisc,hCap,htrace,htubes,hG,hL,hOld,hBoundary,
    hpin,hfloor,hvol,hrec,dCap,hcapMap,hcapSide,w,hOutput,hw,hcapLower,?_⟩
  intro q hq
  have hscale : 8 * Qtarget ≤ Q := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hb := hcapLower q hq
  linarith only [hscale,hb]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end


set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

private theorem exists_neck_family_first_scalar_level_reparametrized_bound_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q →
        ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
          (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
          (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
          ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
            (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
            (∀ s ∈ Ico 0 (t c e), ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
            ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (a r : ℝ), 0 < r →
              (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
              (∀ w : Sphere 2, ∃ z : Sphere 2,
                P.horn c e (F (z, a)) = (N c e).chart ⟨(w, 0), by
                  have hp := inv_pos.mpr (N c e).delta_pos
                  constructor <;> linarith⟩) →
              ∀ z : Sphere 2, ∀ s ∈ Icc (0 : ℝ) a,
                metricScalarAt D.terminal.metric (P.horn c e (F (z, s))) ≤ 3 * Q := by
  obtain ⟨eta, heta, hchoose⟩ :=
    exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε Q hQ
  classical
  choose t ht y δ k N hcenter hscale hδ hk hbefore hprefix using
    fun c e => hchoose P hε c e hQ
  exact ⟨t, y, δ, k, N, fun c e =>
    ⟨ht c e, hcenter c e, hscale c e, hδ c e, hk c e, hbefore c e, hprefix c e⟩⟩

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private theorem rescaled_horn_prefix_scalar_bound
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k) {Q : ℝ}
    (hprefix : ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
      (a r : ℝ), 0 < r →
      (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
      (∀ w : Sphere 2, ∃ z : Sphere 2,
        P.horn c e (F (z, a)) = N.chart ⟨(w, 0), by
          have hp := inv_pos.mpr N.delta_pos
          constructor <;> linarith⟩) →
      ∀ z : Sphere 2, ∀ s ∈ Icc (0 : ℝ) a,
        metricScalarAt D.terminal.metric (P.horn c e (F (z, s))) ≤ Q)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
    {a r : ℝ} (hr : 0 < r)
    (hfix : ∀ q : NeckCylinder, q.2 ≤ r → F q = q)
    (hmatch : ∀ w : Sphere 2, ∃ z : Sphere 2,
      (P.rescaleHornParameters lambda hlambda).horn c e (F (z, a)) =
        N.chart ⟨(w, 0), by
          have hp := inv_pos.mpr N.delta_pos
          constructor <;> linarith⟩) :
    ∀ z : Sphere 2, ∀ s ∈ Icc (0 : ℝ) a,
      metricScalarAt D.terminal.metric
        ((P.rescaleHornParameters lambda hlambda).horn c e (F (z, s))) ≤ Q := by
  let A : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => 0) (fun _ => lambda)
      contMDiff_const contMDiff_const (fun _ => hlambda.ne')
  let G := (A.trans F).trans A.symm
  have hA (q : NeckCylinder) : A q = (q.1, lambda * q.2) := by
    change (q.1, 0 + lambda * q.2) = _
    rw [zero_add]
  have hAi (q : NeckCylinder) : A.symm q = (q.1, q.2 / lambda) := by
    change (q.1, (q.2 - 0) / lambda) = _
    rw [sub_zero]
  have hG (z : Sphere 2) (s : ℝ) : G (z, s / lambda) = A.symm (F (z, s)) := by
    change A.symm (F (A (z, s / lambda))) = _
    rw [hA, mul_div_cancel₀ _ hlambda.ne']
  have hGfix : ∀ q : NeckCylinder, q.2 ≤ r / lambda → G q = q := by
    intro q hq
    change A.symm (F (A q)) = q
    rw [hfix (A q) (by
      rw [hA]
      have hb := (le_div_iff₀ hlambda).mp hq
      simpa only [mul_comm] using hb)]
    exact A.symm_apply_apply q
  have hGmatch : ∀ w : Sphere 2, ∃ z : Sphere 2,
      P.horn c e (G (z, a / lambda)) = N.chart ⟨(w, 0), by
        have hp := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩ := by
    intro w
    obtain ⟨z, hz⟩ := hmatch w
    refine ⟨z, ?_⟩
    rw [hG, hAi]
    exact hz
  intro z s hs
  have hb := hprefix G (a / lambda) (r / lambda) (div_pos hr hlambda)
    hGfix hGmatch z (s / lambda)
    ⟨div_nonneg hs.1 hlambda.le, (div_le_div_iff_of_pos_right hlambda).mpr hs.2⟩
  rw [hG, hAi] at hb
  exact hb

private theorem scalar_le_on_truncatedRegion_of_core_and_prefix
    {coreBound prefixBound : ℝ} (a : ∀ c, P.hornIndex c → ℝ)
    (hcore : ∀ c ∈ P.component, ∀ x ∈ P.core c,
      metricScalarAt D.terminal.metric x ≤ coreBound)
    (hprefix : ∀ c e (z : Sphere 2), ∀ s ∈ Icc (0 : ℝ) (a c e),
      metricScalarAt D.terminal.metric (P.horn c e (z, s)) ≤ prefixBound) :
    ∀ x ∈ P.truncatedRegion a,
      metricScalarAt D.terminal.metric x ≤ max coreBound prefixBound := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  rcases hxc with hxcore | hxhorn
  · exact (hcore c hc x hxcore).trans (le_max_left _ _)
  · obtain ⟨e, q, hq, rfl⟩ := mem_iUnion.mp hxhorn
    exact (hprefix c e q.1 q.2 hq.2).trans (le_max_right _ _)

private theorem scalar_le_on_rescaled_reparametrized_truncatedRegion
    {Q coreBound : ℝ}
    (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
    (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e))
    (hprefix : ∀ c e,
      ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
        (a r : ℝ), 0 < r →
        (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
        (∀ w : Sphere 2, ∃ z : Sphere 2,
          P.horn c e (F (z, a)) = (N c e).chart ⟨(w, 0), by
            have hp := inv_pos.mpr (N c e).delta_pos
            constructor <;> linarith⟩) →
        ∀ z : Sphere 2, ∀ s ∈ Icc (0 : ℝ) a,
          metricScalarAt D.terminal.metric (P.horn c e (F (z, s))) ≤ 3 * Q)
    (hcore : ∀ c ∈ P.component, ∀ x ∈ P.core c,
      metricScalarAt D.terminal.metric x ≤ coreBound)
    (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
    (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
    (a : ∀ c, P.hornIndex c → ℝ)
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e))
    (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ lambda * r c e → F c e q = q)
    (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ)
    (hmatch : ∀ c e (w : Sphere 2), ∃ z : Sphere 2,
      ((P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda).horn c e
        (F c e (z, a c e)) = (N c e).chart ⟨(w, 0), by
          have hp := inv_pos.mpr (N c e).delta_pos
          constructor <;> linarith⟩) :
    let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
    let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
    ∀ x ∈ P'.truncatedRegion a,
      metricScalarAt D.terminal.metric x ≤ max coreBound (3 * Q) := by
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  apply P'.scalar_le_on_truncatedRegion_of_core_and_prefix a hcore
  intro c e z s hs
  exact (P.restrictHornCollars r hr hle).rescaled_horn_prefix_scalar_bound c e (N c e)
    (hprefix c e) lambda hlambda (F c e) (mul_pos hlambda (hr c e))
    (hfix c e) (hmatch c e) z s hs


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_first_hit_reparametrized_horn_matching :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹ + 1 < (2 * ε)⁻¹ →
        ∀ {Q coreBound : ℝ}, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ coreBound) →
          ∃ (δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
            (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
            (lambda : ℝ) (hlambda : 0 < lambda),
            let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
            ∃ (hδ : ∀ c e, δ₀ c e ≤ 2 * ε) (hε1 : 2 * ε < 1)
              (a : ∀ c, P.hornIndex c → ℝ)
              (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
              (γ : ∀ c, P.hornIndex c → ℝ)
              (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (K : ∀ c, P.hornIndex c → Set NeckCylinder)
              (hK : ∀ c e, IsCompact (K c e))
              (hfix : ∀ c e q, q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
              (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
              let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
              (∀ c e, (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e) ∧
              (∀ c e, (Padapt.hornCollar c e).radius + δ⁻¹ < a c e ∧
                (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                  β c e = sphereAntipodalDiffeomorph (n := 2)) ∧
                (γ c e = 1 ∨ γ c e = -1) ∧
                (range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                  range (fun q : HalfNeckCylinder => Padapt.horn c e q.val)) ∧
                ∀ q : Sphere 2, ∀ s : ℝ, |s| ≤ δ⁻¹ →
                  ∃ hq : (β c e q, γ c e * s) ∈ neckBuffer (2 * ε),
                    P'.horn c e (q, a c e - s) =
                      ((N c e).monoDelta (hδ c e) hε1).chart ⟨(β c e q,γ c e*s),hq⟩) ∧
              ∀ x ∈ P'.truncatedRegion a,
                metricScalarAt D.terminal.metric x ≤ max coreBound (3 * Q) := by
  obtain ⟨eta₀, heta₀, hchoose⟩ :=
    TerminalCorePresentation.exists_neck_family_first_scalar_level_reparametrized_bound_tolerance.{u}
  obtain ⟨eta₁, heta₁, hmatch⟩ := exists_reparametrized_horn_matching_of_neck_family.{u}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro D ε Λ P hε δ hδpos hfit Q coreBound hQ hcore
  obtain ⟨t, y, δ₀, k, N, hN⟩ := hchoose P (hε.trans (min_le_left _ _)) (Q := Q) (by simpa only [mul_assoc] using hQ)
  have hδε := fun c e => (hN c e).2.2.2.1
  have hk := fun c e => (hN c e).2.2.2.2.1
  have hcenter : ∀ c e, (N c e).center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
    intro c e
    rw [(hN c e).2.1]
    exact ⟨(y c e,t c e),⟨mem_univ _,(hN c e).1⟩,rfl⟩
  have hscale := fun c e => (hN c e).2.2.1
  obtain ⟨r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfix,hF,hmatching⟩ :=
    hmatch P (hε.trans (min_le_right _ _)) hδpos hfit hQ δ₀ k N hδε hk hcenter hscale
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  refine ⟨δ₀,k,N,r,hr,hle,lambda,hlambda,hδ,hε1,a,β,γ,F,K,hK,hfix,hF,
    (fun c e => ⟨hscale c e,hδε c e,hk c e⟩),hmatching,?_⟩
  apply P.scalar_le_on_rescaled_reparametrized_truncatedRegion δ₀ k N
    (fun c e => (hN c e).2.2.2.2.2.2) hcore r hr hle lambda hlambda F a K hK hfix hF
  intro c e w
  obtain ⟨hw,hval⟩ := (hmatching c e).2.2.2.2 ((β c e).symm w) 0
    (by simp [inv_nonneg.mpr hδpos.le])
  refine ⟨(β c e).symm w, ?_⟩
  change P'.horn c e ((β c e).symm w,a c e) = _
  simp only [sub_zero, mul_zero, (β c e).apply_symm_apply] at hval
  exact hval.trans (by rfl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.ThreeManifold.Surgery
private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)
private local instance {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ) :
    Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2+1) := ⟨by simp⟩

private theorem exists_first_hit_oriented_horn_necks :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : 2 * ε ≤ δ) (hδ1 : δ < 1), δ⁻¹+2 < (2 * ε)⁻¹ →
        ∀ Q coreBound : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ coreBound) →
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
          ∃ (δ₀ : ∀ c, Padapt.hornIndex c → ℝ) (k : ∀ c, Padapt.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (hδ : ∀ c e, δ₀ c e ≤ δ)
            (a : ∀ c, Padapt.hornIndex c → ℝ)
            (F : ∀ c, Padapt.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel,
              NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            let N' := fun j : P'.HornCutIndex => (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
            P'.core = Padapt.core ∧
            (∀ c e, (N c e).scale = Q ∧ δ₀ c e ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e) ∧
            (∀ x ∈ P'.truncatedRegion a, metricScalarAt D.terminal.metric x ≤ max coreBound (3 * Q)) ∧
            ∃ (e : P'.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
              (he : ∀ j, sphereDiffeo (n := 2) (e j) spherePoint = (N' j).sphereMark)
              (side : P'.HornCutIndex → Bool)
              (ν : P'.HornCutIndex → Sphere 2 ≃ Sphere 2),
              let d := fun j => (N' j).rotatedDatum (e j) (he j) (side j)
              (∀ j, LinearMap.det (e j).toLinearMap = 1) ∧
              (∀ c e, δ⁻¹+1 < a c e) ∧
              (∀ j (q : bufferedCylinder δ),
                (d j).oriented.map q = P'.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) ∧
              let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
              ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,side) ∈
                  scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                    (P'.coreRadius^2)⁻¹ ↔
                  side = true) ∧
                MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                  (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f
                    (P'.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  obtain ⟨eta,heta,hmatching⟩ := exists_first_hit_reparametrized_horn_matching
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit Q coreBound hQ hcorebound
  have hδpos : 0 < δ := (mul_pos (by norm_num) P.epsilon_pos).trans_le hεδ
  let δw := (δ⁻¹+1)⁻¹
  have hδw : 0 < δw := inv_pos.mpr (by positivity)
  have hδwi : δw⁻¹ = δ⁻¹+1 := inv_inv _
  have hfitw : δw⁻¹+1 < (2 * ε)⁻¹ := by rw [hδwi]; linarith
  obtain ⟨δraw,k,Nraw,r,hr,hle,lambda,hlambda,hraw,hε1,a,β,γ,F,K,hK,hfix,hF,hNraw,hmatch,hscalar⟩ :=
    hmatching P hε hδw hfitw hQ hcorebound
  let δ₀ := fun (_c : ConnectedComponents D.slab.terminalRegularOpen) (_e : P.hornIndex _c) => 2 * ε
  let N := fun c e => (Nraw c e).monoDelta (hraw c e) hε1
  have hdata : ∀ c e,
      (N c e).scale = Q ∧ δ₀ c e ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e :=
    fun c e => ⟨(hNraw c e).1, le_rfl, (hNraw c e).2.2⟩
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let hδ : ∀ c e, δ₀ c e ≤ δ := fun _ _ => hεδ
  have ham (c) (e : P'.hornIndex c) : δ⁻¹+1 < a c e := by
    have hh := (hmatch c e).1
    rw [hδwi] at hh
    have hp := (Padapt.hornCollar c e).radius_pos
    linarith
  obtain ⟨e,he,side,ν,hdet,hm,hgeometry⟩ := exists_oriented_horn_neck_data_of_matching
    P' hδpos hδ1 hδwi δ₀ k N hδ a ham β γ
      (fun c e => (hmatch c e).2.2.1)
      (fun c e => (hmatch c e).2.2.2.2)
  exact ⟨r,hr,hle,lambda,hlambda,δ₀,k,N,hδ,a,F,K,hK,hfix,hF,rfl,hdata,hscalar,
    e,he,side,ν,hdet,ham,hm,hgeometry⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

private theorem exists_finite_first_hit_oriented_horn_neck_data :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : 2 * ε ≤ δ) (hδ1 : δ < 1), δ⁻¹ + 2 < (2 * ε)⁻¹ →
        ∀ m : ℕ, m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 →
        ∀ Q coreBound : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
        (∀ c ∈ P.component, ∀ x ∈ P.core c,
          metricScalarAt D.terminal.metric x ≤ coreBound) →
        ∃ (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
          (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius)
          (lambda : ℝ) (hlambda : 0 < lambda),
        let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda;
          0 < Q ∧
          ∃ (F : ∀ c, Padapt.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, Padapt.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (Padapt.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = Padapt.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (a : ∀ c, P'.hornIndex c → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ x ∈ P'.truncatedRegion a,
                  metricScalarAt D.terminal.metric x ≤ max coreBound (3 * Q)) ∧
                (∀ c e, δ⁻¹ + 1 < a c e) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a (e j).1.val (e j).2 - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j)) ∧
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∀ p : retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹),
                    metricScalarAt D.terminal.metric
                      (retainedCoreDomainMap f
                        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                          (P'.coreRadius ^ 2)⁻¹) D.slab.terminalRegularOpen hRet p) ≤
                        max coreBound (3 * Q)) ∧
                  ∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j) hδ1).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ 2 * ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j)) := by
  classical
  obtain ⟨eta, heta, hchoose⟩ := exists_first_hit_oriented_horn_necks.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit m hm Q coreBound hQ hcorebound
  let : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
        ThreeModel D.slab.terminalRegularOpen.isOpen)
  obtain ⟨r, hr, hle, lambda, hlambda, δ₀, k, N, hδ, a, F, K, hK, hfix, hF,
    hcore, hdata, hscalarTrunc, rot, hrot, side, ν, hdet, ha, hmap, hf, hd, hside, hRet⟩ :=
    hchoose P hε hεδ hδ1 hfit Q coreBound hQ hcorebound
  let Padapt := (P.restrictHornCollars r hr hle).rescaleHornParameters lambda hlambda
  let P' := Padapt.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let Ns := fun j : P'.HornCutIndex => N j.1.val j.2
  let hm' : ∀ j : P'.HornCutIndex, m + 6 ≤ k j.1.val j.2 :=
    fun j => hm.trans (hdata j.1.val j.2).2.2
  obtain ⟨e, hscalar, hsideFin, hmapFin, hfFin, hdFin, hlocalFin, hRetFin, hfacesFin⟩ :=
    exists_finite_oriented_neck_data_of_chosen_family P' hδ1
      (fun j => δ₀ j.1.val j.2) (fun j => k j.1.val j.2) Ns
      (fun j => hδ j.1.val j.2) rot hrot side ν a hm'
      (fun j => (hdata j.1.val j.2).1) hmap hf hd hRet hside
  let d := fun j =>
    (((Ns (e j)).monoDelta (hδ (e j).1.val (e j).2) hδ1).rotatedDatum
      (rot (e j)) (hrot (e j)) (side (e j))).oriented.lowerOrder (hm' (e j))
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  have hQpos : 0 < Q := (mul_pos
    (mul_pos (by norm_num) (zero_lt_one.trans_le P.Lambda_ge_one))
    (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))).trans hQ
  have hδpos : 0 < δ := (mul_pos (by norm_num) P.epsilon_pos).trans_le hεδ
  have haPos : ∀ c e, 0 < a c e := by
    intro c e
    have hi := inv_pos.mpr hδpos
    linarith [ha c e]
  have hremoved : ∀ c ∈ P'.component, ∀ ec : P'.hornIndex c, ∀ y : Sphere 2,
      (P'.horn c ec (y, a c ec)).val ∈ ⋃ j, removedSlab (f j) := by
    intro c hc ec y
    obtain ⟨j, hj⟩ := e.surjective (⟨⟨c, hc⟩, ec⟩ : P'.HornCutIndex)
    let q : bufferedCylinder δ := ⟨((ν (e j)).symm y, 0), by
      constructor <;> linarith [inv_pos.mpr hδpos]⟩
    refine mem_iUnion.mpr ⟨j, q, ?_, ?_⟩
    · change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
      norm_num
    · change ((d j).map q).val = _
      rw [hmapFin]
      change (P'.horn (e j).1.val (e j).2
        (ν (e j) ((ν (e j)).symm y), a (e j).1.val (e j).2 - 0)).val = _
      rw [(ν (e j)).apply_symm_apply, sub_zero, hj]
  have hboundRet : ∀ x : cutCore f,
      x ∈ retainedCore f
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
          f (P'.coreRadius ^ 2)⁻¹) →
      ∃ p : D.slab.terminalRegularOpen, p.val = x.val ∧
        p ∈ P'.truncatedRegion a ∧ metricScalarAt D.terminal.metric p ≤ max coreBound (3 * Q) :=
    scalar_le_on_retainedCore_of_truncated_bound P' a haPos hscalarTrunc
      f hremoved
  refine ⟨r, hr, hle, lambda, hlambda, hQpos, F, K, hK, hfix, hF, hcore, e,
    a, ν ∘ e, (fun j => (Ns (e j)).center), d,
    hscalar, hscalarTrunc, ha, hsideFin, hmapFin,
    hfFin, hdFin, hlocalFin, hRetFin, hfacesFin, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, _, hpbound⟩ := hboundRet x.val x.property
    have heq : p = retainedCoreDomainMap f
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
          f (P'.coreRadius ^ 2)⁻¹)
        D.slab.terminalRegularOpen hRetFin x := Subtype.ext hp
    exact heq ▸ hpbound
  · refine ⟨(fun j => δ₀ (e j).1.val (e j).2),
      (fun j => k (e j).1.val (e j).2), (fun j => Ns (e j)),
      (fun j => hδ (e j).1.val (e j).2), (fun j => rot (e j)),
      (fun j => hrot (e j)), (fun j => side (e j)), (fun j => hm' (e j)),
      ?_, ?_, ?_⟩
    · intro j
      exact ⟨rfl, (hdata (e j).1.val (e j).2).1,
        (hdata (e j).1.val (e j).2).2.1, (hdata (e j).1.val (e j).2).2.2⟩
    · intro j
      exact hdet (e j)
    · intro j
      exact HEq.rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
