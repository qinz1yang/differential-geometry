import DifferentialGeometry.Geometry.Comparison.Variation.TwistedExponential
import DifferentialGeometry.Geometry.Comparison.Variation.LocalFirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.TwistedEnergy

noncomputable section
open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open Poincare.Geometry.Riemannian.Variation

namespace Poincare.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem exists_minimal_twisted_geodesic_with_endpoint_tangent
    (g : SmoothRiemannianMetric I M) (F : M ≃ₘ⟮I, I⟯ M)
    (hF : ∀ p (v w : TangentSpace I p),
      g.inner (F p) (mfderiv I I F p v) (mfderiv I I F p w) = g.inner p v w)
    (hfree : ∀ p, F p ≠ p) :
    ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic (I := I) g γ ∧
      γ L = F (γ 0) ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      curveEnergy (I := I) g γ 0 L = L ∧
      (∀ c, SmoothNearInterval (I := I) c L → IsTwistedPath F L c →
        L ≤ curveEnergy (I := I) g c 0 L) ∧
      (∀ v : TangentSpace I (γ 0),
        g.inner (γ L) (mfderiv I I F (γ 0) v) (mfderiv 𝓘(ℝ, ℝ) I γ L 1) =
          g.inner (γ 0) v (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ∧
      (mfderiv I I F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γ L 1 : E) := by
  obtain ⟨p, L, γ, hL, _, _, h0, h1, hγ, hg, hspeed, hEγ, hmin⟩ :=
    exists_minimal_twisted_geodesic g F F.continuous hfree
  have htw : γ L = F (γ 0) := h1.trans (congrArg F h0.symm)
  have hpair (v : TangentSpace I (γ 0)) :
      g.inner (γ L) (mfderiv I I F (γ 0) v) (mfderiv 𝓘(ℝ, ℝ) I γ L 1) =
        g.inner (γ 0) v (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) := by
    obtain ⟨δ, f, hδ, hf, hcenter, htwf, hv0, hvL, _⟩ :=
      exists_twisted_endpoint_variation g F hF γ hγ hL htw v
    have hcenter' : (fun t => f (0, t)) = γ := funext hcenter
    have hcc : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hstrip : (Ioo (-1 : ℝ) 1 ×ˢ Icc 0 L) ⊆ (univ ×ˢ Ioo (-δ) (L + δ)) :=
      fun _ hp => ⟨mem_univ _, hcc hp.2⟩
    have hlocal : IsLocalMin (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) 0 := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with s hs
      change curveEnergy (I := I) g (fun t => f (0, t)) 0 L ≤ _
      rw [hcenter', hEγ]
      exact hmin _ (smoothNearInterval_slice (isOpen_univ.prod isOpen_Ioo) hstrip hf hs) (htwf s)
    have hfirst := firstVariation_curveEnergy_geodesic_of_smooth_near_slice g f hL
      (isOpen_univ.prod isOpen_Ioo) (fun _ hp => ⟨mem_univ _, hcc hp.2⟩) hf
      (by rw [hcenter']; exact hg.isGeodesicOn _) (by
        intro t _
        change g.inner (f (0, t)) (mfderiv 𝓘(ℝ, ℝ) I (fun u => f (0, u)) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u => f (0, u)) t 1) = 1
        rw [hcenter', hcenter]
        exact hspeed t)
    have hz := hlocal.deriv_eq_zero
    rw [hfirst.deriv] at hz
    erw [hcenter', hcenter, hcenter, hv0, hvL] at hz
    linarith
  refine ⟨L, γ, hL, hγ, hg, htw, hspeed, hEγ, hmin, hpair, ?_⟩
  let u : TangentSpace I (γ L) := mfderiv I I F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
  let w : TangentSpace I (γ L) := mfderiv 𝓘(ℝ, ℝ) I γ L 1
  have huu : g.inner (γ L) u u = 1 := by
    change g.inner (γ L) (mfderiv I I F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1))
      (mfderiv I I F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) = 1
    rw [htw, hF]
    exact hspeed 0
  have hww : g.inner (γ L) w w = 1 := hspeed L
  have huw : g.inner (γ L) u w = 1 := (hpair _).trans (hspeed 0)
  have hwu : g.inner (γ L) w u = 1 := (g.symm _ _ _).trans huw
  have hzero : g.inner (γ L) (u - w) (u - w) = 0 := by
    simp only [map_sub, sub_apply, huu, hww, huw, hwu]
    norm_num
  by_contra hne
  have hpos := g.pos (γ L) (u - w) (sub_ne_zero.mpr hne)
  linarith

end Poincare.Geometry.Riemannian
