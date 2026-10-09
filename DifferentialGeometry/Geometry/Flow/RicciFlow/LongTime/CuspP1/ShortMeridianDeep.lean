import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianClassMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepCusp

/-!
# CP1-A3 (G1, deep cusp): closed geodesic of a prescribed class, short at depth, and the kernel
transfer along a basepoint change
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1

theorem quotient_map_trans_CPA3 {A : Type*} {C : Type*} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ a₂ : A} (p : Path.Homotopic.Quotient a₀ a₁)
    (q : Path.Homotopic.Quotient a₁ a₂) (f : C(A, C)) :
    Path.Homotopic.Quotient.map (p.trans q) f =
      (Path.Homotopic.Quotient.map p f).trans (Path.Homotopic.Quotient.map q f) := by
  induction p, q using Path.Homotopic.Quotient.ind₂ with
  | mk p q => exact congrArg Path.Homotopic.Quotient.mk (Path.map_trans p q f.continuous)

theorem quotient_map_symm_CPA3 {A : Type*} {C : Type*} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ : A} (p : Path.Homotopic.Quotient a₀ a₁) (f : C(A, C)) :
    Path.Homotopic.Quotient.map p.symm f = (Path.Homotopic.Quotient.map p f).symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

theorem changeBasepoint_map_CPA3 {A : Type*} {C : Type*} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ : A} (f : C(A, C)) (q : Path a₀ a₁) (g : FundamentalGroup A a₁) :
    fundamentalGroupChangeBasepoint (q.map f.continuous) (FundamentalGroup.map f a₁ g) =
      FundamentalGroup.map f a₀ (fundamentalGroupChangeBasepoint q g) := by
  rw [fundamentalGroupChangeBasepoint_apply, fundamentalGroupChangeBasepoint_apply]
  change (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (q.map f.continuous))
      (Path.Homotopic.Quotient.map g f)).trans
        (Path.Homotopic.Quotient.mk (q.map f.continuous)).symm =
    Path.Homotopic.Quotient.map
      (((Path.Homotopic.Quotient.mk q).trans g).trans (Path.Homotopic.Quotient.mk q).symm) f
  rw [quotient_map_trans_CPA3, quotient_map_trans_CPA3, quotient_map_symm_CPA3,
    Path.Homotopic.Quotient.mk_map]

/-- Kernel membership of a loop class transfers along a basepoint change of loop classes. -/
theorem mem_ker_of_changeBasepoint_CPA3 {Y : Type*} [TopologicalSpace Y] (φ : C(Torus, Y))
    (u v : freeLoop Torus) (β : Path (v 0) (u 0))
    (h : fundamentalGroupChangeBasepoint β (loopDegreeClass u 1) = loopDegreeClass v 1)
    (hk : loopDegreeClass u 1 ∈ (FundamentalGroup.map φ (u 0)).ker) :
    loopDegreeClass v 1 ∈ (FundamentalGroup.map φ (v 0)).ker := by
  rw [MonoidHom.mem_ker] at hk ⊢
  rw [← h, ← changeBasepoint_map_CPA3 φ β, hk, map_one]

/-- **Cusp-level content of `PrescribedCuspMeridian` for a prescribed class.** -/
theorem exists_meridian_deepCusp_of_class_CPA3 (H : HyperbolicCusp) (γ : freeLoop Torus)
    (hprim : ∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
      e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1)) :
    ∃ loop : freeLoop Torus,
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
      (∃ β : Path (loop 0) (γ 0),
        fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1) = loopDegreeClass loop 1) ∧
      ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
          (deepCusp_CPA H b).torusMetric (loopLift loop) ∧
        ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
          let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
          (deepCusp_CPA H b).torusMetric.inner (loopLift loop s) v v ≤ L ^ 2 := by
  obtain ⟨loop, hemb, hsm, hgeo, hprim', hβ⟩ :=
    exists_closed_geodesic_of_class_CPA3 H.torusMetric H.torus_flat γ hprim
  obtain ⟨c₀, hc₀, hc⟩ := exists_scale_short_geodesic_CPA H.torusMetric loop hsm hgeo
  refine ⟨loop, hemb, hsm, hprim', hβ, -Real.log c₀, fun b hb => ?_⟩
  have hle : Real.exp (-b) ≤ c₀ := by
    calc Real.exp (-b) ≤ Real.exp (Real.log c₀) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = c₀ := Real.exp_log hc₀
  exact hc (Real.exp (-b)) (Real.exp_pos _) hle

end GC.LongTime.CuspP1
