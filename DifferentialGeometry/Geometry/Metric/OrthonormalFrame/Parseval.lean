import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Ring
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
theorem orthonormal_tangent_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, NeZero.pos _⟩⟩
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have hON : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner_eq (e i) (e j)]
    exact horth i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_coe : ⇑b = e := coe_basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_on : Orthonormal ℝ ⇑b := by rw [hb_coe]; exact hON
  let ob : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    b.toOrthonormalBasis hb_on
  have hob : ∀ i, ob i = e i := by
    intro i
    have h1 : ob i = b i := by
      have := Module.Basis.coe_toOrthonormalBasis b hb_on
      exact congrFun this i
    rw [h1, show b i = e i from congrFun hb_coe i]
  have hrepr := ob.sum_repr' u
  calc
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i)
        = ∑ i : Fin (Module.finrank ℝ E), (inner ℝ (ob i) u : ℝ) • ob i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hob i, hinner_eq (e i) u]
    _ = u := hrepr

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M]
  [BoundarylessManifold I M] in
theorem parseval_family_inner_mul_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (u v : TangentSpace I x) :
    (∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v) = g.inner x u v := by
  classical
  have h := congrArg (fun w : TangentSpace I x => g.inner x w v) (hW u)
  rw [show g.inner x (∑ a : Fin N, g.inner x (W a) u • W a) v =
      ∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v from ?_] at h
  · exact h
  · rw [map_sum (g.inner x) (fun a : Fin N => g.inner x (W a) u • W a) Finset.univ,
      sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul (g.inner x) (g.inner x (W a) u) (W a), smul_apply,
      smul_eq_mul]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
theorem parseval_family_sum_bilin_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    {Z : Type*} [AddCommMonoid Z] [Module ℝ Z]
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] Z) :
    (∑ a : Fin N, B (W a) (W a)) =
      ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
  classical
  have hexp : ∀ u : TangentSpace I x,
      (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u :=
    orthonormal_tangent_expansion (I := I) (M := M) g x e horth
  have hdual : ∀ i j : Fin (Module.finrank ℝ E),
      (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : (∑ a : Fin N, g.inner x (W a) (e j) • W a) = e j := hW (e j)
    have h2 : g.inner x (e i) (e j) =
        ∑ a : Fin N, g.inner x (W a) (e j) * g.inner x (e i) (W a) := by
      conv_lhs => rw [← h1]
      rw [map_sum (g.inner x (e i)) (fun a : Fin N => g.inner x (W a) (e j) • W a)
        Finset.univ]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smul (g.inner x (e i)) (g.inner x (W a) (e j)) (W a), smul_eq_mul]
    rw [← horth i j, h2]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g.symm x (W a) (e j)]
    ring
  calc
    (∑ a : Fin N, B (W a) (W a))
        = ∑ a : Fin N, ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          conv_lhs => rw [← hexp (W a)]
          rw [map_sum B (fun i : Fin (Module.finrank ℝ E) => g.inner x (e i) (W a) • e i)
            Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [map_smul B (g.inner x (e i) (W a)) (e i), LinearMap.smul_apply]
          rw [map_sum (B (e i)) (fun j : Fin (Module.finrank ℝ E) =>
            g.inner x (e j) (W a) • e j) Finset.univ, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul (B (e i)) (g.inner x (e j) (W a)) (e j), smul_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_congr rfl (fun j _ => by
            rw [hdual i j, ite_smul, one_smul, zero_smul])]
          rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin (Module.finrank ℝ E))) i
            (fun j => B (e i) (e j))]
          simp

end DifferentialGeometry.Geometry.Connection

end
