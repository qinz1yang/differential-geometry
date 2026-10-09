import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyTransfer

/-!
# CP1-D5: the ambient-homeomorphism interface for CP1-D4

A jointly smooth family `F` of embeddings of (a neighbourhood of) a compact set `K` into a fixed
manifold `P`, together with open embeddings `ιₛ : P → Yₛ`, `ιₜ : P → Yₜ` into the ambient spaces
at two times and a homeomorphism `e : Yₛ ≃ₜ Yₜ` compatible with them, gives a homeomorphism
`Φ : Yₛ ≃ₜ Yₜ` carrying `fₛ x = ιₛ (F (s, x))` to `fₜ x = ιₜ (F (t, x))` for `x ∈ K`.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function
noncomputable section
namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]

theorem exists_ambient_homeo_of_smooth_family_CPD5 [T2Space P] [SigmaCompactSpace P]
    {F : ℝ × N → P} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    (hinj : ∀ t ∈ J, InjOn (fun y => F (t, y)) K)
    {Ys Yt : Type*} [TopologicalSpace Ys] [TopologicalSpace Yt] [T2Space Ys]
    {ιs : P → Ys} {ιt : P → Yt} (hιs : Topology.IsOpenEmbedding ιs) (e : Ys ≃ₜ Yt)
    (he : ∀ p, e (ιs p) = ιt p) (fs : N → Ys) (ft : N → Yt) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hfs : ∀ x ∈ K, fs x = ιs (F (s, x))) (hft : ∀ x ∈ K, ft x = ιt (F (t, x))) :
    ∃ Φ : Ys ≃ₜ Yt, ∀ x ∈ K, Φ (fs x) = ft x := by
  obtain ⟨Ψ, C, hCc, hsm, hself, hcoc, hsupp, hmap⟩ :=
    exists_ambient_isotopy_of_smooth_family_CPD5 hJ hU hK hKU hab hJab hF himm hinj
  let ψ : P ≃ₜ P := isotopyHomeo_CPD5 Ψ hsm.continuous hself hcoc s t
  obtain ⟨ψ', hψ', -⟩ := exists_homeo_extension_CPD5 hιs hCc ψ (fun x hx => hsupp s t x hx)
  refine ⟨ψ'.trans e, fun x hx => ?_⟩
  change e (ψ' (fs x)) = ft x
  rw [hfs x hx, hψ', he, hft x hx]
  exact congrArg ιt (hmap s hs t ht x hx)

end GC.LongTime.CuspP1
