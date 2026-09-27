import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_mfderiv_radial_of_gradient_coordinate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {L : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (g : SmoothRiemannianMetric I M) (s : ∀ y : M, TangentSpace I y) (f : M → ℝ)
    (phi : PartialDiffeomorph (L.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    {K : Set N} {J : Set ℝ} (hKopen : IsOpen K) (hJopen : IsOpen J)
    (hsource : K ×ˢ J ⊆ phi.source)
    (hf : MDifferentiableOn I 𝓘(ℝ, ℝ) f phi.target)
    (hdf : ∀ y ∈ phi.target, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (hcoordinate : ∀ k ∈ K, ∀ t ∈ J, f (phi (k, t)) = t)
    (hradial : ∀ k ∈ K, ∀ t ∈ J, ∀ a : ℝ,
      mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t)
        (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (0, a)) =
        a • s (phi (k, t)))
    {k : N} (hk : k ∈ K) {t : ℝ} (ht : t ∈ J)
    (u : TangentSpace L k) (a b : ℝ) :
    g.inner (phi (k, t))
      (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t)
        (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (0, a)))
      (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t)
        (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (u, b))) = a * b := by
  have hkt : (k, t) ∈ phi.source := hsource ⟨hk, ht⟩
  have hy : phi (k, t) ∈ phi.target := phi.map_source hkt
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f (phi (k, t)) :=
    (hf _ hy).mdifferentiableAt (phi.open_target.mem_nhds hy)
  have hphiMD : MDifferentiableAt (L.prod 𝓘(ℝ, ℝ)) I phi (k, t) :=
    phi.mdifferentiableAt (by simp) hkt
  have heq : (f ∘ phi) =ᶠ[𝓝 (k, t)] (Prod.snd : N × ℝ → ℝ) := by
    filter_upwards [prod_mem_nhds (hKopen.mem_nhds hk) (hJopen.mem_nhds ht)] with z hz
    exact hcoordinate z.1 hz.1 z.2 hz.2
  have hd : mvfderiv (L.prod 𝓘(ℝ, ℝ)) (f ∘ phi) (k, t)
      (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (u, b)) = b := by
    change mfderiv (L.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ phi) (k, t) (u, b) = b
    rw [heq.mfderiv_eq, mfderiv_snd]
    rfl
  have hchain := mvfderiv_comp_apply (k, t) hfMD hphiMD
    (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (u, b))
  rw [hdf _ hy] at hchain
  have hpair : g.inner (phi (k, t)) (s (phi (k, t)))
      (mfderiv (L.prod 𝓘(ℝ, ℝ)) I phi (k, t)
        (show TangentSpace (L.prod 𝓘(ℝ, ℝ)) (k, t) from (u, b))) = b :=
    hchain.symm.trans hd
  rw [hradial k hk t ht a]
  simp only [map_smul, smul_apply, smul_eq_mul, hpair]

end DifferentialGeometry.Geometry.Connection
