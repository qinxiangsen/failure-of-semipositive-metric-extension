import FailureOfSemipositiveMetricExtension.HisamotoCompactSurface
import FailureOfSemipositiveMetricExtension.HisamotoTensorIsomorphism
import FailureOfSemipositiveMetricExtension.HisamotoHyperplaneBundle
import FailureOfSemipositiveMetricExtension.HisamotoExceptionalSection

/-! The local conclusion in the paper's discussion of Hisamoto Example 4.12.
All geometric objects here are the actual one-point incidence surface, its
strict transform, native tensor/pullback bundles, and tangent-quotient normal.
No product-neighbourhood, trivial normal, or bundle-isomorphism premise occurs. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set
open scoped Manifold ContDiff

/-- The compact actual surface has its usual affine blowup chart at the centre,
and blowdown is an analytic isomorphism on the complement. -/
theorem actual_compact_blowup_certificate :
    CompactSpace Point ∧
      Topology.IsClosedEmbedding (Subtype.val : Point → Ambient) ∧
      centreAffine ∪ awayCentre = univ ∧
      ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω blowdown awayCentre ∧
      ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω liftPlane puncturedPlane :=
  ⟨inferInstance,incidence_inclusion_isClosedEmbedding,standard_blowup_open_cover,
    blowdownComplement_analytic⟩

/-- Every semipositive metric on the degree-two restriction extends over an
actual open product-disc neighbourhood of the entire strict transform. The
ambient (2,-1) bundle is separately identified with the true H tensor O(E). -/
theorem hisamoto_example_4_12_local_extension (i : Fin 2) (t : ℂ) (r : ℝ) (hr : 0 < r)
    (h : LineBundle.FibreMetric 2 (-1) i t) (hh : h.Semipositive) :
    IsOpen (discNeighbourhood i t r) ∧
      strictTransform (ProjectiveLine.param i t) ⊆ discNeighbourhood i t r ∧
      Nonempty ((Direction × Disc t r) ≃ₜ discNeighbourhood i t r) ∧
      Nonempty (LineBundle.SourceTotal 2 (-1) i ≃ₜ LineBundle.TargetTotal 2) ∧
      Nonempty (RulingNormal.NormalTotal i t ≃ₜ (ProjectiveLineBundle.core 0).TotalSpace) ∧
      ∃ H : LineBundle.NeighbourhoodMetric 2 (-1) i, H.Semipositive ∧
        ∀ j p, H.weight j (localParam i (p,t)) = h.weight j p := by
  refine ⟨discNeighbourhood_isOpen i t r,?_,⟨discProductHomeomorph i t r⟩,
    ⟨LineBundle.hisamotoBundleHomeomorph i⟩,⟨RulingNormal.normalBundleHomeomorph i t⟩,
    LineBundle.hisamoto_every_semipositive_metric_extends i t h hh⟩
  rw [strictTransform_eq_ruling_fibre]
  intro q hq
  exact whole_fibre_mem_discNeighbourhood i t r hr ⟨q,hq⟩

/-- The geometric naming of L: H is a genuine blowdown pullback, E is cut out
simply by a global analytic section, and H tensor O(E) is native bidegree (2,-1). -/
theorem hisamoto_line_bundle_certificate :
    Nonempty ((LineBundle.core 1 0).TotalSpace ≃ₜ LineBundle.HyperplaneTotal 1) ∧
      Nonempty (LineBundle.TensorTotal ≃ₜ (LineBundle.core 2 (-1)).TotalSpace) ∧
      ContMDiff 𝓘(ℂ,Coord) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω exceptionalSectionMap ∧
      (∀ q, exceptionalSection q = 0 ↔ q ∈ exceptionalSet) ∧
      ∀ i q, (LineBundle.core 1 (-1)).localTriv (i,0)
        (exceptionalSectionMap (affineParam i 0 q)) = (affineParam i 0 q,q.1) :=
  ⟨⟨LineBundle.hyperplaneBundleHomeomorph 1⟩,⟨LineBundle.tensorBundleHomeomorph⟩,
    exceptionalSection_analytic,exceptionalSection_zero_iff,exceptionalSection_reduced_local⟩

end
end FailureOfSemipositiveMetricExtension.Hisamoto
