import FailureOfSemipositiveMetricExtension.RelativeIncidenceProj
import FailureOfSemipositiveMetricExtension.IdealSheafClosedImmersion

/-! Complex homogeneous vectors determine actual relevant homogeneous prime ideals
in the projective scheme. The explicit incidence equations agree at these genuine
scheme points with the original complex manifold's incidence predicate. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Set

instance incidenceInclusion_isClosedImmersion : IsClosedImmersion incidenceInclusion :=
  IdealSheafGluedSubscheme.inclusion_isClosedImmersion vanishingIdealSheaf

def evaluationHom (t : ℂ) (z : Vector) : PolynomialRing →+* ℂ :=
  eval₂Hom (Polynomial.evalRingHom t) z

@[simp] theorem evaluationHom_apply (t : ℂ) (z : Vector) (f : PolynomialRing) :
    evaluationHom t z f = evaluate t z f := rfl

/-- The prime of a complex homogeneous point is the homogeneous core of its
ordinary evaluation kernel; no continuous global representative is used. -/
def evaluationPrime (t : ℂ) (z : Vector) (hz : z ≠ 0) : projectiveScheme where
  asHomogeneousIdeal := (RingHom.ker (evaluationHom t z)).homogeneousCore grading
  isPrime := (RingHom.ker_isPrime (evaluationHom t z)).homogeneousCore (𝒜 := grading)
  not_irrelevant_le := by
    intro h
    have hex : ∃ i, z i ≠ 0 := by contrapose! hz; exact funext hz
    obtain ⟨i,hi⟩ := hex
    have hX : (X i : PolynomialRing) ∈ HomogeneousIdeal.irrelevant grading := by
      rw [HomogeneousIdeal.mem_irrelevant_iff,GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne grading (isHomogeneous_X Coefficient i) (by decide : 1 ≠ 0)
    have he := Ideal.toIdeal_homogeneousCore_le grading (RingHom.ker (evaluationHom t z)) (h hX)
    exact hi (by simpa [RingHom.mem_ker,evaluationHom,evaluate] using he)

theorem mem_evaluationPrime_iff (t : ℂ) (z : Vector) (hz : z ≠ 0)
    (f : PolynomialRing) {d : ℕ} (hf : IsHomogeneous f d) :
    f ∈ (evaluationPrime t z hz).asHomogeneousIdeal ↔ evaluate t z f = 0 := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le grading (RingHom.ker (evaluationHom t z)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d,hf⟩ h

theorem evaluationPrime_mem_closedLocus_iff (t : ℂ) (z : Vector) (hz : z ≠ 0) :
    evaluationPrime t z hz ∈ closedLocus ↔
      (∀ p i, evaluate t z (pivotPolynomial p i) = 0) ∧
      (∀ r k, evaluate t z (incidencePolynomial r k) = 0) := by
  change equationSet ⊆ (evaluationPrime t z hz).asHomogeneousIdeal ↔ _
  constructor
  · intro h
    constructor
    · intro p i
      exact (mem_evaluationPrime_iff t z hz _ (pivotPolynomial_homogeneous p i)).mp
        (h (Or.inl ⟨(p,i),rfl⟩))
    · intro r k
      exact (mem_evaluationPrime_iff t z hz _ (incidencePolynomial_homogeneous r k)).mp
        (h (Or.inr ⟨(r,k),rfl⟩))
  · rintro ⟨hp,hi⟩ f (⟨⟨p,i⟩,rfl⟩ | ⟨⟨r,k⟩,rfl⟩)
    · exact (mem_evaluationPrime_iff t z hz _ (pivotPolynomial_homogeneous p i)).mpr (hp p i)
    · exact (mem_evaluationPrime_iff t z hz _ (incidencePolynomial_homogeneous r k)).mpr (hi r k)

/-- Membership in the scheme's actual closed support is precisely membership
in the genuine Segre image of the original total space. -/
theorem evaluationPrime_mem_range_incidenceInclusion_iff (t : ℂ) (z : Vector) (hz : z ≠ 0) :
    evaluationPrime t z hz ∈ range incidenceInclusion.base ↔
      (Projectivization.mk ℂ z hz,t) ∈ range relativePoint := by
  rw [incidenceInclusion_range]
  change evaluationPrime t z hz ∈ closedLocus ↔ _
  rw [evaluationPrime_mem_closedLocus_iff,mk_mem_range_relativePoint_iff]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
