import FailureOfSemipositiveMetricExtension.RelativeIncidenceSegreEquations
import FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! A genuine global scheme over `Spec ℂ[T]`: the reduced closed subscheme
of standard projective 47-space cut out by the explicit Segre and incidence
polynomials. Its complex homogeneous zero locus has already been identified
with the original analytic total space. Analytification comparison is separate. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Set

abbrev grading := homogeneousSubmodule Index Coefficient
instance grading_gradedAlgebra : GradedAlgebra grading := MvPolynomial.gradedAlgebra

def projectiveScheme : Scheme := Proj grading

def equationSet : Set PolynomialRing :=
  range (fun p : Index × Index => pivotPolynomial p.1 p.2) ∪
    range (fun p : Fin 4 × MissingIndex => incidencePolynomial p.1 p.2)

theorem equationSet_homogeneous (f : PolynomialRing) (hf : f ∈ equationSet) :
    ∃ d, IsHomogeneous f d := by
  rcases hf with ⟨⟨p,i⟩,rfl⟩ | ⟨⟨r,k⟩,rfl⟩
  · exact ⟨5,pivotPolynomial_homogeneous p i⟩
  · exact ⟨1,incidencePolynomial_homogeneous r k⟩

def closedLocus : Closeds projectiveScheme :=
  ⟨ProjectiveSpectrum.zeroLocus grading equationSet,ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

def vanishingIdealSheaf : projectiveScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal closedLocus

/-- The actual globally glued reduced induced scheme, including its structure sheaf. -/
abbrev incidenceScheme : Scheme := IdealSheafGluedSubscheme.scheme vanishingIdealSheaf

def incidenceInclusion : incidenceScheme ⟶ projectiveScheme :=
  IdealSheafGluedSubscheme.inclusion vanishingIdealSheaf

theorem incidenceInclusion_range : range incidenceInclusion.base = closedLocus := by
  rw [incidenceInclusion,IdealSheafGluedSubscheme.range_inclusion]
  rfl

theorem incidenceInclusion_injective : Function.Injective incidenceInclusion.base :=
  IdealSheafGluedSubscheme.inclusion_injective vanishingIdealSheaf

instance incidenceInclusion_surjectiveOnStalks : SurjectiveOnStalks incidenceInclusion :=
  IdealSheafGluedSubscheme.inclusion_surjectiveOnStalks vanishingIdealSheaf

/-- Coefficients have homogeneous degree zero, so the construction is relative over ℂ[T]. -/
def coefficientToDegreeZero : Coefficient →+* grading 0 where
  toFun c := ⟨C c,isHomogeneous_C Index c⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' a b := Subtype.ext (map_mul C a b)
  map_zero' := Subtype.ext (map_zero C)
  map_add' a b := Subtype.ext (map_add C a b)

def parameterScheme : Scheme := Spec (.of Coefficient)

def projectiveProjection : projectiveScheme ⟶ parameterScheme :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom coefficientToDegreeZero)

def incidenceProjection : incidenceScheme ⟶ parameterScheme :=
  incidenceInclusion ≫ projectiveProjection

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
