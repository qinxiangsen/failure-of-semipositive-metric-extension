import FailureOfSemipositiveMetricExtension.RelativeIncidenceFunctorPoints
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! The globally glued closed incidence scheme is genuinely reduced, including
all sections of its structure sheaf, by its affine vanishing-ideal quotients. -/
namespace FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Set
universe u
variable {X : Scheme.{u}} (Z : Closeds X)

instance vanishingIdeal_localQuotient_reduced (U : X.affineOpens) :
    _root_.IsReduced (Γ(X,U.1) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- Every globally glued vanishing-ideal quotient is a reduced scheme. -/
instance vanishingIdeal_scheme_reduced :
    AlgebraicGeometry.IsReduced (scheme (Scheme.IdealSheafData.vanishingIdeal Z)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hlocal (U : X.affineOpens) : AlgebraicGeometry.IsReduced (I.glueDataObj U) := by
    change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X,U.1) ⧸ I.ideal U)))
    infer_instance
  have hstalk (x : scheme I) : _root_.IsReduced ((scheme I).presheaf.stalk x) := by
    obtain ⟨U,y,rfl⟩ := I.glueData.ι_jointly_surjective x
    haveI : AlgebraicGeometry.IsReduced (I.glueData.U U) := hlocal U
    haveI : _root_.IsReduced ((I.glueData.U U).presheaf.stalk y) :=
      AlgebraicGeometry.isReduced_stalk_of_isReduced (I.glueData.U U) y
    exact isReduced_of_injective ((I.glueData.ι U).stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso ((I.glueData.ι U).stalkMap y)).1
  letI := hstalk
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end
end FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
instance incidenceScheme_isReduced : AlgebraicGeometry.IsReduced incidenceScheme :=
  IdealSheafGluedSubscheme.vanishingIdeal_scheme_reduced closedLocus
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
