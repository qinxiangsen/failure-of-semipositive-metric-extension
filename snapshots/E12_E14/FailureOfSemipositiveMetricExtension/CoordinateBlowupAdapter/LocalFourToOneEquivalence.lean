import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.LocalFourToOne

namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.LocalReduction
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R] (t : R) (a : Fin 3) (r : Fin 4) (e : Fin 4 → Fin 2)

theorem many_local_coeff :
    (localToMany R t a r e).comp (coeffToLocal R t a r e) =
      algebraMap (Coeff R t a r e) (Many R t a r e) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (centreAvoidanceDenominator R t a r e))
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply, coeffToLocal_algebraMap]
  change localToMany R t a r e
    (algebraMap (SlopeRing R t a e) (Local R t a r e)
      (algebraMap (PairPolynomial R) (SlopeRing R t a e) f)) = _
  rw [localToMany_algebraMap, slopeToMany_coeff]
  rfl

theorem local_after_many :
    (localToMany R t a r e).comp (manyToLocal R t a r e) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro f
    change localToMany R t a r e
      (manyToLocal R t a r e (algebraMap (Coeff R t a r e) (Many R t a r e) f)) = _
    rw [manyToLocal_coeff]
    exact RingHom.congr_fun (many_local_coeff R t a r e) f
  · intro s
    simp only [RingHom.comp_apply, manyToLocal_X, localToMany_algebraMap,
      slopeToMany_X, RingHom.id_apply]

theorem many_after_local :
    (manyToLocal R t a r e).comp (localToMany R t a r e) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denom R t a r e))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro f
    simp only [RingHom.comp_apply, localToMany_algebraMap, RingHom.id_apply]
    change manyToLocal R t a r e
      (slopeToMany R t a r e (algebraMap (PairPolynomial R) (SlopeRing R t a e) f)) = _
    rw [slopeToMany_coeff]
    change manyToLocal R t a r e
      (algebraMap (Coeff R t a r e) (Many R t a r e)
        (algebraMap (PairPolynomial R) (Coeff R t a r e) f)) = _
    rw [manyToLocal_coeff, coeffToLocal_algebraMap]
    rfl
  · intro s
    simp only [RingHom.comp_apply, localToMany_algebraMap, slopeToMany_X,
      manyToLocal_X, RingHom.id_apply]

/-- Actual localization of SlopeRing, not a replacement quotient, is exactly
 the coefficient-localized four-relation presentation. -/
def localizationPresentationEquiv : Local R t a r e ≃+* Many R t a r e :=
  RingEquiv.ofHomInv (localToMany R t a r e) (manyToLocal R t a r e)
    (many_after_local R t a r e) (local_after_many R t a r e)

/-- Reuse the already accepted elimination, with its concrete inverses, after
checking the previously missing localization identity. -/
def actualLocalFourToOneEquiv : Local R t a r e ≃+* One R t a r e :=
  (localizationPresentationEquiv R t a r e).trans
    (centreDirectionEliminationEquiv R t a r e).toRingEquiv

@[simp] theorem actualLocalFourToOneEquiv_coeff (f : PairPolynomial R) :
    actualLocalFourToOneEquiv R t a r e
      (algebraMap (SlopeRing R t a e) (Local R t a r e)
        (algebraMap (PairPolynomial R) (SlopeRing R t a e) f)) =
      algebraMap (Coeff R t a r e) (One R t a r e)
        (algebraMap (PairPolynomial R) (Coeff R t a r e) f) := by
  change (Data R t a r e).eliminationEquiv
    (localToMany R t a r e (algebraMap (SlopeRing R t a e) (Local R t a r e)
      (algebraMap (PairPolynomial R) (SlopeRing R t a e) f))) = _
  rw [localToMany_algebraMap, slopeToMany_coeff]
  exact (Data R t a r e).eliminationEquiv.commutes _

@[simp] theorem actualLocalFourToOneEquiv_selected :
    actualLocalFourToOneEquiv R t a r e
      (algebraMap (SlopeRing R t a e) (Local R t a r e) (Ideal.Quotient.mk _ (X r))) =
      Ideal.Quotient.mk _ (X 0) := by
  change (Data R t a r e).eliminationEquiv
    (localToMany R t a r e (algebraMap (SlopeRing R t a e) (Local R t a r e)
      (Ideal.Quotient.mk _ (X r)))) = _
  rw [localToMany_algebraMap, slopeToMany_X]
  exact (Data R t a r e).eliminationEquiv_selected

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.LocalReduction
