import FailureOfSemipositiveMetricExtension.RelativeIncidenceProjComparison

/-! Actual morphisms `Spec ℂ ⟶ Proj ℂ[T][Z]` associated to complex homogeneous
vectors, constructed through a nonzero homogeneous localization chart. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Set HomogeneousLocalization

abbrev complexScheme : Scheme := Spec (.of ℂ)

def complexFieldPoint : complexScheme := ⟨⊥,Ideal.bot_prime⟩

/-- Evaluation on the actual degree-zero homogeneous localization. -/
def chartEvaluation (t : ℂ) (z : Vector) (p : Index) (hp : z p ≠ 0) :
    Away grading (X p) →+* ℂ :=
  (Localization.awayLift (evaluationHom t z) (X p)
    (isUnit_iff_ne_zero.mpr (by simpa [evaluationHom] using hp))).comp
    (algebraMap (Away grading (X p)) (Localization.Away (X p)))

theorem chartEvaluation_mk (t : ℂ) (z : Vector) (p : Index) (hp : z p ≠ 0)
    (n : ℕ) (f : PolynomialRing) (hf : f ∈ grading (n • 1)) :
    chartEvaluation t z p hp (Away.mk grading (isHomogeneous_X Coefficient p) n f hf) =
      evaluate t z f / z p ^ n := by
  have hInv : evaluationHom t z (X p) * (z p)⁻¹ = 1 := by simp [evaluationHom,hp]
  change Localization.awayLift (evaluationHom t z) (X p)
    (isUnit_iff_exists_inv.mpr ⟨(z p)⁻¹,hInv⟩)
    (Localization.mk f ⟨X p ^ n,n,rfl⟩) = _
  rw [Localization.awayLift_mk (evaluationHom t z) (X p) f (z p)⁻¹ hInv n]
  simp [div_eq_mul_inv]

/-- The chart construction is a genuine scheme morphism, not just a map on points. -/
def projectiveFunctorPoint (t : ℂ) (z : Vector) (p : Index) (hp : z p ≠ 0) :
    complexScheme ⟶ projectiveScheme :=
  Spec.map (CommRingCat.ofHom (chartEvaluation t z p hp)) ≫
    Proj.awayι grading (X p) (isHomogeneous_X Coefficient p) (by decide : 0 < 1)

/-- Compatibility between mathlib's scheme and locally-ringed-space versions of
its standard Proj chart map. -/
theorem basicOpenToSpec_toLRSHom (f : PolynomialRing) :
    (Proj.basicOpenToSpec grading f).toLRSHom = ProjectiveSpectrum.Proj.toSpec grading f := by
  unfold ProjectiveSpectrum.Proj.toSpec
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec,Scheme.Opens.toSpecΓ]
  simp only [eqToHom_op,Category.assoc,← Spec.map_comp]
  rfl

theorem basicOpenToSpec_mk_mem (f : PolynomialRing)
    (x : (Proj.basicOpen grading f).toScheme)
    (a : NumDenSameDeg grading (Submonoid.powers f)) :
    HomogeneousLocalization.mk a ∈ ((Proj.basicOpenToSpec grading f).base x).asIdeal ↔
      a.num.val ∈ x.val.asHomogeneousIdeal := by
  change HomogeneousLocalization.mk a ∈
    (((Proj.basicOpenToSpec grading f).toLRSHom).base x).asIdeal ↔ _
  rw [basicOpenToSpec_toLRSHom]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply grading x a

/-- The point underlying the actual morphism is exactly the previously proved
homogeneous evaluation prime. -/
theorem projectiveFunctorPoint_base (t : ℂ) (z : Vector) (hz : z ≠ 0)
    (p : Index) (hp : z p ≠ 0) :
    (projectiveFunctorPoint t z p hp).base complexFieldPoint = evaluationPrime t z hz := by
  have hx : evaluationPrime t z hz ∈ Proj.basicOpen grading (X p) := by
    intro h
    exact hp (by simpa [evaluate] using
      (mem_evaluationPrime_iff t z hz (X p) (isHomogeneous_X Coefficient p)).mp h)
  let x : (Proj.basicOpen grading (X p)).toScheme := ⟨evaluationPrime t z hz,hx⟩
  let e := Proj.basicOpenIsoSpec grading (X p) (isHomogeneous_X Coefficient p) (by decide : 0 < 1)
  have hchart : e.hom.base x =
      (Spec.map (CommRingCat.ofHom (chartEvaluation t z p hp))).base complexFieldPoint := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    obtain ⟨n,f,hf,rfl⟩ := Away.mk_surjective grading (isHomogeneous_X Coefficient p) a
    change Away.mk grading (isHomogeneous_X Coefficient p) n f hf ∈ ((Proj.basicOpenToSpec grading (X p)).base x).asIdeal ↔ _
    rw [HomogeneousLocalization.Away.mk,basicOpenToSpec_mk_mem]
    change f ∈ (evaluationPrime t z hz).asHomogeneousIdeal ↔ chartEvaluation t z p hp (Away.mk grading (isHomogeneous_X Coefficient p) n f hf) = 0
    rw [mem_evaluationPrime_iff t z hz f hf,chartEvaluation_mk]
    simp only [div_eq_zero_iff,pow_ne_zero n hp,or_false]
  change ((e.inv ≫ (Proj.basicOpen grading (X p)).ι).base
    ((Spec.map (CommRingCat.ofHom (chartEvaluation t z p hp))).base complexFieldPoint)) = _
  rw [← hchart]
  change (e.hom ≫ e.inv ≫ (Proj.basicOpen grading (X p)).ι).base x = _
  rw [Iso.hom_inv_id_assoc]
  rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
